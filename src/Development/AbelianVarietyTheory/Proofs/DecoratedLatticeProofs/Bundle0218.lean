import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0196
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Formalism.LocalRingCardinality.Bundle0003
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0197
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0134
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicMatrixRealSizeBoundsAlongRealParametrisatiStatement
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
theorem _root_.GlobalTheory.T.adelicMatrixRealSize_bounds_along_real_parametrisation : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (m n k : ℕ) (L : (Fin k → ℝ) →+ Mx D m n), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsRealParam L → (∃ C : ℝ, ∀ t, GlobalTheory.Unf.realSize θ (L t) ≤ C * ‖t‖) ∧ (Function.Injective L → ∃ C : ℝ, ∀ (x : Mx D m n) t, ‖t‖ ≤ C * (GlobalTheory.Unf.realSize θ (x + L t) + GlobalTheory.Unf.realSize θ x)) := by
  first | exact @GlobalTheory.Unf.realParam_size_bounds | exact GlobalTheory.Unf.realParam_size_bounds | (intros; apply GlobalTheory.Unf.realParam_size_bounds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AmplitudeSchurBoundUniformConstantsStatement
section
open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.amplitudeSchurBound_uniform_constants : ∀ Cg cb Cu cT CT C1 : ℝ, ∃ C₀ : ℝ, ∀ C ≥ C₀, ∃ m₀ : ℝ, ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl C0 : ℝ), Big D large₂ Cl m₀ → cdScaleTie D → BSch D large₂ C' Cl Cg cb Cu cT CT C0 → LocIn D large₂ C' Cl Cg cb Cu cT CT C0 → SchurSt D large₂ C' Cl Cg cb Cu cT CT C0 C1 C := by
  first | exact @GlobalTheory.Amp.schurSt_of_big_tie_uniform | exact GlobalTheory.Amp.schurSt_of_big_tie_uniform | (intros; apply GlobalTheory.Amp.schurSt_of_big_tie_uniform <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselColumnFormCentralTranslationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_column_form_central_translation : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A) (hK : X.LevelSubgroupCharacter) (a : GA D A), GlobalTheory.Core.Mi.IdE X → a ∈ GfC A → a ∈ Subgroup.center (GA D A) → ∃ R : Cu X u hK →ₗ[ℂ] Cu X u hK, Function.Injective R ∧ ∀ (T : Cu X u hK) ξ, B.colForm (R T).1 ξ = rTrans a (B.colForm T.1 ξ) := by
  first | exact @GlobalTheory.Core.Mi.central_acts_on_columns | exact GlobalTheory.Core.Mi.central_acts_on_columns | (intros; apply GlobalTheory.Core.Mi.central_acts_on_columns <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineContractionThetaFunctionIsLocalModel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped Topology

namespace GlobalTheory.ContrModL

section SlopeTestRemainingChoices
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)

theorem ι_mul_incA (x : k) (b : D.host.E) : p.ι x * incA D b = p.ι (x * p.pr b) := by
  have hm : ∀ x y, p.ι (x * y) = p.ι x * p.ι y := fun x y => by
    conv_lhs => rw [← p.π_ι x, ← p.π_ι y, ← RingHom.map_mul, p.ι_π, ← mul_assoc, Witness.e_ι]
  rw [hm]
  change _ = p.ι x * p.ι (p.π (incA D b))
  rw [p.ι_π, ← mul_assoc, mul_comm (p.ι x) p.e, Witness.e_ι]

theorem map_ι_mul_rat {a b c : Type} [Fintype b] (M : Matrix a b k) (N : Matrix b c D.host.E) :
    M.map p.ι * N.map (incA D) = (M * N.map p.pr).map p.ι := by
  ext i j
  simp [Matrix.mul_apply, ι_mul_incA, map_sum]

theorem map_pr_eq {a b : Type} (M : Matrix a b D.host.E) : M.map p.pr = M.map (Witness.prH p) := rfl

variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem core_iA {ρ : ℕ} (B : BesLev D ρ) {s : k} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) : F₀.γ * B.o.iA.map p.pr = fromRows FA.γ (0 : Matrix Unit (Fin B.A.rank) k) := by
  have hβ : B.o.iA.map p.pr * FA.β = F₀.β * fromRows (1 : Matrix n' n' k) (0 : Matrix Unit n' k) := by
    ext r a
    rw [← h.1 r a]
    simp [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply]
  calc F₀.γ * B.o.iA.map p.pr = F₀.γ * (B.o.iA.map p.pr * FA.β) * FA.γ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, FA.βγ, Matrix.mul_one]
    _ = fromRows FA.γ 0 := by
        rw [hβ, ← Matrix.mul_assoc, F₀.γβ, Matrix.one_mul, fromRows_mul, Matrix.one_mul, Matrix.zero_mul]

theorem core_qA {ρ : ℕ} (B : BesLev D ρ) {s : k} (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit))
    (h : p.IsCoreFrame B s FA F₀) :
    FA.γ * B.o.qA.map p.pr * F₀.β = fromCols (1 : Matrix n' n' k) (0 : Matrix n' Unit k) := by
  have hA : FA.γ * B.o.qA.map p.pr * (B.o.iA.map p.pr * FA.β) = 1 := by
    rw [map_pr_eq, map_pr_eq, Matrix.mul_assoc, ← Matrix.mul_assoc (B.o.qA.map _), ← Matrix.map_mul, B.o.qA_iA,
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul, FA.γβ]
  have hB : FA.γ * B.o.qA.map p.pr * B.o.iB.map p.pr = 0 := by
    rw [map_pr_eq, map_pr_eq, Matrix.mul_assoc, ← Matrix.map_mul, B.o.qA_iB, Matrix.map_zero _ (map_zero _),
      Matrix.mul_zero]
  have hc : ∀ r, F₀.β r (Sum.inr ()) = s * ((B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c))) r := by
    intro r
    rw [h.2 r, vecB, map_pr_eq]
    congr 1
    exact (RingHom.map_mulVec (Witness.prH p) B.o.iB B.ζ r)
  have hv : (FA.γ * B.o.qA.map p.pr) *ᵥ ((B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c))) = 0 := by
    rw [Matrix.mulVec_mulVec, hB, Matrix.zero_mulVec]
  generalize (B.o.iB.map p.pr) *ᵥ (fun c => p.pr (B.ζ c)) = v at hc hv
  generalize FA.γ * B.o.qA.map p.pr = X at hA hv ⊢
  ext i (a | u)
  · have := congrFun (congrFun hA i) a
    rw [Matrix.mul_apply] at this
    rw [Matrix.mul_apply, fromCols_apply_inl, ← this]
    simp only [h.1]
  · rw [Matrix.mul_apply, fromCols_apply_inr, Matrix.zero_apply]
    simp only [hc, mul_left_comm _ s, ← Finset.mul_sum]
    have h2 := congrFun hv i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at h2
    rw [h2, mul_zero]

end SlopeTestRemainingChoices
end GlobalTheory.ContrModL

namespace GlobalTheory.ContrModL

section Up
variable {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  (p : Place D k)
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']

theorem up_fromCols {ρ : ℕ} (B : BesLev D ρ) {s : k} (S : HSp D) (FA : Frame k B.A.rank n')
    (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (h : p.IsCoreFrame B s FA F₀) (x : Matrix n n' k) :
    p.up F₀ FS (fromCols x (0 : Matrix n Unit k)) = (B.o.resS S).symm (p.up FA FS x, 0) := by
  have hX : FA.γ * B.o.qA.map p.pr = fromCols (1 : Matrix n' n' k) (0 : Matrix n' Unit k) * F₀.γ := by
    rw [← core_qA p B FA F₀ h, Matrix.mul_assoc _ F₀.β, F₀.βγ, Matrix.mul_one]
  have hx : fromCols x (0 : Matrix n Unit k) = x * fromCols (1 : Matrix n' n' k) (0 : Matrix n' Unit k) := by
    rw [Matrix.mul_fromCols, Matrix.mul_one, Matrix.mul_zero]
  rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, Place.up, Place.up, OrthDec.pA, rat, map_ι_mul_rat, Matrix.mul_assoc (FS.β * x), hX, hx]
  simp only [Matrix.mul_assoc]

theorem up_jA {ρ : ℕ} (B : BesLev D ρ) {s : k} (S : HSp D) (FA : Frame k B.A.rank n')
    (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n) (h : p.IsCoreFrame B s FA F₀)
    (t : Matrix n (n' ⊕ Unit) k) : p.up F₀ FS t ⬝ B.o.jA = p.up FA FS t.toCols₁ := by
  rw [Place.up, Place.up, OrthDec.jA, rat, map_ι_mul_rat, Matrix.mul_assoc _ F₀.γ, core_iA p B FA F₀ h]
  conv_lhs => rw [← fromCols_toCols t]
  rw [Matrix.mul_assoc, fromCols_mul_fromRows, Matrix.mul_zero, add_zero, ← Matrix.mul_assoc]

end Up

section Pass
variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ)

theorem symplOH_zero_r {S T : HSp D} (x : WO S T) : symplOH S T x 0 = 0 := by
  have : hO S T x 0 = 0 := by simp [hO]
  simp [symplOH, symplO, this]

theorem heis_pass {V A L : HSp D} (o : OrthDec V A L) (S : HSp D) (f : WO V S → ℂ) (a u : WO A S) (z : WO L S) :
    heisO ψ V S ((o.resS S).symm (a, 0)) f ((o.resS S).symm (u, z)) =
      ψ (symplOH A S u a) * f ((o.resS S).symm (u + a, z)) := by
  simp only [heisO]
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_r, add_zero,
    ← map_add, Prod.mk_add_mk, add_zero]

end Pass

end GlobalTheory.ContrModL

namespace GlobalTheory.ContrModL

theorem contr_isModel : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (FA : Frame k B.A.rank n') (F₀ : Frame k B.V₀.rank (n' ⊕ Unit)) (FS : Frame k S.rank n), p.IsCoreFrame B s FA F₀ → ∀ (T₁ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] (WO B.V₀ S → ℂ)), p.IsModel ψ F₀ FS T₁ → ∀ (φ₀ : SB (n → k)) (Ξ₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ S B'.V₀ Ξ₂ → ∀ (v : WO S B'.A) (T : SB (Matrix n n' k) →ₗ[ℂ] (WO B.A S → ℂ)), (∀ Ξ₁ u, T Ξ₁ u = GlobalTheory.Unf.contr l S vL (T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Ξ₁)) Ξ₂ u v) → p.IsModel ψ FA FS T := by
  intro D k _ _ _ _ p ψ hψ ρ σ B B' l S vL s hs n n' _ _ _ _ FA F₀ FS hcore T₁ hT₁ φ₀ Ξ₂ hΞ₂ v T hT

  have pass : ∀ (a : WO B.A S) (Φ Φ' : SB (Matrix n n' k)),
      T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Φ') =
        heisO ψ B.V₀ S ((B.o.resS S).symm (a, 0)) (T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Φ)) →
      T Φ' = heisO ψ B.A S a (T Φ) := by
    intro a Φ Φ' e
    funext u
    rw [hT Φ' u, e]
    change _ = ψ (symplOH B.A S u a) * T Φ (u + a)
    rw [hT Φ (u + a)]
    unfold GlobalTheory.Unf.contr
    rw [← integral_const_mul]
    refine congrArg (fun f : WO S B'.L → ℂ => ∫ w in vL.𝓕, f w ∂vL.μ) (funext fun w => ?_)
    rw [heis_pass]
    ring
  refine ⟨fun Φ => ?_, fun x Φ Φ' e => ?_, fun y hy Φ Φ' e => ?_⟩
  ·
    haveI : ∀ m n, BorelSpace (Mx D m n) := fun _ _ => ⟨rfl⟩
    haveI : IsFiniteMeasure (vL.μ.restrict vL.𝓕) :=
      ⟨by rw [Measure.restrict_apply_univ, vL.covol.2.2]; exact ENNReal.one_lt_top⟩
    obtain ⟨C₂, hC₂⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded _ _ ψ hψ Ξ₂ hΞ₂
    have hc : Continuous fun w => Ξ₂ ((B'.o.resT S).symm (v, w)) :=
      hΞ₂.cont.comp ((OrthDec.continuous_resT_symm _ _).comp (Continuous.prodMk continuous_const continuous_id))
    have hint : Integrable (fun w => Ξ₂ ((B'.o.resT S).symm (v, w))) (vL.μ.restrict vL.𝓕) :=
      (integrable_const C₂).mono' hc.aestronglyMeasurable (ae_of_all _ fun w => hC₂ _)
    have h := GlobalTheory.SuperposS.superpos_isTheta D ψ hψ B.V₀ B.A B.L S B.o (T₁ (GlobalTheory.ContractionLocal.colTens φ₀ Φ))
      (hT₁.theta _) (WO S B'.L) (vL.μ.restrict vL.𝓕) (l.κ S) (fun w => Ξ₂ ((B'.o.resT S).symm (v, w)))
      (GlobalTheory.ContractionLocal.continuous_kappa l S).measurable hint
    convert h using 1
    funext u
    rw [hT]
    rfl
  ·
    refine pass (p.up FA FS x) Φ Φ' ?_
    rw [← up_fromCols p B S FA F₀ FS hcore x]
    refine hT₁.trans _ _ _ fun t => ?_
    have h1 : (t + fromCols x (0 : Matrix n Unit k)).toCols₁ = t.toCols₁ + x := by
      ext i j; simp [Matrix.toCols₁]
    have h2 : (fun r => (t + fromCols x (0 : Matrix n Unit k)) r (Sum.inr ())) = fun r => t r (Sum.inr ()) := by
      funext r; simp
    simp only [GlobalTheory.ContractionLocal.colTens_apply, e, h1, h2]
  ·
    refine pass y Φ Φ' (hT₁.modul _ ?_ _ _ fun t => ?_)
    · intro i j
      rw [OrthDec.resS_symm_apply, Matrix.zero_mul, add_zero, Matrix.mul_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [← mul_assoc, hy i c]
    · simp only [GlobalTheory.ContractionLocal.colTens_apply, e]
      rw [B.o.symplO_resS S (p.up F₀ FS t), AddEquiv.apply_symm_apply]
      rw [OrthDec.resS_apply B.o S (p.up F₀ FS t)]
      simp only
      rw [up_jA p B S FA F₀ FS hcore t]
      have : symplO B.L S (p.up F₀ FS t ⬝ B.o.jB) 0 = 0 := by
        have h0 : hO B.L S (p.up F₀ FS t ⬝ B.o.jB) 0 = 0 := by simp [hO]
        simp [symplO, h0]
      simp only [this, add_zero]
      ring

end GlobalTheory.ContrModL

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselPeriodRightTranslationInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bessel_period_right_translation_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (φ : GA D B.A → ℂ) (f : GA D B.V → ℂ) (a : GA D B.A), IsStdChar D ψ (-1) → IsContAut B.A φ → IsContAut B.V f → B.per ψ (rTrans a φ) (rTrans (embA B.d B.o a) f) = B.per ψ φ f := by
  first | exact @GlobalTheory.Core.Mi.per_rTrans | exact GlobalTheory.Core.Mi.per_rTrans | (intros; apply GlobalTheory.Core.Mi.per_rTrans <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockMatrixTwoByTwoFinStandardSkewMap
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StdUnn.Frame

section Generic
variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

theorem submatrix_fromBlocks_mul (a b c d a' b' c' d' : Matrix (Fin n) (Fin n) R) :
    blk4 a b c d * blk4 a' b' c' d' =
      blk4 (a * a' + b * c') (a * b' + b * d') (c * a' + d * c') (c * b' + d * d') := by
  unfold blk4
  rw [Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

theorem block_matrix_one : blk4 (1 : Matrix (Fin n) (Fin n) R) 0 0 1 = 1 := by
  unfold blk4
  rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

theorem blockMatrixTwoByTwoFin_smul (r : R) (a b c d : Matrix (Fin n) (Fin n) R) :
    r • blk4 a b c d = blk4 (r • a) (r • b) (r • c) (r • d) := by
  unfold blk4
  rw [← Matrix.fromBlocks_smul]; rfl

theorem block_matrix_map (f : R → S) (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d).map f = blk4 (a.map f) (b.map f) (c.map f) (d.map f) := by
  unfold blk4
  rw [← Matrix.fromBlocks_map]; rfl

theorem blockMatrixTwoByTwoFin_transpose (a b c d : Matrix (Fin n) (Fin n) R) :
    (blk4 a b c d)ᵀ = blk4 aᵀ cᵀ bᵀ dᵀ := by
  unfold blk4
  rw [← Matrix.fromBlocks_transpose]; rfl

theorem blockMatrixTwoByTwoFin_forall_entries (p : R → Prop) {a b c d : Matrix (Fin n) (Fin n) R} (ha : ∀ i j, p (a i j)) (hb : ∀ i j, p (b i j))
    (hc : ∀ i j, p (c i j)) (hd : ∀ i j, p (d i j)) (i j : Fin (n + n)) : p (blk4 a b c d i j) := by
  unfold blk4
  rw [Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j
  exacts [ha i j, hb i j, hc i j, hd i j]

theorem map_smul_hom (f : R →+* S) {m : Type} (r : R) (a : Matrix m m R) : (r • a).map f = f r • a.map f := by
  ext i j; simp

def frm (K : Matrix (Fin n) (Fin n) R) (e t t' : R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  blk4 1 ((e * t) • K) 1 ((-(e * t')) • K)

def frmInv (H : Matrix (Fin n) (Fin n) R) (e' t t' : R) : Matrix (Fin (n + n)) (Fin (n + n)) R :=
  blk4 (t' • 1) (t • 1) (e' • H) ((-e') • H)

variable {H K : Matrix (Fin n) (Fin n) R} {e e' t t' : R}

theorem frm_mul_inv (hKH : K * H = 1) (he : e * e' = 1) (ht : t + t' = 1) :
    frm K e t t' * frmInv H e' t t' = 1 := by
  unfold frm frmInv
  rw [submatrix_fromBlocks_mul, ← block_matrix_one]
  simp only [Matrix.smul_mul, Matrix.mul_smul, hKH, Matrix.one_mul, smul_smul, ← add_smul]
  congr 1
  · rw [show t' + e' * (e * t) = 1 by linear_combination ht + t * he, one_smul]
  · rw [show t + -e' * (e * t) = 0 by linear_combination (-t) * he, zero_smul]
  · rw [show t' + e' * (-(e * t')) = 0 by linear_combination (-t') * he, zero_smul]
  · rw [show t + -e' * (-(e * t')) = 1 by linear_combination ht + t' * he, one_smul]

theorem adj_frm (c : R →+* R) (hK : (K.map c)ᵀ = K) (hct : c t = t') (hct' : c t' = t) :
    ((frm K e t t').map c)ᵀ = blk4 1 1 ((c e * t') • K) ((-(c e * t)) • K) := by
  unfold frm
  rw [block_matrix_map, blockMatrixTwoByTwoFin_transpose, map_smul_hom, map_smul_hom, Matrix.transpose_smul, Matrix.transpose_smul, hK,
    Matrix.map_one _ c.map_zero c.map_one, Matrix.transpose_one, map_neg, map_mul, map_mul, hct, hct']

theorem gram_frm (ce : R) (hKH : K * H = 1) (hHK : H * K = 1) (ht : t + t' = 1) :
    blk4 1 1 ((ce * t') • K) ((-(ce * t)) • K) * blk4 H 0 0 (-H) * frm K e t t' = blk4 0 (e • 1) (ce • 1) 0 := by
  unfold frm
  rw [submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, hKH, hHK, Matrix.one_mul, Matrix.mul_one, Matrix.mul_zero, add_zero,
    zero_add, Matrix.mul_neg, Matrix.neg_mul, smul_neg, ← neg_smul, smul_smul, ← add_smul]
  congr 1
  · simp
  · congr 1; linear_combination e * ht
  · congr 1; linear_combination ce * ht
  · convert zero_smul R K using 2; ring

theorem norm_frm (ce : R) (f : R →+* S) (hK : (K * K).map f = 1) (ht : t + t' = 1) (h2 : f (2 * t) = 1)
    (h4 : f (e * ce) = 4) :
    (blk4 1 1 ((ce * t') • K) ((-(ce * t)) • K) * frm K e t t').map f = (2 : S) • 1 := by
  unfold frm
  have ht' : f t + f t' = 1 := by rw [← map_add, ht, map_one]
  have h2' : 2 * f t = 1 := by rw [← h2, map_mul, map_ofNat]
  rw [map_mul] at h4
  rw [submatrix_fromBlocks_mul, ← block_matrix_one, blockMatrixTwoByTwoFin_smul]
  simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul, ← add_smul]
  rw [block_matrix_map, map_smul_hom, map_smul_hom, map_smul_hom, hK, smul_zero]
  congr 1
  · rw [← two_smul R, map_smul_hom, Matrix.map_one _ f.map_zero f.map_one, map_ofNat]
  · convert zero_smul S _ using 2
    simp only [map_add, map_neg, map_mul]
    linear_combination f e * h2' - f e * ht'
  · convert zero_smul S _ using 2
    simp only [map_add, map_neg, map_mul]
    linear_combination f ce * ht' - f ce * h2'
  · congr 1
    simp only [map_add, map_neg, map_mul]
    linear_combination (2 * f t * f t') * h4 + (8 * f t) * ht' + (2 - 4 * f t) * h2'

theorem exists_frame_ring (c : R →+* R) (hc : ∀ x, c (c x) = x) (p : R → Prop) (p0 : p 0) (p1 : p 1)
    (pmul : ∀ {x y}, p x → p y → p (x * y)) (pneg : ∀ {x}, p x → p (-x)) (pc : ∀ {x}, p x → p (c x))
    (Hm : GL (Fin n) R) (hH' : (Hm.1.map c)ᵀ = Hm.1) (hI1 : ∀ i j, p (Hm.1 i j)) (hI2 : ∀ i j, p ((Hm⁻¹).1 i j))
    (m : R) (hm : c m = -m) (u ε : Rˣ) (t : R) (hs1 : (ε : R) * u * c u = m) (hs2 : p ε) (hs3 : p (ε⁻¹ : Rˣ))
    (ht1 : t + c t = 1) (ht2 : p t) :
    ∃ M M' : GL (Fin (n + n)) R, (M.1.map c)ᵀ * blk4 Hm.1 0 0 (-Hm.1) * M.1 = m • blk4 0 1 (-1) 0 ∧
      (∀ i j : Fin n, M.1 (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n)) =
        M.1 (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n))) ∧
      ((∀ i j, p (M'.1 i j)) ∧ ∀ i j, p ((M'⁻¹).1 i j)) ∧ M.1 = (u : R) • M'.1 ∧
      ∀ (S : Type) [CommRing S] (f : R →+* S), (Hm.1 * Hm.1).map f = 1 → f (ε * c ε) = 4 → f (2 * t) = 1 →
        ((M.1.map c)ᵀ * M.1).map f = f (2 * u * c u) • 1 := by
  have hKH : (Hm⁻¹).1 * Hm.1 = 1 := Units.inv_mul Hm
  have hHK : Hm.1 * (Hm⁻¹).1 = 1 := Units.mul_inv Hm
  generalize (Hm⁻¹).1 = K at hKH hHK hI2
  have pone : ∀ i j : Fin n, p ((1 : Matrix (Fin n) (Fin n) R) i j) := fun i j => by
    rw [Matrix.one_apply]
    split_ifs
    exacts [p1, p0]
  have hK : (K.map c)ᵀ = K := by
    have h1 : Hm.1 * (K.map c)ᵀ = 1 := by
      conv_lhs => rw [← hH']
      rw [← Matrix.transpose_mul, ← Matrix.map_mul, hKH, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.transpose_one]
    calc (K.map c)ᵀ = K * (Hm.1 * (K.map c)ᵀ) := by rw [← Matrix.mul_assoc, hKH, Matrix.one_mul]
      _ = K := by rw [h1, Matrix.mul_one]
  have hinv := frm_mul_inv (e := (ε : R)) (e' := ((ε⁻¹ : Rˣ) : R)) hKH (Units.mul_inv ε) ht1
  have hadj := adj_frm (e := (ε : R)) c hK rfl (hc t)
  let M' : GL (Fin (n + n)) R := ⟨_, _, hinv, mul_eq_one_comm.1 hinv⟩
  let M : GL (Fin (n + n)) R := ⟨(u : R) • M'.1, ((u⁻¹ : Rˣ) : R) • (M'⁻¹).1,
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.mul_inv, Units.mul_inv, one_smul],
    by rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Units.inv_mul, Units.inv_mul, one_smul]⟩
  have hM : M.1 = (u : R) • frm K (ε : R) t (c t) := rfl
  have hadjM : (M.1.map c)ᵀ = c u • blk4 1 1 ((c ε * c t) • K) ((-(c ε * t)) • K) := by
    rw [← hadj, hM, ← Matrix.transpose_smul, ← map_smul_hom]
  have hcε : c ε * u * c u = -m := by
    have h := congrArg c hs1
    rw [map_mul, map_mul, hc, hm] at h
    linear_combination h
  refine ⟨M, M', ?_, ?_, ⟨?_, ?_⟩, rfl, fun S _ f hR h4 h2 => ?_⟩
  · rw [hadjM, hM, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, gram_frm _ hKH hHK ht1, smul_smul,
      blockMatrixTwoByTwoFin_smul, blockMatrixTwoByTwoFin_smul, smul_zero, smul_zero, smul_smul, smul_smul, smul_neg, ← neg_smul, ← hcε, ← hs1]
    congr 2 <;> ring
  · intro i j
    rw [hM]
    simp only [frm, blk4, Matrix.smul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁]
  · exact blockMatrixTwoByTwoFin_forall_entries p pone (fun i j => pmul (pmul hs2 ht2) (hI2 i j)) pone
      (fun i j => pmul (pneg (pmul hs2 (pc ht2))) (hI2 i j))
  · exact blockMatrixTwoByTwoFin_forall_entries p (fun i j => pmul (pc ht2) (pone i j))
      (fun i j => pmul ht2 (pone i j)) (fun i j => pmul hs3 (hI1 i j))
      (fun i j => pmul (pneg hs3) (hI1 i j))
  · have hKK : (K * K).map f = 1 := by
      have h1 : K * K * (Hm.1 * Hm.1) = 1 := by
        rw [Matrix.mul_assoc, ← Matrix.mul_assoc K Hm.1, hKH, Matrix.one_mul, hKH]
      have h3 : (K * K * (Hm.1 * Hm.1)).map f = (1 : Matrix (Fin n) (Fin n) R).map f := by rw [h1]
      rwa [Matrix.map_mul, hR, Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at h3
    rw [hadjM, hM, Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_smul_hom,
      norm_frm _ _ hKK ht1 h2 h4, smul_smul]
    congr 1
    simp only [map_mul, map_ofNat]
    ring

theorem blockMatrixTwoByTwoFin_standardSkew_map (f : R →+* S) :
    (blk4 (0 : Matrix (Fin n) (Fin n) R) 1 (-1) 0).map f = blk4 0 1 (-1) 0 := by
  rw [block_matrix_map, Matrix.map_zero _ (map_zero _), Matrix.map_neg _ (map_neg _),
    Matrix.map_one _ (map_zero _) (map_one _)]

end Generic

variable {D : D7}

theorem compFin_cA (v : HeightOneSpectrum (𝓞 D.host.F)) (z : AE D) :
    compFin D.host.F D.host.E v (cA D z) = sigR _ D.sp.cm.sig (compFin D.host.F D.host.E v z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a x => rfl

theorem intA_cA {z : AE D} (h : IntA z) : IntA (cA D z) := fun v => by
  rw [compFin_cA]; exact sigR_mem_intLoc _ (h v)

theorem intA_mul {x y : AE D} (hx : IntA x) (hy : IntA y) : IntA (x * y) := fun v => by
  rw [map_mul]; exact Subring.mul_mem _ (hx v) (hy v)

theorem intA_neg {x : AE D} (hx : IntA x) : IntA (-x) := fun v => by
  rw [map_neg]; exact Subring.neg_mem _ (hx v)

theorem intA_zero : IntA (0 : AE D) := fun v => by
  rw [map_zero]; exact Subring.zero_mem _

theorem intA_one : IntA (1 : AE D) := fun v => by
  rw [map_one]; exact Subring.one_mem _

theorem cA_incA_skew {μ : D.host.E} (h : IsSkew μ) : cA D (incA D μ) = -incA D μ := by
  rw [show cA D (incA D μ) = incA D (star μ) from rfl, h.2, map_neg]

theorem rat_Jst (n : ℕ) : (rat (Jst D n) : Mx D (n + n) (n + n)) = blk4 0 1 (-1) 0 := blockMatrixTwoByTwoFin_standardSkew_map (incA D)

theorem exists_frame : ∀ (D : D7) (n : ℕ) (Hm : GL (Fin n) (AE D)), adj Hm.1 = Hm.1 → IntGL Hm → (∀ w, (Hm.1 * Hm.1).map (compInf D.host.F D.host.E w) = 1) → ∀ (μ : D.host.E) (u ε : (AE D)ˣ) (t : AE D), IsSkew μ → ScalData μ u ε → HalfData t → ∃ M M' : GL (Fin (n + n)) (AE D), adj M.1 * dblGram finSumFinEquiv Hm.1 * M.1 = incA D μ • rat (Jst D n) ∧ (∀ i j : Fin n, M.1 (finSumFinEquiv (Sum.inr i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n)) = M.1 (finSumFinEquiv (Sum.inl i : Fin n ⊕ Fin n)) (finSumFinEquiv (Sum.inl j : Fin n ⊕ Fin n))) ∧ IntGL M' ∧ M.1 = (u : AE D) • M'.1 ∧ ∀ w, (adj M.1 * M.1).map (compInf D.host.F D.host.E w) = compInf D.host.F D.host.E w (2 * u * cA D u) • 1 := by
  intro D n Hm hH hI hR μ u ε t hμ hs ht
  obtain ⟨M, M', h1, h2, h3, h4, h5⟩ := exists_frame_ring (cA D) Formalism.L2.Theta.cA_cA IntA intA_zero intA_one
    intA_mul intA_neg intA_cA Hm hH hI.1 hI.2 (incA D μ) (cA_incA_skew hμ) u ε t hs.1 hs.2.1 hs.2.2.1 ht.1 ht.2.1
  refine ⟨M, M', ?_, h2, h3, h4, fun w => h5 _ _ (hR w) (hs.2.2.2 w) (ht.2.2 w)⟩
  rw [rat_Jst]
  exact h1

end GlobalTheory.StdUnn.Frame

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChainStageFormsTwistedLevelLeFinerLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_stage_forms_twisted_level_le_finer_level : ∀ D : D7, FlatLe D := by
  first | exact @GlobalTheory.FlatLevel.flatLe | exact GlobalTheory.FlatLevel.flatLe | (intros; apply GlobalTheory.FlatLevel.flatLe <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompletedHomLatticeStableSplitIdempotentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completed_hom_lattice_stable_split_idempotent : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k) (S T : HSp D) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T) (u : WO S T), u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) → (Matrix.of fun i j => q.e * u i j : WO S T) ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) ∧ ∀ i j, (q.e + cA D q.e) * u i j = u i j := by
  first | exact @GlobalTheory.SplitVac.idem_latO | exact GlobalTheory.SplitVac.idem_latO | (intros; apply GlobalTheory.SplitVac.idem_latO <;> assumption)
end

