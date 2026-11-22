import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0154
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ContinuousResTSymm
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ComplexEmbeddingHermitianQuadrupleSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0032
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0147
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionStar
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0156
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0160

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicUnitaryEveryPointHasCuspScaleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitary_every_point_has_cusp_scale : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ V : HSp D, Near θ V := by
  first | exact @GlobalTheory.CuspGeo.near | exact GlobalTheory.CuspGeo.near | (intros; apply GlobalTheory.CuspGeo.near <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiDoubleUnfoldingBilinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DoubleStepLin

theorem besselFourierJacobi_doubleUnfolding_bilinear : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ), IsContAut B.A φ →
    (∀ (Ξ Ξ' : WO B.V₀ J.W₀ → ℂ) (Θ : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ → IsThetaFunO ψ B.V₀ J.W₀ Ξ' → IsThetaFunO ψ J.W₀ B'.V₀ Θ →
      hand0 s₁ s₂ l vL φ (Ξ + Ξ') Θ = hand0 s₁ s₂ l vL φ Ξ Θ + hand0 s₁ s₂ l vL φ Ξ' Θ) ∧
    (∀ (c : ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ) (Θ : WO J.W₀ B'.V₀ → ℂ), hand0 s₁ s₂ l vL φ (c • Ξ) Θ = c • hand0 s₁ s₂ l vL φ Ξ Θ) ∧
    (∀ (Ξ : WO B.V₀ J.W₀ → ℂ) (Θ Θ' : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ → IsThetaFunO ψ J.W₀ B'.V₀ Θ → IsThetaFunO ψ J.W₀ B'.V₀ Θ' →
      hand0 s₁ s₂ l vL φ Ξ (Θ + Θ') = hand0 s₁ s₂ l vL φ Ξ Θ + hand0 s₁ s₂ l vL φ Ξ Θ') ∧
    (∀ (c : ℂ) (Ξ : WO B.V₀ J.W₀ → ℂ) (Θ : WO J.W₀ B'.V₀ → ℂ), hand0 s₁ s₂ l vL φ Ξ (c • Θ) = c • hand0 s₁ s₂ l vL φ Ξ Θ) := by
  intro D ψ σ B J B' s₁ s₂ l vL φ hφ
  refine ⟨fun Ξ Ξ' Θ hΞ hΞ' hΘ => ?_, fun c Ξ Θ => ?_, fun Ξ Θ Θ' hΞ hΘ hΘ' => ?_, fun c Ξ Θ => ?_⟩
  · have e := GlobalTheory.FinPl.Comm.doubleThetaUnfolding_linear_first_datum s₁ s₂ l vL (Ξ₂ := Θ) hφ hΞ hΞ' hΘ 1
    simpa only [one_smul] using e
  · funext h₁
    simp only [hand0, handFB, pairKer, contractT, thPair, handBF, map_smul, Pi.smul_apply, smul_eq_mul]
    simp_rw [mul_left_comm (φ _) c, integral_const_mul, star_mul', star_star]
    simp_rw [show ∀ x y : ℂ, x * (c * y) = c * (x * y) from fun x y => by ring, integral_const_mul]
  · have e := GlobalTheory.FinPl.Comm.doubleThetaUnfolding_linear_second_datum s₁ s₂ l vL hφ hΞ hΘ hΘ' 1
    simpa only [one_smul] using e
  · funext h₁
    simp only [hand0, handFB, pairKer, contractT, thPair, map_smul, Pi.smul_apply, smul_eq_mul, mul_assoc,
      integral_const_mul]

end GlobalTheory.DoubleStepLin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselFourierJacobiUnfoldingHeisenbergExchange
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.FinPl
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.HeisExchange

open GlobalTheory.Unf.ContrHeis

variable {D : D7}

theorem kappa_mul {ρ σ : ℕ} {B : BesLev D ρ} {B' : BesLev D σ} (l : Link B B'.L B'.ζ) (S : HSp D) (g : GA D S)
    (w : WO S B'.L) : l.κ S (w ⬝ mt S g⁻¹) = mt S g ⬝ l.κ S w := by
  have hτ := (GlobalTheory.Unf.LinkGram.link_gram D ρ B B'.L B'.ζ B'.line l).1
  exact (GlobalTheory.LinkKappa.kappa_props D B.L B'.L S l.τ 1 hτ (l.κ S) (fun _ => rfl)).2.2.2.1 g w

theorem sympl_resT {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (c d : WO S L) :
    symplOH S T ((o.resT S).symm (0, c)) ((o.resT S).symm (0, d)) = symplOH S L c d := by
  rw [o.symplOH_resT, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]

theorem sympl_resS {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (c d : WO L S) :
    symplOH T S ((o.resS S).symm (0, c)) ((o.resS S).symm (0, d)) = symplOH L S c d := by
  rw [o.symplOH_resS, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, symplOH_zero_left, zero_add]

theorem act_resT {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (g : GA D S) (a : GA D A) (c : WO S L) :
    actO S T g (o.emb (a, 1)) ((o.resT S).symm (0, c)) = (o.resT S).symm (0, c ⬝ mt S g⁻¹) := by
  rw [AddEquiv.eq_symm_apply, o.resT_actO, AddEquiv.apply_symm_apply]
  simp only [actO_eq, mt_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.one_mul]

theorem act_resS {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) (g : GA D S) (a : GA D A) (c : WO L S) :
    actO T S (o.emb (a, 1)) g ((o.resS S).symm (0, c)) = (o.resS S).symm (0, mt S g ⬝ c) := by
  rw [AddEquiv.eq_symm_apply, o.resS_actO, AddEquiv.apply_symm_apply]
  simp only [actO_eq, inv_one, mt_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one]

theorem quasi_resT {ψ : AddChar (AF D.host.F) ℂ} {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) {γ : WO S L} (hγ : γ ∈ ratMx D L.rank S.rank) (v : WO S L) :
    f ((o.resT S).symm (0, γ + v)) = ψ (-symplOH S L γ v) * f ((o.resT S).symm (0, v)) := by
  have r : (o.resT S).symm (0, γ) ∈ ratMx D T.rank S.rank := by
    refine (o.mem_ratL_resT S _).2 ?_
    rw [AddEquiv.apply_symm_apply]
    exact ⟨zero_mem _, hγ⟩
  obtain ⟨γ₂, hγ₂⟩ := r
  have q := hf.quasi γ₂ ((o.resT S).symm (0, v))
  have e : ratW T S γ₂ = (o.resT S).symm (0, γ) := hγ₂
  rwa [e, ← map_add, Prod.mk_add_mk, zero_add, sympl_resT] at q

theorem quasi_resS {ψ : AddChar (AF D.host.F) ℂ} {T A L : HSp D} (o : OrthDec T A L) (S : HSp D) {f : WO T S → ℂ}
    (hf : IsThetaFunO ψ T S f) {γ : WO L S} (hγ : γ ∈ ratMx D S.rank L.rank) (v : WO L S) :
    f ((o.resS S).symm (0, γ + v)) = ψ (-symplOH L S γ v) * f ((o.resS S).symm (0, v)) := by
  have r : (o.resS S).symm (0, γ) ∈ ratMx D S.rank T.rank := by
    refine (o.mem_ratL_resS S _).2 ?_
    rw [AddEquiv.apply_symm_apply]
    exact ⟨zero_mem _, hγ⟩
  obtain ⟨γ₂, hγ₂⟩ := r
  have q := hf.quasi γ₂ ((o.resS S).symm (0, v))
  have e : ratW S T γ₂ = (o.resS S).symm (0, γ) := hγ₂
  rwa [e, ← map_add, Prod.mk_add_mk, zero_add, sympl_resS] at q

theorem integral_exchange {ψ : AddChar (AF D.host.F) ℂ} {S L : HSp D} (vL : VolM D L.rank S.rank) (T Y : WO S L → ℂ)
    (hT : ∀ γ ∈ ratMx D L.rank S.rank, ∀ v, T (γ + v) = ψ (-symplOH S L γ v) * T v)
    (hY : ∀ γ ∈ ratMx D L.rank S.rank, ∀ v, Y (γ + v) = ψ (symplOH S L γ v) * Y v) (x : WO S L) :
    ∫ v in vL.𝓕, T v * (ψ (-symplOH S L v x) * Y (v + x)) ∂vL.μ =
      ∫ v in vL.𝓕, ψ (symplOH S L v (-x)) * T (v + -x) * Y v ∂vL.μ := by
  have neg : ∀ v y : WO S L, symplOH S L v (-y) = -symplOH S L v y := by
    intro v y
    have h := GlobalTheory.OrientedHeis.symplOH_add_right (S := S) (T := L) v y (-y)
    rw [add_neg_cancel, symplOH_zero_right] at h
    linear_combination -h
  rw [← covolOne_integral_add vL.covol (fun v => ψ (symplOH S L v (-x)) * T (v + -x) * Y v) ?_ x]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show _ = ψ (symplOH S L (v + x) (-x)) * T (v + x + -x) * Y (v + x)
    rw [add_neg_cancel_right, neg, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_self, add_zero]
    ring
  · intro γ hγ a
    show ψ (symplOH S L (γ + a) (-x)) * T (γ + a + -x) * Y (γ + a) = ψ (symplOH S L a (-x)) * T (a + -x) * Y a
    rw [add_assoc, hT γ hγ, hY γ hγ, GlobalTheory.OrientedHeis.symplOH_add_left, GlobalTheory.OrientedHeis.symplOH_add_right,
      AddChar.map_add_eq_mul]
    have e : ψ (symplOH S L γ (-x)) * ψ (-(symplOH S L γ a + symplOH S L γ (-x))) * ψ (symplOH S L γ a) = 1 := by
      rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_zero_eq_one ψ]
      congr 1
      ring
    linear_combination (ψ (symplOH S L a (-x)) * T (a + -x) * Y a) * e

theorem besselFourierJacobi_unfolding_heisenberg_exchange : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (B : BesLev D (σ + 1)) (J : JacLev D (σ + 1)) (B' : BesLev D σ) (s₁ : StepBF ψ B J) (s₂ : StepFB ψ J B') (l : Link B B'.L B'.ζ) (vL : VolM D B'.L.rank J.W₀.rank) (φ : GA D B.A → ℂ), IsContAut B.A φ →
    ∀ (Ξ : WO B.V₀ J.W₀ → ℂ) (Θ : WO J.W₀ B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ J.W₀ Ξ → IsThetaFunO ψ J.W₀ B'.V₀ Θ → ∀ w₀ : WO J.W₀ B'.L,
      hand0 s₁ s₂ l vL φ (heisO ψ B.V₀ J.W₀ ((B.o.resS J.W₀).symm (0, l.κ J.W₀ w₀)) Ξ) Θ =
        hand0 s₁ s₂ l vL φ Ξ (heisO ψ J.W₀ B'.V₀ ((B'.o.resT J.W₀).symm (0, -w₀)) Θ) := by
  intro D ψ σ B J B' s₁ s₂ l vL φ _ Ξ Θ hΞ hΘ w₀
  funext h₁
  refine integral_congr_ae (Filter.Eventually.of_forall fun h₀ => ?_)
  have key := integral_exchange (ψ := ψ) vL
    (fun v => s₂.om₀ (h₀, B'.o.emb (h₁, 1)) Θ ((B'.o.resT J.W₀).symm (0, v)))
    (fun v => liftA B.o s₁.om₀ B.vA φ Ξ h₀ (l.κ J.W₀ v))
    (fun γ hγ v => quasi_resT B'.o J.W₀ (s₂.weil₀.om_pres _ _ hΘ) hγ v)
    (fun γ hγ v => by
      simp only [liftA]
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
      beta_reduce
      rw [kappa_add, quasi_resS B.o J.W₀ (s₁.weil₀.om_pres _ _ hΞ) (kappa_rat l _ γ hγ), symplOH_kappa, neg_neg]
      ring) (w₀ ⬝ mt J.W₀ h₀⁻¹)
  simp only [pairKer, contractT, thPair, handBF_eq, RCLike.star_def, Complex.conj_conj]
  refine Eq.trans ?_ (key.trans ?_)
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    beta_reduce
    congr 1
    simp only [liftA]
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
    beta_reduce
    rw [s₁.weil₀.om_heis _ _ _ _ hΞ, act_resS, ← kappa_mul, heisO, sympl_resS, symplOH_kappa, ← map_add,
      Prod.mk_add_mk, add_zero, ← kappa_add]
    ring
  · refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    beta_reduce
    rw [s₂.weil₀.om_heis _ _ _ _ hΘ, act_resT, heisO, sympl_resT, ← map_add, Prod.mk_add_mk, add_zero, Matrix.neg_mul]

end GlobalTheory.FinPl.HeisExchange

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselLineContractionHeisenbergInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselLineContraction_heisenberg_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ σ : ℕ) (B : BesLev D ρ) (B' : BesLev D σ) (l : Link B B'.L B'.ζ) (S : HSp D) (vL : VolM D B'.L.rank S.rank) (Ξ₁ : WO B.V₀ S → ℂ) (Ξ₂ : WO S B'.V₀ → ℂ), IsThetaFunO ψ B.V₀ S Ξ₁ → IsThetaFunO ψ S B'.V₀ Ξ₂ → ∀ x : WO S B'.L, GlobalTheory.Unf.contr l S vL (heisO ψ B.V₀ S ((B.o.resS S).symm (0, l.κ S x)) Ξ₁) (heisO ψ S B'.V₀ ((B'.o.resT S).symm (0, x)) Ξ₂) = GlobalTheory.Unf.contr l S vL Ξ₁ Ξ₂ := by
  first | exact @GlobalTheory.Unf.ContrHeis.contr_heisO | exact GlobalTheory.Unf.ContrHeis.contr_heisO | (intros; apply GlobalTheory.Unf.ContrHeis.contr_heisO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjBesselCharacterIsUnfoldingThetaFunctionOfGraStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjBesselCharacter_isUnfoldingThetaFunction_of_gram_zero : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ρ : ℕ) (B : BesLev D ρ) (W : HSp D) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), gramQ W x₀ = 0 → IsTh ψ B.d W x₀ fun n => star (psiBes ψ B.d 1 (vecB B.o B.ζ) n) := by
  first | exact @GlobalTheory.Unf.CutChar.conjBessel_isTh | exact GlobalTheory.Unf.CutChar.conjBessel_isTh | (intros; apply GlobalTheory.Unf.CutChar.conjBessel_isTh <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContDiffHeisenbergSuperpositionThetaFunctionReal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SuperposSmooth

open GlobalTheory.FockCompare GlobalTheory.OrientedHeis

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

def dl (ψ : AddChar (AF D.host.F) ℂ) (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (u : RW T S) (F : WO S T → ℂ) :
    WO S T → ℂ :=
  fun y => deriv (fun s : ℝ => heisO ψ S T (iotaW σ T S (s • u)) F y) 0

def bas (S T : HSp D) : Module.Basis (Fin (Module.finrank ℝ (RW T S))) ℝ (RW T S) := Module.finBasis ℝ (RW T S)

def coordC (S T : HSp D) (i : Fin (Module.finrank ℝ (RW T S))) : RW T S →L[ℝ] ℂ :=
  (LinearMap.toContinuousLinearMap ((bas S T).coord i)).smulRight (1 : ℂ)

theorem clm_expand (φ : RW T S →L[ℝ] ℂ) : φ = ∑ i, φ (bas S T i) • coordC S T i := by
  ext u
  have e : φ u = ∑ i, (bas S T).repr u i • φ (bas S T i) := by
    conv_lhs => rw [← (bas S T).sum_repr u]
    rw [map_sum]
    simp only [map_smul]
  rw [e]
  simp [coordC, ContinuousLinearMap.sum_apply, Complex.real_smul, mul_comm]

theorem norm_heisO_le (hψ : IsStdChar D ψ (-1)) (x : WO S T) {G : WO S T → ℂ} {C : ℝ} (hC : ∀ y, ‖G y‖ ≤ C)
    (w : WO S T) : ‖heisO ψ S T x G w‖ ≤ C := by
  unfold heisO
  rw [norm_mul, hψ.1.2.1, one_mul]
  exact hC _

theorem theta_dl (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    (u : RW T S) : IsThetaFunO ψ S T (dl ψ σ S T u F) := by
  obtain ⟨L, hL, hLe⟩ := (smooth_iff_sm_and_real_lines D θ σ h T S).2.2 u
  have e : dl ψ σ S T u F = dLine ψ S T L F := by
    funext y
    unfold dl dLine
    simp only [hLe]
  rw [e]
  exact theta_dLine h.inf hψ hL hF

def sco (ψ : AddChar (AF D.host.F) ℂ) (σ : (D.what₂.Tau → ℂ) →+ AE D) (S T : HSp D) (F : WO S T → ℂ) (u z : RW T S)
    (w : WO S T) : ℂ :=
  (Real.pi * Complex.I) * ((omO S T z u : ℝ) : ℂ) * heisO ψ S T (iotaW σ T S z) F w +
    heisO ψ S T (iotaW σ T S z) (dl ψ σ S T u F) w

theorem hasFDerivAt_pt (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    (w : WO S T) (c : ℂ) (z : RW T S) :
    HasFDerivAt (fun z : RW T S => c * heisO ψ S T (iotaW σ T S z) F w)
      (∑ i, (c * sco ψ σ S T F (bas S T i) z w) • coordC S T i) z := by
  have hs := GlobalTheory.T.contDiff_heisenbergTranslate_thetaFunction_realCoords D θ σ h ψ hψ S T F hF w
  have hd : HasFDerivAt (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F w)
      (fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F w) z) z :=
    ((hs.1.differentiable (by simp)) z).hasFDerivAt
  have e : c • fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F w) z =
      ∑ i, (c * sco ψ σ S T F (bas S T i) z w) • coordC S T i := by
    rw [clm_expand (fderiv ℝ (fun z : RW T S => heisO ψ S T (iotaW σ T S z) F w) z), Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, hs.2 z (bas S T i)]
    rfl
  rw [← e]
  exact hd.const_mul c

theorem aesm_heisO (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {G : WO S T → ℂ} (hG : IsThetaFunO ψ S T G)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) (z : RW T S) :
    AEStronglyMeasurable (fun x => heisO ψ S T (iotaW σ T S z) G (v x)) μ := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  exact ((theta_heisO_real h.inf hψ (h.real_iota T S z) hG).cont.measurable.comp hv).aestronglyMeasurable

theorem integrable_heisO (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {G : WO S T → ℂ} (hG : IsThetaFunO ψ S T G)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) {a : Ω → ℂ}
    (ha : Integrable a μ) (z : RW T S) :
    Integrable (fun x => a x * heisO ψ S T (iotaW σ T S z) G (v x)) μ := by
  obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ G hG
  exact ha.mul_bdd (aesm_heisO h hψ hG μ hv z) (Filter.Eventually.of_forall fun x => norm_heisO_le hψ _ hC _)

theorem aesm_sco (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) (u z : RW T S) :
    AEStronglyMeasurable (fun x => sco ψ σ S T F u z (v x)) μ :=
  ((aesm_heisO h hψ hF μ hv z).const_mul _).add (aesm_heisO h hψ (theta_dl h hψ hF u) μ hv z)

theorem integral_sco (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) {a : Ω → ℂ}
    (ha : Integrable a μ) (u z : RW T S) :
    Integrable (fun x => a x * sco ψ σ S T F u z (v x)) μ ∧
      ∫ x, a x * sco ψ σ S T F u z (v x) ∂μ =
        (Real.pi * Complex.I) * ((omO S T z u : ℝ) : ℂ) * (∫ x, a x * heisO ψ S T (iotaW σ T S z) F (v x) ∂μ) +
          ∫ x, a x * heisO ψ S T (iotaW σ T S z) (dl ψ σ S T u F) (v x) ∂μ := by
  have e : (fun x => a x * sco ψ σ S T F u z (v x)) = fun x =>
      (Real.pi * Complex.I) * ((omO S T z u : ℝ) : ℂ) * (a x * heisO ψ S T (iotaW σ T S z) F (v x)) +
        a x * heisO ψ S T (iotaW σ T S z) (dl ψ σ S T u F) (v x) := by
    funext x; unfold sco; ring
  have i1 := (integrable_heisO h hψ hF μ hv ha z).const_mul ((Real.pi * Complex.I) * ((omO S T z u : ℝ) : ℂ))
  have i2 := integrable_heisO h hψ (theta_dl h hψ hF u) μ hv ha z
  rw [e]
  exact ⟨i1.add i2, by rw [integral_add i1 i2, integral_const_mul]⟩

theorem hasFDerivAt_superpos (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) {a : Ω → ℂ}
    (ha : Integrable a μ) (z₀ : RW T S) :
    HasFDerivAt (fun z : RW T S => ∫ x, a x * heisO ψ S T (iotaW σ T S z) F (v x) ∂μ)
      (∑ i, ((Real.pi * Complex.I) * ((omO S T z₀ (bas S T i) : ℝ) : ℂ) *
          (∫ x, a x * heisO ψ S T (iotaW σ T S z₀) F (v x) ∂μ) +
        ∫ x, a x * heisO ψ S T (iotaW σ T S z₀) (dl ψ σ S T (bas S T i) F) (v x) ∂μ) • coordC S T i) z₀ := by
  obtain ⟨C, hC⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ F hF
  have hCd : ∀ i, ∃ C' : ℝ, ∀ y, ‖dl ψ σ S T (bas S T i) F y‖ ≤ C' := fun i =>
    GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ (theta_dl h hψ hF (bas S T i))
  choose Cd hCd using hCd
  have hM : ∀ i, ∃ M : ℝ, ∀ z ∈ Metric.closedBall z₀ 1, ‖omO S T z (bas S T i)‖ ≤ M := fun i =>
    (isCompact_closedBall z₀ 1).exists_bound_of_continuousOn
      (LinearMap.continuous_of_finiteDimensional ((omO S T).flip (bas S T i))).continuousOn
  choose M hM using hM
  have hsco : ∀ i, ∀ z ∈ Metric.ball z₀ 1, ∀ w,
      ‖sco ψ σ S T F (bas S T i) z w‖ ≤ Real.pi * M i * C + Cd i := by
    intro i z hz w
    unfold sco
    refine (norm_add_le _ _).trans (add_le_add ?_ (norm_heisO_le hψ _ (hCd i) w))
    rw [norm_mul, norm_mul]
    have h1 : ‖(Real.pi : ℂ) * Complex.I‖ = Real.pi := by simp [Real.pi_pos.le]
    have h2 : ‖((omO S T z (bas S T i) : ℝ) : ℂ)‖ ≤ M i := by
      rw [Complex.norm_real]; exact hM i z (Metric.ball_subset_closedBall hz)
    have h3 := norm_heisO_le hψ (iotaW σ T S z) hC w
    rw [h1]
    have hM0 : 0 ≤ M i := (norm_nonneg _).trans h2
    gcongr
  have key := hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := μ)
    (F := fun z x => a x * heisO ψ S T (iotaW σ T S z) F (v x))
    (F' := fun z x => ∑ i, (a x * sco ψ σ S T F (bas S T i) z (v x)) • coordC S T i)
    (bound := fun x => ‖a x‖ * ∑ i, (Real.pi * M i * C + Cd i) * ‖coordC S T i‖) (Metric.ball_mem_nhds z₀ one_pos)
    (Filter.Eventually.of_forall fun z => (ha.aestronglyMeasurable.mul (aesm_heisO h hψ hF μ hv z)))
    (integrable_heisO h hψ hF μ hv ha z₀)
    (Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
      (ha.aestronglyMeasurable.mul (aesm_sco h hψ hF μ hv (bas S T i) z₀)).smul_const _)
    (Filter.Eventually.of_forall fun x z hz => by
      refine (norm_sum_le _ _).trans ?_
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_smul, norm_mul, mul_assoc]
      gcongr
      exact hsco i z hz (v x))
    (ha.norm.mul_const _)
    (Filter.Eventually.of_forall fun x z _ => hasFDerivAt_pt h hψ hF (v x) (a x) z)
  refine key.congr_fderiv ?_
  rw [integral_finset_sum _ fun i _ => (integral_sco h hψ hF μ hv ha (bas S T i) z₀).1.smul_const _]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_smul_const, (integral_sco h hψ hF μ hv ha (bas S T i) z₀).2]

theorem contDiff_superpos_nat (h : Chart θ σ) (hψ : IsStdChar D ψ (-1)) {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) {v : Ω → WO S T} (hv : Measurable v) {a : Ω → ℂ} (ha : Integrable a μ) (n : ℕ) :
    ∀ F : WO S T → ℂ, IsThetaFunO ψ S T F →
      ContDiff ℝ n (fun z : RW T S => ∫ x, a x * heisO ψ S T (iotaW σ T S z) F (v x) ∂μ) := by
  induction n with
  | zero =>
    intro F hF
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun z =>
      (hasFDerivAt_superpos h hψ hF μ hv ha z).continuousAt)
  | succ n ih =>
    intro F hF
    rw [show ((n + 1 : ℕ) : WithTop ℕ∞) = (n : WithTop ℕ∞) + 1 by norm_cast, contDiff_succ_iff_hasFDerivAt]
    refine ⟨_, ?_, fun z => hasFDerivAt_superpos h hψ hF μ hv ha z⟩
    refine ContDiff.sum fun i _ => ContDiff.smul_const ?_ _
    have hom : ContDiff ℝ n fun z : RW T S => ((omO S T z (bas S T i) : ℝ) : ℂ) :=
      Complex.ofRealCLM.contDiff.comp (LinearMap.toContinuousLinearMap ((omO S T).flip (bas S T i))).contDiff
    exact ((contDiff_const.mul hom).mul (ih F hF)).add (ih _ (theta_dl h hψ hF (bas S T i)))

end GlobalTheory.SuperposSmooth

theorem GlobalTheory.SuperposSmooth.main : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), GlobalTheory.FockCompare.Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (v : Ω → WO S T) (a : Ω → ℂ), Measurable v → Integrable a μ → ContDiff ℝ ∞ (fun z : GlobalTheory.FockCompare.RW T S => ∫ x, a x * heisO ψ S T (GlobalTheory.FockCompare.iotaW σ T S z) F (v x) ∂μ) := by
  intro D θ σ h ψ hψ S T F hF Ω _ μ v a hv ha
  exact contDiff_infty.2 fun n => GlobalTheory.SuperposSmooth.contDiff_superpos_nat h hψ μ hv ha n F hF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteRightTranslateFiniteA
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.RTr

theorem cuspFormsArchimedeanKFinite_rightTranslate_finite : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A), IsInfFam θ → ∀ k ∈ GfC A,
    ∀ u ∈ A0 θ A cA, rTr A k u ∈ A0 θ A cA :=
  fun _ _ _ _ hθ _ hk _ hu => rTr_fin_mem_cuspForms hθ Kinf_le hu hk

end GlobalTheory.Core.Rk.RTr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteStarCompMem
section
noncomputable section

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory.Core.Rk.CuspConj

theorem isKFinite_conj {G : Type} [Group G] {K : Subgroup G} {Φ : G → ℂ} (h : GlobalTheory.Doubling.IsKFinite K Φ) :
    GlobalTheory.Doubling.IsKFinite K fun g => conj (Φ g) := by
  unfold GlobalTheory.Doubling.IsKFinite GlobalTheory.Doubling.kSpan at *
  refine GlobalTheory.Mem.AutConj.finiteDimensional_span_star h ?_
  rintro f ⟨k, hk, rfl⟩
  refine ⟨k, hk, ?_⟩
  funext g
  show star (conj (Φ (g * k))) = Φ (g * k)
  rw [starRingEnd_apply, star_star]

theorem conj_comp_mem_A0 : ∀ (D : D7) (θ : InfFam D) (A : HSp D) (cA : CptF A), IsInfFam θ → ∀ u ∈ A0 θ A cA, (fun g => conj (u g)) ∈ A0 θ A cA := by
  intro D θ A cA hθ u hu
  have hu' : u ∈ autForms θ A (Kinf θ A cA) ⊓ cuspCont A := hu
  show (fun g => conj (u g)) ∈ autForms θ A (Kinf θ A cA) ⊓ cuspCont A
  obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hu'
  obtain ⟨hs, hk⟩ := mem_autForms.1 h1
  refine Submodule.mem_inf.2 ⟨mem_autForms.2 ⟨?_, isKFinite_conj hk⟩, conj_mem_cuspCont h2⟩
  exact GlobalTheory.Mem.AutConj.isAutFunSm_star D θ hθ A u hs

end GlobalTheory.Core.Rk.CuspConj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingHeightEqOneLatticeStabilizerComponents
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem hgt_one_components : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → (∀ v, ∀ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram Λ v, GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV V Λ v k = 1) ∧ (∀ κ ∈ GfC V, ∀ w, GlobalTheory.AdelicU.projArch D.sp.cm.sig V.gram w κ = 1) ∧ ∀ b ∈ GinfC V, ∀ v, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v b = 1 := by
  intro D V Λ hΛ
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨fun v k hk => ?_, fun κ hκ w => ?_, fun b hb v => ?_⟩
  · have hK := (GlobalTheory.Doubling.ioH_mem_KFin (L := Λ) (GlobalTheory.Doubling.gram_hdbl V) (g := k) (g' := 1)).2 ⟨hk, one_mem _⟩
    have := GlobalTheory.Doubling.hgtH_of_mem (GlobalTheory.Doubling.continuous_absEv v) (GlobalTheory.Doubling.isCompact_KFin v) hK
    unfold GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift.hgtV
    exact_mod_cast this
  · exact GlobalTheory.AdelicU.mem_finPts_iff_forall.1 hκ w
  · exact GlobalTheory.AdelicU.mem_infPts_iff_forall.1 hb v

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.EqOfSameDoubleCosetCompletionRowRepresentativesStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_same_doubleCoset_completion_rowRepresentatives : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → ∀ (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m), L.Ok Ch sel mu cst G s → IdxProd sel mu cst L → ∀ j c (h : j + 1 + c = s), Set.InjOn (DoubleCoset.mk (GlobalTheory.RootEx.R k (XIx (Fin R.k) (Fin R.t) (j + 1)) (c + 1) 1) ((W.T s R).lev (j + 1) (c + 1) (by omega)).J ) {g : GL (XIx (Fin R.k) (Fin R.t) (j + 1) ⊕ Fin (c + 1)) k | ∃ b : L.β (j + 1), IsGL ι (L.h (j + 1) b P) g} := by
  first | exact @GlobalTheory.TwBridge.RepsInj.reps_injOn | exact GlobalTheory.TwBridge.RepsInj.reps_injOn | (intros; apply GlobalTheory.TwBridge.RepsInj.reps_injOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFlagUnipotentCoordinateMeasurableEquivStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_flagUnipotent_coordinate_measurableEquiv : ∀ (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), ∃ e : skewA D ρ × (Mx D ρ V₀.rank × UX D ρ) ≃ᵐ flagN d, ∀ p, (e p : GA D V) = d.nC p.1 * (d.nB p.2.1 * d.levi p.2.2.1) := by
  first | exact @GlobalTheory.Unf.flagCoord_measEquiv | exact GlobalTheory.Unf.flagCoord_measEquiv | (intros; apply GlobalTheory.Unf.flagCoord_measEquiv <;> assumption)
end

