import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0501
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0502
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0492
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0021
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleThetaUnfoldingEquivariantUnitaryGroups
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0483
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0506
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0422
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0345
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PureTensorOZeroEqJetP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0510
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTupleChainAdelicData
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0503

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelBaseValueEquivariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleMixedModel_baseValue_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ρ : ℕ) (B : BesLev D ρ) (J : JacLev D ρ) (s : StepBF ψ B J) (om' : Om B.V₀ J.W), IsWeilDatumO ψ B.V₀ J.W s.χV s.χW om' → ∀ (Ψ : WO B.V J.W → ℂ), IsThetaFunO ψ B.V J.W Ψ → (∀ (u : UX D ρ) h₀, ∀ n ∈ radX J.d, ∀ h', evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (embA B.d B.o h₀, n * J.d.emb0 h') Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = s.om₀ (B.o.emb (h₀, 1), 1) (opA ψ J.d B.o B.ζ s.om₀ n h' (evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ))))) ∧ ∀ (u γ : UX D ρ), evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (1, J.d.levi γ.1) Ψ) (xZero J.d ⬝ u.1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) = evalAt ψ B.d J.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (xZero J.d ⬝ (γ⁻¹ * u).1.1) (yZero B.V₀ ρ (vecB B.o B.ζ)) := by
  first | exact @GlobalTheory.Unf.evalAt_xZero_yZero | exact GlobalTheory.Unf.evalAt_xZero_yZero | (intros; apply GlobalTheory.Unf.evalAt_xZero_yZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubleMixedModelValueAtZeroEquivariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleMixedModel_valueAtZero_equivariant : ∀ (D : D7), Descent D → ∀ (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (Ψ : WO J.W B.V → ℂ), IsThetaFunO ψ J.W B.V Ψ → ∀ (g : GA D J.W₀), ∀ n ∈ flagN B.d, ∀ (h : GA D B.A) (x : Mx D B.V.rank (σ + 1)), evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 (s.om (J.d.emb0 g, n * embA B.d B.o h) Ψ) x 0 = s.om₀ (g, B.o.emb (h, 1)) (evalAt ψ J.d B.d s.vS.μ s.vS.𝓕 s.vT.μ s.vT.𝓕 Ψ (mt B.V (n * embA B.d B.o h)⁻¹ ⬝ x) 0) := by
  first | exact @GlobalTheory.Unf.FB.evalAt_zero_equivariant | exact GlobalTheory.Unf.FB.evalAt_zero_equivariant | (intros; apply GlobalTheory.Unf.FB.evalAt_zero_equivariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledThetaVectorFixedUnramifiedStabilizerStatement
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
theorem _root_.GlobalTheory.T.doubledTheta_vector_fixed_unramified_stabilizer : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ → ∀ v ∉ Sf, ∀ k ∈ KFin D.sp.cm.sig (dblSp A).gram LA v, omh (emb D.sp.cm.sig (dblSp A).gram v k, 1) (delta A B Φ₁ Φ₂) = delta A B Φ₁ Φ₂ := by
  first | exact @GlobalTheory.Core.Rk.IP.VacFix.main | exact GlobalTheory.Core.Rk.IP.VacFix.main | (intros; apply GlobalTheory.Core.Rk.IP.VacFix.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalSStatement
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
theorem _root_.GlobalTheory.T.doublingSiegelWeilSection_mem_degeneratePrincipalSeries : GlobalTheory.Published.WeilRepresentationUnitaryPair → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A B : HSp D) (χB : (AE D)ˣ →* Circle) (omh : WRep (dblSp A) B), IsWeilDatumO ψ (dblSp A) B 1 χB omh → ∀ (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), IsCovolOne (ratL B A) ν 𝓕 → ∀ φ, IsThetaFunO ψ (dblSp A) B φ → ∀ a : GL (Fin A.rank) (AE D), IsKFinVec omh (Khat A a) φ → swSec A B omh ν 𝓕 φ ∈ degPS A a χB⁻¹ (sZero A B) := by
  first | exact @GlobalTheory.SwSecMem.swSec_mem_degPS | exact GlobalTheory.SwSecMem.swSec_mem_degPS | (intros; apply GlobalTheory.SwSecMem.swSec_mem_degPS <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DualIsotropicLineMemCompletionIffStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.LatPair GlobalTheory.SeeSaw GlobalTheory.FinPl ValuativeRel
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dualIsotropicLine_mem_completion_iff : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ)
    (L : Lat S) (L₀ : Lat S₀) (𝔟 : ℕ → FI D) (v : Pl D), IsSelfDualC S L → MonoId d L L₀ 𝔟 v → ∀ i : Fin ρ, 𝔟 i ≠ 0 →
      ∀ t ∈ idAt D (· = v), colMul d.jY i t ∈ latV S L (· = v) ↔ cA D t ∈ idV (𝔟 i)⁻¹ v := by
  first | exact @GlobalTheory.DualLine.dualLine_mem_iff | exact GlobalTheory.DualLine.dualLine_mem_iff | (intros; apply GlobalTheory.DualLine.dualLine_mem_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsBilinearEquivariantOrthogonalSummandLift
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
open GlobalTheory.FinPl GlobalTheory.FinPl.SrcGl
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.SrcTheta

section Lift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S A L T : HSp D} (o : OrthDec S A L) {χS χT : (AE D)ˣ →* Circle}
  {om : Om S T}

theorem contAut_ker (hW : IsWeilDatumO ψ S T χS χT om) {φ : GA D A → ℂ} {Ξ : WO S T → ℂ} (hφ : IsContAut A φ)
    (hΞ : IsThetaFunO ψ S T Ξ) (h : GA D T) (u : WO L T) :
    IsContAut A fun a => φ a * om (o.emb (a, 1), h) Ξ ((o.resS T).symm (0, u)) := by
  refine ⟨fun γ hγ a => ?_, hφ.2.mul ((hW.om_cont Ξ hΞ _).comp
    ((o.continuous_emb.comp (continuous_id.prodMk continuous_const)).prodMk continuous_const))⟩
  have e := GlobalTheory.T.weilRepresentation_rational_translate_substitution D ψ _ _ _ _ _ hW Ξ hΞ _ (o.emb_mem_GQ hγ (one_mem _)) 1 (one_mem _) (o.emb (a, 1)) h
    ((o.resS T).symm (0, u))
  rw [← map_mul, Prod.mk_mul_mk, one_mul, one_mul, inv_one, mt_one, Matrix.one_mul] at e
  beta_reduce
  rw [hφ.1 γ hγ, e]
  congr 2
  rw [OrthDec.resS_symm_apply, Matrix.zero_mul, zero_add, Matrix.mul_assoc, OrthDec.pB_emb, mt_one, Matrix.one_mul]

theorem liftA_add_left (hA : CoCpt A) (vA : Vol A) (hW : IsWeilDatumO ψ S T χS χT om) {φ φ' : GA D A → ℂ}
    {Ξ : WO S T → ℂ} (hφ : IsContAut A φ) (hφ' : IsContAut A φ') (hΞ : IsThetaFunO ψ S T Ξ) :
    liftA o om vA (φ + φ') Ξ = liftA o om vA φ Ξ + liftA o om vA φ' Ξ := by
  funext h w
  simp only [liftA, Pi.add_apply, add_mul]
  exact integral_add (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ hΞ h _))
    (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ' hΞ h _))

theorem liftA_add_right (hA : CoCpt A) (vA : Vol A) (hW : IsWeilDatumO ψ S T χS χT om) {φ : GA D A → ℂ}
    {Ξ Ξ' : WO S T → ℂ} (hφ : IsContAut A φ) (hΞ : IsThetaFunO ψ S T Ξ) (hΞ' : IsThetaFunO ψ S T Ξ') :
    liftA o om vA φ (Ξ + Ξ') = liftA o om vA φ Ξ + liftA o om vA φ Ξ' := by
  funext h w
  simp only [liftA, map_add, Pi.add_apply, mul_add]
  exact integral_add (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ hΞ h _))
    (Comm.IsContAut.integrableOn hA vA (contAut_ker o hW hφ hΞ' h _))

theorem liftA_smul_left (vA : Vol A) (c : ℂ) (φ : GA D A → ℂ) (Ξ : WO S T → ℂ) :
    liftA o om vA (c • φ) Ξ = c • liftA o om vA φ Ξ := by
  funext h w
  simp only [liftA, Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul _ _

theorem liftA_smul_right (vA : Vol A) (c : ℂ) (φ : GA D A → ℂ) (Ξ : WO S T → ℂ) :
    liftA o om vA φ (c • Ξ) = c • liftA o om vA φ Ξ := by
  funext h w
  simp only [liftA, map_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
  exact integral_const_mul _ _

theorem liftA_equiv (vA : Vol A) (hW : IsWeilDatumO ψ S T χS χT om) {φ : GA D A → ℂ} {Ξ : WO S T → ℂ}
    (hφ : IsContAut A φ) (hΞ : IsThetaFunO ψ S T Ξ) (a : GA D A) :
    liftA o om vA (fun x => φ (x * a)) (om (o.emb (a, 1), 1) Ξ) = liftA o om vA φ Ξ := by
  funext h w
  simp only [liftA]
  refine Eq.trans ?_ (Comm.integral_right vA (contAut_ker o hW hφ hΞ h w).1 a)
  congr 1
  funext x
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]

end Lift

theorem exists_linear_of_rel {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (P : Submodule ℂ M) (R : M → N → Prop) (hex : ∀ x ∈ P, ∃! y, R x y)
    (hlin : ∀ (c : ℂ) x y x' y', R x y → R x' y' → R (c • x + x') (c • y + y')) :
    ∃ G : M →ₗ[ℂ] N, (∀ x, ∃ x', R x' (G x)) ∧ ∀ x ∈ P, R x (G x) := by
  choose F hF hFu using fun x : P => hex x.1 x.2
  have hc : ∀ (c : ℂ) (x x' : P), F (c • x + x') = c • F x + F x' := fun c x x' =>
    (hFu (c • x + x') _ (hlin c _ _ _ _ (hF x) (hF x'))).symm
  have h0 : F 0 = 0 := by
    have := hc 1 0 0
    simp only [one_smul, add_zero] at this
    exact left_eq_add.1 this
  let F' : P →ₗ[ℂ] N :=
    { toFun := F
      map_add' := fun x y => by simpa using hc 1 x y
      map_smul' := fun c x => by simpa [h0] using hc c x 0 }
  obtain ⟨Q, hQ⟩ := P.exists_isCompl
  refine ⟨F' ∘ₗ P.linearProjOfIsCompl Q hQ, fun x => ⟨_, hF _⟩, fun x hx => ?_⟩
  have e : P.linearProjOfIsCompl Q hQ x = ⟨x, hx⟩ := Submodule.linearProjOfIsCompl_apply_left hQ ⟨x, hx⟩
  rw [LinearMap.comp_apply, e]
  exact hF ⟨x, hx⟩

theorem exists_theta : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : SplitPt D k) (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (ψ : AddChar (AF D.host.F) ℂ) (S A L T : HSp D) (o : OrthDec S A L) (ζ : Fin L.rank → D.host.E), IsLineVec L ζ → CoCpt A → ∀ (vA : Vol A) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (α : Frame p A n') (α₀ : Frame p S (n' ⊕ Fin 1)) (β : Frame p T n), IsSumFrame o ζ α α₀ → ∃ lS : kˣ →* ℂˣ, (CharUnramAt D χT p.v → IsUnram lS) ∧ ∀ (LS : Lat S) (LT : Lat T) (f₀ : WO S T → ℂ), IsSelfDualC S LS → IsSelfDualC T LT → Vac ψ S T LS LT (· = p.v) f₀ → ∃ θ : GlobalTheory.FinPl.SrcGl.CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ), (∀ (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ) (f : WO S T → ℂ), Over ψ α₀ β LS LT f₀ Φ f → θ v Φ = liftA o om vA v f) ∧ ∀ (g : GL n' k) (v : GlobalTheory.FinPl.SrcGl.CA A) (Φ : Matrix n (n' ⊕ Fin 1) k → ℂ), Φ ∈ SB (Matrix n (n' ⊕ Fin 1) k) → θ (GlobalTheory.FinPl.SrcGl.caRep α g v) (fun x => Φ (x * (GlobalTheory.FinPl.SrcGl.blk g).val)) = ((lS (Matrix.GeneralLinearGroup.det g) : ℂˣ) : ℂ)⁻¹ • θ v Φ := by
  intro D k _ _ _ _ p n n' _ _ _ _ ψ S A L T o ζ _ hA vA χS χT om hW α α₀ β hsum
  obtain ⟨lS, lT, hlS, -, hlin⟩ := GlobalTheory.T.splitPlace_linearModel_latticeVacuum_base D k p ψ S T χS χT om hW
  refine ⟨lS, hlS, fun LS LT f₀ hLS hLT hvac => ?_⟩
  obtain ⟨hex, hth, -⟩ := GlobalTheory.T.splitPlace_baseVacuum_datum_exists_unique D k p n (n' ⊕ Fin 1) ψ hW.std S T α₀ β LS LT hLS hLT f₀ hvac
  obtain ⟨G, hG, hGP⟩ := exists_linear_of_rel (SB (Matrix n (n' ⊕ Fin 1) k)) (Over ψ α₀ β LS LT f₀) hex
    (fun c x y x' y' h h' => (hlin n _ α₀ β LS LT f₀ x y h).2.2 c x' y' h')
  have hGt : ∀ Φ, IsThetaFunO ψ S T (G Φ) := fun Φ => (hG Φ).elim fun x hx => (hth _ _ hx).1
  have hGf : ∀ Φ f, Over ψ α₀ β LS LT f₀ Φ f → G Φ = f := fun Φ f h =>
    (hex Φ h.2.2.2.1).unique (hGP Φ h.2.2.2.1) h
  let θ : CA A →ₗ[ℂ] (Matrix n (n' ⊕ Fin 1) k → ℂ) →ₗ[ℂ] (GA D T → WO L T → ℂ) :=
    LinearMap.mk₂ ℂ (fun v Φ => liftA o om vA v (G Φ))
      (fun v v' Φ => liftA_add_left o hA vA hW v.2 v'.2 (hGt Φ))
      (fun c v Φ => liftA_smul_left o vA c v (G Φ))
      (fun v Φ Φ' => by rw [map_add]; exact liftA_add_right o hA vA hW v.2 (hGt Φ) (hGt Φ'))
      (fun c v Φ => by rw [map_smul]; exact liftA_smul_right o vA c v (G Φ))
  have hθ : ∀ (v : CA A) Φ, θ v Φ = liftA o om vA v (G Φ) := fun _ _ => rfl
  refine ⟨θ, fun v Φ f h => by rw [hθ, hGf Φ f h], fun g v Φ hΦ => ?_⟩
  have h1 := (hlin n _ α₀ β LS LT f₀ Φ _ (hGP Φ hΦ)).1 (blk g) 1
  have hdet : Matrix.GeneralLinearGroup.det (blk g) = Matrix.GeneralLinearGroup.det g := by
    ext
    simp [Matrix.GeneralLinearGroup.val_det_apply]
  have hemb : α₀.gl (blk g) = o.emb (α.gl g, 1) := by
    rw [Comm.emb_gl hsum]
    congr 1
  have hfun : (fun x : Matrix n (n' ⊕ Fin 1) k => (lS (Matrix.GeneralLinearGroup.det (blk g)) : ℂ) *
      (lT (Matrix.GeneralLinearGroup.det (1 : GL n k)) : ℂ) * Φ (((1 : GL n k)⁻¹ : GL n k).val * x * (blk g).val)) =
      (lS (Matrix.GeneralLinearGroup.det g) : ℂ) • fun x => Φ (x * (blk g).val) := by
    funext x
    simp only [hdet, map_one, Units.val_one, mul_one, inv_one, Matrix.one_mul, Pi.smul_apply, smul_eq_mul]
  rw [hfun, hemb, map_one] at h1
  have h2 : θ (caRep α g v) ((lS (Matrix.GeneralLinearGroup.det g) : ℂ) • fun x => Φ (x * (blk g).val)) = θ v Φ := by
    rw [hθ, hθ, hGf _ _ h1]
    exact liftA_equiv o vA hW v.2 (hGt Φ) (α.gl g)
  rw [← h2, map_smul, inv_smul_smul₀ (Units.ne_zero _)]

end GlobalTheory.FinPl.SrcTheta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCentralGlueLocalHomotheties
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch

noncomputable section

namespace GlobalTheory.Core.Mi.LatGlue

variable {D : D7}

theorem mt_mul (S : HSp D) (a b : GA D S) : Formalism.L2.Theta.mt S (a * b) = Formalism.L2.Theta.mt S a * Formalism.L2.Theta.mt S b := by
  first | rfl | simp [Formalism.L2.Theta.mt, map_mul]

theorem mt_one (S : HSp D) : Formalism.L2.Theta.mt S 1 = 1 := by
  first | rfl | simp [Formalism.L2.Theta.mt]

theorem mem_congGrp {V : HSp D} {I : Ideal (AE D)} {g : GA D V} :
    g ∈ GlobalTheory.FinPl.congGrp V I ↔ ∀ i j, Formalism.L2.Theta.mt V g i j - (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j ∈ I := by
  unfold GlobalTheory.FinPl.congGrp
  rw [MonoidHom.mem_ker]
  constructor
  · intro h i j
    have := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ I) => x.1 i j) h
    rw [← Ideal.Quotient.eq]
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this
  · intro h
    ext i j
    have := h i j
    rw [← Ideal.Quotient.eq] at this
    simp [Formalism.L2.Theta.mt, Matrix.one_apply] at this ⊢
    exact this

theorem idAt_le_idOff {v w : GlobalTheory.FinPl.Pl D} (h : v ≠ w) : idAt D (· = w) ≤ GlobalTheory.FinPl.idOff D (· = v) := by
  intro a ha
  unfold idAt at ha
  unfold GlobalTheory.FinPl.idOff
  simp only [Submodule.mem_inf, Submodule.mem_iInf] at ha ⊢
  intro u
  have hu : u.1 = v := u.2
  exact ha.2 ⟨u.1, fun e => h (hu.symm.trans e)⟩

theorem mulVec_fix {S : HSp D} {v w : GlobalTheory.FinPl.Pl D} (hvw : v ≠ w) {h : GA D S} (hh : h ∈ grpAt S (· = w))
    {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D (· = v)) : Formalism.L2.Theta.mt S h *ᵥ y = y := by
  obtain ⟨ε, -, -, -, hA, hO⟩ := (GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (· = v)).1
  have hh' := (mem_congGrp).1 hh
  have key : (Formalism.L2.Theta.mt S h - 1) *ᵥ y = 0 := by
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have h1 : (Formalism.L2.Theta.mt S h - 1) i j * y j ∈ idAt D (· = v) := Ideal.mul_mem_left _ _ (hy j)
    have h2 : (Formalism.L2.Theta.mt S h - 1) i j * y j ∈ GlobalTheory.FinPl.idOff D (· = v) :=
      Ideal.mul_mem_right _ _ (idAt_le_idOff hvw (by simpa using hh' i j))
    rw [← (hA _).1 h1]
    exact (hO _).1 h2
  rw [Matrix.sub_mulVec, sub_eq_zero, Matrix.one_mulVec] at key
  exact key

theorem scal_mulVec {n : ℕ} (c : AE D) (y : Fin n → AE D) : (c • (1 : Matrix (Fin n) (Fin n) (AE D))) *ᵥ y = c • y := by
  first | rw [Matrix.smul_mulVec, Matrix.one_mulVec] | simp [Matrix.smul_mulVec] | (ext i; simp [Matrix.mulVec, dotProduct, Matrix.one_apply])

end GlobalTheory.Core.Mi.LatGlue

namespace GlobalTheory.Core.Mi.LatGlue

variable {D : D7}

set_option maxHeartbeats 800000 in

theorem glue_finset {V A : HSp D} (e : GA D A →* GA D V)
    (he : ∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ grpAt A (· = v), e a ∈ grpAt V (· = v))
    (a : GlobalTheory.FinPl.Pl D → GA D A) (c : GlobalTheory.FinPl.Pl D → AE D) (z : GlobalTheory.FinPl.Pl D → GA D V)
    (ha : ∀ v, CenAt A v (a v)) (hz : ∀ v, CenAt V v (z v))
    (hzm : ∀ v, Formalism.L2.Theta.mt V (z v) = c v • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) (s : Finset (GlobalTheory.FinPl.Pl D)) :
    ∃ α ∈ GfC A, α ∈ Subgroup.center (GA D A) ∧ ∃ ζ ∈ Subgroup.center (GA D V),
      (∀ v ∈ s, ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
        Formalism.L2.Theta.mt V (e α) *ᵥ y = Formalism.L2.Theta.mt V (e (a v)) *ᵥ y ∧ Formalism.L2.Theta.mt V ζ *ᵥ y = c v • y) ∧
      (∀ v ∉ s, ∀ y : Fin V.rank → AE D, (∀ i, y i ∈ idAt D (· = v)) →
        Formalism.L2.Theta.mt V (e α) *ᵥ y = y ∧ Formalism.L2.Theta.mt V ζ *ᵥ y = y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨1, one_mem _, one_mem _, 1, one_mem _, fun v hv => absurd hv (Finset.notMem_empty v), fun v _ y _ => ?_⟩
    rw [map_one, mt_one, Matrix.one_mulVec]
    exact ⟨rfl, rfl⟩
  | insert w s hws ih =>
    obtain ⟨α, hαG, hαC, ζ, hζC, hin, hout⟩ := ih
    have hwG : a w ∈ GfC A := ((GlobalTheory.FinPl.KOpen.mem_grpAt_iff A _ (a w)).1 (ha w).1).1
    refine ⟨a w * α, mul_mem hwG hαG, mul_mem (ha w).2 hαC, z w * ζ, mul_mem (hz w).2 hζC, ?_, ?_⟩
    · intro v hv y hy
      rcases Finset.mem_insert.1 hv with rfl | hvs
      · obtain ⟨h1, h2⟩ := hout v hws y hy
        refine ⟨?_, ?_⟩
        · rw [map_mul, mt_mul, ← Matrix.mulVec_mulVec, h1]
        · rw [mt_mul, ← Matrix.mulVec_mulVec, h2, hzm, scal_mulVec]
      · have hvw : v ≠ w := fun h => hws (h ▸ hvs)
        obtain ⟨h1, h2⟩ := hin v hvs y hy
        have ca : a w * α = α * a w := ((Subgroup.mem_center_iff.1 (ha w).2) α).symm
        have cz : z w * ζ = ζ * z w := ((Subgroup.mem_center_iff.1 (hz w).2) ζ).symm
        refine ⟨?_, ?_⟩
        · rw [ca, map_mul, mt_mul, ← Matrix.mulVec_mulVec, mulVec_fix hvw (he w _ (ha w).1) hy, h1]
        · rw [cz, mt_mul, ← Matrix.mulVec_mulVec, mulVec_fix hvw (hz w).1 hy, h2]
    · intro v hv y hy
      have hvw : v ≠ w := fun h => hv (h ▸ Finset.mem_insert_self w s)
      have hvs : v ∉ s := fun h => hv (Finset.mem_insert_of_mem h)
      obtain ⟨h1, h2⟩ := hout v hvs y hy
      refine ⟨?_, ?_⟩
      · rw [map_mul, mt_mul, ← Matrix.mulVec_mulVec, h1, mulVec_fix hvw (he w _ (ha w).1) hy]
      · rw [mt_mul, ← Matrix.mulVec_mulVec, h2, mulVec_fix hvw (hz w).1 hy]

set_option maxHeartbeats 800000 in

theorem glue : ∀ (D : D7) (V A : HSp D) (e : GA D A →* GA D V) (g : GA D V) (L M : Lat V), IsSelfDualC V L → IsSelfDualC V M → (∀ v : GlobalTheory.FinPl.Pl D, ∀ a ∈ grpAt A (· = v), e a ∈ grpAt V (· = v)) → (∀ v : GlobalTheory.FinPl.Pl D, ∃ (a : GA D A) (c : AE D), CenAt A v a ∧ NormOneAt v c ∧ SMoves V c (g * e a) L M v) → ∃ a ∈ GfC A, a ∈ Subgroup.center (GA D A) ∧ ∃ z ∈ Subgroup.center (GA D V), Moves V (z * (g * e a)) L M (fun _ => True) := by
  intro D V A e g L M hL hM he hloc
  classical
  choose a c ha hc hs using hloc
  choose z hz hzm using fun v => GlobalTheory.T.exists_centralUnitary_scalar_of_normOneIdele D V v (c v) (hc v)
  obtain ⟨M', hM'sd, hgM'⟩ := (GlobalTheory.T.selfDual_image_adelicPoint_wittCore D V L hL).1 g
  obtain ⟨T, hT⟩ := GlobalTheory.FinPl.latV_eq_off_finite D V M' M hM'sd.1 hM.1
  have hoff : ∀ v ∉ T, Moves V g L M (· = v) := fun v hv y hy => by
    rw [hgM' _ y hy, hT v hv]
  obtain ⟨α, hαG, hαC, ζ, hζC, hin, hout⟩ := glue_finset e he a c z ha hz hzm T
  refine ⟨α, hαG, hαC, ζ, hζC, ?_⟩
  have comm : ζ * (g * e α) = g * e α * ζ := ((Subgroup.mem_center_iff.1 hζC) _).symm
  have hmt : ∀ y : Fin V.rank → AE D, Formalism.L2.Theta.mt V (ζ * (g * e α)) *ᵥ y =
      Formalism.L2.Theta.mt V g *ᵥ (Formalism.L2.Theta.mt V (e α) *ᵥ (Formalism.L2.Theta.mt V ζ *ᵥ y)) := fun y => by
    rw [comm, mt_mul, mt_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have loc : ∀ v, Moves V (ζ * (g * e α)) L M (· = v) := by
    intro v y hy
    rw [hmt]
    by_cases hv : v ∈ T
    · obtain ⟨h1, h2⟩ := hin v hv y hy
      rw [h2, Matrix.mulVec_smul, h1, Matrix.mulVec_smul, Matrix.mulVec_mulVec, ← mt_mul]
      exact hs v y hy
    · obtain ⟨h1, h2⟩ := hout v hv y hy
      rw [h2, h1]
      exact hoff v hv y hy
  intro y hy
  rw [GlobalTheory.FinPlLoc.part_lat _ V L y hL.1, GlobalTheory.FinPlLoc.part_lat _ V M _ hM.1]
  have hsupp : ∀ i, (Formalism.L2.Theta.mt V (ζ * (g * e α)) *ᵥ y) i ∈ idAt D (fun _ => True) := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  refine and_congr (iff_of_true hy hsupp) (forall_congr' fun v => imp_congr_right fun _ =>
    forall_congr' fun x => forall_congr' fun hx => ?_)
  have hxy : ∀ i, (x • y) i ∈ idAt D (· = v) := fun i => by
    rw [Pi.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hx.1
  rw [← Matrix.mulVec_smul]
  exact loc v (x • y) hxy

end GlobalTheory.Core.Mi.LatGlue

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compactOpen_latticeStabilizerAtPlaces : ∀ (D : D7) (V : HSp D) (L : Lat V), IsSelfDualC V L → ∀ P : Pl D → Prop, ∃ K : Subgroup (GA D V), (∀ g, g ∈ K ↔ InK V L P g) ∧ IsCompact (K : Set (GA D V)) ∧ IsOpen ((K.subgroupOf (grpAt V P) : Subgroup _) : Set (grpAt V P)) := by
  first | exact @GlobalTheory.FinPl.KOpen.exists_compact_open | exact GlobalTheory.FinPl.KOpen.exists_compact_open | (intros; apply GlobalTheory.FinPl.KOpen.exists_compact_open <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsNonzeroJetScaleTrueColumns
section
set_option genSizeOfSpec false
set_option genInjectivity false

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdForm.JetScales

theorem exists_jetS : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X →
    ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ ψ θ, IsStdChar (I.rec7 l Z) ψ (-1) → IsInfFam θ →
      ∃ s, JetS I l Z ψ θ s := by
  intro B X I hI hP l Z ψ θ hψ hθ
  have hstep : ∀ j (hj : j + 1 ≤ B.R.m), ∃ s : ℂ, s ≠ 0 ∧ ∀ f, IsHol θ ((I.rec7 l Z).sp.X j) ((I.rec7 l Z).sp.X (j + 1)) ψ f → ∀ P,
      pureTensorO ψ θ _ _ (fun _ => 1) (fun _ => 1) (fun _ => 1) (fun _ => 1) f P 0 =
        jetP _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj)) (rankN (I.rec7 l Z) (j + 1) hj) s (ColDat.xiS θ j hj f) P :=
    fun j hj => GlobalTheory.AdForm.JetRead.pureTensorO_zero_eq_jetP (I.rec7 l Z) ψ θ _ _ _ _ (rankN (I.rec7 l Z) j (Nat.le_of_succ_le hj))
      (rankN (I.rec7 l Z) (j + 1) hj) I.A.δ I.A.sc (stdPair_world I hI l Z ψ θ hψ hθ j)
  refine ⟨fun j => if hj : j + 1 ≤ B.R.m then (hstep j hj).choose else 1, fun j hj => ?_⟩
  simp only [dif_pos hj]
  exact (hstep j hj).choose_spec

end GlobalTheory.AdForm.JetScales
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSelfDualLatticePatchedAtPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel IsLocalRing GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw GlobalTheory.FinPl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_lattice_patched_at_places : ∀ (D : D7) (S : HSp D) (L L' : Lat S), IsSelfDualC S L → IsSelfDualC S L' → ∀ Z : Finset (Pl D), ∃ M : Lat S, IsSelfDualC S M ∧ (∀ x ∈ Z, latV S M (· = x) = latV S L' (· = x)) ∧ ∀ x, x ∉ Z → latV S M (· = x) = latV S L (· = x) := by
  first | exact @GlobalTheory.FinPl.Patch.patch | exact GlobalTheory.FinPl.Patch.patch | (intros; apply GlobalTheory.FinPl.Patch.patch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsTupleChainAdelicDataStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
open GlobalTheory.SeeSaw GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tupleChain_adelicData : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι), ∃ (Ch : ℕ → Type) (_ : ∀ i, Fintype (Ch i)) (A : TwDat I l Z u a Ch), A.Is ∧ Nonempty (Unique (Ch B.R.m)) ∧ ∀ i, i < B.R.m → ∀ β, A.kb i β = TC.kStd X u (B.R.N i) := by
  first | exact @GlobalTheory.AdForm.exists_twDat | exact GlobalTheory.AdForm.exists_twDat | (intros; apply GlobalTheory.AdForm.exists_twDat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FrameLatticeMembershipCriterionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_lattice_membership_criterion : ∀ (D : D7) (u : D.what₂.Word) (d : GlobalTheory.SeeSaw.Dat D u) (τ : ∀ j h, Matrix (Fin (d.bes j 0 h).L.rank) (Fin d.Lz.rank) D.host.E) (PP : Formalism.L2.DIV.Pl D.host.E) (G : GlobalTheory.LocMod.GAt d τ PP) (ρ : ℕ) (h0 : 0 + 2 * ρ + 2 = D.R.m) (L : Lat (d.st 0).V), (∀ y : GlobalTheory.StepData.XIx (Fin D.R.k) (Fin D.R.t) 0 ⊕ Fin (G.s + 1) → G.k, (fun r => G.q.sec (((G.FY 0 (G.s + 1) (zero_add _)).β *ᵥ y) r)) ∈ latV (d.st 0).V L (· = G.q.v) ↔ (∀ a, y (Sum.inl a) ∈ 𝒪[G.k]) ∧ ∀ i : Fin (G.s + 1), ((((G.S.ϖ : G.kˣ) : G.k) ^ (i.1 + 1))⁻¹ * y (Sum.inr i)) ∈ 𝒪[G.k]) → WShape G.q (d.bes 0 ρ h0).d (d.bes 0 ρ h0).o (d.bes 0 ρ h0).ζ L (fun i => (((G.S.ϖ : G.kˣ) : G.k) ^ (i.1 + 1))⁻¹) (fun i => (((G.S.ϖ : G.kˣ) : G.k) ^ (2 * ρ - i.1 + 1))⁻¹) ((((G.S.ϖ : G.kˣ) : G.k) ^ (ρ + 1))⁻¹) 1 (d.x 0).L := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.wShape_of_besFrame | exact GlobalTheory.Core.Mi.LatMatch.wShape_of_besFrame | (intros; apply GlobalTheory.Core.Mi.LatMatch.wShape_of_besFrame <;> assumption)
end

