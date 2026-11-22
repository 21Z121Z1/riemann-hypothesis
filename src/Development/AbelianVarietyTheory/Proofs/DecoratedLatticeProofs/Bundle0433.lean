import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FockCoefficientExtremalEqDiscreteSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0426
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0453
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0486
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactSubgroupsActOnFockVectorsAllSignatures
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0416
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0033
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0349
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PhiTTransport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0417
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FrameTopAlt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0418
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0005
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.VacOfShape
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0419
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftPairingLowestWeightSchurPolarisation
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues

namespace GlobalTheory.CoefSchur

theorem sesq_eq_of_diag {E : Type*} [AddCommGroup E] [Module ℂ E]
    (F G : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ) (h : ∀ x, F x x = G x x) : F = G := by
  have h0 : ∀ x, (F - G) x x = 0 := fun x => by simp [h x]
  suffices hD : ∀ x y, (F - G) x y = 0 by
    ext x y
    have := hD x y
    simpa [sub_eq_zero] using this
  intro x y
  have h1 := h0 (x + y)
  have h2 := h0 (x + Complex.I • y)
  simp only [map_add, LinearMap.add_apply, LinearMap.map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul, h0, Complex.conj_I, mul_zero, add_zero, zero_add] at h1 h2
  have hI := Complex.I_sq
  linear_combination (-(Complex.I) / 2 * Complex.I) * h1 + (Complex.I / 2) * h2 + ((F - G) x y) * hI

theorem schur_sesq {G : Type*} [Group G] {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] [Nontrivial E] (ρ : G →* Module.End ℂ E)
    (hu : ∀ h x y, ⟪ρ h x, ρ h y⟫_ℂ = ⟪x, y⟫_ℂ)
    (hirr : ∀ U : Submodule ℂ E, (∀ h, Submodule.map (ρ h) U ≤ U) → U = ⊥ ∨ U = ⊤)
    (B : E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ) (hB : ∀ h x y, B (ρ h x) (ρ h y) = B x y) :
    ∃ c : ℂ, ∀ x y, B x y = c * ⟪y, x⟫_ℂ := by
  classical
  let b := stdOrthonormalBasis ℂ E
  let A : E →ₗ[ℂ] E := ∑ i, (B.flip (b i)).smulRight (b i)
  have hA : ∀ x y, B x y = ⟪y, A x⟫_ℂ := by
    intro x y
    conv_lhs => rw [← b.sum_repr' y]
    simp [A, map_sum, inner_sum, inner_smul_right, inner_conj_symm, mul_comm]
  have hcomm : ∀ h x, A (ρ h x) = ρ h (A x) := by
    intro h x
    apply ext_inner_left ℂ
    intro y
    have hy : ρ h (ρ h⁻¹ y) = y := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    calc ⟪y, A (ρ h x)⟫_ℂ = B (ρ h x) y := (hA _ _).symm
      _ = B (ρ h x) (ρ h (ρ h⁻¹ y)) := by rw [hy]
      _ = B x (ρ h⁻¹ y) := hB _ _ _
      _ = ⟪ρ h⁻¹ y, A x⟫_ℂ := hA _ _
      _ = ⟪ρ h (ρ h⁻¹ y), ρ h (A x)⟫_ℂ := (hu _ _ _).symm
      _ = ⟪y, ρ h (A x)⟫_ℂ := by rw [hy]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue A
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  have hinv : ∀ h, Submodule.map (ρ h) (Module.End.eigenspace A c) ≤ Module.End.eigenspace A c := by
    rintro h _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Module.End.mem_eigenspace_iff] at hx
    rw [Module.End.mem_eigenspace_iff, hcomm, hx, map_smul]
  have htop : Module.End.eigenspace A c = ⊤ := by
    rcases hirr _ hinv with h | h
    · exfalso
      have hmem : v ∈ Module.End.eigenspace A c := Module.End.mem_eigenspace_iff.mpr hv.apply_eq_smul
      rw [h, Submodule.mem_bot] at hmem
      exact hv.2 hmem
    · exact h
  refine ⟨c, fun x y => ?_⟩
  have hx : x ∈ Module.End.eigenspace A c := htop ▸ Submodule.mem_top
  rw [Module.End.mem_eigenspace_iff] at hx
  rw [hA, hx, inner_smul_right]

end GlobalTheory.CoefSchur

namespace GlobalTheory.CoefSchur

section
variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
  {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {μ : Measure (WO S T)} {𝓧 : Set (WO S T)}

theorem integrable_mul_conj (hW : IsWeilDatumO ψ S T χS χT om) (hC : IsCovolOne (ratL T S) μ 𝓧)
    {a b : WO S T → ℂ} (ha : IsThetaFunO ψ S T a) (hb : IsThetaFunO ψ S T b) :
    Integrable (fun x => a x * (starRingEnd ℂ) (b x)) (μ.restrict 𝓧) := by
  refine (GlobalTheory.RawLift.FockCoef.integrable_pair hW hC hb ha).congr
    (Filter.Eventually.of_forall fun x => ?_)
  show star (b x) * a x = a x * (starRingEnd ℂ) (b x)
  rw [starRingEnd_apply, mul_comm]

theorem thetaFunctionPairing_weilAction_invariant (hW : IsWeilDatumO ψ S T χS χT om) (hC : IsCovolOne (ratL T S) μ 𝓧)
    (p : GA D S × GA D T) {a b : WO S T → ℂ} (ha : IsThetaFunO ψ S T a)
    (hb : IsThetaFunO ψ S T b) : l2 μ 𝓧 (om p a) (om p b) = l2 μ 𝓧 a b := by
  have key : ∀ f g : WO S T → ℂ, l2 μ 𝓧 f g = GlobalTheory.RawLift.thetaIP μ 𝓧 g f := by
    intro f g
    simp only [l2, Lift.pet, GlobalTheory.RawLift.thetaIP]
    congr 1
    funext x
    rw [starRingEnd_apply, mul_comm]
  rw [key, key, GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om μ 𝓧 hW hC p b a hb ha]

noncomputable def thetaForm (hW : IsWeilDatumO ψ S T χS χT om) (hC : IsCovolOne (ratL T S) μ 𝓧)
    {E : Type*} [AddCommGroup E] [Module ℂ E] (a b : E →ₗ[ℂ] (WO S T → ℂ))
    (ha : ∀ x, IsThetaFunO ψ S T (a x)) (hb : ∀ y, IsThetaFunO ψ S T (b y)) :
    E →ₗ[ℂ] E →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun x y => l2 μ 𝓧 (a x) (b y))
    (fun x x' y => by
      simp only [map_add, l2, Lift.pet, Pi.add_apply, add_mul]
      exact integral_add (integrable_mul_conj hW hC (ha x) (hb y))
        (integrable_mul_conj hW hC (ha x') (hb y)))
    (fun c x y => by
      simp only [map_smul, l2, Lift.pet, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]
      exact integral_const_mul c _)
    (fun x y y' => by
      simp only [map_add, l2, Lift.pet, Pi.add_apply, mul_add]
      exact integral_add (integrable_mul_conj hW hC (ha x) (hb y))
        (integrable_mul_conj hW hC (ha x) (hb y')))
    (fun c x y => by
      simp only [map_smul, l2, Lift.pet, Pi.smul_apply, smul_eq_mul, map_mul]
      rw [← integral_const_mul]
      congr 1
      funext z
      ring)

theorem thetaForm_apply (hW : IsWeilDatumO ψ S T χS χT om) (hC : IsCovolOne (ratL T S) μ 𝓧)
    {E : Type*} [AddCommGroup E] [Module ℂ E] (a b : E →ₗ[ℂ] (WO S T → ℂ))
    (ha : ∀ x, IsThetaFunO ψ S T (a x)) (hb : ∀ y, IsThetaFunO ψ S T (b y)) (x y : E) :
    thetaForm hW hC a b ha hb x y = l2 μ 𝓧 (a x) (b y) := rfl

end

end GlobalTheory.CoefSchur

namespace GlobalTheory.CoefSchur

theorem realElt_one {D : D7} (θ : InfFam D) (hθ : IsInfFam θ) (T : HSp D) :
    realElt θ T 1 = 1 := by
  classical
  obtain ⟨L, -, hL2, -, -, -, hLat, -, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ T hθ
  have h1UH : ∀ τ, (1 : Matrix (Fin T.rank) (Fin T.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D T τ) := by
    intro τ; simp [Formalism.QuantumDeterminants.UH]
  have h1UG : (1 : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) ∈ GlobalTheory.HolDict.UG (gramAt D T) :=
    fun τ => h1UH τ
  have hL1 : L 1 = 1 := by
    have := hL2 1 h1UG 1 h1UG
    rw [mul_one] at this
    exact mul_left_cancel (a := L 1) (by rw [mul_one]; exact this.symm)
  have hat : ∀ τ, atTau θ T τ 1 = 1 := by
    intro τ; rw [hLat τ 1 (h1UH τ), Pi.mulSingle_one, hL1]
  simp [realElt, hat]

theorem thetaLiftPairing_lowestWeight_schur_polarisation_alt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsInfFam θ → IsWeilDatumO ψ S T χS χT om → ∀ (Sp : D.what₂.Tau → SPar) (M : DSModel T Sp), ∀ (μ : Measure (WO S T)) (𝓧 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓧 → ∀ c : CoefA S, c.Is → ∀ pt : PolF D T.rank S.rank →ₗ[ℂ] (WO S T → ℂ), (∀ P, IsThetaFunO ψ S T (pt P)) → ∀ (Δ : PolF D T.rank S.rank) (io : LowT M →ₗ[ℂ] c.W →ₗ[ℂ] PolF D T.rank S.rank), IsIoW θ M c om (fun P => pt P) Δ io → (∀ w : c.W, ∃ N : ℂ, ∀ g : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ)) → ∀ (e e' : ∀ ρ, lowT M ρ), l2 μ 𝓧 (om (1, realElt θ T g) (pt (io (PiTensorProduct.tprod ℂ e) w))) (pt (io (PiTensorProduct.tprod ℂ e') w)) = N * (∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ)) → ∀ g : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ, (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ)) → ∀ (e e' : ∀ ρ, lowT M ρ) (w w' : c.W), l2 μ 𝓧 (om (1, realElt θ T g) (pt (io (PiTensorProduct.tprod ℂ e) w))) (pt (io (PiTensorProduct.tprod ℂ e') w')) = l2 μ 𝓧 (pt Δ) (pt Δ) * (∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ) * ⟪w', w⟫_ℂ := by
  intro D ψ θ S T χS χT om hθ hW Sp M μ 𝓧 hC c hc pt hpt Δ io hio hN g hg e e' w w'
  obtain ⟨hio1, -, v₀, w₀, hv₀, hw₀, hΔ⟩ := hio
  haveI : Nontrivial c.W := hc.2.2.2.1
  have hr1 := realElt_one θ hθ T
  have hom1 : om (1, realElt θ T 1) = 1 := by rw [hr1]; exact map_one om
  have hth : ∀ p P, IsThetaFunO ψ S T (om p (pt P)) := fun p P => hW.om_pres p _ (hpt P)
  let b₀ : c.W →ₗ[ℂ] (WO S T → ℂ) := pt.comp (io (PiTensorProduct.tprod ℂ v₀))
  let B := thetaForm hW hC b₀ b₀ (fun _ => hpt _) (fun _ => hpt _)
  have hBinf : ∀ u ∈ GinfC S, ∀ x y, B (c.ρ u x) (c.ρ u y) = B x y := by
    intro u hu x y
    have hio1' : ∀ (x : LowT M) (w : c.W), om (u, 1) (pt (io x w)) = pt (io x (c.ρ u w)) := hio1 u hu
    simp only [B, thetaForm_apply, b₀, LinearMap.comp_apply]
    rw [← hio1', ← hio1']
    exact thetaFunctionPairing_weilAction_invariant hW hC _ (hpt _) (hpt _)
  have hBinv : ∀ h x y, B (c.ρ h x) (c.ρ h y) = B x y := by
    intro h x y
    obtain ⟨L, -, -, -, -, -, -, hdec, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ S hθ
    obtain ⟨a, ha, u, hu, rfl⟩ := hdec h
    rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, hc.1 a ha, Module.End.one_apply,
      Module.End.one_apply]
    exact hBinf u hu x y
  obtain ⟨lam, hlam⟩ := schur_sesq c.ρ hc.2.1 hc.2.2.2.2 B hBinv
  have hlam0 : lam = l2 μ 𝓧 (pt Δ) (pt Δ) := by
    have := hlam w₀ w₀
    simp only [B, thetaForm_apply, b₀, LinearMap.comp_apply, hΔ] at this
    rw [this, inner_self_eq_norm_sq_to_K, hw₀]; simp
  have hP0 : ∏ ρ, ⟪((v₀ ρ : M.sm ρ) : M.H ρ), M.rep ρ ((1 : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) ρ) ((v₀ ρ : M.sm ρ) : M.H ρ)⟫_ℂ = 1 := by
    apply Finset.prod_eq_one
    intro ρ _
    have hfr : M.fr ρ * (1 : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) ρ * (M.fr ρ)⁻¹ = 1 := by
      rw [Pi.one_apply, mul_one]
      exact Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (M.fr_unit ρ))
    have hσ : M.σ ρ 1 = 1 := (M.ds ρ).2.2.1.1.1
    rw [DSModel.rep, hfr, hσ, ContinuousLinearMap.one_apply, inner_self_eq_norm_sq_to_K, hv₀ ρ]; simp
  have h1mem : ∀ ρ, (1 : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ) := by
    intro ρ; simp [Formalism.QuantumDeterminants.UH]
  have hdiag : ∀ x : c.W, ∀ g : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ,
      (∀ ρ, g ρ ∈ Formalism.QuantumDeterminants.UH (gramAt D T ρ)) → ∀ e e' : ∀ ρ, lowT M ρ,
      l2 μ 𝓧 (om (1, realElt θ T g) (pt (io (PiTensorProduct.tprod ℂ e) x)))
        (pt (io (PiTensorProduct.tprod ℂ e') x)) = l2 μ 𝓧 (pt Δ) (pt Δ) *
        (∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ) * ⟪x, x⟫_ℂ := by
    intro x g hg e e'
    obtain ⟨N, hNx⟩ := hN x
    have h1 := hNx 1 h1mem v₀ v₀
    rw [hP0, mul_one, hom1, Module.End.one_apply] at h1
    have hBx : B x x = N := h1
    rw [hlam, hlam0] at hBx
    rw [hNx g hg e e', ← hBx]; ring
  let F : c.W →ₗ[ℂ] c.W →ₗ⋆[ℂ] ℂ := thetaForm hW hC
    ((om (1, realElt θ T g)).comp (pt.comp (io (PiTensorProduct.tprod ℂ e))))
    (pt.comp (io (PiTensorProduct.tprod ℂ e'))) (fun _ => hth _ _) (fun _ => hpt _)
  let G : c.W →ₗ[ℂ] c.W →ₗ⋆[ℂ] ℂ := (l2 μ 𝓧 (pt Δ) (pt Δ) *
    ∏ ρ, ⟪((e' ρ : M.sm ρ) : M.H ρ), M.rep ρ (g ρ) ((e ρ : M.sm ρ) : M.H ρ)⟫_ℂ) • (innerₛₗ ℂ).flip
  have hFG := sesq_eq_of_diag F G (fun x => by
    simp only [F, G, thetaForm_apply, LinearMap.comp_apply, LinearMap.smul_apply,
      LinearMap.flip_apply, smul_eq_mul]
    exact hdiag x g hg e e')
  have := LinearMap.congr_fun₂ hFG w w'
  simp only [F, G, thetaForm_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.flip_apply, smul_eq_mul] at this
  exact this

end GlobalTheory.CoefSchur
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaPairAnalyticHypothesesOfDiscreteSeries
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.PairLift GlobalTheory.Chain.RealIt
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PairLift

theorem inputs_of_chosenSeries :
    GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay →
      GlobalTheory.Published.CasselmanWallach → ∀ (D : D7) (X : ProvA), ChosenSeries X → Inputs D X := by
  intro hDS hHC hDec hCW D X hX
  exact
    { chosen := hX
      hc := hHC
      decay := hDec
      bridge := GlobalTheory.CoverModel.modelsAreCoverSeries_all hDS hHC D
      vacChar := GlobalTheory.VacuumCharacter.vacChar D
      lie := GlobalTheory.LieScalar.lieFockAll D
      cpt := GlobalTheory.CompactFockAction.compactFockAll D
      dense := GlobalTheory.FockDensity.fockDense D
      laws := GlobalTheory.Chain.LiftReg.liftProps_obj hDec D
      const := GlobalTheory.T.constantTermLift_isotropicSubspace D
      ext := GlobalTheory.T.gkMapCuspForms_extends_to_smoothVectors hHC hCW D }

end GlobalTheory.PairLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionStableLocalLatticeShapeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.transvectionStable_localLattice_shape : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (i : n) (L : Submodule 𝒪[k] (n → k)) (c : k), 3 ≤ Fintype.card n → c ≠ 0 → (∀ x ∈ L, ∀ (b d : n) (t : 𝒪[k]), b ≠ d → (b ≠ i ∨ t ∈ IsLocalRing.maximalIdeal 𝒪[k]) → x + Pi.single b ((t : k) * x d) ∈ L) → (∀ x ∈ L, ∀ j, c⁻¹ * x j ∈ 𝒪[k]) → (∃ x ∈ L, ∃ j, x j = c) → (∀ x : n → k, x ∈ L ↔ ∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∨ (∀ x : n → k, x ∈ L ↔ (∀ j, c⁻¹ * x j ∈ 𝒪[k]) ∧ ∃ s : 𝒪[k], s ∈ IsLocalRing.maximalIdeal 𝒪[k] ∧ (s : k) = c⁻¹ * x i) := by
  first | exact @GlobalTheory.LatPairStab.stable_lattice_shape | exact GlobalTheory.LatPairStab.stable_lattice_shape | (intros; apply GlobalTheory.LatPairStab.stable_lattice_shape <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueColumnsBranchingMapEquivariantNonzeroCommonStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trueColumns_branchingMap_equivariant_nonzero_common : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (hN : B.R.N B.R.m = (B.R.N B.R.m - 1) + 1), (∀ τ, Formalism.L2.Col.Br.Interlace hN (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m τ) (sgT (D := (I.rec7 l Z)) u τ)) ∧ BrEqv hN _ _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m) (sgT (D := (I.rec7 l Z)) u) (lowOf I l Z u) ∧ (∃ Φ ∈ ValC _ (Formalism.L2.Forms.lamT (D := (I.rec7 l Z)) u B.R.m), lowOf I l Z u Φ ≠ 0) ∧ ∀ (a : I.ι) z c (y : FrN (I.rec7 l Z) (B.R.N B.R.m - 1)), (I.per l u a).lowerMap z c ⟨y.1, y.2⟩ = lowOf I l Z u (fun y' => z c ⟨y'.1, y'.2⟩) y := by
  first | exact @GlobalTheory.TrueBranch.branching_true_columns | exact GlobalTheory.TrueBranch.branching_true_columns | (intros; apply GlobalTheory.TrueBranch.branching_true_columns <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TupleLevelPosOddBadPrimesPrimeToLevelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw GlobalTheory.Fam GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tupleLevel_pos_odd_badPrimes_prime_to_level : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (u : B.Word) (a : I.ι), 0 < levC I.sel (I.tup a) (I.cst a) u ∧ Odd (levC I.sel (I.tup a) (I.cst a) u) ∧ (∀ Q ∈ Formalism.L2.Col.Sall (Pr := B.primes X) I.sel (I.tup a) u, ((B.host.QS * B.host.q * B.host.d : ℕ) : 𝓞 B.host.E) ∉ Q.asIdeal) := by
  first | exact @GlobalTheory.TupLevel.levC_pos_odd_and_off | exact GlobalTheory.TupLevel.levC_pos_odd_and_off | (intros; apply GlobalTheory.TupLevel.levC_pos_odd_and_off <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPrimeCongruentMapsFrameReadingsBound
section
noncomputable section

namespace GlobalTheory.Transport.TwistRead

section Gen

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix
open GlobalTheory.Transport.LevelDatum

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {hc : Formalism.BasicNotions.CMData F E}
  {a b : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

omit [NumberField E] [StarRing E] in
theorem toMatrix_inFr (f : Sp E a ≃ₗ[E] Sp E a) (f' : Sp E b ≃ₗ[E] Sp E b) (x : HomE E a b) :
    LinearMap.toMatrix' f'.toLinearMap * LinearMap.toMatrix' (inFr f f' x) = LinearMap.toMatrix' x * LinearMap.toMatrix' f.toLinearMap := by
  rw [← LinearMap.toMatrix'_comp, ← LinearMap.toMatrix'_comp]
  exact congrArg _ (LinearMap.ext fun z => f'.apply_symm_apply _)

theorem map_ptFr {n : ℕ} {g : GL (Fin n) (AfE F E)} {p : DecoF E n ST SG Q} (h : IsPtOf hc g p) {P : HeightOneSpectrum (𝓞 E)}
    (hPQ : P ∈ Q) (hPG : P ∉ SG) :
    (LinearMap.toMatrix' (ptFr p P).toLinearMap).map (algebraMap E (P.adicCompletion E)) =
      (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.map_apply, Matrix.map_apply, LinearMap.toMatrix'_apply, ptFr_of_mem p hPG hPQ]
  exact (h.fr ⟨P, hPQ⟩ i j).symm

omit [StarRing E] in
theorem map_inv_mul_map {n : ℕ} (P : HeightOneSpectrum (𝓞 E)) (g : GL (Fin n) (AfE F E)) :
    ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) *
      (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P) = 1 := by
  rw [← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem map_read {g : GL (Fin a) (AfE F E)} {g' : GL (Fin b) (AfE F E)} {p : DecoF E a ST SG Q} {p' : DecoF E b ST SG Q}
    (h : IsPtOf hc g p) (h' : IsPtOf hc g' p') {P : HeightOneSpectrum (𝓞 E)} (hPQ : P ∈ Q) (hPG : P ∉ SG) (x : HomE E a b) :
    (LinearMap.toMatrix' (inFr (ptFr p P) (ptFr p' P) x)).map (algebraMap E (P.adicCompletion E)) =
      (mid g g' x).map (adAt F P) := by
  have f1 := congrArg (fun A => Matrix.map A (algebraMap E (P.adicCompletion E))) (toMatrix_inFr (ptFr p P) (ptFr p' P) x)
  simp only [Matrix.map_mul] at f1
  rw [map_ptFr h hPQ hPG, map_ptFr h' hPQ hPG] at f1
  have hx : (LinearMap.toMatrix' x).map (algebraMap E (P.adicCompletion E)) = (adMat F x).map (adAt F P) :=
    Matrix.ext fun i j => (adAt_inclE F P _).symm
  unfold mid
  rw [Matrix.map_mul, Matrix.map_mul, ← hx, Matrix.mul_assoc, ← f1, ← Matrix.mul_assoc, map_inv_mul_map, Matrix.one_mul]

theorem read_sub_le {k y : GL (Fin a) (AfE F E)} {k' y' : GL (Fin b) (AfE F E)} {p q : DecoF E a ST SG Q} {p' q' : DecoF E b ST SG Q}
    (hp : IsPtOf hc k p) (hpN : p.deco.1.N = stdLat E a) (hp' : IsPtOf hc k' p') (hpN' : p'.deco.1.N = stdLat E b)
    (hq : IsPtOf hc (y * k) q) (hq' : IsPtOf hc (y' * k') q') {P : HeightOneSpectrum (𝓞 E)} (hPQ : P ∈ Q) (hPG : P ∉ SG)
    (M₀ : ℕ) (x x₀ : HomE E a b)
    (h : ∀ r s, Valued.v (adAt F P ((mid y y' x - adMat F x₀) r s)) ≤ Valued.v ((M₀ : ℕ) : P.adicCompletion E)) (r : Fin b) (s : Fin a) :
    P.valuation E ((LinearMap.toMatrix' (inFr (ptFr q P) (ptFr q' P) x) - LinearMap.toMatrix' (inFr (ptFr p P) (ptFr p' P) x₀)) r s) ≤
      P.valuation E ((M₀ : ℕ) : E) := by
  have hd : mid (y * k) (y' * k') x - mid k k' x₀ =
      ((k'⁻¹ : GL (Fin b) (AfE F E)) : Matrix (Fin b) (Fin b) (AfE F E)) * (mid y y' x - adMat F x₀) *
        (k : Matrix (Fin a) (Fin a) (AfE F E)) := by
    unfold mid
    rw [_root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul]
    simp only [Matrix.mul_assoc]
  have hA : ∀ r s, Valued.v (adAt F P (((k'⁻¹ : GL (Fin b) (AfE F E)) : Matrix (Fin b) (Fin b) (AfE F E)) r s)) ≤ 1 := fun r s => by
    have := Splice.valued_inv_mul_le (w := P) (hpN' ▸ hp'.lat) (carries_one (F := F) b) le_rfl r s
    rwa [mul_one] at this
  have hK : ∀ r s, Valued.v (adAt F P ((k : Matrix (Fin a) (Fin a) (AfE F E)) r s)) ≤ 1 := fun r s => by
    have := Splice.valued_inv_mul_le (w := P) (carries_one (F := F) a) (hpN ▸ hp.lat) le_rfl r s
    rwa [inv_one, one_mul] at this
  have e1 := congrFun (congrFun (map_read hq hq' hPQ hPG x) r) s
  have e2 := congrFun (congrFun (map_read hp hp' hPQ hPG x₀) r) s
  simp only [Matrix.map_apply] at e1 e2
  rw [← valued_algebraMap, ← valued_algebraMap, map_natCast, Matrix.sub_apply, map_sub, e1, e2, ← map_sub, ← Matrix.sub_apply, hd]
  rw [Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_le _ fun j _ => ?_
  rw [map_mul, map_mul]
  refine (mul_le_of_le_one_right' (hK j s)).trans ?_
  rw [Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul, map_mul]
  exact (mul_le_of_le_one_left' (hA r l)).trans (h l j)

end Gen

end GlobalTheory.Transport.TwistRead

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2.Ker

namespace GlobalTheory.Transport.TwistRead

theorem qread : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (u : B.Word) (a : I.ι) (i : ℕ) (P : Formalism.L2.Col.rowSG (B.primes X) I.sel (I.tup a)),
    P.1 ∈ I.Q a → Disjoint (B.primes X).vGs (I.Q a) →
    ∀ (p q : PtAt B.R I.sel (I.tup a) (I.cst a) u i) (p' q' : PtAt B.R I.sel (I.tup a) (I.cst a) u (i + 1))
    (k y : TC.GA B (B.R.N i)) (k' y' : TC.GA B (B.R.N (i + 1))),
    TC.PtOf k p.1.1 → p.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i) →
    TC.PtOf k' p'.1.1 → p'.1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N (i + 1)) →
    TC.PtOf (y * k) q.1.1 → TC.PtOf (y' * k') q'.1.1 →
    ∀ (M₀ : ℕ) (x x₀ : Formalism.L2.Col.HomE B.fields.E (B.R.N i) (B.R.N (i + 1))),
      GlobalTheory.Transport.CongAt B P.1 M₀ y y' x x₀ →
      ∀ r s, P.1.valuation B.fields.E
        ((LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) q.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) q'.1.1 P) x) -
          LinearMap.toMatrix' (Formalism.L2.Col.inFr (Formalism.L2.Col.frsF I.sel (I.tup a) p.1.1 P) (Formalism.L2.Col.frsF I.sel (I.tup a) p'.1.1 P) x₀)) r s) ≤
        P.1.valuation B.fields.E ((M₀ : ℕ) : B.fields.E) := by
  intro B X I u a i P hP hd p q p' q' k y k' y' hp hpN hp' hpN' hq hq' M₀ x x₀ hC r s
  rw [frsF_eq_ptFr, frsF_eq_ptFr, frsF_eq_ptFr, frsF_eq_ptFr]
  exact read_sub_le hp hpN hp' hpN' hq hq' hP (Finset.disjoint_right.1 hd hP) M₀ x x₀ (fun r s => hC r s) r s

end GlobalTheory.Transport.TwistRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TypeDataLocalRelationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.type_data_local_relation : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} (W : RealPack ex) (u : D.what₂.Word), PkHyp W → ∀ (f : FamCh W u) (v : VCom f.c) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat f.c k ι), f.RowOK → f.ColOK → v.Is → VTie f v → ShapeOff v o → ∀ t j, j < D.R.m → ∃ μ, IsWeilDatumO f.c.ψ _ _ μ μ ((f.t t).kom j) ∧ ∀ i, GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.CharUnramAt D μ (o.p i).v := by
  first | exact @GlobalTheory.Fam.kom_weil_unram | exact GlobalTheory.Fam.kom_weil_unram | (intros; apply GlobalTheory.Fam.kom_weil_unram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldedTermBasePointEqFlatMapPairingStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedTerm_basePoint_eq_flatMap_pairing : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (s : StepFB ψ J B), ∀ (vb : VolM D (σ + 1) J.W₀.rank) (vL : VolM D B.L.rank J.W₀.rank) (y : WO J.W₀ B.L → ℂ) (Ψ : WO J.W B.V → ℂ), Quasi ψ J.W₀ B.L y → IsThetaFunO ψ J.W B.V Ψ → fl ψ J.d B.V s.vS vb s.vU (th J ψ B y) (x0 B) Ψ = tFlat s vL y Ψ ∧ ∀ M : ℝ, (∀ w, ‖y w‖ ≤ M) → ‖tFlat s vL y Ψ‖ₑ ≤ ENNReal.ofReal M * ∫⁻ u, ∫⁻ b in vb.𝓕, ‖J.d.mixS B.V ψ s.vS.μ s.vS.𝓕 Ψ (x0 B ⬝ u.1.1) (x0 B ⬝ b)‖ₑ ∂vb.μ ∂s.vU.ν := by
  first | exact @GlobalTheory.Unf.FB.fl_base_eq_tFlat | exact GlobalTheory.Unf.FB.fl_base_eq_tFlat | (intros; apply GlobalTheory.Unf.FB.fl_base_eq_tFlat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAverageTranslateEqSmulBranchingMapStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.KJInf Formalism.L2.Ker
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAverage_translate_eq_smul_branchingMap : ∀ (ι : Type) [Fintype ι] (N n : ℕ) (hN : N = n + 1) (G : ι → Matrix (Fin N) (Fin N) ℂ) (G' : ι → Matrix (Fin n) (Fin n) ℂ) (lam : ι → DomWeight N) (sg : ι → DomWeight n), (∀ τ, Formalism.L2.Col.Br.Interlace hN (lam τ) (sg τ)) → ∀ T₀, BrEqv hN G G' lam sg T₀ → (∃ Φ ∈ ValC G lam, T₀ Φ ≠ 0) → ∀ (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [MeasurableSpace K] [BorelSpace K] (ν : Measure K) [IsProbabilityMeasure ν] [ν.IsMulLeftInvariant] (r : K → ι → Matrix (Fin n) (Fin n) ℂ), OntoUni r → ∀ (y : Frames G) (yk : K → Frames G), (∀ k, ∃ kt, (∀ τ, GlobalTheory.BranchFormula.IsBlock hN (kt τ) (r k τ) 1) ∧ IsTr kt y (yk k)) → ∀ J ∈ ValC G' sg, ∀ Jk : K → Frames G' → ℂ, (∀ k z z', IsTr (r k) z z' → Jk k z' = J z) → ∃ c : ℂ, ∀ Φ ∈ ValC G lam, ∀ ℓ : (Frames G' → ℂ) →ₗ[ℂ] ℂ, ∫ k, ℓ (Jk k) * Φ (yk k) ∂ν = c * ℓ (T₀ Φ) := by
  first | exact @GlobalTheory.KJAvg.avg_eq_mul_branch | exact GlobalTheory.KJAvg.avg_eq_mul_branch | (intros; apply GlobalTheory.KJAvg.avg_eq_mul_branch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VolumeSeeSawTupleLevelEqSphericalDivIndexStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl GlobalTheory.Fam ValuativeRel IsLocalRing
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.volume_seeSaw_tuple_level_eq_spherical_div_index : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : GlobalTheory.QPl.QFam v t), F.Pins w → (∀ j, j < D.R.m → IsSelfDualC (c.V j) (v.N j) → ∀ (μ : Measure (GfC (c.V j))), μ.IsHaarMeasure → ∀ (U U' : Subgroup (GA D (c.V j))) (b : GA D (c.V j)), b ∈ GfC _ → U ≤ GfC _ → IsCompact (U : Set (GA D (c.V j))) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC (c.V j))) : Set (GfC (c.V j))) → (∀ κ, InK _ (v.N j) (· ∈ w.Q) κ → κ ∈ U) → (∀ g ∈ U, Moves _ g (v.N j) (v.N j) (· ∈ w.Q)) → (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i d hd x, (mt _ g).map (F.Q i).q.pr = ((F.Q i).FY j d hd).β * x.val * ((F.Q i).FY j d hd).γ → x ∈ ((F.Q i).T.lev j d hd).J) → μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((F.Q i).idx j : ℝ) = μ.real {g | b * g.1 * b⁻¹ ∈ U}) ∧ (IsSelfDualC c.T v.NT → (∀ i, IsOpen ((F.Q i).T.levTop.J : Set (GL (F.Q i).Z (F.Q i).k))) → ∀ (μ : Measure (GfC c.T)), μ.IsHaarMeasure → ∀ (U U' : Subgroup (GA D c.T)) (b : GA D c.T), b ∈ GfC _ → U ≤ GfC _ → IsCompact (U : Set (GA D c.T)) → IsOpen ((U.subgroupOf (GfC _) : Subgroup (GfC c.T)) : Set (GfC c.T)) → (∀ κ, InK _ v.NT (· ∈ w.Q) κ → κ ∈ U) → (∀ g ∈ U, Moves _ g v.NT v.NT (· ∈ w.Q)) → (∀ g, g ∈ U' ↔ g ∈ U ∧ ∀ i (x : GL (F.Q i).Z (F.Q i).k), (mt _ g).map (F.Q i).q.pr = (F.Q i).FT.β * x.val * (F.Q i).FT.γ → x ∈ (F.Q i).T.levTop.J) → μ.real {g | b * g.1 * b⁻¹ ∈ U'} * ∏ i, ((F.Q i).idx D.R.m : ℝ) = μ.real {g | b * g.1 * b⁻¹ ∈ U}) := by
  first | exact @GlobalTheory.LevIdx.vol_level_eq | exact GlobalTheory.LevIdx.vol_level_eq | (intros; apply GlobalTheory.LevIdx.vol_level_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepresentationValueAtOriginLeviFactorStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepresentation_value_at_origin_leviFactor : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T) (om₀ : Om S₀ T), IsWeilDatumO ψ S T χS χT om → IsWeilDatumO ψ S₀ T χS χT om₀ → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → (∀ g, d.mixS T ψ μ 𝓕 (om (d.emb0 g, 1) f) 0 = om₀ (g, 1) (d.mixS T ψ μ 𝓕 (f) 0)) ∧ (∀ a : GL (Fin ρ) (AE D), Matrix.GeneralLinearGroup.det a = 1 → d.mixS T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = d.mixS T ψ μ 𝓕 (f) 0) ∧ ∀ a : GL (Fin ρ) (AE D), d.mixS T ψ μ 𝓕 (om (d.levi a, 1) f) 0 = ((((χT (Matrix.GeneralLinearGroup.det a))⁻¹ : Circle) : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.halfMod T.rank a : ℂ)) • d.mixS T ψ μ 𝓕 (f) 0 := by
  first | exact @GlobalTheory.LeviOrigin.value_at_origin | exact GlobalTheory.LeviOrigin.value_at_origin | (intros; apply GlobalTheory.LeviOrigin.value_at_origin <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WittCoreEmbeddingStabilisesIffCoreStabilisesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (latV Moves MonoAt OrthAt PrimAt idAt intAt grpAt colMul Lat SplitPt GoodBF GluedCore IsSumFrame)
open GlobalTheory.SeeSaw (idV dI FI)
open ValuativeRel
open GlobalTheory.Core.Mi.LatMatch
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.wittCoreEmbedding_stabilises_iff_core_stabilises : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (M : Lat S₀) (v : GlobalTheory.FinPl.Pl D) (γ : GA D S₀), MonoAt d L M v → (Moves S (d.emb0 γ) L L (· = v) ↔ Moves S₀ γ M M (· = v)) := by
  first | exact @GlobalTheory.Core.Mi.LatMatch.moves_emb0_iff_moves_of_monoAt | exact GlobalTheory.Core.Mi.LatMatch.moves_emb0_iff_moves_of_monoAt | (intros; apply GlobalTheory.Core.Mi.LatMatch.moves_emb0_iff_moves_of_monoAt <;> assumption)
end

