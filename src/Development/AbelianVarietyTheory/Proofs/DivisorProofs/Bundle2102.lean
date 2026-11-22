import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1616
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSchwartzNe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1862
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1864
import Development.AbelianVarietyTheory.Definitions.Divisors.LiftFrameEmbeddingBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1139
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1214
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2082
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2081
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0201
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CentralInvolutionRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1816
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2079
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0135
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0929
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0012
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2084
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelMapIntegrableDistribution
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open scoped Classical

noncomputable section

namespace GlobalTheory.HaarPull

open GlobalTheory.DiagForm GlobalTheory.DiagUniq

attribute [local instance] GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele
  GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField
  GlobalTheory.DiagForm.measAf GlobalTheory.DiagForm.borelAf

variable {F : Type} [Field F] [NumberField F] {ι κ : Type} [Fintype ι] [Fintype κ]

theorem pureA_mulVec_glue (D : Matrix κ ι F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ)
    (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (p : Vi F ι × Vf F ι) :
    pureA F f g (D.map (algebraMap F (AF F)) *ᵥ glue p) =
      f (fun k => ∑ i, mixedEmbedding F (D k i) * eI F ι p.1 i) *
      g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ p.2) := by
  unfold pureA
  congr 2 <;> funext k
  · refine ((map_sum ((InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp
        (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
        (fun i => algebraMap F (AF F) (D k i) * glue p i) Finset.univ)).trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    refine (map_mul _ _ _).trans ?_
    change InfiniteAdeleRing.ringEquiv_mixedSpace F (algebraMap F (InfiniteAdeleRing F) (D k i)) *
      InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (eI F ι p.1 i)) = _
    rw [RingEquiv.apply_symm_apply, InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]
  · exact (map_sum (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F))
        (fun i => algebraMap F (AF F) (D k i) * glue p i) Finset.univ)

theorem integrable_SB {g : Vf F ι → ℂ} (hg : g ∈ SB (Vf F ι)) : Integrable g Measure.addHaar :=
  hg.1.continuous.integrable_of_hasCompactSupport hg.2

theorem pureA_glue_eq (D : Matrix κ ι F)
    (T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] SchwartzMap (ι → mixedEmbedding.mixedSpace F) ℂ)
    (hT : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (a : ι → mixedEmbedding.mixedSpace F),
        T f a = f (fun k => ∑ i, mixedEmbedding F (D k i) * a i))
    (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :
    (fun p : Vi F ι × Vf F ι => pureA F f g (D.map (algebraMap F (AF F)) *ᵥ glue p)) =
      fun p => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι) (T f) p.1 *
        g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ p.2) := by
  funext p
  rw [pureA_mulVec_glue, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hT]

theorem integrable_glue (D : Matrix κ ι F) (hD : ∀ z : ι → F, D *ᵥ z = 0 → z = 0)
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) :
    Integrable (fun p : Vi F ι × Vf F ι => Φ (D.map (algebraMap F (AF F)) *ᵥ glue p)) (mu F ι) := by
  obtain ⟨T, hT⟩ := GlobalTheory.ArchPull.exists_pull F ι κ D hD
  induction hΦ using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨f, g, hg, rfl⟩ := hx
    rw [pureA_glue_eq D T hT f g]
    exact (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι) (T f)).integrable.mul_prod
      (integrable_SB (GlobalTheory.FinPull.pullback_mem_SB F ι κ D hD g hg))
  | zero => exact integrable_zero _ _ _
  | add x y _ _ hx hy => exact hx.add hy
  | smul c x _ hx => exact hx.smul c

end GlobalTheory.HaarPull

namespace GlobalTheory

open GlobalTheory.DiagForm GlobalTheory.DiagUniq GlobalTheory.HaarPull

theorem integral_pull_injective : ∀ (F : Type) [Field F] [NumberField F] (ι κ : Type) [Fintype ι] [Fintype κ] (D : Matrix κ ι F),
    (∀ z : ι → F, D *ᵥ z = 0 → z = 0) →
    ∀ ν : @Measure (ι → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) ν →
      (∀ Φ ∈ schA F κ, (letI : MeasurableSpace (ι → AF F) := borel _;
        Integrable (fun w => Φ (D.map (algebraMap F (AF F)) *ᵥ w)) ν)) ∧
      ∀ g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ T : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ →L[ℂ] ℂ,
        ∀ f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, (letI : MeasurableSpace (ι → AF F) := borel _;
          ∫ w, pureA F f g (D.map (algebraMap F (AF F)) *ᵥ w) ∂ν) = T f := by
  intro F _ _ ι κ _ _ D hD ν hν
  letI : MeasurableSpace (ι → AF F) := borel _
  haveI : BorelSpace (ι → AF F) := ⟨rfl⟩
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := hν
  haveI : ((mu F ι).map (glueE F ι)).IsAddHaarMeasure := (glueE F ι).isAddHaarMeasure_map _
  have h := Measure.isAddLeftInvariant_eq_smul ν ((mu F ι).map (glueE F ι))
  set c := Measure.addHaarScalarFactor ν ((mu F ι).map (glueE F ι))
  have me := (glueE F ι).toHomeomorph.measurableEmbedding
  refine ⟨fun Φ hΦ => ?_, fun g hg => ?_⟩
  · rw [h]
    refine Integrable.smul_measure_nnreal ?_
    exact me.integrable_map_iff.2 (integrable_glue D hD hΦ)
  · obtain ⟨T, hT⟩ := GlobalTheory.ArchPull.exists_pull F ι κ D hD
    refine ⟨(((c : ℝ) : ℂ) * ∫ v, g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ v) ∂(Measure.addHaar : Measure (Vf F ι))) •
      ((SchwartzMap.integralCLM ℂ (volume : Measure (Vi F ι))).comp
        ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι)).comp T)), fun f => ?_⟩
    rw [h, integral_smul_nnreal_measure]
    change c • ∫ x, pureA F f g (D.map (algebraMap F (AF F)) *ᵥ x) ∂((mu F ι).map (glueE F ι).toHomeomorph) = _
    rw [me.integral_map]
    have e := pureA_glue_eq D T hT f g
    change c • ∫ p, (fun p : Vi F ι × Vf F ι => pureA F f g (D.map (algebraMap F (AF F)) *ᵥ glue p)) p ∂(mu F ι) = _
    rw [e, mu, integral_prod_mul (fun u : Vi F ι => SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (eI F ι) (T f) u)
      (fun v : Vf F ι => g (D.map (algebraMap F (FiniteAdeleRing (𝓞 F) F)) *ᵥ v))]
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, SchwartzMap.integralCLM_apply,
      smul_eq_mul, NNReal.smul_def, Complex.real_smul]
    ring

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimpleModuleLinkageDualWeylLatticeReduction
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CapelliLink

open Formalism.CohomologicalDescent.DepthNonnegative GlobalTheory.ExpFrame Formalism.CohomologicalDescent.LD

theorem pure_step {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] (τ : ι)
    (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam))
    (Fab : Fin N × Fin N → FreeAlgebra O (Letter O N ι))
    (hF : ∀ (p : Fin N × Fin N) (x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ))),
      ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)),
        (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O p.1 p.2 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧
        evalE O N lam P (Fab p) (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y))
    (Φ : FreeAlgebra O (Fin N × Fin N)) :
    ∀ x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ)), ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)),
      (y : MvPolynomial (Fin N × Fin N) O) = evalPol O N Φ (x τ : MvPolynomial (Fin N × Fin N) O) ∧
      evalE O N lam P (FreeAlgebra.lift O Fab Φ) (PiTensorProduct.tprod O x) =
        PiTensorProduct.tprod O (Function.update x τ y) := by
  induction Φ using FreeAlgebra.induction with
  | grade0 r =>
    intro x
    refine ⟨r • x τ, ?_, ?_⟩
    · rw [AlgHom.commutes, Module.algebraMap_end_apply]; rfl
    · rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, MultilinearMap.map_update_smul,
        Function.update_eq_self]
  | grade1 p =>
    intro x
    obtain ⟨y, hy, he⟩ := hF p x
    refine ⟨y, ?_, ?_⟩
    · rw [hy]; simp [evalPol]
    · rw [FreeAlgebra.lift_ι_apply]; exact he
  | mul Φ₁ Φ₂ h₁ h₂ =>
    intro x
    obtain ⟨y₂, hy₂, he₂⟩ := h₂ x
    obtain ⟨y₁, hy₁, he₁⟩ := h₁ (Function.update x τ y₂)
    refine ⟨y₁, ?_, ?_⟩
    · rw [hy₁, Function.update_self, hy₂, map_mul, Module.End.mul_apply]
    · rw [map_mul, map_mul, Module.End.mul_apply, he₂, he₁, Function.update_idem]
  | add Φ₁ Φ₂ h₁ h₂ =>
    intro x
    obtain ⟨y₁, hy₁, he₁⟩ := h₁ x
    obtain ⟨y₂, hy₂, he₂⟩ := h₂ x
    refine ⟨y₁ + y₂, ?_, ?_⟩
    · rw [Submodule.coe_add, hy₁, hy₂, map_add, LinearMap.add_apply]
    · rw [map_add, map_add, LinearMap.add_apply, he₁, he₂, MultilinearMap.map_update_add]

theorem scalar_of {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] (τ : ι)
    (lam : ι → ℕ → ℕ) (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam))
    (Fab : Fin N × Fin N → FreeAlgebra O (Letter O N ι))
    (hF : ∀ (p : Fin N × Fin N) (x : ∀ σ, Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam σ))),
      ∃ y : Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)),
        (y : MvPolynomial (Fin N × Fin N) O) = Formalism.GradedWeylDivisibility.rowDiv O p.1 p.2 1 (x τ : MvPolynomial (Fin N × Fin N) O) ∧
        evalE O N lam P (Fab p) (PiTensorProduct.tprod O x) = PiTensorProduct.tprod O (Function.update x τ y))
    (Φ : FreeAlgebra O (Fin N × Fin N)) (c : O)
    (hΦ : ∀ f ∈ Formalism.GradedWeylDivisibility.dualWeyl O N N (res N (lam τ)), evalPol O N Φ f = c • f) :
    evalE O N lam P (FreeAlgebra.lift O Fab Φ) = c • (1 : Module.End O (NablaT O N lam)) := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  obtain ⟨y, hy, he⟩ := pure_step τ lam P Fab hF Φ x
  have hyc : y = c • x τ := Subtype.ext (by rw [hy, hΦ _ (x τ).2]; rfl)
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, he, hyc,
    MultilinearMap.map_update_smul, Function.update_eq_self]
  simp

def evalA (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) (hP : ∀ σ w, IsProj O N lam σ w (P σ w)) :
    FreeAlgebra O (Letter O N ι) →ₐ[O] alg O N lam :=
  FreeAlgebra.lift O (Sum.elim (grpA O N lam) fun p =>
    ⟨P p.1 p.2, Algebra.subset_adjoin (Or.inr ⟨p.1, p.2, hP p.1 p.2⟩)⟩)

theorem evalA_coe (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) (hP : ∀ σ w, IsProj O N lam σ w (P σ w))
    (Φ : FreeAlgebra O (Letter O N ι)) :
    ((evalA O N lam P hP Φ : alg O N lam) : Module.End O (NablaT O N lam)) = evalE O N lam P Φ := by
  have h : (alg O N lam).val.comp (evalA O N lam P hP) = evalE O N lam P := by
    apply FreeAlgebra.hom_ext
    funext p
    rcases p with g | p
    · simp [evalA, evalE, grpA]
    · simp [evalA, evalE]
  exact DFunLike.congr_fun h Φ

theorem compat {O : Type} [CommRing O] {N : ℕ} {ι : Type} [DecidableEq ι] {lam mu : ι → ℕ → ℕ} {ϖ : O}
    {Gm : Type} [AddCommGroup Gm] [Module (alg O N lam) Gm]
    (P : ι → (Fin N → ℕ) → Module.End O (NablaT O N lam)) (hP : ∀ σ w, IsProj O N lam σ w (P σ w))
    (Q : ι → (Fin N → ℕ) → Module.End O (NablaT O N mu)) (hQ : ∀ σ w, IsProj O N mu σ w (Q σ w))
    (ψ : Gm →+ (NablaT O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu))))
    (h2 : ∀ (c : O) z, ψ (algebraMap O (alg O N lam) c • z) = c • ψ z)
    (h3 : ∀ g z y, ψ z = Submodule.Quotient.mk y →
      ψ (grpA O N lam g • z) = Submodule.Quotient.mk (grp O N mu g y))
    (h4 : ∀ τ w (a : alg O N lam) (a' : Module.End O (NablaT O N mu)), IsProj O N lam τ w a →
      IsProj O N mu τ w a' → ∀ z y, ψ z = Submodule.Quotient.mk y → ψ (a • z) = Submodule.Quotient.mk (a' y))
    (Φ : FreeAlgebra O (Letter O N ι)) :
    ∀ z y, ψ z = Submodule.Quotient.mk y →
      ψ (evalA O N lam P hP Φ • z) = Submodule.Quotient.mk (evalE O N mu Q Φ y) := by
  induction Φ using FreeAlgebra.induction with
  | grade0 r =>
    intro z y h
    rw [AlgHom.commutes, AlgHom.commutes, h2, h, Module.algebraMap_end_apply, Submodule.Quotient.mk_smul]
  | grade1 p =>
    intro z y h
    rcases p with g | ⟨σ, w⟩
    · simp only [evalA, evalE, FreeAlgebra.lift_ι_apply, Sum.elim_inl]; exact h3 g z y h
    · simp only [evalA, evalE, FreeAlgebra.lift_ι_apply, Sum.elim_inr]
      exact h4 σ w _ (Q σ w) (hP σ w) (hQ σ w) z y h
  | mul Φ₁ Φ₂ h₁ h₂ =>
    intro z y h
    rw [map_mul, map_mul, mul_smul, Module.End.mul_apply]
    exact h₁ _ _ (h₂ z y h)
  | add Φ₁ Φ₂ h₁ h₂ =>
    intro z y h
    rw [map_add, map_add, add_smul, map_add, LinearMap.add_apply, h₁ z y h, h₂ z y h, Submodule.Quotient.mk_add]

theorem dvd_of_smul_eq_zero {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {V : Type}
    [AddCommGroup V] [Module O V] {ϖ : O} (hϖ : Irreducible ϖ) (d : O) (y : V)
    (hne : (Submodule.Quotient.mk y : V ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O V)) ≠ 0)
    (h0 : d • (Submodule.Quotient.mk y : V ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O V)) = 0) : ϖ ∣ d := by
  by_contra hd
  have hu : IsUnit d := by
    by_contra hnu
    have hm : d ∈ IsLocalRing.maximalIdeal O := hnu
    rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hm
    exact hd hm
  obtain ⟨u, rfl⟩ := hu
  apply hne
  have h1 := congrArg (fun q => (↑u⁻¹ : O) • q) h0
  simpa [smul_smul] using h1

theorem int_dvd_of {O : Type} [CommRing O] {ϖ : O} (hϖ : ¬ IsUnit ϖ) {l : ℕ} (hl : l.Prime)
    (hϖl : ϖ ∣ (l : O)) (d : ℤ) (hd : ϖ ∣ (d : O)) : (l : ℤ) ∣ d := by
  by_contra h
  have hc : IsCoprime (l : ℤ) d := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h' : Nat.Coprime l d.natAbs := (Nat.Prime.coprime_iff_not_dvd hl).2 (fun h' => h (Int.natCast_dvd.2 h'))
    simpa [Int.gcd] using h'
  obtain ⟨u, v, huv⟩ := hc
  have h1 : ϖ ∣ ((u * l + v * d : ℤ) : O) := by
    push_cast
    exact dvd_add (dvd_mul_of_dvd_right hϖl _) (dvd_mul_of_dvd_right hd _)
  rw [huv, Int.cast_one] at h1
  exact hϖ (isUnit_of_dvd_one h1)

set_option synthInstance.maxHeartbeats 400000 in

theorem linkage : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type)
    [Fintype ι] [DecidableEq ι] (lam : ι → ℕ → ℕ) (mu : ι → ℕ → ℕ) (l : ℕ) (ϖ : O), l.Prime → Irreducible ϖ →
    ϖ ∣ (l : O) → (∀ τ, Antitone (res N (lam τ))) → (∀ τ, Antitone (res N (mu τ))) →
    ∀ (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm → SubQ O N lam ϖ Gm →
    Embeds O N lam mu ϖ Gm → ∀ τ,
    (∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))) =
      ∏ a : Fin N, (Polynomial.X + Polynomial.C (((mu τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l)) := by
  intro O _ _ _ _ N ι _ _ lam mu l ϖ hl hϖ hϖl hlam hmu Gm _ _ _ hSub hEmb τ
  obtain ⟨U, π, hπ, -⟩ := hSub
  obtain ⟨ψ, hψ, h2, h3, h4⟩ := hEmb
  choose P hP _ using fun σ w => GlobalTheory.T.existsUnique_dualWeylWeightProjector O N ι lam σ w
  choose Q hQ _ using fun σ w => GlobalTheory.T.existsUnique_dualWeylWeightProjector O N ι mu σ w
  obtain ⟨M, hM⟩ : ∃ M, M = ∑ c : Fin N, lam τ c + ∑ c : Fin N, mu τ c := ⟨_, rfl⟩
  choose Fab hFab using fun p : Fin N × Fin N => GlobalTheory.T.polarisationOperator_formula_groupAndProjectors O N ι τ M p.1 p.2
  obtain ⟨Fk, hFk⟩ := GlobalTheory.T.capelliCoeff_dualWeyl_eq_coeff_prod O N
  have hscal : ∀ (nu : ι → ℕ → ℕ) (R : ι → (Fin N → ℕ) → Module.End O (NablaT O N nu)),
      (∀ σ, Antitone (res N (nu σ))) → (∀ σ w, IsProj O N nu σ w (R σ w)) → ∑ c : Fin N, nu τ c ≤ M → ∀ k,
      evalE O N nu R (FreeAlgebra.lift O Fab (Fk k)) =
        (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((nu τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • 1 := by
    intro nu R hnu hR hb k
    apply scalar_of τ nu R Fab (fun p x => hFab p nu R hnu hR hb x)
    intro f hf
    exact hFk (res N (nu τ)) (hnu τ) f hf k
  obtain ⟨z, hz⟩ := exists_ne (0 : Gm)
  obtain ⟨u, rfl⟩ := hπ z
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (ψ (π u))
  have hne : (Submodule.Quotient.mk y : NablaT O N mu ⧸ (Ideal.span {ϖ} • ⊤ : Submodule O (NablaT O N mu))) ≠ 0 := by
    rw [hy]; intro h; apply hz; apply hψ; rw [h, map_zero]
  have key : ∀ k, ϖ ∣ ((((∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k -
      (∏ a : Fin N, (Polynomial.X + Polynomial.C (((mu τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ)) : O) := by
    intro k
    apply dvd_of_smul_eq_zero hϖ _ y hne
    have hL := hscal lam P hlam hP (by omega) k
    have hMu := hscal mu Q hmu hQ (by omega) k
    have hc := compat P hP Q hQ ψ h2 h3 h4 (FreeAlgebra.lift O Fab (Fk k)) (π u) y hy.symm
    have hA : evalA O N lam P hP (FreeAlgebra.lift O Fab (Fk k)) • π u =
        algebraMap O (alg O N lam) (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • π u := by
      have hu' : evalA O N lam P hP (FreeAlgebra.lift O Fab (Fk k)) • u =
          algebraMap O (alg O N lam) (((∏ a : Fin N, (Polynomial.X + Polynomial.C (((lam τ a : ℤ) - (a : ℕ) : ℤ)))).coeff k : ℤ) : O) • u := by
        apply Subtype.ext
        change ((evalA O N lam P hP _ : alg O N lam) : Module.End O _) (u : NablaT O N lam) =
          ((algebraMap O (alg O N lam) _ : alg O N lam) : Module.End O _) (u : NablaT O N lam)
        rw [evalA_coe, hL, LinearMap.smul_apply, Module.End.one_apply, Subalgebra.coe_algebraMap,
          Module.algebraMap_end_apply]
      rw [← π.map_smul, hu', π.map_smul]
    rw [hA, h2, hMu, ← hy] at hc
    rw [Int.cast_sub, sub_smul, sub_eq_zero, hc]
    simp [Submodule.Quotient.mk_smul]
  have hmap : ∀ nu : ι → ℕ → ℕ,
      (∏ a : Fin N, (Polynomial.X + Polynomial.C (((nu τ a : ℤ) - (a : ℕ) : ℤ) : ZMod l))) =
        (∏ a : Fin N, (Polynomial.X + Polynomial.C (((nu τ a : ℤ) - (a : ℕ) : ℤ)))).map (Int.castRingHom (ZMod l)) := by
    intro nu; simp [Polynomial.map_prod]
  rw [hmap lam, hmap mu]
  ext k
  rw [Polynomial.coeff_map, Polynomial.coeff_map, eq_intCast, eq_intCast, ZMod.intCast_eq_intCast_iff_dvd_sub, ← neg_sub]
  exact dvd_neg.2 (int_dvd_of hϖ.not_isUnit hl hϖl _ (key k))

end GlobalTheory.CapelliLink

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallUnipotentUnitaryElementIsOneProofStatement
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallUnipotentUnitaryElementIsOne_proof : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], GlobalTheory.IndefiniteRowSideFullHecke.SmallUnipotentElements.SmallElementStatement E := by
  first | exact @GlobalTheory.SmallElement.smallElement | exact GlobalTheory.SmallElement.smallElement | (intros; apply GlobalTheory.SmallElement.smallElement <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPartRealisationWithScalarsCharOfWeak
section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn

theorem splitPartRealisationWithScalars_char_of_weak : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Y : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Y cX) (Csz : ℝ) (p : PtAt ex Csz), p.R.toRealDat.ExAt → SingleIndexPlacesAreTwisted p → (R2 p).Char (F2 p) := by
  intro D L hT Gi Gl Kc Y cX ex Csz p hE hW
  have hc := Formalism.IndefR.Links.RealDat3.characterisation_of_weak p.charW hE
  exact GlobalTheory.BigOn.char_charOf D _ _ _ p.P.A3.A _ p.R.toRealDat (F2 p) hc.lev ⟨hc.grp.red_R, hc.grp.red_L, hc.grp.levels, hc.grp.record, hc.grp.chiW⟩ hc.fam hc.models hc.chain hc.thP
    ⟨GlobalTheory.T.splitPart_nonzeroIndexPlaces_twisted D L hT Gi Gl Kc Y cX ex Csz p hW, hc.tup.mu_off, hc.tup.mu_used, hc.tup.mu_ne, hc.tup.mu_conj, hc.tup.mu_on⟩

end GlobalTheory.BigOn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepCharacterUniformiserValueUnitAwayTwistStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Chars Base stepFac chrW eps idealVal gauss unifAt PsiUnr)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.stepCharacter_uniformiserValue_unit_away_twist : ∀ {D : D7} {T : Type} {Lc : LevCh D T} {sc : Consts} (G : GridData Lc sc) (W : G.Weil) (S : GridChoice W Set.univ) {μ₀ : T},
    Lc.Is μ₀ → NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (t : T) {v : HeightOneSpectrum (𝓞 D.host.F)}
      (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      (Lc.C.mu0 j).UnrAt (GlobalTheory.AdelicU.splitPrime τ) → (G.ch.chiH (D.R.m - i)).UnrAt (GlobalTheory.AdelicU.splitPrime τ) →
      GlobalTheory.AdelicU.splitPrime τ ∈ twPl G t →
      ∃ x : D.what₂.LL, D.what₂.embLL x = ((chrW (GlobalTheory.SqStep.chs G i j t).ν τ (unifAt v) : ℂˣ) : ℂ) ∧
        GlobalTheory.Square.IsAwayUnit (Qn G t) x := by
  first | exact @GlobalTheory.TwistStepVal.step_val | exact GlobalTheory.TwistStepVal.step_val | (intros; apply GlobalTheory.TwistStepVal.step_val <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TameKernelTypePlaceThetaVectorLatticeFixed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.KerTypeVec

theorem typeVec_fixed : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ (eg eQ : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum eQ Q → IsTypeVec R i eg fg → IsSelfDualC (Vc D i) (R.ΛV i) ∧ IsSelfDualC (Wc D i) (R.ΛW i) ∧ IsThetaFunO R.ψ (Vc D i) (Wc D i) fg ∧ ∀ u ∈ latAll (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i), (IsHalf eQ u ∨ IsHalf (cA D eQ) u) → heisO R.ψ (Vc D i) (Wc D i) u fg = fg := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC _ i _ ξ χ ξR Q ω φ hK hQt eg eQ fg heg heQ hfg
  obtain ⟨t, hQt⟩ := hQt
  have sdV : IsSelfDualC (Vc D i) (R.ΛV i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βV i)
  have sdW : IsSelfDualC (Wc D i) (R.ΛW i) :=
    GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hC.lev.βW i)
  have hvac := hK.vecOf.1
  have hψ : IsStdChar D R.ψ (-1) := hvac.1
  have hth0 : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vacP i) := hvac.2.theta
  have hlat := hvac.2.lat
  have fixQ := Formalism.IndefR.Fin.LevelGroupLemmas.Lat.heisO_fix_of_latVac R.ψ hlat heQ
  have hQpl := hK.pl
  have hdisj : Disjoint R.Pg (R.Q t) := Formalism.IndefR.Fin.disjoint_Pg_Q R.toLevCh hC.lev t
  obtain ⟨⟨esg, hesg, hegs⟩, -⟩ := heg
  obtain ⟨⟨esQ, hesQ, heQs⟩, -⟩ := heQ
  have h1 : eQ * eg = 0 := by
    rw [hegs, heQs, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun P' hP' => Finset.sum_eq_zero fun P hP => ?_
    exact Formalism.IndefR.Fin.idem_orth ((hQpl P' hP').2 P' hP') (hesQ P' hP') (hesg P hP)
      (fun h => Finset.disjoint_left.1 hdisj hP (h ▸ hQt hP'))
  have h2 : eQ * cA D eg = 0 := by
    rw [hegs, heQs, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_eq_zero fun P' hP' => Finset.sum_eq_zero fun P hP => ?_
    refine Formalism.IndefR.Fin.idem_orth_conj ((hQpl P' hP').2 P' hP') (hesQ P' hP') (hesg P hP) fun hc => ?_
    obtain ⟨⟨q, hq, hcard, -, hqg⟩, -⟩ := hQpl P' hP'
    obtain ⟨k, hk⟩ := (hC.lev.Pg P).1 hP
    exact Formalism.IndefR.Fin.not_two_primes P.isPrime.ne_top hq (D.host.g_prime k) (hqg k)
      (Formalism.IndefR.Fin.nat_mem_of_conj hc (Formalism.IndefR.Fin.char_mem hq hcard))
      (Formalism.IndefR.Fin.g_mem_of_div R.toLevCh.C hk)
  have h3 : eg * cA D eQ = 0 := by
    have := congrArg (cA D) h2
    rwa [map_mul, Formalism.L2.Theta.cA_cA, map_zero, mul_comm] at this
  have h4 : cA D eg * cA D eQ = 0 := by rw [← map_mul, mul_comm, h1, map_zero]
  refine ⟨sdV, sdW, GlobalTheory.VecTheta.isThetaFunO_of_thetaAt hψ hvac.2.inf hfg hth0, fun u hu hh => ?_⟩
  refine GlobalTheory.VacFix.heisO_fix_of_isThetaAt D R.ψ _ _ (cA D eg) _ 1 (R.vacP i) _ fg u hfg
    (fun a b => ?_) (fun a b => ?_) (fixQ u hu hh)
  · rcases hh with hh | hh
    · rw [← hh a b, ← mul_assoc, mul_comm (cA D eg), h2, zero_mul]
    · rw [← hh a b, ← mul_assoc, h4, zero_mul]
  · rw [Formalism.L2.Theta.cA_cA]
    rcases hh with hh | hh
    · rw [← hh a b, ← mul_assoc, mul_comm eg, h1, zero_mul]
    · rw [← hh a b, ← mul_assoc, h3, zero_mul]

end GlobalTheory.KerTypeVec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusActionModelCoordinatesStatement
section
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_action_model_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' →
    ∀ (g : UA σ X.J) (u : Fin n × Fin d → ℝ), (∀ j, 0 < u j) →
    (∀ z : Matrix (Fin n) (Fin d) (AE F E), M.co.e (mat g * z) =
      (fun j => GlobalTheory.TorusTheta.infScale F ((u j)⁻¹) * (M.co.e z).1 j,
       fun j => GlobalTheory.TorusTheta.infScale F (u j) * (M.co.e z).2 j)) →
    ∃ κ : ℂ, ‖κ‖ ^ 2 = ∏ j, u j ^ Module.finrank ℚ F ∧
      ∀ Φ ∈ schA F (Fin n × Fin d), ∀ x, om (g, 1) Φ x = κ * Φ (fun j => GlobalTheory.TorusTheta.infScale F (u j) * x j) := by
  first | exact @GlobalTheory.TorusDilate.main | exact GlobalTheory.TorusDilate.main | (intros; apply GlobalTheory.TorusDilate.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistCharacterOfArtinStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_character_of_artin : GlobalTheory.Published.GlobalArtinReciprocity → TwAdm → TwChr := by
  first | exact @GlobalTheory.TwistChr.twChr_of_twAdm | exact GlobalTheory.TwistChr.twChr_of_twAdm | (intros; apply GlobalTheory.TwistChr.twChr_of_twAdm <;> assumption)
end

