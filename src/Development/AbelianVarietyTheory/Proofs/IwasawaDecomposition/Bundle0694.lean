import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsExtendResidue
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0040
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0655
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0678
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0619
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0446
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0470
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0471
import Formalism.LocalToGlobal.HilbertRowConditions.RowPinMin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0601
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0659
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceBoundedOfAevalMonicEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0652
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0567
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SpanRTensorRangeTensorAction
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open scoped TensorProduct
open GlobalTheory.EigenSplit GlobalTheory.HTLat GlobalTheory.TotalFrame

namespace GlobalTheory.RedEig

theorem rTensor_mul_one_tmul {O R k : Type} [CommRing O] [CommRing R] [CommRing k] (ρ₀ : R →+* k) (χ : O →+* R) (e : R ⊗[ℤ] O)
    (he : ∀ a : O, e * ((1 : R) ⊗ₜ[ℤ] a) = χ a • e) (a : O) :
    ρ₀.toIntAlgHom.toLinearMap.rTensor O e * ((1 : k) ⊗ₜ[ℤ] a) = ρ₀ (χ a) • ρ₀.toIntAlgHom.toLinearMap.rTensor O e := by
  let Φ := Algebra.TensorProduct.map ρ₀.toIntAlgHom (AlgHom.id ℤ O)
  have hΦ : ∀ t, ρ₀.toIntAlgHom.toLinearMap.rTensor O t = Φ t := fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul r b => simp [Φ]
    | add x y hx hy => rw [map_add, map_add, hx, hy]
  have hsm : ∀ (r : R) t, Φ (r • t) = ρ₀ r • Φ t := fun r t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul s b => simp [Φ, TensorProduct.smul_tmul']
    | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]
  rw [hΦ, ← hsm, ← he a, map_mul]
  simp [Φ]

theorem span_rTensor_range_tensorAction {O R k Λ : Type} [CommRing O] [CommRing R] [CommRing k] [AddCommGroup Λ] [Module O Λ]
    (ρ₀ : R →+* k) (e : R ⊗[ℤ] O) :
    Submodule.span k ((ρ₀.toIntAlgHom.toLinearMap.rTensor Λ) ''
      (LinearMap.range (tensorAction (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) e) : Set (R ⊗[ℤ] Λ)))
    = LinearMap.range (tensorAction (baseChangeAction k (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ))
        (ρ₀.toIntAlgHom.toLinearMap.rTensor O e)) := by
  set red := ρ₀.toIntAlgHom.toLinearMap.rTensor Λ
  have key : ∀ (e : R ⊗[ℤ] O) (m : R ⊗[ℤ] Λ),
      red (tensorAction (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) e m)
        = tensorAction (baseChangeAction k (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ))
            (ρ₀.toIntAlgHom.toLinearMap.rTensor O e) (red m) := by
    intro e m
    induction e using TensorProduct.induction_on with
    | zero => simp
    | tmul r a =>
      rw [LinearMap.rTensor_tmul, tensorAction_tmul, tensorAction_tmul]
      induction m using TensorProduct.induction_on with
      | zero => simp
      | tmul s l => simp [red, TensorProduct.smul_tmul']
      | add x y hx hy => rw [map_add, smul_add, map_add, hx, hy, map_add, map_add, smul_add]
    | add x y hx hy => rw [map_add, LinearMap.add_apply, map_add, hx, hy, map_add, map_add, LinearMap.add_apply]
  have hspan : Submodule.span k (Set.range red) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    induction x using TensorProduct.induction_on with
    | zero => exact Submodule.zero_mem _
    | tmul c l =>
      have : c ⊗ₜ[ℤ] l = c • red (1 ⊗ₜ l) := by simp [red, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
    | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  have himg : (red '' (LinearMap.range (tensorAction (baseChangeAction R (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ)) e) : Set (R ⊗[ℤ] Λ)))
      = (tensorAction (baseChangeAction k (Module.toModuleEnd ℤ Λ : O →+* Module.End ℤ Λ))
            (ρ₀.toIntAlgHom.toLinearMap.rTensor O e)) '' Set.range red := by
    ext y
    simp only [LinearMap.coe_range, Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
      exact ⟨red m, ⟨m, rfl⟩, (key e m).symm⟩
    · rintro ⟨_, ⟨m, rfl⟩, rfl⟩
      exact ⟨_, ⟨m, rfl⟩, key e m⟩
  rw [himg, Submodule.span_image, hspan, Submodule.map_top]

theorem baseChangeAction_regular_apply {O R : Type} [CommRing O] [CommRing R] (a : O) (t : R ⊗[ℤ] O) :
    baseChangeAction R (Module.toModuleEnd ℤ O : O →+* Module.End ℤ O) a t = t * ((1 : R) ⊗ₜ[ℤ] a) := by
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul r b => simp [Algebra.TensorProduct.tmul_mul_tmul, mul_comm]
  | add x y hx hy => rw [map_add, hx, hy, add_mul]

theorem exists_generator {V M : Type} [CommRing V] [Nontrivial V] [AddCommGroup M] [Module V M] (P : Submodule V M)
    [Module.Free V P] [Module.Finite V P] (h1 : Module.finrank V P = 1) {Q : Submodule V M} (hQ : IsCompl P Q) :
    ∃ e ∈ P, P ≤ Submodule.span V {e} ∧ ∃ f : M →ₗ[V] V, f e = 1 := by
  let b := Module.finBasisOfFinrankEq V P h1
  refine ⟨b 0, (b 0).2, fun x hx => ?_, (b.coord 0).comp (Submodule.linearProjOfIsCompl P Q hQ), ?_⟩
  · have := b.sum_repr ⟨x, hx⟩
    rw [Fin.sum_univ_one] at this
    rw [Submodule.mem_span_singleton]
    exact ⟨b.repr ⟨x, hx⟩ 0, by simpa using congrArg Subtype.val this⟩
  · rw [LinearMap.comp_apply, show P.linearProjOfIsCompl Q hQ (b 0) = b 0 from
      Submodule.linearProjOfIsCompl_apply_left hQ _]
    simp

theorem exists_eigBar_eq_range : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (p : ℕ) (ct : At S κ p) (τ : PsiT D),
  ∃ ε : ct.kbar ⊗[ℤ] 𝓞 D.host.E, ε ≠ 0 ∧
    (∀ a : 𝓞 D.host.E, ε * ((1 : ct.kbar) ⊗ₜ[ℤ] a) = ct.ρ₀ (embV κ.c ct.W (embOf D τ) a) • ε) ∧
    ct.eigBar τ = LinearMap.range (tensorAction (baseChangeAction ct.kbar (Module.toModuleEnd ℤ S.Dw.La : 𝓞 D.host.E →+* Module.End ℤ S.Dw.La)) ε) := by
  intro D A N j S κ p ct τ
  let σ : (D.host.E →+* ℂ) → 𝓞 D.host.E →+* ct.V₀ := fun i => embV κ.c ct.W i
  have hσ : Function.Injective σ := by
    intro i i' h
    refine IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 D.host.E)) (RingHom.ext fun a => ?_)
    have := congrArg (fun g : 𝓞 D.host.E →+* ct.V₀ => (((g a : ct.V₀) : κ.c.F) : ℂ)) h
    exact this
  have hc : Fintype.card (D.host.E →+* ℂ) = Module.finrank ℚ D.host.E := NumberField.Embeddings.card _ _
  have h1 := GlobalTheory.T.finrank_eigenspace_embedding_one σ hσ hc (embOf D τ)
  set P := eigenSub (baseChangeAction ct.V₀ (Module.toModuleEnd ℤ (𝓞 D.host.E) : 𝓞 D.host.E →+* Module.End ℤ (𝓞 D.host.E))) (σ (embOf D τ)) with hP
  have : Module.Free ct.V₀ P := free_eigenSub_of_valuationRing _ _
  have : Module.Finite ct.V₀ P := finite_eigenSub_of_valuationRing _ _
  obtain ⟨Q, hQ⟩ := exists_isCompl_eigenSub_of_valuationRing
    (baseChangeAction ct.V₀ (Module.toModuleEnd ℤ (𝓞 D.host.E) : 𝓞 D.host.E →+* Module.End ℤ (𝓞 D.host.E))) (σ (embOf D τ))
  obtain ⟨e, he, hle, f, hf⟩ := exists_generator P h1 hQ
  have heig : ∀ a : 𝓞 D.host.E, e * ((1 : ct.V₀) ⊗ₜ[ℤ] a) = σ (embOf D τ) a • e := fun a => by
    rw [← baseChangeAction_regular_apply]; exact mem_eigenSub.1 he a
  have hρ : ∀ x, ct.ρ₀ x = 0 → x ∈ IsLocalRing.maximalIdeal ct.V₀ := fun x hx => by
    rw [At.ρ₀, RingHom.comp_apply] at hx
    exact (IsLocalRing.residue_eq_zero_iff x).1 ((algebraMap (IsLocalRing.ResidueField ct.V₀) ct.kbar).injective (hx.trans (map_zero _).symm))
  have : Module.Finite (𝓞 D.host.E) S.Dw.La := S.Dw.fin
  have : Module.Projective (𝓞 D.host.E) S.Dw.La := S.Dw.proj
  refine ⟨ct.ρ₀.toIntAlgHom.toLinearMap.rTensor _ e, GlobalTheory.T.rTensor_residue_nonzero_of_split ct.ρ₀ hρ e f hf, rTensor_mul_one_tmul ct.ρ₀ _ e heig, ?_⟩
  rw [At.eigBar, At.eigLat, GlobalTheory.T.eigenspace_rank_one_span (σ (embOf D τ)) e he hle]
  exact span_rTensor_range_tensorAction ct.ρ₀ e

end GlobalTheory.RedEig
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkSpecializesCompatRingMap
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.TorRef

theorem stalkClosedPointTo_comp_spMap_specializes (X : Scheme.{0}) {R W : Type} [CommRing R] [IsLocalRing R]
    [CommRing W] [IsLocalRing W] (ξ : Sp R ⟶ X) (g : R →+* W)
    (hs : (spMap g ≫ ξ) (closedPoint W) ⤳ ξ (closedPoint R)) (a : X.presheaf.stalk (ξ (closedPoint R))) :
    (Scheme.stalkClosedPointTo (spMap g ≫ ξ)).hom ((X.presheaf.stalkSpecializes hs).hom a) =
      g ((Scheme.stalkClosedPointTo ξ).hom a) := by
  have key : X.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo (spMap g ≫ ξ) =
      Scheme.stalkClosedPointTo ξ ≫ CommRingCat.ofHom g := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (ξ (closedPoint R))), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.Spec_stalkClosedPointTo_fromSpecStalk,
      Spec.map_comp, Category.assoc, Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  exact congrArg (fun q => q.hom a) key

end GlobalTheory.TorRef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolCell

namespace GlobalTheory.PolFan

section Depth

variable {O : Type} [CommRing O] (bar : O → O) (ψ w : InvFun O)

def IsStarDepth {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) (t : ℝ) : Prop :=
  0 ≤ t ∧ ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (v : LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
    v ∈ balForms bar X ∧ (∀ y, 0 ≤ v y y) ∧ w.evalZ v = 1 ∧ InRCone γ v ∧ B ∈ rcone γ ∧ B - t • toReal v ∈ rcone γ

def depthSet (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : Set ℝ :=
  {t | ∃ (X₁ : Type) (_ : AddCommGroup X₁) (_ : Module O X₁) (_ : Module.Finite O X₁) (r : (Fin n → O) →ₗ[O] X₁)
    (B₁ : X₁ →ₗ[ℤ] X₁ →ₗ[ℤ] ℝ), Function.Surjective r ∧ (∀ x, (∀ y, B₁ x y = 0) → x = 0) ∧
    (∀ a b, B a b = B₁ (r a) (r b)) ∧ IsStarDepth bar ψ w B₁ t}

variable {bar ψ w}

theorem depthSet_comp {n m : ℕ} {r : (Fin n → O) →ₗ[O] (Fin m → O)} (hr : Function.Surjective r)
    (B : (Fin m → O) → (Fin m → O) → ℝ) : depthSet bar ψ w n (fun a b => B (r a) (r b)) = depthSet bar ψ w m B := by
  ext t
  constructor
  · rintro ⟨X₁, i1, i2, i3, ρ, B₁, hρ, hrad, hB, hd⟩
    have hker : LinearMap.ker r ≤ LinearMap.ker ρ := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      refine hrad _ fun y => ?_
      obtain ⟨y', rfl⟩ := hρ y
      have h1 := hB x y'
      have h2 := hB 0 y'
      simp only [hx, map_zero, LinearMap.zero_apply] at h1 h2
      rw [← h1, h2]
    let ρ' : (Fin m → O) →ₗ[O] X₁ :=
      (LinearMap.ker r).liftQ ρ hker ∘ₗ (r.quotKerEquivOfSurjective hr).symm.toLinearMap
    have hρ' : ∀ a, ρ' (r a) = ρ a := fun a => by
      have : (r.quotKerEquivOfSurjective hr).symm (r a) = Submodule.Quotient.mk a := by
        rw [LinearEquiv.symm_apply_eq]; rfl
      simp only [ρ', LinearMap.comp_apply, LinearEquiv.coe_coe, this, Submodule.liftQ_apply]
    refine ⟨X₁, i1, i2, i3, ρ', B₁, fun x => ?_, hrad, fun a b => ?_, hd⟩
    · obtain ⟨a, rfl⟩ := hρ x
      exact ⟨r a, hρ' a⟩
    · obtain ⟨a, rfl⟩ := hr a
      obtain ⟨b, rfl⟩ := hr b
      rw [hρ', hρ']
      exact hB a b
  · rintro ⟨X₁, i1, i2, i3, ρ, B₁, hρ, hrad, hB, hd⟩
    exact ⟨X₁, i1, i2, i3, ρ ∘ₗ r, B₁, hρ.comp hr, hrad, fun a b => hB (r a) (r b), hd⟩

theorem depthSet_zero (B : (Fin 0 → O) → (Fin 0 → O) → ℝ) : depthSet bar ψ w 0 B = ∅ := by
  refine Set.eq_empty_of_forall_notMem fun t ⟨X₁, i1, i2, i3, ρ, B₁, hρ, _, _, _, _, _, v, _, _, _, hv, _⟩ => ?_
  haveI : Subsingleton X₁ := ⟨fun x y => by
    obtain ⟨a, rfl⟩ := hρ x
    obtain ⟨b, rfl⟩ := hρ y
    rw [Subsingleton.elim a b]⟩
  rw [InvFun.evalZ, w.eval_of_subsingleton] at hv
  exact zero_ne_one hv

variable (bar ψ w)

def starDepth : InvFun O where
  toFun n B := sSup (depthSet bar ψ w n B)
  inv n m r hr B := by rw [depthSet_comp hr]
  zero B := by rw [depthSet_zero, Real.sSup_empty]

def starFun (K D : ℕ) : InvFun O where
  toFun n B := D * (K * ψ.toFun n B + (starDepth bar ψ w).toFun n B)
  inv n m r hr B := by simp only [InvFun.inv _ _ _ r hr]
  zero B := by simp only [InvFun.zero, mul_zero, add_zero]

variable {bar ψ w}

theorem starDepth_toFun_nonneg (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : 0 ≤ (starDepth bar ψ w).toFun n B :=
  Real.sSup_nonneg fun _ h => h.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.choose_spec.2.2.2.1

theorem starDepth_eval_nonneg {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (B : X → X → ℝ) :
    0 ≤ (starDepth bar ψ w).eval X B := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.eval_eq _ hr]
  exact starDepth_toFun_nonneg n _

theorem starFun_eval {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (K D : ℕ) (B : X → X → ℝ) :
    (starFun bar ψ w K D).eval X B = D * (K * ψ.eval X B + (starDepth bar ψ w).eval X B) := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' O X
  rw [InvFun.eval_eq _ hr, InvFun.eval_eq _ hr, InvFun.eval_eq _ hr]
  rfl

theorem starFun_evalZ {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (K D : ℕ)
    (β : LinearMap.BilinForm ℤ X) :
    (starFun bar ψ w K D).evalZ β = D * (K * ψ.evalZ β + (starDepth bar ψ w).evalZ β) :=
  starFun_eval K D _

theorem starFun_evalR {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] (K D : ℕ)
    (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :
    evalR (starFun bar ψ w K D) B = D * (K * evalR ψ B + evalR (starDepth bar ψ w) B) :=
  starFun_eval K D _

theorem starDepth_zeroFun (n : ℕ) (B : (Fin n → O) → (Fin n → O) → ℝ) : (starDepth bar ψ (zeroFun O)).toFun n B = 0 := by
  have : depthSet bar ψ (zeroFun O) n B = ∅ :=
    Set.eq_empty_of_forall_notMem fun t ⟨X₁, i1, i2, i3, ρ, B₁, _, _, _, _, _, _, v, _, _, _, hv, _⟩ => by
      rw [zeroFun_evalZ] at hv
      exact zero_ne_one hv
  show sSup _ = 0
  rw [this, Real.sSup_empty]

end Depth

section Twist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E)

theorem isTwInv_starFun {ψ w : InvFun (𝓞 E)} (hψ : IsTwInv H ψ) (hd : IsTwInv H (starDepth H.bar ψ w)) (K D : ℕ) :
    IsTwInv H (starFun H.bar ψ w K D) := fun σ hσ n B => by
  show _ * (_ * _ + _) = _ * (_ * _ + _)
  rw [hψ σ hσ n B, hd σ hσ n B]

end Twist

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StrictlyConcavePolFanConeRealForms
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolCell

theorem strictWith_real : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (φ : InvFun ℤ) (N m : ℕ)
    (u : Fin m → LinearMap.BilinForm ℤ X) (w : (X × X) →₀ ℤ), IsPolFanOn (id : ℤ → ℤ) φ X → IsCone (id : ℤ → ℤ) φ u →
    StrictWith (id : ℤ → ℤ) φ N (linW w) u → (∀ B ∈ rcone u, (N : ℝ) * evalR φ B = evalW w B) ∧
      ∀ B ∈ psdCone (id : ℤ → ℤ) X, (N : ℝ) * evalR φ B ≤ evalW w B ∧ ((N : ℝ) * evalR φ B = evalW w B → B ∈ rcone u) := by
  intro X _ _ φ N m u w hF hu hS
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨?_, ?_⟩
  · rintro B ⟨t, ht, rfl⟩
    rw [(linearOn_iff φ u).1 hu.linear t ht, evalW_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [h1 i]; ring
  · intro B hB
    obtain ⟨m', γ, c, hγ, hc, rfl⟩ := hF.cover B hB
    have hle : ∀ i, (N : ℝ) * φ.evalZ (γ i) ≤ linW w (γ i) := fun i => h2 _ (hγ.mem i) (hγ.nonneg i)
    rw [(linearOn_iff φ γ).1 hγ.linear c hc, evalW_sum, Finset.mul_sum]
    have hterm : ∀ i, (N : ℝ) * (c i * φ.evalZ (γ i)) ≤ c i * linW w (γ i) := fun i => by
      rw [mul_left_comm]; exact mul_le_mul_of_nonneg_left (hle i) (hc i)
    refine ⟨Finset.sum_le_sum fun i _ => hterm i, fun he => ?_⟩
    have heq : ∀ i, (N : ℝ) * (c i * φ.evalZ (γ i)) = c i * linW w (γ i) :=
      fun i => (Finset.sum_eq_sum_iff_of_le fun i _ => hterm i).1 he i (Finset.mem_univ i)
    have hd : ∀ i, ∃ d : Fin m → ℝ, (∀ j, 0 ≤ d j) ∧ c i • toReal (γ i) = ∑ j, d j • toReal (u j) := by
      intro i
      rcases (hc i).eq_or_lt with h0 | h0
      · exact ⟨0, fun _ => le_rfl, by simp [← h0]⟩
      · have hi : (N : ℝ) * φ.evalZ (γ i) = linW w (γ i) := by
          have := heq i
          rw [mul_left_comm] at this
          exact mul_left_cancel₀ h0.ne' this
        obtain ⟨k, e, hk, hke⟩ := h3 _ (hγ.mem i) (hγ.nonneg i) hi
        refine ⟨fun j => c i * e j / k, fun j => by positivity, LinearMap.ext₂ fun a b => ?_⟩
        have := LinearMap.congr_fun₂ hke a b
        simp only [LinearMap.smul_apply, LinearMap.sum_apply, nsmul_eq_mul, smul_eq_mul] at this
        have hk' : (k : ℝ) ≠ 0 := by positivity
        have this' : (k : ℝ) * (γ i a b : ℝ) = ∑ j, (e j : ℝ) * (u j a b : ℝ) := by exact_mod_cast this
        simp only [LinearMap.smul_apply, LinearMap.sum_apply, toReal_apply, smul_eq_mul]
        calc c i * (γ i a b : ℝ) = c i / k * (k * γ i a b) := by field_simp
          _ = ∑ j, c i * e j / k * u j a b := by
            rw [this', Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
    choose d hd0 hd1 using hd
    refine ⟨fun j => ∑ i, d i j, fun j => Finset.sum_nonneg fun i _ => hd0 i j, ?_⟩
    simp only [hd1, Finset.sum_smul]
    exact Finset.sum_comm

end GlobalTheory.PolCell
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaCoefficientBoundedAlongHolomorphicArcStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaCoefficient_bounded_along_holomorphicArc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) [Algebra (FractionRing ℂ) ℂ] [IsScalarTower ℂ (FractionRing ℂ) ℂ] (V : ValuationSubring c.F) (Y : Model Xo c V.subtype) (a : ArcIn Dw l V.subtype ℂ (σ.comp V.subtype)) (χ : Sp (PowerSeries ℂ) ⟶ Y.X) (W : GlobalTheory.ArcQ.Wit Y a χ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (Ha : HolArc Y σ a χ W Fu) (th : a.D₀.P.L.Sec) (Θ : GlobalTheory.ArcQ.ThetaDat Ha th) (M : GChart Y), Formalism.L2.PjFree.GoodEmb c σ → IsTypeFn H Dw.p Dw.q ty → PushInvertible Y.t.G Y.t.PP.L → χ ≫ Y.s = spMap (PowerSeries.C (R := ℂ)) ≫ spMap (σ.comp V.subtype) → (∀ x : Sp (PowerSeries ℂ), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) → ⊤ ≤ χ ⁻¹ᵁ M.U → ∃ T C : ℝ, 0 < C ∧ ∀ w : ℂ, T < w.im → ∀ yF : Sp ℂ ⟶ Xo.XF c, yF ≫ pullback.fst _ _ = Fu.u Ha.i (Ha.Pw w) → yF ≫ pullback.snd _ _ = spMap σ → ∀ (hz : ⊤ ≤ (yF ≫ Y.j) ⁻¹ᵁ M.U) (x : KeyIn ℂ) (φ : x.P.A.left ⟶ Y.t.G.left), GlobalTheory.ArcNormal.KeyAtVia M (yF ≫ Y.j) hz x φ → ∀ (u : HolUnif x.P.A x.P.L g) (c₀ : ℂ), u.IsRig x.rig → GlobalTheory.ArcNormal.ArcFib Y σ Fu Ha.i (Ha.Pw w) x φ u → u.IsFn x.th (fun z => c₀ * thetaChar (Θ.τ w) Θ.c₁ Θ.c₂ (Θ.h.mulVec z)) → C⁻¹ ≤ ‖c₀‖ ∧ ‖c₀‖ ≤ C := by
  first | exact @GlobalTheory.ArcNormal.theta_const_bounded | exact GlobalTheory.ArcNormal.theta_const_bounded | (intros; apply GlobalTheory.ArcNormal.theta_const_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TiedSKAtWitnesses
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Top.Bl.WitSK

def of_sigma_eq {α : Type*} {β : α → Type*} {a b : Σ x, β x} (h : a = b) (P : ∀ x, β x → Sort*) (hb : P b.1 b.2) :
    P a.1 a.2 := by
  subst h; exact hb

end GlobalTheory.Mem.Top.Bl.WitSK

open Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2.TC Matrix in
set_option maxHeartbeats 1600000 in

theorem GlobalTheory.Mem.Top.Bl.tiedSK_at_witnesses : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (p : Prm hL) (K : Ctx) (q : WPt p.s K), ∀ (S : Formalism.L2.LinkedFamilyData q.O.ex) (t : Formalism.L2.Ker.KerEntTied q.O.ex), SPin q S → KPin q t → ∃ T : Formalism.L2.TiedDataSK q.O.ex, T.toTiedDataS = S ∧ T.ker = t ∧ (∀ u i hi, T.crd u i hi = 1) ∧ Formalism.L2.Rows.RowPinMin T ∧ Formalism.L2.JointsS S ∧ Nonempty (PLift (Formalism.L2.Theta.WeilCompatibleEquivariance S.theta.W)) := by
  intro hL p K q S t hS hKp
  obtain ⟨he, hTw⟩ := hS.tw
  have hK := hKp.std
  have hC : TC.StdC q.w.I q.w.l q.Z S.cols := hS.cols ▸ q.x.col.std
  have hsp := GlobalTheory.Mem.Col2.TC.spaces_in_coordinates q.w.I q.w.ok q.w.pins q.w.l q.Z
  have hD : TC.StdDt q.w.I q.w.l q.Z S.full.1.base.dt := by
    have key : ∀ (C : ColsTiedSym (q.w.D q.Z)) (F : ColsFullS C), C = q.x.col.C → HEq F q.x.col.full →
        TC.StdDt q.w.I q.w.l q.Z F.1.base.dt := by
      intro C F hC' hF
      subst hC'
      cases hF
      exact q.x.col.stdDt
    exact key _ _ hS.cols hS.full
  have hcf : S.n.cf = TC.cf q.w.I q.w.l q.Z := congrArg Sigma.fst hS.chr
  have hdiv : Nonempty (Formalism.L2.Host.DivisorCharacterCompatibility (q.w.D q.Z) S.n.cf q.O.ex.nch S.n.tp q.O.X) :=
    ⟨WitSK.of_sigma_eq hS.chr (fun c tp => Formalism.L2.Host.DivisorCharacterCompatibility (q.w.D q.Z) c q.O.ex.nch tp q.O.X) q.x.div.chr⟩
  have hψ : Formalism.L2.Theta.IsStdChar (q.w.D q.Z) S.theta.W.ψ (-1) :=
    WitSK.of_sigma_eq hS.theta (fun _ A => Formalism.L2.Theta.IsStdChar (q.w.D q.Z) A.W.ψ (-1)) q.x.th.std
  have hweq : Formalism.L2.Theta.WeilCompatibleEquivariance S.theta.W :=
    WitSK.of_sigma_eq hS.theta (fun _ A => Formalism.L2.Theta.WeilCompatibleEquivariance A.W) q.x.th.weq
  refine ⟨{ S with ker := t, crd := fun u i hi => 1, crd_gram := ?_, crd_lat := ?_, ker_sharp := ?_, ker_frm := ?_ }, rfl, rfl,
    fun _ _ _ => rfl, ⟨fun u => ?_, fun u μ hμ _ h1 => ?_, q.x.what₂.r.Y.bu⟩,
    GlobalTheory.Mem.JointsTrue.jointsS_true q.w.I q.w.ok q.w.pins q.w.l q.Z _ _ _ _ _ _ _ q.O.ex S hC hD hcf hS.dt hdiv hψ, ⟨⟨hweq⟩⟩⟩
  · intro u i hi
    rw [(hsp.2.2.2 i hi).1, Units.val_one, mul_one]
    ext a b
    simp [cT, Matrix.one_apply]
    exact if_congr eq_comm rfl rfl
  · intro u i hi x
    rw [(hsp.2.2.2 i hi).2.1 x, Units.val_one, Matrix.one_mulVec]
    rfl
  · intro μ
    rw [GlobalTheory.Mem.Col2.TC.KerSK.sharp_heq hK.X_eq (GlobalTheory.Mem.Col2.TC.KerSK.rowSG_heq hK.X_eq hK.Pr hK.sel hK.S hK.tup) hK.cst μ]
    exact q.w.ok.sharp μ
  · intro u μ i hi y τ
    rw [hK.O.frm u μ i y]
    have h1 : Formalism.L2.Forms.atInf (Formalism.L2.Forms.embT (q.w.D q.Z)) (Units.val (1 : GL (Fin ((q.w.D q.Z).R.N i)) (q.w.D q.Z).host.E)) τ = 1 := by
      simp [Formalism.L2.Forms.atInf]
    rw [h1, one_mul]
    have hY := hTw.1.eY u μ i hi
    rw [GlobalTheory.Mem.Col2.TC.KerSK.ch_cast he] at hY
    simp only [twYS, Equiv.trans_apply, hY, Equiv.refl_symm, Equiv.refl_apply, eYS]
    split_ifs with h
    · exact congrFun ((hC u).eY i hi h y).symm τ
    · exact congrFun ((hC u).eYC i _ _ y).symm τ
  · exact GlobalTheory.Mem.Col2.LowerTie.lowerMap_tie q.w.I q.w.ok q.w.pins q.w.l q.Z u _ _ _ (hC u)
  · exact GlobalTheory.Mem.Col2.LowerTie.lowerMap_tieTw q.w.I q.w.ok q.w.pins q.w.l q.Z q.w.l0 _ _ _ _ _ _ _ q.O.ex _ he hC hTw u μ hμ h1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorsionCountThroughExponentialLatticeKernelStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_count_through_exponential_lattice_kernel : ∀ (Q : Type) [Group Q] (g r N : ℕ) (e : (Fin g → ℂ) → Q) (b : Fin r → Fin g → ℂ) (T : Set Q), 0 < N → (∀ v w, e (v + w) = e v * e w) → Function.Surjective e → IsLatBasis {w | e w = 1} b → (∀ τ ∈ T, τ ^ N = 1) → Nat.card {p : Q // p ^ N = 1} * Nat.card T = N ^ (2 * g) → ∃ S : Set (Fin r → ZMod N), N ^ r * Nat.card S = N ^ (2 * g) ∧ ∀ a : Fin r → ℤ, (fun j => (a j : ZMod N)) ∈ S → e ((N : ℂ)⁻¹ • ∑ j, a j • b j) ∈ T := by
  first | exact @GlobalTheory.ShFam.Hor.LogCh.exp_lattice_torsion_count | exact GlobalTheory.ShFam.Hor.LogCh.exp_lattice_torsion_count | (intros; apply GlobalTheory.ShFam.Hor.LogCh.exp_lattice_torsion_count <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceBoundedOfAevalMonicEqZeroStatement
section
open Matrix GlobalTheory.RedTh NumberField GlobalTheory.PolFan ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_bounded_of_aeval_monic_eq_zero : ∀ (p : Polynomial ℤ), p.Monic → ∀ n : ℕ, ∃ K : ℝ, ∀ M : Matrix (Fin n) (Fin n) ℤ, Polynomial.aeval M p = 0 → ((M.trace : ℤ) : ℝ) ≤ K := by
  first | exact @GlobalTheory.RedTh.trace_le_of_aeval_monic_eq_zero | exact GlobalTheory.RedTh.trace_le_of_aeval_monic_eq_zero | (intros; apply GlobalTheory.RedTh.trace_le_of_aeval_monic_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationExpansionFunctionalEquation
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PsiCompare

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem feq_of_expandsAt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (k : ℕ), 1 ≤ k → ∀ (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), (∀ e : ℕ, U.ExpandsAt e k σ f) → ∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + k • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) k α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) k mu α) κ.left z J).val := by
  intro R _ _ _ hCN G _ _ hSA D A U k hk σ f hE mu α T κ y z J hJ
  have hR : AdmBase R (maximalIdeal R) := admissibleBase_of_completeNormalLocalCharZero hCN
  have := hR.1
  obtain ⟨s, hs⟩ := exists_sec U.LG.isLB (φ' := fun _ : Fin 1 => pullback.fst G.hom (jK R))
    (ε' := fun _ => ((k : ℕ) : ℤ)) (fun _ _ h => by simp only [Category.comp_id])
    (H1.SectionArithmetic.pullSec σ (pullback.fst G.hom (jK R)))
  have hU := U.expand k hk
  obtain ⟨E, hsE, -⟩ := hU.1 s
  obtain ⟨g, hg, hgE⟩ := IntegralExpansionLocal.main R (maximalIdeal R) le_rfl D A G U.toUnifPre k σ s
    (SectionScalarValuation.secScal_of_sval U.LG.isLB fun y J hJ =>
      ((hs _ _ y J hJ).trans (H1.SectionArithmetic.sval_pullSec _ _ _ y hJ)).symm) E hsE
  have H := (comb_eq_zero_iff_expansion_comb_eq_zero R _ hR D A G U.toUnifPre k 2 ![1, -1] ![σ, σ] ![f, g]
    (fun i => by fin_cases i; exacts [hE, hg])).1 (fun j => by
      simp [Fin.sum_univ_two, Out.scal])
  obtain rfl : f = g := funext fun α => SecOps.sec_ext fun j => by
    have := H α j
    simpa [Fin.sum_univ_two, Out.scal, add_neg_eq_zero] using this
  let ρ : T ⟶ DegPre.BF D.toPre (FractionRing R) := lift κ y
  have ρ₁ : ρ ≫ fst _ _ = κ := lift_fst _ _
  have ρ₂ : ρ ≫ DegPre.prB D.toPre (FractionRing R) = y := lift_snd _ _
  obtain ⟨⟨u, hu, hc⟩, hv⟩ := gen_fe (D := D.toPre) (F := FractionRing R) GlobalTheory.globalFns_holds k mu α
  have vu := hv u hu hc _ ρ z J hJ
  have hrel := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 (E.fe mu α u hu hc) _ ρ.left z J hJ
  rw [← SectionScalarValuation.secScal_sval (hgE _) _ z hJ, ← SectionScalarValuation.secScal_sval (hgE _) _ z hJ] at hrel
  have htr : (ρ ≫ DegPre.trF D.toPre (FractionRing R) mu) ≫ DegPre.prB D.toPre (FractionRing R) =
      y * cP D.toPre T mu := by
    rw [Category.assoc, trF_eq, tr_pr, MonObj.comp_mul, ρ₂, comp_cP, comp_cP]
  rw [vu] at hrel
  rw [← htr, ← congrArg (fun q => sval (f (α + k • mu)) q.left z J) ρ₂]
  rw [ρ₁] at hrel
  simp only [Over.comp_left]
  exact hrel

end GlobalTheory.PsiCompare
end
end

