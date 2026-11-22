import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0028
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RadfordShufflePolynomialHolds
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RadicalNoFixedVectors
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0012
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0897
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0003
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0316
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0319
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0321
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0314
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0303

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactorisableRestrictedTensorLevel
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped InnerProductSpace
open Formalism.MainNotions.KudlaSiegelWeil (Restr)

namespace GlobalTheory.FixedSpan

section General

variable {ι G H : Type} {Γ Hs : ι → Type} [Group G] [∀ i, Group (Γ i)] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)]
  {p : ∀ i, G →* Γ i} {δ : ∀ i, Γ i →* (Hs i →L[ℂ] Hs i)} {ξ : ∀ i, Hs i} {π : G →* (H →L[ℂ] H)}
  {B : (∀ i, Hs i) → H}

theorem mem_closure_span_of_orthogonal [DecidableEq ι] [CompleteSpace H] (h : IsRestrTensor p δ ξ π B)
    (U : ∀ i, Submodule ℂ (Hs i)) [∀ i, (U i).HasOrthogonalProjection] (hξ : ∀ᶠ i in cofinite, ξ i ∈ U i) (x : H)
    (hx : ∀ z, Restr ξ z → ∀ i, ∀ w ∈ (U i)ᗮ, ⟪x, B (Function.update z i w)⟫_ℂ = 0) :
    x ∈ (Submodule.span ℂ {z | ∃ y, Restr ξ y ∧ (∀ i, y i ∈ U i) ∧ z = B y}).topologicalClosure := by
  set Y := (Submodule.span ℂ {z | ∃ y, Restr ξ y ∧ (∀ i, y i ∈ U i) ∧ z = B y}).topologicalClosure with hY
  haveI : CompleteSpace Y := (Submodule.isClosed_topologicalClosure _).completeSpace_coe
  obtain ⟨a, ha, u, hu, rfl⟩ := Y.exists_add_mem_mem_orthogonal x
  have h1 : ∀ z, Restr ξ z → ∀ i, ∀ w ∈ (U i)ᗮ, ⟪a, B (Function.update z i w)⟫_ℂ = 0 := fun z hz i w hw => by
    have : Y ≤ (ℂ ∙ B (Function.update z i w))ᗮ :=
      Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 (by
        rintro _ ⟨y, hy, hyU, rfl⟩
        refine Submodule.mem_orthogonal_singleton_iff_inner_left.2 ?_
        rw [h.inner_update hz hy, Submodule.inner_right_of_mem_orthogonal (hyU i) hw, zero_mul]))
        (Submodule.isClosed_orthogonal _)
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (this ha)
  have h2 : ∀ z, Restr ξ z → ∀ i, ∀ w ∈ (U i)ᗮ, ⟪u, B (Function.update z i w)⟫_ℂ = 0 := fun z hz i w hw => by
    have := hx z hz i w hw
    rwa [inner_add_left, h1 z hz i w hw, zero_add] at this
  have h3 : ∀ s : Finset ι, ∀ y, Restr ξ y → (∀ i ∉ s, y i ∈ U i) → ⟪u, B y⟫_ℂ = 0 := fun s => by
    induction s using Finset.induction_on with
    | empty =>
      intro y hy hyU
      exact Submodule.inner_left_of_mem_orthogonal (K := Y)
        (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨y, hy, fun i => hyU i (by simp), rfl⟩)) hu
    | insert i s hi ih =>
      intro y hy hyU
      obtain ⟨b, hb, c, hc, e⟩ := (U i).exists_add_mem_mem_orthogonal (y i)
      have e1 : B y = B (Function.update y i b) + B (Function.update y i c) := by
        have := h.pure_update hy i 1 b c
        rwa [one_smul, one_smul, ← e, Function.update_eq_self] at this
      rw [e1, inner_add_right, h2 y hy i c hc, add_zero]
      refine ih _ (SmallThetaModules.restr_update hy i b) fun j hj => ?_
      by_cases hji : j = i
      · subst hji; rwa [Function.update_self]
      · rw [Function.update_of_ne hji]
        exact hyU j (by simp [hji, hj])
  have h4 : u = 0 := h.ext fun y hy => by
    have hf : ({i | y i ≠ ξ i} ∪ {i | ξ i ∈ U i}ᶜ).Finite := Set.Finite.union hy hξ
    rw [inner_zero_right, inner_eq_zero_symm]
    refine h3 hf.toFinset y hy fun i hi => ?_
    simp only [Set.Finite.mem_toFinset, Set.mem_union, Set.mem_setOf_eq, Set.mem_compl_iff, not_or, not_not] at hi
    exact hi.1 ▸ hi.2
  rwa [h4, add_zero]

theorem exists_update_clm [DecidableEq ι] (h : IsRestrTensor p δ ξ π B) {y : ∀ i, Hs i} (hy : Restr ξ y) (v : ι) :
    ∃ T : Hs v →L[ℂ] H, ∀ w, T w = B (Function.update y v w) := by
  have hr := SmallThetaModules.restr_update hy v
  have h0 : B (Function.update y v 0) = 0 := h.ext fun z hz => by simp [h.inner_update hy hz]
  let T : Hs v →ₗ[ℂ] H :=
    { toFun := fun x => B (Function.update y v x)
      map_add' := fun a b => by simpa using h.pure_update hy v 1 a b
      map_smul' := fun c a => by simpa [h0] using h.pure_update hy v c a 0 }
  have hT : ∀ x, ‖T x‖ ≤ √‖∏ᶠ (u) (_ : u ≠ v), ⟪y u, y u⟫_ℂ‖ * ‖x‖ := fun x => by
    have e := h.inner_update hy (hr x) v x
    rw [Function.update_self, finprod_congr fun u => finprod_congr fun hu : u ≠ v => by
      rw [Function.update_of_ne hu]] at e
    have e' := congrArg norm e
    rw [norm_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at e'
    refine le_of_sq_le_sq (le_of_eq ?_) (by positivity)
    rw [mul_pow, Real.sq_sqrt (norm_nonneg _), mul_comm]
    simpa [T] using e'
  exact ⟨T.mkContinuous _ hT, fun _ => rfl⟩

end General

def fixedSub {G X : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X] (ρ : G →* (X →L[ℂ] X))
    (K : Subgroup G) : Submodule ℂ X := ⨅ k ∈ K, LinearMap.ker ((ρ k - 1 : X →L[ℂ] X) : X →ₗ[ℂ] X)

theorem mem_fixedSub {G X : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X] {ρ : G →* (X →L[ℂ] X)}
    {K : Subgroup G} {x : X} : x ∈ fixedSub ρ K ↔ ∀ k ∈ K, ρ k x = x := by
  simp [fixedSub, sub_eq_zero]

theorem isClosed_fixedSub {G X : Type} [Group G] [NormedAddCommGroup X] [InnerProductSpace ℂ X]
    (ρ : G →* (X →L[ℂ] X)) (K : Subgroup G) : IsClosed (fixedSub ρ K : Set X) := by
  have : (fixedSub ρ K : Set X) = ⋂ k ∈ K, {x | ρ k x = x} := by
    ext x; simp [mem_fixedSub]
  rw [this]
  exact isClosed_biInter fun k _ => isClosed_eq (ρ k).continuous continuous_id

theorem inner_eq_zero_of_fixed {Γ X H : Type} [Group Γ] [TopologicalSpace Γ] [NormedAddCommGroup X]
    [InnerProductSpace ℂ X] [CompleteSpace X] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {ρ : Γ →* (X →L[ℂ] X)} (hρ : IsUnitaryRep ρ) {τ : Γ → (H →L[ℂ] H)}
    (hτ : ∀ g a b, ⟪τ g a, τ g b⟫_ℂ = ⟪a, b⟫_ℂ) (T : X →L[ℂ] H) (hT : ∀ g w, T (ρ g w) = τ g (T w))
    {K : Subgroup Γ} {x : H} (hx : ∀ k ∈ K, τ k x = x) {w : X} (hw : w ∈ (fixedSub ρ K)ᗮ) : ⟪x, T w⟫_ℂ = 0 := by
  rw [← ContinuousLinearMap.adjoint_inner_left]
  refine Submodule.inner_right_of_mem_orthogonal (mem_fixedSub.2 fun k hk => ext_inner_right ℂ fun z => ?_) hw
  obtain ⟨z, rfl⟩ : ∃ z', z = ρ k z' := ⟨ρ k⁻¹ z, by
    rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one, ContinuousLinearMap.one_apply]⟩
  rw [inner_map_map hρ, ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_left, hT]
  conv_rhs => rw [← hx k hk, hτ]

theorem mem_closure_span_fixed : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GAd σ J →* (H →L[ℂ] H)), IsIrrUnitary π → ∀ (R : ∀ v, IrrU (GPl σ J v)) (ξ : ∀ v, (R v).H) (B : (∀ v, (R v).H) → H), IsFactorisation σ J (fun v => (R v).π) ξ π B → ∀ (Kp : ∀ v : HeightOneSpectrum (𝓞 F), Subgroup (GLoc σ J v)), (∀ᶠ v in cofinite, ∀ k ∈ Kp v, (R (.inr v)).π k (ξ (.inr v)) = ξ (.inr v)) → ∀ x : H, (∀ v, ∀ k ∈ Kp v, π (emb σ J v k) x = x) → x ∈ (Submodule.span ℂ {z | ∃ y, Restr ξ y ∧ (∀ v, ∀ k ∈ Kp v, (R (.inr v)).π k (y (.inr v)) = y (.inr v)) ∧ z = B y}).topologicalClosure := by
  intro F E _ _ _ _ _ σ n J H _ _ π hπ R ξ B h Kp hξ x hx
  classical
  haveI := hπ.complete
  haveI := fun v => (R v).isIrr.complete
  let K : ∀ v, Subgroup (GPl σ J v) := fun v => match v with
    | .inl _ => ⊥
    | .inr v => Kp v
  haveI : ∀ v, CompleteSpace (fixedSub (R v).π (K v)) := fun v => (isClosed_fixedSub _ _).completeSpace_coe
  have hK : ∀ y : ∀ v, (R v).H, ∀ w, y (.inl w) ∈ fixedSub (R (.inl w)).π (K (.inl w)) := fun y w =>
    mem_fixedSub.2 fun k hk => by
      rw [Subgroup.mem_bot.1 hk, map_one, ContinuousLinearMap.one_apply]
  have key := mem_closure_span_of_orthogonal h (fun v => fixedSub (R v).π (K v)) ?_ x ?_
  · refine Submodule.topologicalClosure_mono (Submodule.span_mono ?_) key
    rintro _ ⟨y, hy, hyU, rfl⟩
    exact ⟨y, hy, fun v => mem_fixedSub.1 (hyU (.inr v)), rfl⟩
  · refine (Set.Finite.image Sum.inr hξ).subset ?_
    rintro (w | v) hv
    · exact absurd (hK ξ w) hv
    · exact ⟨v, fun e => hv (mem_fixedSub.2 e), rfl⟩
  · intro z hz v w hw
    obtain ⟨T, hT⟩ := exists_update_clm h hz v
    rw [← hT]
    refine inner_eq_zero_of_fixed (R v).isIrr.unitary (τ := fun g => π (embPl σ J v g))
      (fun g a b => inner_map_map hπ.unitary _ a b) T (fun g a => ?_) (K := K v) ?_ hw
    · rw [hT, hT, h.apply_embPl (SmallThetaModules.restr_update hz v a), Function.update_self, Function.update_idem]
    · rcases v with v | v
      · intro k hk
        rw [Subgroup.mem_bot.1 hk, map_one, map_one, ContinuousLinearMap.one_apply]
      · exact hx v

end GlobalTheory.FixedSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartLocalToFiniteAdelicComponentNe
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

namespace GlobalTheory.LocFinComp

theorem prV_swap_snd {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (u : HeightOneSpectrum (𝓞 F)) (x : AF F ⊗[F] E) :
    Formalism.UG.prV (E := E) u (Algebra.TensorProduct.comm F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) E
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x)) =
    Algebra.TensorProduct.comm F (Fv F u) E (Algebra.TensorProduct.map (evFin F u) (AlgHom.id F E) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => exact Eq.refl _
  | add x y hx hy => simp only [map_add, hx, hy]

theorem finE_locFin_map_prV_ne : ∀ {D : D7} (V : HSp D) {v u : HeightOneSpectrum (𝓞 D.host.F)}, u ≠ v → ∀ (g : Gv V v), (Formalism.IndefR.Lev.finE V (locFin V v g : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) u) = 1 := by
  intro D V v u huv g
  have hp : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram u (locFin V v g : GA D V) = 1 :=
    GlobalTheory.AdelicU.proj_emb_ne D.sp.cm.sig V.gram huv g
  have hm := congrArg (fun y => (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram y).val) hp
  simp only [GlobalTheory.AdelicU.matHom_proj, map_one, Units.val_one] at hm
  ext i j
  have hij := congrFun (congrFun hm i) j
  have key := prV_swap_snd (F := D.host.F) (E := D.host.E) u
    ((Formalism.L2.Theta.matHom V (locFin V v g : GA D V)).val i j)
  refine key.trans ((congrArg (Algebra.TensorProduct.comm _ _ _) hij).trans ?_)
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply_ne h]

end GlobalTheory.LocFinComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartLocalToFiniteAdelicComponentSelf
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Cx
open GlobalTheory.LiftRows

open scoped TensorProduct

namespace GlobalTheory.FinLocSelf

theorem prV_swap_sndA {D : D7} (v : HeightOneSpectrum (𝓞 D.host.F)) (x : AF D.host.F ⊗[D.host.F] D.host.E) :
    Formalism.UG.prV (E := D.host.E) v (Formalism.IndefR.Lev.swapAE D
      (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E) x)) =
    Algebra.TensorProduct.comm D.host.F (Fv D.host.F v) D.host.E (compFin D.host.F D.host.E v x) := by
  have h : ((Algebra.TensorProduct.map (AlgHom.id D.host.F D.host.E) (Formalism.UG.evalV D.host.F v)).comp
      ((Algebra.TensorProduct.comm D.host.F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) D.host.E).toAlgHom.comp
        (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)))) =
      (Algebra.TensorProduct.comm D.host.F (Fv D.host.F v) D.host.E).toAlgHom.comp
        (Algebra.TensorProduct.map (evFin D.host.F v) (AlgHom.id D.host.F D.host.E)) :=
    Algebra.TensorProduct.ext' fun _ _ => rfl
  exact DFunLike.congr_fun h x

theorem finE_locFin_map_prV {D : D7} (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) (g : Gv V v) :
    (Formalism.IndefR.Lev.finE V (locFin V v g : GA D V)).val.map (Formalism.UG.prV (E := D.host.E) v) =
      (GlobalTheory.AdelicU.matHom _ D.sp.cm.sig V.gram g).val.map
        (Algebra.TensorProduct.comm D.host.F (Fv D.host.F v) D.host.E) := by
  conv_rhs => rw [← proj_emb_self D.sp.cm.sig V.gram v g]
  rw [matHom_proj]
  ext i j
  exact prV_swap_sndA v _

end GlobalTheory.FinLocSelf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePartMemCompactOfIsotropicAnnihilator
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMeanAnnih

theorem finPart_mem_compact : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ U : AddSubgroup (WO V W), IsOpen (U : Set (WO V W)) → ∃ K : Set (Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E)), IsCompact K ∧ ∀ y : Mx D a b, (∀ u ∈ U, u.map (infPart D) = 0 → ψ (symplO V W (GlobalTheory.IsoMean.emb V W P Q y) u) = 1) → y.map (finPart D) ∈ K := by
  intro D V W a b P Q hP hQ ψ hψ U hU
  obtain ⟨d, c, e, hce⟩ := GlobalTheory.T.finitePart_eq_sum_trace_traceDualBasis D
  have hm : ∀ p : Fin a × Fin b × Fin d, ∃ m : Matrix (Fin W.rank) (Fin V.rank) D.host.E,
      ∀ (y : Mx D a b) (r : AF D.host.F), symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (r • m.map (incA D)) =
        r * Algebra.trace (AF D.host.F) (AE D) (incA D (c p.2.2) * y p.1 p.2.1) :=
    fun p => GlobalTheory.T.exists_rational_test_matrix_isolates_entry D V W a b P Q hP hQ p.1 p.2.1 (c p.2.2)
  choose m hm using hm
  haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
  haveI : ContinuousSMul (AF D.host.F) (AE D) := IsModuleTopology.toContinuousSMul _ _
  let φ : (Fin a × Fin b × Fin d) → Af D.host.F → WO V W :=
    fun p t => (pairA D.host.F 0 t) • (m p).map (incA D)
  have hpair : Continuous fun t : Af D.host.F => pairA D.host.F 0 t := continuous_const.prodMk continuous_id
  have hφ : ∀ p, Continuous (φ p) := fun p =>
    Continuous.smul (f := fun t : Af D.host.F => pairA D.host.F 0 t) (g := fun _ => (m p).map (incA D)) hpair continuous_const
  have hφ0 : ∀ p, φ p 0 = 0 := fun p => by
    have : pairA D.host.F 0 (0 : Af D.host.F) = 0 := rfl
    simp only [φ, this, zero_smul]
  have hO : (⋂ p, φ p ⁻¹' (U : Set (WO V W))) ∈ nhds (0 : Af D.host.F) :=
    Filter.iInter_mem.2 fun p => (hφ p).continuousAt.preimage_mem_nhds
      (hU.mem_nhds (by rw [hφ0]; exact U.zero_mem))
  obtain ⟨K₀, hK₀, hmem⟩ := GlobalTheory.T.exists_compact_annihilator_finiteAdeles_stdChar D ψ hψ _ hO
  haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : ContinuousSMul (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.toContinuousSMul _ _
  haveI : ContinuousAdd (Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.toContinuousAdd (Af D.host.F) _
  let g : (Fin a × Fin b × Fin d → Af D.host.F) → Matrix (Fin a) (Fin b) (Af D.host.F ⊗[D.host.F] D.host.E) :=
    fun z => Matrix.of fun i j => ∑ l, z (i, j, l) ⊗ₜ[D.host.F] e l
  have hg : Continuous g := by
    refine continuous_matrix fun i j => ?_
    show Continuous fun z : Fin a × Fin b × Fin d → Af D.host.F => ∑ l, z (i, j, l) ⊗ₜ[D.host.F] e l
    refine continuous_finset_sum _ fun l _ => ?_
    have : (fun z : Fin a × Fin b × Fin d → Af D.host.F => z (i, j, l) ⊗ₜ[D.host.F] e l) =
        fun z => z (i, j, l) • ((1 : Af D.host.F) ⊗ₜ[D.host.F] e l) := by
      funext z; rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [this]
    exact Continuous.smul (continuous_apply (A := fun _ : Fin a × Fin b × Fin d => Af D.host.F) (i, j, l))
      (continuous_const (y := ((1 : Af D.host.F) ⊗ₜ[D.host.F] e l)))
  refine ⟨g '' Set.pi Set.univ (fun _ => K₀), (isCompact_univ_pi fun _ => hK₀).image hg, fun y hy =>
    ⟨fun p => sndA D.host.F (Algebra.trace (AF D.host.F) (AE D) (incA D (c p.2.2) * y p.1 p.2.1)),
      fun p _ => hmem _ fun t ht => ?_, ?_⟩⟩
  · have hu : φ p t ∈ U := Set.mem_iInter.1 ht p
    have hinf : (φ p t).map (infPart D) = 0 := by
      ext k l
      simp only [φ, Matrix.map_apply, Matrix.smul_apply, Matrix.zero_apply]
      change infPart D (pairA D.host.F 0 t • ((1 : AF D.host.F) ⊗ₜ[D.host.F] m p k l)) = 0
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      change (fstA D.host.F (pairA D.host.F 0 t)) ⊗ₜ[D.host.F] (m p k l) = 0
      exact TensorProduct.zero_tmul _ _
    have h1 := hy _ hu hinf
    simp only [φ] at h1
    rw [hm] at h1
    convert h1 using 2
    exact Prod.ext (zero_mul _).symm rfl
  · ext i j
    simp only [g, Matrix.of_apply, Matrix.map_apply]
    rw [hce]

end GlobalTheory.IsoMeanAnnih
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockBargmannReproducingFormula
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

namespace GlobalTheory.FockRepr

theorem expand_real (κ : Type) [Fintype κ] (x : κ → ℝ) :
    HasSum (fun m : κ →₀ ℕ => m.prod fun k n => x k ^ n / (n.factorial : ℝ)) (Real.exp (∑ k, x k)) := by
  have h := GlobalTheory.T.hasSum_finsupp_prod_pow_div_factorial_exp_sum κ (fun k => (x k : ℂ))
  rw [← Complex.ofReal_sum, ← Complex.ofReal_exp] at h
  refine Complex.hasSum_ofReal.mp ?_
  convert h using 1
  funext m
  simp only [Finsupp.prod, Complex.ofReal_prod, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_natCast]

theorem conjMono_continuous {ι : Type} [Fintype ι] {a b : ℕ} (m : DVar ι a b →₀ ℕ) : Continuous (conjMono m) := by
  unfold conjMono Finsupp.prod; fun_prop

theorem gq_continuous {ι : Type} [Fintype ι] {a b : ℕ} (c : ι → ℝ) : Continuous (gq (a := a) (b := b) c) := by
  unfold gq; fun_prop

theorem bargmann_repr : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ G : VCx ι a b → ℂ, Differentiable ℂ G → (∃ M : ℝ, ∀ z, ‖G z‖ ≤ M * Real.exp (gq c z / 2)) → ∀ z₀, G z₀ = ((∏ τ, (c τ / Real.pi) ^ (a * b) : ℝ) : ℂ) * ∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z) : ℂ) * G z := by
  intro ι _ a b c hc G hG ⟨M, hM⟩ z₀
  have hbk : ∀ z, bk c z₀ z = ∑ k : DVar ι a b, (c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2) := by
    intro z; simp only [bk, Fintype.sum_prod_type]
  let coef : (DVar ι a b →₀ ℕ) → ℂ := fun m => m.prod fun k n => ((c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2) ^ n / (n.factorial : ℂ)
  have hcm : ∀ (m : DVar ι a b →₀ ℕ) z, coef m * conjMono m z = m.prod fun k n => ((c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2)) ^ n / (n.factorial : ℂ) := by
    intro m z
    simp only [coef, conjMono, ← Finsupp.prod_mul]
    refine Finset.prod_congr rfl fun k _ => ?_
    ring
  let F : (DVar ι a b →₀ ℕ) → VCx ι a b → ℂ := fun m z => coef m * (conjMono m z * (Real.exp (-gq c z) : ℂ) * G z)
  have hlim : ∀ z, HasSum (fun m => F m z) (Complex.exp (bk c z₀ z) * (Real.exp (-gq c z) : ℂ) * G z) := by
    intro z
    have := (GlobalTheory.T.hasSum_finsupp_prod_pow_div_factorial_exp_sum (DVar ι a b) (fun k => (c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2))).mul_right ((Real.exp (-gq c z) : ℂ) * G z)
    rw [← hbk] at this
    have e : (fun m => F m z) = fun m => (m.prod fun k n => ((c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2 * conj (z k.1 k.2.1 k.2.2)) ^ n / (n.factorial : ℂ)) * ((Real.exp (-gq c z) : ℂ) * G z) := by
      funext m
      rw [← hcm]
      simp only [F]
      ring
    rw [e, mul_assoc]
    exact this
  have hnorm : ∀ m z, ‖F m z‖ = (m.prod fun k n => (‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) ^ n / (n.factorial : ℝ)) * (Real.exp (-gq c z) * ‖G z‖) := by
    intro m z
    have e1 : F m z = (coef m * conjMono m z) * ((Real.exp (-gq c z) : ℂ) * G z) := by simp only [F]; ring
    rw [e1, hcm, norm_mul, norm_mul, Finsupp.prod, Finsupp.prod, norm_prod, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
    congr 1
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [norm_div, norm_pow, norm_mul, Complex.norm_natCast, RCLike.norm_conj]
  have hnsum : ∀ z, HasSum (fun m => ‖F m z‖) (Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * ‖G z‖)) := by
    intro z
    simp only [hnorm]
    exact (expand_real (DVar ι a b) _).mul_right _
  have hGc : Continuous G := hG.continuous
  have hFc : ∀ m, Continuous (F m) := by
    intro m
    have h1 := conjMono_continuous m
    have h2 := gq_continuous (a := a) (b := b) c
    simp only [F]
    fun_prop
  have hS : Continuous fun z : VCx ι a b => ∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖ := by
    fun_prop
  have hint : Integrable (fun z => ∑' m, ‖F m z‖) := by
    have e : (fun z => ∑' m, ‖F m z‖) = fun z => Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * ‖G z‖) := by
      funext z; exact (hnsum z).tsum_eq
    rw [e]
    refine ((GlobalTheory.T.integrable_gaussian_exp_linear_norm_term_complex_matrix ι a b c hc z₀).const_mul M).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · have h2 := gq_continuous (a := a) (b := b) c
      exact Continuous.aestronglyMeasurable (by fun_prop)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hz := hM z
      calc Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * ‖G z‖)
          ≤ Real.exp (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) * (Real.exp (-gq c z) * (M * Real.exp (gq c z / 2))) := by
            gcongr
        _ = M * Real.exp ((∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2) := by
            rw [show (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) - gq c z / 2
              = (∑ k : DVar ι a b, ‖(c k.1 : ℂ) * z₀ k.1 k.2.1 k.2.2‖ * ‖z k.1 k.2.1 k.2.2‖) + (-gq c z) + gq c z / 2 by ring,
              Real.exp_add, Real.exp_add]
            ring
  have hsumI : HasSum (fun m => ∫ z, F m z) (∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z) : ℂ) * G z) :=
    hasSum_integral_of_dominated_convergence (fun m z => ‖F m z‖) (fun m => (hFc m).aestronglyMeasurable)
      (fun m => Filter.Eventually.of_forall fun z => le_rfl) (Filter.Eventually.of_forall fun z => (hnsum z).summable)
      hint (Filter.Eventually.of_forall hlim)
  set P : ℝ := ∏ τ, (Real.pi / c τ) ^ (a * b) with hP
  have hFm : ∀ m, ∫ z, F m z = (P : ℂ) * ((m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ)) * derivAt0 G m) := by
    intro m
    simp only [F]
    rw [MeasureTheory.integral_const_mul, GlobalTheory.T.gaussian_conjMonomial_moment_eq_taylor_coefficient ι a b c hc G hG ⟨M, hM⟩ m]
    have hc' : coef m * (((m.prod fun k n => (c k.1)⁻¹ ^ n : ℝ)) : ℂ) = m.prod fun k n => z₀ k.1 k.2.1 k.2.2 ^ n / (n.factorial : ℂ) := by
      simp only [coef, Finsupp.prod, Complex.ofReal_prod, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      have : (c k.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hc k.1).ne'
      push_cast
      rw [mul_pow, mul_div_assoc, mul_comm, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ this, one_pow, one_mul]
    rw [← hc']
    ring
  have hT := (GlobalTheory.T.hasSum_taylorSeries_derivAtOrigin_coordinateSpace ι a b G hG z₀).mul_left (P : ℂ)
  simp only [← hFm] at hT
  have heq := hsumI.unique hT
  rw [heq, ← mul_assoc]
  have h1 : (∏ τ, (c τ / Real.pi) ^ (a * b) : ℝ) * P = 1 := by
    rw [hP, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [← mul_pow]
    have : c τ ≠ 0 := (hc τ).ne'
    have : Real.pi ≠ 0 := Real.pi_ne_zero
    rw [show c τ / Real.pi * (Real.pi / c τ) = 1 by field_simp, one_pow]
  rw [← Complex.ofReal_mul, h1, Complex.ofReal_one, one_mul]

end GlobalTheory.FockRepr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodFormsLeRangeThetaAdjointBaseTupleStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftRows
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_forms_le_range_theta_adjoint_base_tuple : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}, A3.fam3.Ok3 s → R.WeakCharacterisation F → R.toRealDat.ExAt → UpInjW R.toRealDat → (∀ j t, (A3.A.fam.L j t).OkH ∧ (A3.liftI j t).InertRationalAdjoint) → R.PGEquiv F → R.toRealDat.LUnif → ∀ j, U2.goodW A3 (R.toCx3 F) j ≤ LinearMap.range ((R.toCx3 F).θ' j A3.A.fam.μ0) := by
  first | exact @GlobalTheory.LiftOntoGood.goodW_le_range | exact GlobalTheory.LiftOntoGood.goodW_le_range | (intros; apply GlobalTheory.LiftOntoGood.goodW_le_range <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HarishChandraAnalyticity
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

namespace GlobalTheory.Published

theorem harishChandraAnalyticity_of_admissible_of_analytic :
    GlobalTheory.Published.IrreducibleUnitaryAdmissible → GlobalTheory.Published.KFiniteCoefficientsAnalytic →
      GlobalTheory.Published.HarishChandraAnalyticity :=
  fun hadm han =>
    ⟨fun n ε H _ _ _ π hπ v w hv _ => GlobalTheory.T.admissible_unitary_K_finite.2 han n ε H π hπ v w hv, GlobalTheory.T.levi_submodule_dense hadm han⟩

end GlobalTheory.Published
end

