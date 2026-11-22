import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0337
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0045
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0103
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0943
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0311
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0335
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0168
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0159
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerEqZeroOfMemClosureSpan
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

noncomputable section
open scoped InnerProductSpace

namespace GlobalTheory.TensorTrace

section Hilbert

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem inner_eq_zero_of_mem_closure_span {S : Set H} {a : H} (h : ∀ x ∈ S, ⟪x, a⟫_ℂ = 0)
    {x : H} (hx : x ∈ (Submodule.span ℂ S).topologicalClosure) : ⟪x, a⟫_ℂ = 0 := by
  have hle : (Submodule.span ℂ S).topologicalClosure ≤ (ℂ ∙ a)ᗮ := by
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_orthogonal _)
    rw [Submodule.span_le]
    intro y hy
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h y hy)
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hx)

variable {W : Type} [AddCommGroup W] [Module ℂ W]

theorem exists_orthonormal (L : W →ₗ[ℂ] H) (hL : Function.Injective L) (Z : Submodule ℂ W)
    [FiniteDimensional ℂ Z] :
    ∃ (n : ℕ) (z : Fin n → W), (∀ j, z j ∈ Z) ∧ Orthonormal ℂ (fun j => L (z j)) ∧
      (∀ x ∈ Z, L x = ∑ j, ⟪L (z j), L x⟫_ℂ • L (z j)) ∧
      (∀ (f : W →ₗ[ℂ] W) (hf : ∀ x ∈ Z, f x ∈ Z),
        LinearMap.trace ℂ Z (f.restrict hf) = ∑ j, ⟪L (z j), L (f (z j))⟫_ℂ) := by
  let LZ := L ∘ₗ Z.subtype
  have hLZ : Function.Injective LZ := hL.comp Subtype.val_injective
  let e := LinearEquiv.ofInjective LZ hLZ
  haveI : FiniteDimensional ℂ (LinearMap.range LZ) := LinearEquiv.finiteDimensional e
  let b := stdOrthonormalBasis ℂ (LinearMap.range LZ)
  have he : ∀ x : Z, ((e x : LinearMap.range LZ) : H) = L x := fun x => rfl
  have hb : ∀ j, L ((e.symm (b j) : Z) : W) = (b j : H) := fun j => by
    rw [← he, e.apply_symm_apply]
  refine ⟨_, fun j => ((e.symm (b j) : Z) : W), fun j => (e.symm (b j)).2, ?_, ?_, ?_⟩
  · rw [orthonormal_iff_ite]
    intro j k
    simp only [hb]
    rw [← Submodule.coe_inner]
    exact orthonormal_iff_ite.1 b.orthonormal j k
  · intro x hx
    have h1 := congrArg (fun v : LinearMap.range LZ => (v : H)) (b.sum_repr' (e ⟨x, hx⟩))
    simp only [Submodule.coe_sum, Submodule.coe_smul, he] at h1
    simp only [hb]
    conv_lhs => rw [← h1]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_inner, he]
  · intro f hf
    rw [← LinearMap.trace_conj' _ e, LinearMap.trace_eq_sum_inner _ b]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Submodule.coe_inner, hb, LinearEquiv.conj_apply]
    rfl

end Hilbert

section Tensor

variable {ι : Type} [Fintype ι] {Hs : ι → Type} [∀ i, NormedAddCommGroup (Hs i)]
  [∀ i, InnerProductSpace ℂ (Hs i)] {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def evalAt (T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs H) (u : ∀ i, Hs i) : W →ₗ[ℂ] H where
  toFun w := T w u
  map_add' a b := by simp
  map_smul' c a := by simp

theorem evalAt_apply (T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs H) (u : ∀ i, Hs i) (w : W) :
    evalAt T u w = T w u := rfl

variable {T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs H} {β : W → W → ℂ}

theorem beta_eq (hβ : ∀ w w' y y', ⟪T w' y', T w y⟫_ℂ = β w w' * ∏ i, ⟪y' i, y i⟫_ℂ)
    {u : ∀ i, Hs i} (hu : ∀ i, ⟪u i, u i⟫_ℂ = 1) (w w' : W) :
    β w w' = ⟪evalAt T u w', evalAt T u w⟫_ℂ := by
  rw [evalAt_apply, evalAt_apply, hβ]
  simp only [hu, Finset.prod_const_one, mul_one]

theorem evalAt_injective (hβ : ∀ w w' y y', ⟪T w' y', T w y⟫_ℂ = β w w' * ∏ i, ⟪y' i, y i⟫_ℂ)
    {u : ∀ i, Hs i} (hu : ∀ i, ⟪u i, u i⟫_ℂ = 1) (hT : Function.Injective T) :
    Function.Injective (evalAt T u) := by
  refine (injective_iff_map_eq_zero _).2 fun w hw => hT ?_
  rw [map_zero]
  ext y
  have h1 : β w w = 0 := by rw [beta_eq hβ hu, hw, inner_zero_left]
  have h2 : ⟪T w y, T w y⟫_ℂ = 0 := by rw [hβ, h1, zero_mul]
  simpa using inner_self_eq_zero.1 h2

variable [CompleteSpace H]

theorem starProjection_tensor
    (hβ : ∀ w w' y y', ⟪T w' y', T w y⟫_ℂ = β w w' * ∏ i, ⟪y' i, y i⟫_ℂ)
    {z : W} (hz : β z z = 1) (w : W) (y : ∀ i, Hs i) :
    (Submodule.span ℂ {x | ∃ y', x = T z y'}).topologicalClosure.starProjection (T w y) = β w z • T z y := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun x hx => ?_
  · exact Submodule.smul_mem _ _ (Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨y, rfl⟩))
  · rw [inner_eq_zero_symm]
    refine inner_eq_zero_of_mem_closure_span ?_ hx
    rintro _ ⟨y', rfl⟩
    rw [inner_sub_right, inner_smul_right, hβ, hβ, hz, one_mul, sub_self]

theorem starProjection_eq_zero_tensor {z : W} {v : H} (hv : ∀ y, ⟪T z y, v⟫_ℂ = 0) :
    (Submodule.span ℂ {x | ∃ y', x = T z y'}).topologicalClosure.starProjection v = 0 := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (Submodule.zero_mem _) fun x hx => ?_
  rw [sub_zero, inner_eq_zero_symm]
  exact inner_eq_zero_of_mem_closure_span (by rintro _ ⟨y, rfl⟩; exact hv y) hx

end Tensor

theorem hasTrace_finiteRank_tensor : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Hs : ι → Type) [∀ i, NormedAddCommGroup (Hs i)] [∀ i, InnerProductSpace ℂ (Hs i)] [∀ i, CompleteSpace (Hs i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (W : Type) [AddCommGroup W] [Module ℂ W] (T : W →ₗ[ℂ] ContinuousMultilinearMap ℂ Hs H) (β : W → W → ℂ), (∀ w w' y y', inner ℂ (T w' y') (T w y) = β w w' * ∏ i, inner ℂ (y' i) (y i)) → Function.Injective T → (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure = ⊤ → ∀ (A : W →ₗ[ℂ] W) (c : ℂ), GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.HasFinTrace A c → ∀ Z : Submodule ℂ W, FiniteDimensional ℂ Z → LinearMap.range A ≤ Z → (∀ w, (∀ z ∈ Z, β w z = 0) → A w = 0) → ∀ (B : ∀ i, Hs i →L[ℂ] Hs i) (b : ι → ℂ), (∀ i, HasTrace (B i) (b i)) → ∀ X : H →L[ℂ] H, (∀ w y, X (T w y) = T (A w) fun i => B i (y i)) → HasTrace X (c * ∏ i, b i) := by
  intro ι _ _ Hs _ _ _ H _ _ _ W _ _ T β hβ hT hdense A c hA Z _ hAZ hA0 B b hB X hX
  by_cases hnt : ∀ i, Nontrivial (Hs i)
  · obtain ⟨u, hu⟩ : ∃ u : ∀ i, Hs i, ∀ i, ⟪u i, u i⟫_ℂ = 1 := by
      have hv : ∀ i, ∃ v : Hs i, v ≠ 0 := fun i => @exists_ne _ (hnt i) 0
      choose v hv using hv
      refine ⟨fun i => ((‖v i‖ : ℂ)⁻¹) • v i, fun i => ?_⟩
      rw [inner_self_eq_norm_sq_to_K, norm_smul, norm_inv, Complex.norm_real, norm_norm,
        inv_mul_cancel₀ (norm_ne_zero_iff.2 (hv i))]
      simp
    obtain ⟨n, z, hzZ, hon, hdec, htr⟩ :=
      exists_orthonormal (evalAt T u) (evalAt_injective hβ hu hT) Z
    have hzz : ∀ j, β (z j) (z j) = 1 := fun j => by
      have := orthonormal_iff_ite.1 hon j j
      simp only [if_pos rfl] at this
      rw [beta_eq hβ hu]
      exact this
    have hAw : ∀ w, A w = ∑ j, β w (z j) • A (z j) := by
      intro w
      have hperp : ∀ k, ⟪evalAt T u (z k), evalAt T u (w - ∑ j, β w (z j) • z j)⟫_ℂ = 0 := by
        intro k
        have h1 := hon.inner_right_fintype (fun j => β w (z j)) k
        rw [map_sub, map_sum, inner_sub_right]
        simp only [map_smul]
        rw [h1, beta_eq hβ hu, sub_self]
      have h0 : A (w - ∑ j, β w (z j) • z j) = 0 := by
        refine hA0 _ fun x hx => ?_
        rw [beta_eq hβ hu, hdec x hx, sum_inner]
        exact Finset.sum_eq_zero fun k _ => by rw [inner_smul_left, hperp k, mul_zero]
      rw [map_sub, map_sum, sub_eq_zero] at h0
      simpa only [map_smul] using h0
    let P : Fin n → H →L[ℂ] H := fun j =>
      (Submodule.span ℂ {x | ∃ y', x = T (z j) y'}).topologicalClosure.starProjection
    have hXsum : X = ∑ j, X ∘L P j := by
      refine ContinuousLinearMap.ext_on (Submodule.dense_iff_topologicalClosure_eq_top.2 hdense) ?_
      rintro _ ⟨w, y, rfl⟩
      rw [ContinuousLinearMap.sum_apply]
      simp only [ContinuousLinearMap.comp_apply, P, starProjection_tensor hβ (hzz _), map_smul, hX]
      rw [hAw w, map_sum, ContinuousMultilinearMap.sum_apply]
      simp only [map_smul, ContinuousMultilinearMap.smul_apply]
    have hj : ∀ j, GlobalTheory.OpTrace.HasTrace (X ∘L P j) (β (A (z j)) (z j) * ∏ i, b i) := fun j =>
      GlobalTheory.T.hilbertTensor_traceClass_hasTrace_prod ι Hs H (T (z j)) (T (A (z j))) (β (A (z j)) (z j)) (β (A (z j)) (A (z j)))
        (fun y y' => by rw [hβ, hzz, one_mul]) (fun y y' => hβ _ _ _ _) (fun y y' => hβ _ _ _ _) B b hB
        (X ∘L P j)
        (fun y => by
          simp only [ContinuousLinearMap.comp_apply, P, starProjection_tensor hβ (hzz j), hzz j, one_smul, hX])
        (fun v hv => by
          simp only [ContinuousLinearMap.comp_apply, P, starProjection_eq_zero_tensor hv, map_zero])
    have hf : ∀ x ∈ Z, A x ∈ Z := fun x _ => hAZ (LinearMap.mem_range_self A x)
    have hc : c = ∑ j, β (A (z j)) (z j) := by
      have h1 := GlobalTheory.IndefiniteRowSideFullHecke.RangeTrace.hasFinTrace_of_range_le W A Z hAZ
      rw [← hA.2, h1.2, htr A hf]
      simp only [beta_eq hβ hu]
    rw [hXsum]
    refine ⟨GlobalTheory.OpTrace.isTraceClass_sum _ fun j _ => (hj j).1, ?_⟩
    rw [GlobalTheory.OpTrace.trace_sum _ fun j _ => (hj j).1, hc, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => (hj j).2
  · push_neg at hnt
    obtain ⟨i0, hi0⟩ := hnt
    have hTz : ∀ w y, T w y = 0 := fun w y => (T w).map_coord_zero i0 (Subsingleton.elim _ _)
    have hH : ∀ v : H, v = 0 := by
      intro v
      have hv : v ∈ (Submodule.span ℂ {v | ∃ w y, v = T w y}).topologicalClosure := by
        rw [hdense]; exact Submodule.mem_top
      have := inner_eq_zero_of_mem_closure_span (a := v)
        (by rintro _ ⟨w, y, rfl⟩; rw [hTz, inner_zero_left]) hv
      exact inner_self_eq_zero.1 this
    have hX0 : X = 0 := ContinuousLinearMap.ext fun v => hH _
    have hB0 : B i0 = 0 := ContinuousLinearMap.ext fun v => Subsingleton.elim _ _
    have hb0 : b i0 = 0 := by rw [← (hB i0).2, hB0, GlobalTheory.OpTrace.trace_zero]
    rw [hX0, Finset.prod_eq_zero (Finset.mem_univ i0) hb0, mul_zero]
    exact ⟨GlobalTheory.OpTrace.isTraceClass_zero, GlobalTheory.OpTrace.trace_zero⟩

end GlobalTheory.TensorTrace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsPureTensorBaseVectorAndLocalFactor
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting GlobalTheory.PlaceTensor
open scoped TensorProduct ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocalPure

variable {D : D7}

theorem wAt_add {m n : ℕ} (p : Place D) (x y : Mx D m n) : wAt p (x + y) = wAt p x + wAt p y := by
  rw [wAt_eq_smul, wAt_eq_smul, wAt_eq_smul, smul_add]

theorem wAt_zero {m n : ℕ} (p : Place D) : wAt p (0 : Mx D m n) = 0 := by
  rw [wAt_eq_smul, smul_zero]

theorem wAt_two {m n : ℕ} (p : Place D) (x : Mx D m n) : wAt p (2 • x) = 2 • wAt p x := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_comm]

theorem wAt_wAt_self {m n : ℕ} (p : Place D) (x : Mx D m n) : wAt p (wAt p x) = wAt p x := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, ((GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).1 p)]

theorem wAt_wAt_ne {m n : ℕ} {p q : Place D} (h : p ≠ q) (x : Mx D m n) : wAt p (wAt q x) = 0 := by
  rw [wAt_eq_smul, wAt_eq_smul, smul_smul, ((GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.1 p q h), zero_smul]

theorem wAt_sum_of_notMem {m n : ℕ} {p : Place D} {P : Finset (Place D)} (h : p ∉ P) (x : Mx D m n) :
    wAt p (∑ r ∈ P, wAt r x) = 0 := by
  rw [wAt_eq_smul, Finset.smul_sum]
  refine Finset.sum_eq_zero fun r hr => ?_
  have hpr : p ≠ r := fun e => h (e ▸ hr)
  rw [← wAt_eq_smul]
  exact wAt_wAt_ne hpr x

theorem wAt_sum_of_mem {m n : ℕ} {p : Place D} {P : Finset (Place D)} (h : p ∈ P) (x : Mx D m n) :
    wAt p (∑ r ∈ P, wAt r x) = wAt p x := by
  rw [wAt_eq_smul, Finset.smul_sum, Finset.sum_eq_single_of_mem p h]
  · rw [← wAt_eq_smul]
    exact wAt_wAt_self p x
  · intro r _ hrp
    rw [← wAt_eq_smul]
    exact wAt_wAt_ne (Ne.symm hrp) x

theorem symplO_wAt (S T : HSp D) {p : Place D} (w : WO S T) {z : WO S T} (hz : wAt p z = 0) :
    symplO S T (wAt p w) z = 0 := by
  rw [wAt_eq_smul, GlobalTheory.SplitScalar.symplO_smul, (GlobalTheory.T.cmAdeleIdempotentOfPlace_properties D).2.2.1 p, ← wAt_eq_smul, hz,
    GlobalTheory.SplitScalar.symplO_zero_right]

section

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
  {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {f₀ : WO S T → ℂ} {μ : Measure (WO S T)} {𝓕 : Set (WO S T)}

theorem ip_base (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) : ipO μ 𝓕 f₀ f₀ = 1 := by
  obtain ⟨-, -, -, -, hff, -⟩ := GlobalTheory.T.theta_inner_product_hermitian D ψ S T μ 𝓕 (base_std h) hμ f₀ f₀ (base_theta h) (base_theta h)
  rw [hff, restrictedTensorBasePoint_norm_sq h hμ]
  simp

theorem ip_heis_wAt (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) (p : Place D) (w : WO S T)
    {f g : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hg : IsThetaFunO ψ S T g)
    (vf : VacAt ψ θ S T sS sT ΛS ΛT p f) (vg : VacAt ψ θ S T sS sT ΛS ΛT p g) :
    ipO μ 𝓕 g (heisO ψ S T (wAt p w) f) = ipO μ 𝓕 f₀ (heisO ψ S T (wAt p w) f₀) * ipO μ 𝓕 g f := by
  have h0 := base_vacAt h p
  have hb := base_theta h
  rcases p with v | τ
  · obtain ⟨γ, hγ⟩ := GlobalTheory.T.heisenberg_compression_finite_place_lattice_vacua_scalar D ψ S T ΛS ΛT μ 𝓕 (base_std h) h.2.2.1 h.2.2.2.1 hμ v w
    have e0 := hγ f₀ f₀ hb hb h0 h0
    rw [ip_base h hμ, mul_one] at e0
    rw [hγ f g hf hg vf vg, e0]
  · obtain ⟨γ, hγ⟩ := GlobalTheory.T.heisenberg_compression_real_place_fock_vacua_scalar D ψ θ S T μ 𝓕 (base_std h) (base_inf h) hμ τ (sS τ) (sT τ) (h.1 τ) (h.2.1 τ) w
    have e0 := hγ f₀ f₀ hb hb h0 h0
    rw [ip_base h hμ, mul_one] at e0
    rw [hγ f g hf hg vf vg, e0]

theorem ip_heis_sum (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) (w z : WO S T)
    {y : WO S T → ℂ} (hy : IsThetaFunO ψ S T y) (P : Finset (Place D)) (hz : ∀ p ∈ P, wAt p z = 0)
    (vy : ∀ p ∈ P, VacAt ψ θ S T sS sT ΛS ΛT p y) :
    ipO μ 𝓕 y (heisO ψ S T (∑ p ∈ P, wAt p w + z) f₀) =
      (∏ p ∈ P, ipO μ 𝓕 f₀ (heisO ψ S T (wAt p w) f₀)) * ipO μ 𝓕 y (heisO ψ S T z f₀) := by
  classical
  have hψ := base_std h
  have hb := base_theta h
  have hth := (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  revert hz vy
  refine Finset.induction_on P ?_ ?_
  · intro _ _
    rw [Finset.sum_empty, zero_add, Finset.prod_empty, one_mul]
  · intro a P ha ih hz vy
    have hzP : ∀ p ∈ P, wAt p z = 0 := fun p hp => hz p (Finset.mem_insert_of_mem hp)
    have vyP : ∀ p ∈ P, VacAt ψ θ S T sS sT ΛS ΛT p y := fun p hp => vy p (Finset.mem_insert_of_mem hp)
    have hZ : wAt a (∑ p ∈ P, wAt p w + z) = 0 := by
      rw [wAt_add, wAt_sum_of_notMem ha, hz a (Finset.mem_insert_self a P), add_zero]
    have hv : VacAt ψ θ S T sS sT ΛS ΛT a (heisO ψ S T (∑ p ∈ P, wAt p w + z) f₀) :=
      (GlobalTheory.T.fockVacua_localFactors_stable_heisenberg_away D ψ θ S T sS sT ΛS ΛT hψ (base_inf h) f₀ hb).1 a _ hZ (base_vacAt h a)
    rw [Finset.sum_insert ha, Finset.prod_insert ha, add_assoc,
      GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (symplO_wAt S T w hZ),
      ip_heis_wAt h hμ a w (hth _ _ hb) hy hv (vy a (Finset.mem_insert_self a P)), ih hzP vyP]
    ring

private theorem isLatVac_of_isBase (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) :
    IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun _ => True) f₀ := by
  have hv := h.2.2.2.2
  unfold IsVacO at hv
  obtain ⟨-, hv2⟩ := hv
  cases hv2
  assumption

theorem isPure_local (h : IsBase ψ θ S T sS sT ΛS ΛT f₀) (hμ : IsCovolOne (ratL T S) μ 𝓕) (q : Place D)
    (x : Place D → WO S T → ℂ) (hx : IsLocal ψ θ S T sS sT ΛS ΛT q (x q)) (hq : ∀ p, p ≠ q → x p = f₀) :
    IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x (x q) := by
  classical
  have hfull := isLatVac_of_isBase h
  unfold IsPure IsRestricted
  refine ⟨⟨fun p => ?_, ?_⟩, hx.1, fun w => ?_⟩
  · by_cases hpq : p = q
    · subst hpq
      exact hx
    · rw [hq p hpq]
      exact base_isLocal h p
  · refine (Set.finite_singleton q).subset fun p hp => ?_
    by_contra hpq
    exact hp (hq p hpq)
  · obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT h.2.2.1 h.2.2.2.1 w
    obtain ⟨u, hu, hw⟩ := hP₀ (insert q P₀) (Finset.subset_insert q P₀)
    have hqP : q ∈ insert q P₀ := Finset.mem_insert_self q P₀
    generalize insert q P₀ = P at hw hqP

    have key : ∀ p ∈ P, wAt p (2 • u) = 0 := by
      intro p hp
      have e := congrArg (wAt p) hw
      rw [wAt_add, wAt_sum_of_mem hp] at e
      calc wAt p (2 • u) = wAt p w + wAt p (2 • u) - wAt p w := by abel
        _ = wAt p w - wAt p w := by rw [← e]
        _ = 0 := sub_self _
    have hS : symplO S T (∑ p ∈ P, wAt p w) (2 • u) = 0 := by
      refine Finset.sum_induction _ (fun t => symplO S T t (2 • u) = 0) ?_
        (GlobalTheory.SplitScalar.symplO_zero_left S T _) (fun p hp => symplO_wAt S T w (key p hp))
      intro a b (ha : symplO S T a (2 • u) = 0) (hb : symplO S T b (2 • u) = 0)
      show symplO S T (a + b) (2 • u) = 0
      have e := GlobalTheory.SplitScalar.symplO_sub_left S T (a + b) b (2 • u)
      rw [show a + b - b = a by abel, ha, hb, sub_zero] at e
      exact e.symm
    have hsub : Function.mulSupport (fun p => ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀)) ⊆ ↑P := by
      intro p hp
      by_contra hpP
      apply hp
      have hpq : p ≠ q := fun e => hpP (e ▸ hqP)
      have ew : wAt p w = wAt p (2 • u) := by
        conv_lhs => rw [hw]
        rw [wAt_add, wAt_sum_of_notMem hpP, zero_add]
      show ipO μ 𝓕 (x p) (heisO ψ S T (wAt p w) f₀) = 1
      rw [hq p hpq, ew, wAt_two]
      have hh : heisO ψ S T (2 • wAt p u) f₀ = f₀ := by
        rcases p with v | τ
        · have hv : IsLatVac (heisO ψ S T) (latO S T ΛS ΛT fun u => u = v) f₀ := base_vacAt h (.inl v)
          exact hv.1 _ (latO_mono (fun v' hv' => Sum.inl_injective hv'.2)
            (GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT (fun _ => True) u hu (.inl v)).1)
        · rw [(GlobalTheory.T.weilMatrixComponentAtPlace_mem_completedLattice D S T ΛS ΛT (fun _ => True) u hu (.inr τ)).2.2 (fun v _ => Sum.inl_ne_inr),
            smul_zero, GlobalTheory.SplitScalar.heisO_zero]
      rw [hh, ip_base h hμ]
    have e1 : heisO ψ S T w f₀ = heisO ψ S T (∑ p ∈ P, wAt p w) f₀ := by
      conv_lhs => rw [hw]
      rw [GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T hS, hfull.1 u hu]
    have e2 : ipO μ 𝓕 (x q) (heisO ψ S T w f₀) =
        (∏ p ∈ P.erase q, ipO μ 𝓕 f₀ (heisO ψ S T (wAt p w) f₀)) * ipO μ 𝓕 (x q) (heisO ψ S T (wAt q w) f₀) := by
      rw [e1, ← Finset.sum_erase_add P (fun p => wAt p w) hqP]
      exact ip_heis_sum h hμ w (wAt q w) hx.1 (P.erase q) (fun p hp => wAt_wAt_ne (Finset.ne_of_mem_erase hp) w)
        (fun p hp => vacAt_of_isLocal hx (Finset.ne_of_mem_erase hp))
    refine ⟨P.finite_toSet.subset hsub, ?_⟩
    rw [finprod_eq_prod_of_mulSupport_subset _ hsub, ← Finset.prod_erase_mul P _ hqP, e2]
    congr 1
    refine Finset.prod_congr rfl fun p hp => ?_
    rw [hq p (Finset.ne_of_mem_erase hp)]

end

theorem isPure_base_and_local : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) (f₀ : WO S T → ℂ) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsBase ψ θ S T sS sT ΛS ΛT f₀ → IsCovolOne (ratL T S) μ 𝓕 → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ (fun _ => f₀) f₀ ∧ ∀ (q : Place D) (x : Place D → WO S T → ℂ), IsLocal ψ θ S T sS sT ΛS ΛT q (x q) → (∀ p, p ≠ q → x p = f₀) → IsPure ψ θ S T sS sT ΛS ΛT μ 𝓕 f₀ x (x q) := by
  classical
  intro D ψ θ S T sS sT ΛS ΛT f₀ μ 𝓕 h hμ
  refine ⟨?_, fun q x hx hq => isPure_local h hμ q x hx hq⟩
  rcases isEmpty_or_nonempty (Place D) with hE | ⟨⟨q⟩⟩
  · unfold IsPure IsRestricted
    refine ⟨⟨fun p => isEmptyElim p, Set.toFinite _⟩, base_theta h, fun w => ⟨Set.toFinite _, ?_⟩⟩
    rw [finprod_of_isEmpty]
    obtain ⟨P₀, hP₀⟩ := GlobalTheory.T.exists_eq_sum_weilComponents_add_two_smul_lattice D S T ΛS ΛT h.2.2.1 h.2.2.2.1 w
    obtain ⟨u, hu, hw⟩ := hP₀ P₀ subset_rfl
    rw [Finset.eq_empty_of_isEmpty P₀, Finset.sum_empty, zero_add] at hw
    rw [hw, (isLatVac_of_isBase h).1 u hu, ip_base h hμ]
  · exact isPure_local h hμ q (fun _ => f₀) (base_isLocal h q) (fun _ _ => rfl)

end GlobalTheory.LocalPure

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsReading
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.TripleRead

variable {D : D7}

def toUX (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (g : GA D X) : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.UB J :=
  ⟨⟨(mt X g).submatrix e e, (mt X g⁻¹).submatrix e e,
    by rw [Matrix.submatrix_mul_equiv]; simp only [Formalism.L2.Theta.mt, map_inv, Units.mul_inv]; exact Matrix.submatrix_one_equiv e,
    by rw [Matrix.submatrix_mul_equiv]; simp only [Formalism.L2.Theta.mt, map_inv, Units.inv_mul]; exact Matrix.submatrix_one_equiv e⟩, by
    subst hJ
    have k : (mt X g)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ * (mt X g).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ := by
      have := congrArg transpose (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.mt_gram X g)
      rw [transpose_mul, transpose_mul, transpose_transpose, ← Matrix.mul_assoc] at this
      exact this
    show ((mt X g).submatrix e e)ᵀ * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • (X.gramᵀ).submatrix e e) *
      ((mt X g).submatrix e e).map (cA D) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM (D.host.xi0 • (X.gramᵀ).submatrix e e)
    rw [GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM_smul, Matrix.mul_smul, Matrix.smul_mul]
    congr 1
    have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM ((X.gramᵀ).submatrix e e) = (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM X.gramᵀ).submatrix e e := rfl
    have e2 : ((mt X g).submatrix e e).map (cA D) = ((mt X g).map (cA D)).submatrix e e := rfl
    rw [e1, e2, Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, k]⟩

theorem toUX_val (X : HSp D) {k : ℕ} (e : Fin k ≃ Fin X.rank) {J : Matrix (Fin k) (Fin k) D.host.E}
    (hJ : J = D.host.xi0 • (X.gramᵀ).submatrix e e) (g : GA D X) : (toUX X e hJ g).1.1 = (mt X g).submatrix e e := rfl

end GlobalTheory.TripleRead

namespace GlobalTheory.TripleRead

variable {D : D7}

structure IsReading (ψ : AddChar (AF D.host.F) ℂ) {W W₁ X : HSp D} (A : Fr W) (A₁ : Fr W₁) (B : Fr X)
    (α β : (AE D)ˣ →* Circle) (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank)
    (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E) : Prop where

  ψ : Bs.ψ = ψ

  JW : Γ.V.J = (1 : D.host.E) • W.gram

  JW₁ : Γ.V'.J = (-1 : D.host.E) • W₁.gram

  JX : Γ.W.J = D.host.xi0 • (X.gramᵀ).submatrix e e

  cart : ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = conj (tauE D τ x)) ∧ Γ.V.θ w = A.cart τ ∧ Γ.V'.θ w = -A₁.cart τ ∧
    Γ.W.θ w = ((B.cart τ).submatrix e e).map conj

  α : Xc.α = α

  β : Xc.β = β

def ptO {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d) (x : Matrix (Fin d) (Fin m) (AE D)) :
    Matrix (Fin m) (Fin k) (AE D) :=
  ((x * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹)ᵀ).submatrix id e

def thO {m k : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E m} {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k}
    (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z) (ψ : AddChar (AF D.host.F) ℂ) {d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E)
    (e : Fin k ≃ Fin d) (Φ : (Fin m × Fin k → AF D.host.F) → ℂ) (x : Matrix (Fin d) (Fin m) (AE D)) : ℂ :=
  GlobalTheory.WeilM.thetaSum D.host.F (Mo.co.rho ψ (ptO G e x) Φ)

def IsTransp (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) {M X : HSp D} {k : ℕ} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E M.rank}
    {Z : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E k} (Mo : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model D.sp.cm.sig Y Z)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Y Z) (ω : WRep M X) (e : Fin k ≃ Fin X.rank)
    (gM : GA D M → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Y.J) (gX : GA D X → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA D.sp.cm.sig Z.J) : Prop :=
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F (Fin M.rank × Fin k), ∀ g h,
    thO Mo ψ (sgn ε M).gram e (om (gM g, gX h) Φ) = ω (g, h) (thO Mo ψ (sgn ε M).gram e Φ)

end GlobalTheory.TripleRead

end
end

