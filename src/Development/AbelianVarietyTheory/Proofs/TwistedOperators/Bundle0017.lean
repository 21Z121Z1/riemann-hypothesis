import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.DecompOfNormalStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0013
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroAtOneOfIteratedDerivsVanishOfGrowthStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_at_one_of_iteratedDerivs_vanish_of_growth : ∀ (φ : ℕ → ℝ → ℂ) (a b : ℝ), (∀ k t, HasDerivAt (φ k) (φ (k + 1) t) t) → (∀ k, φ k 0 = 0) → (∀ k t, ‖φ k t‖ ^ 2 ≤ b * a ^ k * k.factorial) → φ 0 1 = 0 := by
  first | exact @GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth | exact GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth | (intros; apply GlobalTheory.vanish_at_one_of_derivs_vanish_of_growth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfAeFundamentalDomainOfLeftInvariantStatement
section
open MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_ae_zero_on_fundamentalDomain : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsHaarMeasure] (𝓕 : Set G), IsFundamentalDomain Γ 𝓕 μ → ∀ F : G → ℂ, Continuous F → (∀ γ ∈ Γ, ∀ x, F (γ * x) = F x) → (∀ᵐ x ∂(μ.restrict 𝓕), F x = 0) → ∀ x, F x = 0 := by
  first | exact @GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant | exact GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant | (intros; apply GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfMemBoth
section
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.OntoLinAlg

open Formalism.IndefR.U2

variable {I A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
  [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B]

theorem op_mem_ker {θ : A →ₗ[ℂ] B} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
    (hI : Intw θ op opB) (i : I) {k : A} (hk : k ∈ LinearMap.ker θ) : op i k ∈ LinearMap.ker θ := by
  rw [LinearMap.mem_ker] at hk ⊢
  rw [hI, hk, map_zero]

theorem op_mem_orth {θ : A →ₗ[ℂ] B} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
    (hI : Intw θ op opB) (hA : AdjClosed op) (i : I) {v : A} (hv : v ∈ (LinearMap.ker θ)ᗮ) :
    op i v ∈ (LinearMap.ker θ)ᗮ := by
  rw [Submodule.mem_orthogonal] at hv ⊢
  intro u hu
  obtain ⟨i', hi'⟩ := hA i
  rw [← LinearMap.adjoint_inner_left, ← hi']
  exact hv _ (op_mem_ker hI i' hu)

theorem eq_zero_of_mem_both {K : Submodule ℂ A} {z : A} (h1 : z ∈ K) (h2 : z ∈ Kᗮ) : z = 0 := by
  have := (Submodule.mem_orthogonal _ _).mp h2 z h1
  exact inner_self_eq_zero.mp this

theorem ontoParts_of {θ : A →ₗ[ℂ] B} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
    {good : Submodule ℂ A} {goodB : Submodule ℂ B} (Ix : Set (I → ℂ))
    (hI : Intw θ op opB) (hA : AdjClosed op) (hOnto : goodB ≤ LinearMap.range θ)
    (hPr : ∀ y ∈ good, ((LinearMap.ker θ).starProjection y : A) ∈ good)
    (hInj : ∀ (c : I → ℂ) (x y : A), x ∈ eigPart op c → θ x ≠ 0 → y ∈ eigPart op c ⊓ good → θ y = 0 → y = 0) :
    OntoParts (LinearMap.adjoint θ) op opB good goodB Ix := by
  intro c hc y hy
  set K := LinearMap.ker θ with hK
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc.2
  obtain ⟨x0, hx0⟩ := hOnto hw.2
  set x := x0 - K.starProjection x0 with hxdef
  have hxo : x ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal x0
  have hθx : θ x = w := by
    have : θ (K.starProjection x0) = 0 := LinearMap.mem_ker.mp (Submodule.starProjection_apply_mem K x0)
    rw [hxdef, map_sub, this, sub_zero, hx0]
  have hxe : x ∈ eigPart op c := by
    rw [mem_eigPart]
    intro i
    have hz1 : op i x - c i • x ∈ Kᗮ := Submodule.sub_mem _ (op_mem_orth hI hA i hxo) (Submodule.smul_mem _ _ hxo)
    have hz2 : op i x - c i • x ∈ K := by
      rw [hK, LinearMap.mem_ker, map_sub, map_smul, hI, hθx, (mem_eigPart.mp hw.1) i, sub_self]
    exact sub_eq_zero.mp (eq_zero_of_mem_both hz2 hz1)
  set y1 := K.starProjection y with hy1
  have hy1K : y1 ∈ K := Submodule.starProjection_apply_mem K y
  have hy2 : y - y1 ∈ Kᗮ := Submodule.sub_starProjection_mem_orthogonal y
  have hy1e : y1 ∈ eigPart op c := by
    rw [mem_eigPart]
    intro i
    have hyi := (mem_eigPart.mp hy.1) i
    have e : op i y1 - c i • y1 = -(op i (y - y1) - c i • (y - y1)) := by
      rw [map_sub, smul_sub, hyi]; abel
    have hz1 : op i y1 - c i • y1 ∈ K := Submodule.sub_mem _ (op_mem_ker hI i hy1K) (Submodule.smul_mem _ _ hy1K)
    have hz2 : op i y1 - c i • y1 ∈ Kᗮ := by
      rw [e]
      exact Submodule.neg_mem _ (Submodule.sub_mem _ (op_mem_orth hI hA i hy2) (Submodule.smul_mem _ _ hy2))
    exact sub_eq_zero.mp (eq_zero_of_mem_both hz1 hz2)
  have hy10 : y1 = 0 := hInj c x y1 hxe (by rw [hθx]; exact hw0) ⟨hy1e, hPr y hy.2⟩ (LinearMap.mem_ker.mp hy1K)
  rw [← LinearMap.orthogonal_ker]
  have : y = y - y1 := by rw [hy10, sub_zero]
  rw [this]
  exact hy2

end GlobalTheory.OntoLinAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsClmOfGramEqSmulStatement
section
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_clm_of_gram_eq_smul' : ∀ {α Hs E : Type} [NormedAddCommGroup Hs] [InnerProductSpace ℂ Hs] [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] (u : α → Hs) (f : α → E) (K : ℝ), (∀ a b, ⟪f a, f b⟫_ℂ = (K : ℂ) * ⟪u a, u b⟫_ℂ) → Dense (Submodule.span ℂ (Set.range u) : Set Hs) → ∃ A : Hs →L[ℂ] E, ∀ a, A (u a) = f a := by
  first | exact @GlobalTheory.exists_clm_of_gram_eq_smul | exact GlobalTheory.exists_clm_of_gram_eq_smul | (intros; apply GlobalTheory.exists_clm_of_gram_eq_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDescendPeriodicTrig
section
open MeasureTheory

namespace GlobalTheory

theorem trigPoly_dense_periodic : ∀ (G : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G] [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] (Γ : AddSubgroup G) [DiscreteTopology Γ] (K : Set G), IsCompact K → (∀ x, ∃ γ ∈ Γ, γ + x ∈ K) → ∀ (A : Type) [AddCommGroup A] (χ : A → G → ℂ), (∀ a, Continuous (χ a)) → (∀ a x y, χ a (x + y) = χ a x * χ a y) → (∀ a b x, χ (a + b) x = χ a x * χ b x) → (∀ x, χ 0 x = 1) → (∀ a x, ‖χ a x‖ = 1) → (∀ x, (∀ a, χ a x = 1) ↔ x ∈ Γ) → ∀ Φ : G → ℂ, Continuous Φ → (∀ γ ∈ Γ, ∀ x, Φ (γ + x) = Φ x) → ∀ ε : ℝ, 0 < ε → ∃ (s : Finset A) (c : A → ℂ), ∀ x, ‖Φ x - ∑ a ∈ s, c a * χ a x‖ ≤ ε := by
  first
  | exact @_root_.GlobalTheory.QuotientDescentTwistedOperators.approx
  | exact _root_.GlobalTheory.QuotientDescentTwistedOperators.approx
  | (apply _root_.GlobalTheory.QuotientDescentTwistedOperators.approx <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuotientDescentTwistedOperators.approx <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuotientDescentTwistedOperators.approx <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuotientDescentTwistedOperators.approx ..)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualFrameSpanUnitaryRepresentationStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_frame_span_unitary_representation : ∀ {G H : Type} [Mul G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]
    (K : Set G) (ρ : G → (H →ₗ[ℂ] H)) (hmul : ∀ g ∈ K, ∀ h ∈ K, g * h ∈ K)
    (hρ : ∀ g ∈ K, ∀ h ∈ K, ρ (g * h) = ρ g ∘ₗ ρ h)
    (hadj : ∀ g ∈ K, ∃ g' ∈ K, LinearMap.adjoint (ρ g) = ρ g'), ∃ (m : ℕ) (k : Fin m → G) (B : Fin m → (H →ₗ[ℂ] H)), (∀ j, k j ∈ K) ∧
      (∀ A : H →ₗ[ℂ] H, ∀ g ∈ K, LinearMap.trace ℂ H (ρ g ∘ₗ A) =
        ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ A) * LinearMap.trace ℂ H (ρ g ∘ₗ B j)) ∧
      (∀ i, ∀ h ∈ K, B i ∘ₗ ρ h = ∑ j, LinearMap.trace ℂ H (ρ (k j) ∘ₗ (B i ∘ₗ ρ h)) • B j) := by
  first | exact @GlobalTheory.DualFrameSpan.dual_frame | exact GlobalTheory.DualFrameSpan.dual_frame | (intros; apply GlobalTheory.DualFrameSpan.dual_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDualPairIsUnitDetBlocksStatement
section
open scoped Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dual_pair_isUnit_det_blocks' : ∀ {R : Type} [CommRing R] [IsLocalRing R], IsUnit (2 : R) → ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) R), IsUnit S.det →
    ∀ (G₁ G₂ : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R), IsUnit G₁.det →
      G₁ᵀ * Matrix.fromBlocks S 0 0 (-S) * G₂ = Matrix.fromBlocks S 0 0 (-S) →
      ∃ X₁ X₂ : Matrix (Fin n) (Fin n) R, X₁ᵀ * S + S * X₂ = 0 ∧
        IsUnit (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ + G₁.toBlocks₂₁ + G₁.toBlocks₂₂ +
          X₁ * (G₁.toBlocks₁₁ + G₁.toBlocks₁₂ - G₁.toBlocks₂₁ - G₁.toBlocks₂₂)).det ∧
        IsUnit (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ + G₂.toBlocks₂₁ + G₂.toBlocks₂₂ +
          X₂ * (G₂.toBlocks₁₁ + G₂.toBlocks₁₂ - G₂.toBlocks₂₁ - G₂.toBlocks₂₂)).det := by
  first | exact @GlobalTheory.exists_dual_pair_isUnit_det_blocks | exact GlobalTheory.exists_dual_pair_isUnit_det_blocks | (intros; apply GlobalTheory.exists_dual_pair_isUnit_det_blocks <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteDimensionalOrbitOfBoundedRankGeneratStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteDimensional_orbit_of_boundedRank_generated : ∀ (V ι K : Type) [AddCommGroup V] [Module ℂ V] (U : Set ι) (G : Set V) (P : Submodule ℂ V) (D : ι → V →ₗ[ℂ] V)
    (m : ℕ) (L : Fin m → V →ₗ[ℂ] V) (T : K → V →ₗ[ℂ] V) (a : K → ι → ι),
    FiniteDimensional ℂ (Submodule.span ℂ G) →
    (∀ u ∈ U, ∀ f, D u f ∈ Submodule.span ℂ (Set.range fun i => L i f)) →
    G ⊆ P → (∀ u ∈ U, ∀ f ∈ P, D u f ∈ P) →
    (∀ N : Submodule ℂ V, G ⊆ N → (∀ u ∈ U, ∀ f ∈ N, D u f ∈ N) → P ≤ N) →
    (∀ k, ∀ g ∈ G, T k g ∈ Submodule.span ℂ G) → (∀ k, ∀ u ∈ U, a k u ∈ U) →
    (∀ k, ∀ u ∈ U, ∀ f ∈ P, T k (D u f) = D (a k u) (T k f)) →
    ∀ f ∈ P, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ ∀ k, T k f ∈ S := by
  first | exact @GlobalTheory.exists_finiteDimensional_orbit_of_generated | exact GlobalTheory.exists_finiteDimensional_orbit_of_generated | (intros; apply GlobalTheory.exists_finiteDimensional_orbit_of_generated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteReproducingOfSubmodule
section
namespace GlobalTheory

open Finset

theorem exists_finite_reproducing_of_submodule {X : Type} (V : Submodule ℂ (X → ℂ))
    (F : Finset ↥V) :
    ∃ (S : Finset X) (u : X → ↥V), ∀ f ∈ F, f = ∑ x ∈ S, (f : X → ℂ) x • u x := by
  first
  | exact @_root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation
  | exact _root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation
  | (apply _root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation <;> assumption)
  | (intros; apply _root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LagrangeInterpolationExistence.exists_interpolation ..)

theorem finsupp_sum_multilinear_eq_of_prod_eq {ι : Type} [Fintype ι] [DecidableEq ι]
    {X : ι → Type} (V : ∀ k, Submodule ℂ (X k → ℂ)) {R : Type} [AddCommGroup R] [Module ℂ R]
    (M : MultilinearMap ℂ (fun k => ↥(V k)) R) {A : Type} (τ τ' : A →₀ ℂ)
    (φ φ' : A → ∀ k, ↥(V k))
    (h : ∀ z : ∀ k, X k, (τ.sum fun a c => c * ∏ k, (φ a k : X k → ℂ) (z k)) =
      τ'.sum fun a c => c * ∏ k, (φ' a k : X k → ℂ) (z k)) :
    (τ.sum fun a c => c • M (φ a)) = τ'.sum fun a c => c • M (φ' a) := by
  classical
  let T : Finset A := τ.support ∪ τ'.support
  let F : ∀ k, Finset ↥(V k) := fun k => T.image (fun a => φ a k) ∪ T.image (fun a => φ' a k)
  choose S u hSu using fun k => exists_finite_reproducing_of_submodule (V k) (F k)
  have key : ∀ w : ∀ k, ↥(V k), (∀ k, w k ∈ F k) →
      M w = ∑ z ∈ Fintype.piFinset S, (∏ k, (w k : X k → ℂ) (z k)) • M (fun k => u k (z k)) := by
    intro w hw
    have hw' : w = fun k => ∑ x ∈ S k, (w k : X k → ℂ) x • u k x :=
      funext fun k => hSu k (w k) (hw k)
    conv_lhs => rw [hw']
    rw [MultilinearMap.map_sum_finset]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [MultilinearMap.map_smul_univ]
  have expand : ∀ (σ : A →₀ ℂ) (ψ : A → ∀ k, ↥(V k)), σ.support ⊆ T →
      (∀ a ∈ T, ∀ k, ψ a k ∈ F k) →
      (σ.sum fun a c => c • M (ψ a)) = ∑ z ∈ Fintype.piFinset S,
        (σ.sum fun a c => c * ∏ k, (ψ a k : X k → ℂ) (z k)) • M (fun k => u k (z k)) := by
    intro σ ψ hσ hψ
    unfold Finsupp.sum
    rw [Finset.sum_congr rfl fun a ha => congrArg (σ a • ·) (key (ψ a) (hψ a (hσ ha)))]
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [expand τ φ Finset.subset_union_left
      (fun a ha k => Finset.mem_union_left _ (Finset.mem_image_of_mem _ ha)),
    expand τ' φ' Finset.subset_union_right
      (fun a ha k => Finset.mem_union_right _ (Finset.mem_image_of_mem _ ha))]
  exact Finset.sum_congr rfl fun z _ => by rw [h z]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFinsetGeneratingOperatorStableBounded
section
open scoped TensorProduct

namespace GlobalTheory.StabGen

open GlobalTheory.TensHead

variable {M : Type} [AddCommGroup M] [Module ℂ M]

def stabClosure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) : Submodule ℂ M :=
  sInf {N | Rel ≤ N ∧ Stab Op N ∧ S ⊆ N}

theorem rel_le_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    Rel ≤ stabClosure Op Rel S :=
  le_sInf fun _ hN => hN.1

theorem subset_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    S ⊆ stabClosure Op Rel S := fun _ hx =>
  Submodule.mem_sInf.2 fun _ hN => hN.2.2 hx

theorem stab_closure (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M) (S : Set M) :
    Stab Op (stabClosure Op Rel S) := by
  intro g hg x hx
  rw [stabClosure, Submodule.mem_sInf] at hx ⊢
  intro N hN
  exact hN.2.1 g hg x (hx N hN)

theorem closure_le {Op : Set (Module.End ℂ M)} {Rel N : Submodule ℂ M} {S : Set M}
    (h1 : Rel ≤ N) (h2 : Stab Op N) (h3 : S ⊆ N) : stabClosure Op Rel S ≤ N :=
  sInf_le ⟨h1, h2, h3⟩

theorem closure_mono {Op : Set (Module.End ℂ M)} {Rel : Submodule ℂ M} {S T : Set M}
    (h : S ⊆ T) : stabClosure Op Rel S ≤ stabClosure Op Rel T :=
  closure_le (rel_le_closure Op Rel T) (stab_closure Op Rel T)
    (h.trans (subset_closure Op Rel T))

noncomputable def chainSet [DecidableEq M] (pick : Finset M → M) : ℕ → Finset M
  | 0 => ∅
  | n + 1 => insert (pick (chainSet pick n)) (chainSet pick n)

theorem exists_finset_generating (Op : Set (Module.End ℂ M)) (Rel : Submodule ℂ M)
    (hL : ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ M), StrictMono N →
        (∀ j, Rel ≤ N j ∧ ∀ g ∈ Op, ∀ x ∈ N j, g x ∈ N j) → m ≤ L) :
    ∃ F : Finset M, ∀ N : Submodule ℂ M, Rel ≤ N → GlobalTheory.TensHead.Stab Op N →
      (↑F : Set M) ⊆ ↑N → N = ⊤ := by
  classical
  obtain ⟨L, hL⟩ := hL
  by_contra hne
  push_neg at hne
  have hx : ∀ F : Finset M, ∃ x, x ∉ stabClosure Op Rel (F : Set M) := by
    intro F
    obtain ⟨N, h1, h2, h3, h4⟩ := hne F
    by_contra h
    push_neg at h
    exact h4 (eq_top_iff.2 fun x _ => closure_le h1 h2 h3 (h x))
  choose pick hpick using hx
  have hD : StrictMono fun n => stabClosure Op Rel (↑(chainSet pick n) : Set M) := by
    refine strictMono_nat_of_lt_succ fun n => lt_of_le_of_ne ?_ ?_
    · exact closure_mono (Finset.coe_subset.2 (Finset.subset_insert _ _))
    · intro h
      apply hpick (chainSet pick n)
      have hmem : pick (chainSet pick n) ∈ stabClosure Op Rel (↑(chainSet pick (n + 1)) : Set M) :=
        subset_closure Op Rel _ (by simp [chainSet])
      rw [← h] at hmem
      exact hmem
  have := hL (L + 1) (fun j => stabClosure Op Rel (↑(chainSet pick j) : Set M))
    (fun a b hab => hD hab) (fun j => ⟨rel_le_closure _ _ _, stab_closure _ _ _⟩)
  omega

end GlobalTheory.StabGen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHasDerivAtZeroOfMapAddMulStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hasDerivAt_zero_of_map_add_mul' : ∀ ν : ℝ → ℂ, ν 0 = 1 → (∀ s t, ν (s + t) = ν s * ν t) → ContinuousAt ν 0 → ∃ a : ℂ, HasDerivAt ν a 0 := by
  first | exact @GlobalTheory.exists_hasDerivAt_zero_of_map_add_mul | exact GlobalTheory.exists_hasDerivAt_zero_of_map_add_mul | (intros; apply GlobalTheory.exists_hasDerivAt_zero_of_map_add_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIrreducibleSubrepWithGroupAlgebraFixedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_irreducible_subrep_with_groupAlgebra_fixed : ∀ (G G' W : Type) [Group G] [Finite G] [Fintype G'] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ G W) (i : G' → G) (c : G' → ℂ) (x : W), x ≠ 0 → ∑ g, c g • ρ (i g) x = x → ∃ U : Subrepresentation ρ, FiniteDimensional ℂ U.toSubmodule ∧ U.toRepresentation.IsIrreducible ∧ ∃ y : U.toSubmodule, y ≠ 0 ∧ ∑ g, c g • U.toRepresentation (i g) y = y := by
  first | exact @GlobalTheory.FixedVec.exists_irreducible_subrep_fixed | exact GlobalTheory.FixedVec.exists_irreducible_subrep_fixed | (intros; apply GlobalTheory.FixedVec.exists_irreducible_subrep_fixed <;> assumption)
end

