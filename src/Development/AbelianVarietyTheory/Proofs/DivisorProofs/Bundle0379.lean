import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0345
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0005
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RingKrullDimQuotientEqOfMemMinimalPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0177
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0346
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0081
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterSemidirectOrbitCrossTerms
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizedSuperlatticeOfRiemannForm
section
set_option autoImplicit false

noncomputable section

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UnimodOver

open Module

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_basis (Λ : Submodule ℤ V) [DiscreteTopology Λ]
    (hs : Submodule.span ℝ (Λ : Set V) = ⊤) :
    ∃ (n : ℕ) (b : Basis (Fin n) ℝ V), Submodule.span ℤ (Set.range b) = Λ := by
  haveI : IsZLattice ℝ Λ := ⟨hs⟩
  haveI : Module.Free ℤ Λ := ZLattice.module_free ℝ Λ
  let b := (Module.Free.chooseBasis ℤ Λ).reindex (Fintype.equivFin _)
  exact ⟨_, b.ofZLatticeBasis ℝ Λ, b.ofZLatticeBasis_span ℝ Λ⟩

theorem discrete_dual (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤) :
    DiscreteTopology (B.dualSubmodule Λ) := by
  classical
  obtain ⟨n, b, hb⟩ := exists_basis Λ hs
  rw [← hb, LinearMap.BilinForm.dualSubmodule_span_of_basis B hB b]
  infer_instance

theorem discrete_of_le {L M : Submodule ℤ V} [DiscreteTopology M] (h : L ≤ M) :
    DiscreteTopology L :=
  DiscreteTopology.of_continuous_injective (continuous_inclusion h) (Set.inclusion_injective h)

theorem span_of_le {L M : Submodule ℤ V} (hs : Submodule.span ℝ (L : Set V) = ⊤) (h : L ≤ M) :
    Submodule.span ℝ (M : Set V) = ⊤ := by
  rw [eq_top_iff, ← hs]
  exact Submodule.span_mono h

theorem exists_nsmul_mem {L M : Submodule ℤ V} [DiscreteTopology M]
    (hs : Submodule.span ℝ (L : Set V) = ⊤) (h : L ≤ M) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ M, N • x ∈ L := by
  haveI := discrete_of_le h
  haveI : IsZLattice ℝ L := ⟨hs⟩
  haveI : IsZLattice ℝ M := ⟨span_of_le hs h⟩
  have hr : finrank ℤ (L.comap M.subtype) = finrank ℤ M := by
    rw [(Submodule.comapSubtypeEquivOfLe h).finrank_eq, ZLattice.rank ℝ L, ZLattice.rank ℝ M]
  haveI hfin : Finite (M ⧸ L.comap M.subtype) := Submodule.finiteQuotientOfFreeOfRankEq _ hr
  refine ⟨Nat.card (M ⧸ L.comap M.subtype), Nat.card_pos, fun x hx => ?_⟩
  have h1 := (L.comap M.subtype).toAddSubgroup.nsmul_index_mem ⟨x, hx⟩
  exact h1

theorem exists_selfDual (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (hA : B.IsAlt)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤)
    (hint : Λ ≤ B.dualSubmodule Λ) :
    ∃ M : Submodule ℤ V, Λ ≤ M ∧ M ≤ B.dualSubmodule Λ ∧ B.dualSubmodule M = M := by
  haveI := discrete_dual B hB Λ hs
  set D := B.dualSubmodule Λ with hD
  haveI : IsZLattice ℝ D := ⟨span_of_le hs hint⟩
  haveI : IsNoetherian ℤ D := inferInstance
  have anti : ∀ {L M : Submodule ℤ V}, L ≤ M → B.dualSubmodule M ≤ B.dualSubmodule L :=
    fun h _ hy x hx => hy x (h hx)
  obtain ⟨M, ⟨h1, h2⟩, hmax⟩ := (set_has_maximal_iff_noetherian.2 this)
    {M : Submodule ℤ D | Λ ≤ M.map D.subtype ∧
      M.map D.subtype ≤ B.dualSubmodule (M.map D.subtype)}
    ⟨Λ.comap D.subtype, by
      simp only [Set.mem_setOf_eq, Submodule.map_comap_subtype, inf_eq_right.2 hint]
      exact ⟨le_rfl, hint⟩⟩
  refine ⟨M.map D.subtype, h1, Submodule.map_subtype_le _ _, le_antisymm ?_ h2⟩
  intro w hw
  have hwD : w ∈ D := anti h1 hw
  have hle : M ≤ M ⊔ Submodule.span ℤ {⟨w, hwD⟩} := le_sup_left
  have heq : M = M ⊔ Submodule.span ℤ {⟨w, hwD⟩} := by
    by_contra hne
    refine hmax _ ⟨h1.trans (Submodule.map_mono hle), ?_⟩ (lt_of_le_of_ne hle hne)
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hx₂
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy₂
    have e1 := h2 ⟨x₁, hx₁, rfl⟩ _ ⟨y₁, hy₁, rfl⟩
    have e2 := hw _ ⟨y₁, hy₁, rfl⟩
    have e3 := hw _ ⟨x₁, hx₁, rfl⟩
    have e4 : B (x₁ : V) w = - B w (x₁ : V) := (hA.neg_eq _ _).symm
    have e5 : B w w = 0 := hA w
    have e6 : B (D.subtype (x₁ + a • ⟨w, hwD⟩)) (D.subtype (y₁ + c • ⟨w, hwD⟩)) =
        B (D.subtype x₁) (D.subtype y₁) + a • B w (D.subtype y₁) - c • B w (D.subtype x₁) := by
      simp only [Submodule.subtype_apply, Submodule.coe_add, Submodule.coe_smul, map_add, map_zsmul,
        LinearMap.add_apply, LinearMap.smul_apply, e4, e5, smul_zero, smul_neg, add_zero]
      ring
    rw [e6]
    exact sub_mem (add_mem e1 (Submodule.smul_mem _ _ e2)) (Submodule.smul_mem _ _ e3)
  have : (⟨w, hwD⟩ : D) ∈ M := by
    rw [heq]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  exact ⟨_, this, rfl⟩

theorem dualSubmoduleToDual_surjective (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤) :
    Function.Surjective (B.dualSubmoduleToDual Λ) := by
  classical
  obtain ⟨n, b, hb⟩ := exists_basis Λ hs
  have hbmem : ∀ i, b i ∈ Λ := fun i => hb ▸ Submodule.subset_span ⟨i, rfl⟩
  intro φ
  set y : V := ∑ i, (φ ⟨b i, hbmem i⟩ : ℤ) • B.dualBasis hB b i with hy
  have hymem : y ∈ B.dualSubmodule Λ := by
    rw [← hb, LinearMap.BilinForm.dualSubmodule_span_of_basis B hB b]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hLI : LinearIndependent ℤ b := b.linearIndependent.restrict_scalars' ℤ
  let bΛ : Module.Basis (Fin n) ℤ Λ := (Module.Basis.span hLI).map (LinearEquiv.ofEq _ _ hb)
  have hbΛ : ∀ i, (bΛ i : V) = b i := fun i => by simp [bΛ, Module.Basis.span_apply]
  refine ⟨⟨y, hymem⟩, bΛ.ext fun j => ?_⟩
  apply Int.cast_injective (α := ℝ)
  have hspec := LinearMap.BilinForm.dualSubmoduleParing_spec B ⟨y, hymem⟩ (bΛ j)
  simp only [algebraMap_int_eq, Int.coe_castRingHom] at hspec
  rw [LinearMap.BilinForm.dualSubmoduleToDual_apply_apply, hspec]
  simp only [hbΛ, hy, map_sum, LinearMap.sum_apply, map_zsmul, LinearMap.smul_apply,
    LinearMap.BilinForm.apply_dualBasis_left, smul_ite, smul_zero, zsmul_eq_mul, mul_one,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]
  congr 2
  exact Subtype.ext (hbΛ j).symm

theorem exists_unimodular (B : LinearMap.BilinForm ℝ V) (hB : B.Nondegenerate) (hA : B.IsAlt)
    (Λ : Submodule ℤ V) [DiscreteTopology Λ] (hs : Submodule.span ℝ (Λ : Set V) = ⊤)
    (hint : Λ ≤ B.dualSubmodule Λ) :
    ∃ (M : Submodule ℤ V) (N : ℕ) (Ef : LinearMap.BilinForm ℤ M),
      Λ ≤ M ∧ 0 < N ∧ (∀ x ∈ M, N • x ∈ Λ) ∧ DiscreteTopology M ∧
      Submodule.span ℝ (M : Set V) = ⊤ ∧ (∀ a b : M, (Ef a b : ℝ) = B a b) ∧
      Function.Bijective Ef := by
  obtain ⟨M, h1, h2, h3⟩ := exists_selfDual B hB hA Λ hs hint
  haveI := discrete_dual B hB Λ hs
  haveI : DiscreteTopology M := discrete_of_le h2
  have hsM := span_of_le hs h1
  obtain ⟨N, hN, hNM⟩ := exists_nsmul_mem hs h1
  let e := LinearEquiv.ofEq _ _ h3.symm
  refine ⟨M, N, (B.dualSubmoduleToDual M).comp e.toLinearMap, h1, hN, hNM, this, hsM, ?_, ?_⟩
  · intro a b
    exact B.dualSubmoduleParing_spec (e a) b
  · exact Function.Bijective.comp (g := B.dualSubmoduleToDual M) (f := e)
      ⟨B.dualSubmoduleToDual_injective hB M hsM, dualSubmoduleToDual_surjective B hB M hsM⟩
      e.bijective

end General

def imForm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) : LinearMap.BilinForm ℝ (Fin g → ℂ) :=
  LinearMap.mk₂ ℝ (fun z w => (z ⬝ᵥ Hm.mulVec (star w)).im)
    (fun a b w => by simp [add_dotProduct])
    (fun r a w => by simp [smul_dotProduct])
    (fun a b w => by simp [Matrix.mulVec_add, dotProduct_add])
    (fun r a w => by simp [Matrix.mulVec_smul, dotProduct_smul])

theorem imForm_apply {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    imForm Hm z w = (z ⬝ᵥ Hm.mulVec (star w)).im := rfl

theorem imForm_isAlt {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) :
    (imForm Hm).IsAlt := by
  have key : ∀ u : Fin g → ℂ, star (star u ⬝ᵥ Hm.mulVec u) = star u ⬝ᵥ Hm.mulVec u := by
    intro u
    rw [← Matrix.star_dotProduct (Hm.mulVec u) u, Matrix.star_mulVec, h.eq, ← Matrix.dotProduct_mulVec]
  intro z
  rw [imForm_apply]
  have hq := key (star z)
  rw [star_star] at hq
  exact Complex.conj_eq_iff_im.mp hq

theorem imForm_nondegenerate {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian)
    (hp : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) :
    (imForm Hm).Nondegenerate := by
  have hL : ∀ z : Fin g → ℂ, (∀ w, imForm Hm z w = 0) → z = 0 := by
    intro z hz
    by_contra hne
    have h1 := hz (Complex.I • z)
    rw [imForm_apply, star_smul, Complex.star_def, Complex.conj_I, Matrix.mulVec_smul, dotProduct_smul,
      smul_eq_mul] at h1
    have h2 := hp z hne
    simp [Complex.mul_im] at h1
    linarith
  have hR : ∀ w : Fin g → ℂ, (∀ z, imForm Hm z w = 0) → w = 0 := by
    intro w hw
    by_contra hne
    have h1 := hw (Complex.I • w)
    rw [imForm_apply, smul_dotProduct, smul_eq_mul] at h1
    have h2 := hp w hne
    simp [Complex.mul_im] at h1
    linarith
  first
    | exact ⟨hL, hR⟩
    | exact hL

theorem exists_unimodular_overlattice :
    ∀ (g : ℕ) (Λ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ),
    DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
    (∀ l ∈ Λ, ∀ l' ∈ Λ, ∃ n : ℤ, (l ⬝ᵥ Hm.mulVec (star l')).im = n) →
    ∃ (Λ₁ : Submodule ℤ (Fin g → ℂ)) (N : ℕ) (Ef : LinearMap.BilinForm ℤ Λ₁),
      Λ ≤ Λ₁ ∧ 0 < N ∧ (∀ x ∈ Λ₁, (N : ℂ) • x ∈ Λ) ∧ DiscreteTopology Λ₁ ∧
      Submodule.span ℝ (Λ₁ : Set (Fin g → ℂ)) = ⊤ ∧
      (∀ a b : Λ₁, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef := by
  intro g Λ Hm hd hs hH hp hint
  obtain ⟨M, N, Ef, h1, h2, h3, h4, h5, h6, h7⟩ :=
    exists_unimodular (imForm Hm) (imForm_nondegenerate hH hp) (imForm_isAlt hH) Λ hs
      (fun x hx y hy => by
        obtain ⟨n, hn⟩ := hint x hx y hy
        exact Submodule.mem_one.2 ⟨n, by rw [imForm_apply, hn]; simp⟩)
  refine ⟨M, N, Ef, h1, h2, fun x hx => ?_, h4, h5, h6, h7⟩
  rw [Nat.cast_smul_eq_nsmul]
  exact h3 x hx

end GlobalTheory.UnimodOver
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScalingCompatibleExpansionAtInfinityStatement
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scaling_compatible_expansion_at_infinity : ∀ (F : Type) [Field F] [CharZero F], ∃ (σ : RatFunc F →+* RatFunc F) (j : RatFunc F →+* LaurentSeries F) (r₂ rh : LaurentSeries F →+* LaurentSeries F), r₂.comp (algebraMap (PowerSeries F) (LaurentSeries F)) = (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale 2) ∧ r₂.comp (algebraMap (RatFunc F) (LaurentSeries F)) = (algebraMap (RatFunc F) (LaurentSeries F)).comp σ ∧ rh.comp (algebraMap (PowerSeries F) (LaurentSeries F)) = (algebraMap (PowerSeries F) (LaurentSeries F)).comp (PowerSeries.rescale 2⁻¹) ∧ rh.comp j = j.comp σ ∧ j.comp RatFunc.C = (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C ∧ (algebraMap (RatFunc F) (LaurentSeries F)).comp RatFunc.C = (algebraMap (PowerSeries F) (LaurentSeries F)).comp PowerSeries.C := by
  first | exact @GlobalTheory.Nef.InfScale.scaling_expansion_infinity | exact GlobalTheory.Nef.InfScale.scaling_expansion_infinity | (intros; apply GlobalTheory.Nef.InfScale.scaling_expansion_infinity <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparableNormalisationReducedFibres
section
open Polynomial

namespace GlobalTheory
open GroundTheory.FunctionField GroundTheory.Arith.SchemeCoh KaehlerDifferential

theorem ringKrullDim_eq_one_of_isDedekindDomain_of_not_isField (A : Type) [CommRing A] [IsDedekindDomain A] (h : ¬ IsField A) : ringKrullDim A = 1 := by
  have hle : ringKrullDim A ≤ 1 := Ring.krullDimLE_iff.mp (inferInstance : Ring.KrullDimLE 1 A)
  have h0 : ringKrullDim A ≠ 0 := fun h0 => h (by
      have : Ring.KrullDimLE 0 A := by
        rw [Ring.krullDimLE_iff, h0]
        rfl
      exact Ring.KrullDimLE.isField_of_isDomain)
  have hnn : 0 ≤ ringKrullDim A := ringKrullDim_nonneg_of_nontrivial
  generalize ringKrullDim A = d at hle h0 hnn ⊢
  induction d using WithBot.recBotCoe with
  | bot => exact absurd hnn (by simp)
  | coe n =>
    have h1 : n ≤ 1 := by exact_mod_cast hle
    have h2 : n ≠ 0 := by exact_mod_cast h0
    rw [le_antisymm h1 (Order.one_le_iff_ne_zero.mpr h2)]
    rfl

theorem exists_aeval_finite_of_ringKrullDim_eq_one : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A],
    ringKrullDim A = 1 → ∃ t : A, (Polynomial.aeval (R := k) t).Finite := by
  intro k A _ _ _ _ _ hdim
  obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  have hs : ringKrullDim A = s := by
    let _ : Algebra (MvPolynomial (Fin s) k) A := g.toRingHom.toAlgebra
    have _ : Algebra.IsIntegral (MvPolynomial (Fin s) k) A := ⟨fun x => hfin.to_isIntegral x⟩
    have _ : FaithfulSMul (MvPolynomial (Fin s) k) A :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 hg
    rw [GlobalTheory.ringKrullDim_eq_of_isIntegral (MvPolynomial (Fin s) k) A,
      MvPolynomial.ringKrullDim_of_isNoetherianRing, ringKrullDim_eq_zero_of_field]
    simp
  have hs1 : s = 1 := by
    rw [hdim] at hs
    exact_mod_cast hs.symm
  subst hs1
  refine ⟨g (MvPolynomial.X 0), ?_⟩
  let e : k[X] →ₐ[k] MvPolynomial (Fin 1) k := Polynomial.aeval (MvPolynomial.X 0)
  have he : Function.Surjective e := by
    rw [← AlgHom.range_eq_top]
    change (Polynomial.aeval (R := k) (MvPolynomial.X (R := k) (0 : Fin 1))).range = ⊤
    rw [← Algebra.adjoin_singleton_eq_range_aeval, ← MvPolynomial.adjoin_range_X, Set.range_unique]
    rfl
  have hcomp : Polynomial.aeval (R := k) (g (MvPolynomial.X 0)) = g.comp e := by
    apply Polynomial.algHom_ext
    simp [e]
  rw [hcomp]
  exact RingHom.Finite.comp hfin (RingHom.Finite.of_surjective _ he)

theorem aeval_injective_of_finite_of_not_isField : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A] (y : A),
    (Polynomial.aeval (R := k) y).Finite → ¬ IsField A → Function.Injective (Polynomial.aeval (R := k) y) := by
  intro k A _ _ _ _ y hy hA
  rw [injective_iff_map_eq_zero]
  by_contra hne
  push_neg at hne
  obtain ⟨p, hp, hp0⟩ := hne
  have hyi : IsIntegral k y := (show IsAlgebraic k y from ⟨p, hp0, hp⟩).isIntegral
  set B : Subalgebra k A := (Polynomial.aeval (R := k) y).range with hB
  haveI : Algebra.IsIntegral k B := by
    constructor
    rintro ⟨z, q, rfl⟩
    have : IsIntegral k (Polynomial.aeval y q) := by
      rw [Polynomial.aeval_eq_sum_range]
      refine IsIntegral.sum _ fun i _ => ?_
      exact (hyi.pow i).smul _
    exact (isIntegral_algHom_iff B.val Subtype.val_injective).1 this
  haveI : Algebra.IsIntegral k A := by
    constructor
    intro x
    have hx : (Polynomial.aeval (R := k) y).toRingHom.IsIntegralElem x := hy.to_isIntegral x
    obtain ⟨f, hfm, hf⟩ := hx
    let φ : k[X] →+* B := (Polynomial.aeval (R := k) y).rangeRestrict.toRingHom
    have hxB : IsIntegral B x := by
      refine ⟨f.map φ, hfm.map φ, ?_⟩
      rw [Polynomial.eval₂_map]
      have e : (algebraMap B A).comp φ = (Polynomial.aeval (R := k) y).toRingHom := RingHom.ext fun q => rfl
      rw [e]
      exact hf
    exact isIntegral_trans x hxB
  exact hA ((Algebra.IsIntegral.isField_iff_isField (algebraMap k A).injective).1 (Field.toIsField k))

theorem exists_D_algebraMap_fractionRing_ne_zero : ∀ (k A : Type) [Field k] [CommRing A] [IsDomain A] [Algebra k A]
    [IsFunctionField k (FractionRing A)],
    ∃ a : A, D k (FractionRing A) (algebraMap A (FractionRing A) a) ≠ 0 := by
  intro k A _ _ _ _ _
  have hnt := kaehlerDifferential_nontrivial (k := k) (K := FractionRing A)
  by_contra h
  push_neg at h
  have hall : ∀ x : FractionRing A, D k (FractionRing A) x = 0 := by
    intro x
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) x
    rw [div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv, h a, h b]
    simp
  have htop : (⊤ : Submodule (FractionRing A) Ω[FractionRing A⁄k]) = ⊥ := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_eq_bot]
    rintro _ ⟨x, rfl⟩
    exact hall x
  obtain ⟨ω, hω⟩ := exists_ne (0 : Ω[FractionRing A⁄k])
  have hmem : ω ∈ (⊥ : Submodule (FractionRing A) Ω[FractionRing A⁄k]) := htop ▸ Submodule.mem_top
  exact hω ((Submodule.mem_bot _).1 hmem)

theorem isFunctionField_fractionRing_of_ringKrullDim_eq_one (k A : Type) [Field k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] (hR : ringKrullDim A = 1) :
    IsFunctionField k (FractionRing A) := by
  have htrA : Algebra.trdeg k A = 1 := by
    obtain ⟨s, g, hg, hfin⟩ := exists_finite_inj_algHom_of_fg k A
    have hs := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_eq_of_normalization k g hg hfin.to_isIntegral
    rw [hR] at hs
    have hs1 : s = 1 := by exact_mod_cast hs.symm
    subst hs1
    rw [GroundTheory.Arith.Abelian.Jacobian.trdeg_eq_of_normalization k g hg hfin.to_isIntegral]
    simp
  have htr : Algebra.trdeg k (FractionRing A) = 1 := by
    have : FaithfulSMul A (FractionRing A) :=
      (faithfulSMul_iff_algebraMap_injective _ _).2 (IsFractionRing.injective A _)
    have : Algebra.IsAlgebraic A (FractionRing A) :=
      IsLocalization.isAlgebraic (FractionRing A) (nonZeroDivisors A)
    rw [← trdeg_add_eq k A (A := FractionRing A), htrA, trdeg_eq_zero (R := A) (A := FractionRing A),
      add_zero]
  have : Algebra.Transcendental k (FractionRing A) := by
    rw [← trdeg_ne_zero_iff, htr]
    exact one_ne_zero
  obtain ⟨x, hx⟩ := Algebra.Transcendental.transcendental (R := k) (A := FractionRing A)
  refine ⟨x, hx, ?_⟩
  have hbx : IsTranscendenceBasis k ((↑) : ({x} : Set (FractionRing A)) → FractionRing A) :=
    AlgebraicIndependent.isTranscendenceBasis_of_trdeg_le_of_finite
      ((algebraicIndependent_singleton_iff (⟨x, rfl⟩ : ({x} : Set (FractionRing A)))).2 hx)
      (by rw [htr, Cardinal.mk_singleton])
  have halg := hbx.isAlgebraic_field
  rw [Subtype.range_coe] at halg
  have : Algebra.EssFiniteType A (FractionRing A) :=
    Algebra.EssFiniteType.of_isLocalization (FractionRing A) (nonZeroDivisors A)
  have : Algebra.EssFiniteType k (FractionRing A) := Algebra.EssFiniteType.comp k A (FractionRing A)
  have : Algebra.EssFiniteType (IntermediateField.adjoin k {x}) (FractionRing A) :=
    Algebra.EssFiniteType.of_comp k _ (FractionRing A)
  exact Algebra.finite_of_essFiniteType_of_isAlgebraic

theorem exists_separable_normalisation_reduced_fibres : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A], ¬ IsField A → ∃ y : A, (Polynomial.aeval (R := k) y).Finite ∧ ∃ δ : k[X], δ ≠ 0 ∧ ∀ α : k, δ.eval α ≠ 0 → ∀ Q : Ideal A, Q.IsMaximal → y - algebraMap k A α ∉ Q ^ 2 := by
  intro k A _ _ _ _ _ _ hA
  have hdim : ringKrullDim A = 1 := ringKrullDim_eq_one_of_isDedekindDomain_of_not_isField A hA
  haveI : IsFunctionField k (FractionRing A) :=
    isFunctionField_fractionRing_of_ringKrullDim_eq_one k A hdim
  obtain ⟨t, ht⟩ := exists_aeval_finite_of_ringKrullDim_eq_one k A hdim
  obtain ⟨a, ha⟩ := exists_D_algebraMap_fractionRing_ne_zero k A
  have key : ∃ y : A, (Polynomial.aeval (R := k) y).Finite ∧
      D k (FractionRing A) (algebraMap A (FractionRing A) y) ≠ 0 := by
    by_cases hD : D k (FractionRing A) (algebraMap A (FractionRing A) t) = 0
    · obtain ⟨M, hM⟩ := GlobalTheory.T.noether_normalization_finite_aeval_pow_add k A t a ht
      refine ⟨t ^ M + a, hM, ?_⟩
      rw [map_add, map_pow, map_add, Derivation.leibniz_pow, hD, smul_zero, smul_zero, zero_add]
      exact ha
    · exact ⟨t, ht, hD⟩
  obtain ⟨y, hy, hDy⟩ := key
  haveI := isSeparable_of_D_ne_zero hDy
  exact ⟨y, hy, GlobalTheory.T.reduced_fibres_almost_all_of_separable_dedekind_curve k A y hy (aeval_injective_of_finite_of_not_isField k A y hy hA) this⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTopDegreeCoefficientFormAndEqOnTopForms
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential

namespace GlobalTheory.PD

theorem isTop_exists_and_eq (k : Type) [Field k] [CharZero k] (F K : Type) [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra F K] [IsScalarTower k F K] (d : ℕ) (x : Fin (d + 1) → F) :
    IsFinCover k K x → (∃ τ : DR k K →ₗ[K] K, IsTop k K x τ) ∧
      ∀ τ : DR k K →ₗ[K] K, IsTop k K x τ → ∀ y ∈ ⋀[K]^d Ω[K⁄k], y = τ y • vol0 k K x := by
  intro h
  refine ⟨h.exists_isTop, fun τ hτ y hy => ?_⟩
  obtain ⟨b, hb⟩ := h.exists_basis
  set u : Fin d → K := fun j => (algebraMap F K (x j.succ / x 0))⁻¹
  have hu : ∀ j, u j ≠ 0 := fun j =>
    inv_ne_zero ((map_ne_zero _).2 (div_ne_zero (h.pd.ne _) (h.pd.ne 0)))
  have hp : (∏ j, u j) ≠ 0 := Finset.prod_ne_zero_iff.2 fun j _ => hu j
  have hv : vol0 k K x = (∏ j, u j) • ExteriorAlgebra.ιMulti K d b := by
    rw [← AlternatingMap.map_smul_univ]
    simp only [vol0, hb, u]

  have key : ∀ c : K, c • vol0 k K x = τ (c • vol0 k K x) • vol0 k K x := by
    intro c
    rw [map_smul, hτ.1, smul_eq_mul, mul_one]
  rw [← ExteriorAlgebra.ιMulti_span_fixedDegree] at hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨m, rfl⟩ := hz
    have e : ExteriorAlgebra.ιMulti K d m = (b.det m * (∏ j, u j)⁻¹) • vol0 k K x := by
      rw [hv, smul_smul, mul_assoc, inv_mul_cancel₀ hp, mul_one]
      rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff K]
      intro φ
      have h2 := congrArg (fun g => g m)
        (AlternatingMap.eq_smul_basis_det b (φ.compAlternatingMap (ExteriorAlgebra.ιMulti K d)))
      simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at h2
      rw [map_sub, map_smul, h2, smul_eq_mul, mul_comm, sub_self]
    rw [e]
    exact key _
  | zero => simp
  | add a c _ _ ha hc => rw [map_add, add_smul, ← ha, ← hc]
  | smul r a _ ha => rw [map_smul, smul_eq_mul, mul_smul, ← ha]

end GlobalTheory.PD
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePlaceOrdEqOneStatement
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_place_ord_eq_one_of_transcendental_generator : ∀ (k L : Type) [Field k] [Field L] [Algebra k L] (x : L), Transcendental k x → k⟮x⟯ = ⊤ → ∃ v : Place k L, ord v x = 1 ∧ ∀ w : Place k L, w.1 x < 1 → w = v := by
  first | exact @GlobalTheory.Nef.exists_unique_place_ord_eq_one | exact GlobalTheory.Nef.exists_unique_place_ord_eq_one | (intros; apply GlobalTheory.Nef.exists_unique_place_ord_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryMulIntegralOfNormMaximalOrderUnitStatement
section
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_mul_integral_of_norm_maximalOrder_unit : ∀ {O K A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing A] [Algebra K A] [Algebra O A] [IsScalarTower O K A] [Module.Finite K A] [IsReduced A]
    (σ : K →+* K), (∀ a : O, ∃ b : O, σ (algebraMap O K a) = algebraMap O K b) →
    ∀ τ : A →+* A, (∀ a, τ (τ a) = a) → (∀ k, τ (algebraMap K A k) = algebraMap K A (σ k)) →
    ∀ x : Aˣ, IsIntegral O (τ (x : A) * x) → IsIntegral O (τ ((x⁻¹ : Aˣ) : A) * ((x⁻¹ : Aˣ) : A)) →
    ∃ t : Aˣ, τ (t : A) * t = 1 ∧ IsIntegral O ((t : A) * ((x⁻¹ : Aˣ) : A)) ∧
      IsIntegral O (((t⁻¹ : Aˣ) : A) * (x : A)) := by
  first | exact @GlobalTheory.UnitAdj.exists_unitary_mul_integral | exact GlobalTheory.UnitAdj.exists_unitary_mul_integral | (intros; apply GlobalTheory.UnitAdj.exists_unitary_mul_integral <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterSemidirectOrbitCrossTermsStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_virtualCharacter_semidirect_orbit_cross_terms : ∀ (G Γ : Type) [Group G] [Finite G] [Group Γ] [Fintype Γ] (φ : Γ →* MulAut G) (s : Γ), (Nat.card Γ).Prime → s ≠ 1 → ∀ a b : G → ℂ, a ∈ Virt ℂ ℂ G → b ∈ Virt ℂ ℂ G → ∃ Z ∈ Virt ℂ ℂ (G ⋊[φ] Γ), (∀ g, Z (inl g) = ∏ t : Γ, (a (φ t g) + b (φ t g)) - ∏ t : Γ, a (φ t g) - ∏ t : Γ, b (φ t g)) ∧ ∀ δ, Z (inl δ * inr s) = 0 := by
  first | (exact @GlobalTheory.CrossOrbit.cross_terms_induced) | (exact GlobalTheory.CrossOrbit.cross_terms_induced) | (intros; apply GlobalTheory.CrossOrbit.cross_terms_induced <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVirtualCharacterTwistedHarishChandraInductStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_virtualCharacter_twistedHarishChandraInductionGL : ∀ (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F'] (a b n : ℕ), n = a + b → ∀ X ∈ Virt ℂ ℂ (GHat F F' a), ∃ Z ∈ Virt ℂ ℂ (GHat F F' n), ∀ (t : F' ≃ₐ[F] F') (δ : GL (Fin n) F'), Z (inl δ * inr t) = hcTw (t : F' →+* F') a b (fun d => X (inl d * inr t)) (fun _ => 1) n δ := by
  first | (exact @GlobalTheory.Shin.HatInd.hat_ind) | (exact GlobalTheory.Shin.HatInd.hat_ind) | (intros; apply GlobalTheory.Shin.HatInd.hat_ind <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteTypeFieldStrictlyHenselianStatement
section
open GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sH_of_isField_finiteType_of_isAlgClosed : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B] [Algebra.FiniteType k B], IsField B → SH B := by
  first | (exact @GlobalTheory.field_finiteType_algClosed_SH) | (exact GlobalTheory.field_finiteType_algClosed_SH) | (intros; apply GlobalTheory.field_finiteType_algClosed_SH  <;> assumption)
end

