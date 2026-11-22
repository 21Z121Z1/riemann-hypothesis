import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticChartsRealizationCompPointEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0731
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0784
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0741
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0756
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0732
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0700
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0785
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0791
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0622
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0013
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0792
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairAtInvNatSmulSelf
section
noncomputable section

namespace GlobalTheory.ColNorms.SumBound

open NumberField IsDedekindDomain
open Formalism.L2.DIV Formalism.L2.Col GlobalTheory.ColNorms
open scoped ComplexOrder Matrix

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : GSD K) (v : InfinitePlace K)

theorem pairAt_add_left (x y z : S.V) : S.pairAt v (x + y) z = S.pairAt v x z + S.pairAt v y z := by
  simp only [GSD.pairAt, map_add, Finsupp.add_apply, add_mul, Finset.sum_add_distrib]

theorem pairAt_add_right (x y z : S.V) : S.pairAt v x (y + z) = S.pairAt v x y + S.pairAt v x z := by
  simp only [GSD.pairAt, map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairAt_smul_left (a : K) (x y : S.V) :
    S.pairAt v (a • x) y = starRingEnd ℂ (v.embedding a) * S.pairAt v x y := by
  simp only [GSD.pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, mul_assoc]

theorem pairAt_smul_right (a : K) (x y : S.V) :
    S.pairAt v x (a • y) = v.embedding a * S.pairAt v x y := by
  simp only [GSD.pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem pairAt_zero_left (y : S.V) : S.pairAt v 0 y = 0 := by
  simp [GSD.pairAt]

theorem pairAt_zero_right (y : S.V) : S.pairAt v y 0 = 0 := by
  simp [GSD.pairAt]

theorem pairAt_sum_left {α : Type*} (s : Finset α) (x : α → S.V) (y : S.V) :
    S.pairAt v (∑ i ∈ s, x i) y = ∑ i ∈ s, S.pairAt v (x i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairAt_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pairAt_add_left, ih]

theorem pairAt_sum_right {α : Type*} (s : Finset α) (x : α → S.V) (y : S.V) :
    S.pairAt v y (∑ i ∈ s, x i) = ∑ i ∈ s, S.pairAt v y (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [pairAt_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, pairAt_add_right, ih]

theorem pairAt_self_nonneg (h : PosAt S v) (x : S.V) : 0 ≤ (S.pairAt v x x).re := by
  have h1 := h.dotProduct_mulVec_nonneg (fun i => v.embedding (S.bV.repr x i))
  have h2 : S.pairAt v x x = star (fun i => v.embedding (S.bV.repr x i)) ⬝ᵥ
      (S.gramV.map v.embedding) *ᵥ (fun i => v.embedding (S.bV.repr x i)) := by
    simp only [GSD.pairAt, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply, mul_assoc]
    rfl
  rw [h2]
  exact (Complex.nonneg_iff.mp h1).1

theorem pairAt_smul_self (a : K) (x : S.V) :
    (S.pairAt v (a • x) (a • x)).re = ‖v.embedding a‖ ^ 2 * (S.pairAt v x x).re := by
  rw [pairAt_smul_left, pairAt_smul_right, ← mul_assoc, Complex.conj_mul', ← Complex.ofReal_pow, Complex.re_ofReal_mul]

theorem pairAt_inv_nat_smul_self (n : ℕ) (x : S.V) :
    (S.pairAt v (((n : K))⁻¹ • x) (((n : K))⁻¹ • x)).re = ((n : ℝ)⁻¹) ^ 2 * (S.pairAt v x x).re := by
  rw [pairAt_smul_self]
  simp

theorem pairAt_cross_le (h : PosAt S v) (x y : S.V) :
    (S.pairAt v x y).re + (S.pairAt v y x).re ≤ (S.pairAt v x x).re + (S.pairAt v y y).re := by
  have h1 := pairAt_self_nonneg S v h (x + (-1 : K) • y)
  rw [pairAt_add_left, pairAt_add_right, pairAt_add_right, pairAt_smul_left, pairAt_smul_left,
    pairAt_smul_right, pairAt_smul_right] at h1
  simp at h1
  linarith

theorem pairAt_sum_le (h : PosAt S v) {α : Type*} (s : Finset α) (x : α → S.V) :
    (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re ≤ (s.card : ℝ) * ∑ i ∈ s, (S.pairAt v (x i) (x i)).re := by
  have e1 : (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re = ∑ i ∈ s, ∑ j ∈ s, (S.pairAt v (x i) (x j)).re := by
    rw [pairAt_sum_left, Complex.re_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [pairAt_sum_right, Complex.re_sum]
  have e2 : (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re = ∑ i ∈ s, ∑ j ∈ s, (S.pairAt v (x j) (x i)).re := by
    rw [e1, Finset.sum_comm]
  have e3 : ∑ i ∈ s, ∑ j ∈ s, ((S.pairAt v (x i) (x j)).re + (S.pairAt v (x j) (x i)).re) ≤
      ∑ i ∈ s, ∑ j ∈ s, ((S.pairAt v (x i) (x i)).re + (S.pairAt v (x j) (x j)).re) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => pairAt_cross_le S v h _ _
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at e3
  linarith

theorem ipAt_re (h : S.Ok) (φ ψ : S.D → S.V) :
    (S.ipAt h v φ ψ).re = ∑ c ∈ @Finset.univ _ h.fintypeCl,
      (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ * (S.pairAt v (φ (S.outSec.rep c)) (ψ (S.outSec.rep c))).re := by
  unfold GSD.ipAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_inv, Complex.re_ofReal_mul]

theorem inv_nat_le_one (n : ℕ) : ((n : ℝ))⁻¹ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · exact inv_le_one_of_one_le₀ (by exact_mod_cast hn)

theorem ipAt_self_nonneg (h : S.Ok) (hp : PosAt S v) (φ : S.D → S.V) : 0 ≤ (S.ipAt h v φ φ).re := by
  rw [ipAt_re]
  exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (pairAt_self_nonneg S v hp _)

theorem ipAt_self_le (h : S.Ok) (hp : PosAt S v) (φ : S.D → S.V) (B : ℝ)
    (hB : ∀ d, (S.pairAt v (φ d) (φ d)).re ≤ B) : (S.ipAt h v φ φ).re ≤ (Nat.card S.Cl : ℝ) * B := by
  rw [ipAt_re]
  letI := h.fintypeCl
  calc _ ≤ ∑ _c : S.Cl, B := Finset.sum_le_sum fun c _ => by
        have h0 := pairAt_self_nonneg S v hp (φ (S.outSec.rep c))
        exact ((mul_le_mul_of_nonneg_right (inv_nat_le_one _) h0).trans (by rw [one_mul])).trans (hB _)
    _ = _ := by simp [Nat.card_eq_fintype_card]

variable {S} in

theorem appOf_le {S' : GSD K} (A : ClsKer S S') (h : S.Ok) (hp : PosAt S v) (hp' : PosAt S' v) (t : ℝ) (ht : 0 ≤ t)
    (φ : S.D → S.V) (d' : S'.D) (hA : ∀ d, OpLe S S' v (A.k d d') t) :
    (S'.pairAt v (A.appOf h S.outSec φ d') (A.appOf h S.outSec φ d')).re ≤
      (Nat.card S.Cl : ℝ) * (t * (S.ipAt h v φ φ).re) := by
  letI := h.fintypeCl
  unfold ClsKer.appOf
  refine (pairAt_sum_le S' v hp' _ _).trans ?_
  rw [Finset.card_univ, Nat.card_eq_fintype_card, ipAt_re, Finset.mul_sum _ _ t]
  refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c _ => ?_) (by positivity)
  rw [pairAt_inv_nat_smul_self]
  have h0 := pairAt_self_nonneg S v hp (φ (S.outSec.rep c))
  have h1 := hA (S.outSec.rep c) (φ (S.outSec.rep c))
  have h2 := inv_nat_le_one ((S.toCSD h).wt c)
  have h3 : (0 : ℝ) ≤ (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ := by positivity
  change (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ ^ 2 * _ ≤ _
  generalize (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ = w at *
  calc _ ≤ w ^ 2 * (t * (S.pairAt v (φ (S.outSec.rep c)) (φ (S.outSec.rep c))).re) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ ≤ w * (t * (S.pairAt v (φ (S.outSec.rep c)) (φ (S.outSec.rep c))).re) :=
        mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
    _ = _ := by ring

end GlobalTheory.ColNorms.SumBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialFreeResolutionsHomotopyEquivalent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem resolution_lift_of_exact {O : Type} [CommRing O] {P A B C : Type}
    [AddCommGroup P] [Module O P] [Module.Projective O P]
    [AddCommGroup A] [Module O A] [AddCommGroup B] [Module O B] [AddCommGroup C] [Module O C]
    {u : A →ₗ[O] B} {v : B →ₗ[O] C} (huv : Function.Exact u v) (w : P →ₗ[O] B)
    (hw : v ∘ₗ w = 0) : ∃ l : P →ₗ[O] A, u ∘ₗ l = w := by
  have hr : ∀ x, w x ∈ LinearMap.range u := fun x => by
    rw [← LinearMap.exact_iff.mp huv, LinearMap.mem_ker]
    exact LinearMap.congr_fun hw x
  obtain ⟨l, hl⟩ := Module.projective_lifting_property u.rangeRestrict (w.codRestrict _ hr)
    u.surjective_rangeRestrict
  refine ⟨l, ?_⟩
  ext x
  have := congrArg Subtype.val (LinearMap.congr_fun hl x)
  simpa using this

theorem resolutions_homotopy_equivalent : ∀ (O : Type) [CommRing O] (N : Type) [AddCommGroup N] [Module O N] (F₀ : Type) [AddCommGroup F₀] [Module O F₀] [Module.Free O F₀] [Module.Finite O F₀] (F₁ : Type) [AddCommGroup F₁] [Module O F₁] [Module.Free O F₁] [Module.Finite O F₁] (F₂ : Type) [AddCommGroup F₂] [Module O F₂] [Module.Free O F₂] [Module.Finite O F₂] (F₃ : Type) [AddCommGroup F₃] [Module O F₃] [Module.Free O F₃] [Module.Finite O F₃] (G₀ : Type) [AddCommGroup G₀] [Module O G₀] [Module.Free O G₀] [Module.Finite O G₀] (G₁ : Type) [AddCommGroup G₁] [Module O G₁] [Module.Free O G₁] [Module.Finite O G₁] (G₂ : Type) [AddCommGroup G₂] [Module O G₂] [Module.Free O G₂] [Module.Finite O G₂] (ε : F₀ →ₗ[O] N) (d₁ : F₁ →ₗ[O] F₀) (d₂ : F₂ →ₗ[O] F₁) (d₃ : F₃ →ₗ[O] F₂) (ν : G₀ →ₗ[O] N) (e₁ : G₁ →ₗ[O] G₀) (e₂ : G₂ →ₗ[O] G₁), Function.Surjective ε → Function.Exact d₁ ε → Function.Exact d₂ d₁ → Function.Exact d₃ d₂ → Function.Surjective ν → Function.Exact e₁ ν → Function.Exact e₂ e₁ → ∃ (a₀ : F₀ →ₗ[O] G₀) (a₁ : F₁ →ₗ[O] G₁) (a₂ : F₂ →ₗ[O] G₂) (b₀ : G₀ →ₗ[O] F₀) (b₁ : G₁ →ₗ[O] F₁) (b₂ : G₂ →ₗ[O] F₂) (h₀ : F₀ →ₗ[O] F₁) (h₁ : F₁ →ₗ[O] F₂) (h₂ : F₂ →ₗ[O] F₃) (k₀ : G₀ →ₗ[O] G₁) (k₁ : G₁ →ₗ[O] G₂), e₁ ∘ₗ a₁ = a₀ ∘ₗ d₁ ∧ e₂ ∘ₗ a₂ = a₁ ∘ₗ d₂ ∧ d₁ ∘ₗ b₁ = b₀ ∘ₗ e₁ ∧ d₂ ∘ₗ b₂ = b₁ ∘ₗ e₂ ∧ LinearMap.id - b₁ ∘ₗ a₁ = d₂ ∘ₗ h₁ + h₀ ∘ₗ d₁ ∧ LinearMap.id - b₂ ∘ₗ a₂ = d₃ ∘ₗ h₂ + h₁ ∘ₗ d₂ ∧ LinearMap.id - a₁ ∘ₗ b₁ = e₂ ∘ₗ k₁ + k₀ ∘ₗ e₁ := by
  intro O _ N _ _ F₀ _ _ _ _ F₁ _ _ _ _ F₂ _ _ _ _ F₃ _ _ _ _ G₀ _ _ _ _ G₁ _ _ _ _ G₂ _ _ _ _
    ε d₁ d₂ d₃ ν e₁ e₂ hε hd1 hd2 hd3 hν he1 he2
  obtain ⟨a₀, ha₀⟩ := Module.projective_lifting_property ν ε hν
  obtain ⟨b₀, hb₀⟩ := Module.projective_lifting_property ε ν hε
  have ha₀' : ∀ x, ν (a₀ x) = ε x := fun x => LinearMap.congr_fun ha₀ x
  have hb₀' : ∀ x, ε (b₀ x) = ν x := fun x => LinearMap.congr_fun hb₀ x
  obtain ⟨a₁, ha₁⟩ := resolution_lift_of_exact he1 (a₀ ∘ₗ d₁) (by
    ext x; simp [ha₀', Function.Exact.apply_apply_eq_zero hd1])
  have ha₁' : ∀ x, e₁ (a₁ x) = a₀ (d₁ x) := fun x => LinearMap.congr_fun ha₁ x
  obtain ⟨a₂, ha₂⟩ := resolution_lift_of_exact he2 (a₁ ∘ₗ d₂) (by
    ext x; simp [ha₁', Function.Exact.apply_apply_eq_zero hd2])
  obtain ⟨b₁, hb₁⟩ := resolution_lift_of_exact hd1 (b₀ ∘ₗ e₁) (by
    ext x; simp [hb₀', Function.Exact.apply_apply_eq_zero he1])
  have hb₁' : ∀ x, d₁ (b₁ x) = b₀ (e₁ x) := fun x => LinearMap.congr_fun hb₁ x
  obtain ⟨b₂, hb₂⟩ := resolution_lift_of_exact hd2 (b₁ ∘ₗ e₂) (by
    ext x; simp [hb₁', Function.Exact.apply_apply_eq_zero he2])
  obtain ⟨h₀, hh₀⟩ := resolution_lift_of_exact hd1 (LinearMap.id - b₀ ∘ₗ a₀) (by
    ext x; simp [hb₀', ha₀'])
  have hh₀' : ∀ x, d₁ (h₀ x) = x - b₀ (a₀ x) := fun x => by
    simpa using LinearMap.congr_fun hh₀ x
  obtain ⟨h₁, hh₁⟩ := resolution_lift_of_exact hd2 (LinearMap.id - b₁ ∘ₗ a₁ - h₀ ∘ₗ d₁) (by
    ext x; simp [hb₁', ha₁', hh₀'])
  have hh₁' : ∀ x, d₂ (h₁ x) = x - b₁ (a₁ x) - h₀ (d₁ x) := fun x => by
    simpa using LinearMap.congr_fun hh₁ x
  obtain ⟨h₂, hh₂⟩ := resolution_lift_of_exact hd3 (LinearMap.id - b₂ ∘ₗ a₂ - h₁ ∘ₗ d₂) (by
    ext x
    have e1 := LinearMap.congr_fun hb₂ (a₂ x)
    have e2 := LinearMap.congr_fun ha₂ x
    simp only [LinearMap.comp_apply] at e1 e2
    simp [hh₁', e1, e2, Function.Exact.apply_apply_eq_zero hd2])
  obtain ⟨k₀, hk₀⟩ := resolution_lift_of_exact he1 (LinearMap.id - a₀ ∘ₗ b₀) (by
    ext x; simp [hb₀', ha₀'])
  have hk₀' : ∀ x, e₁ (k₀ x) = x - a₀ (b₀ x) := fun x => by
    simpa using LinearMap.congr_fun hk₀ x
  obtain ⟨k₁, hk₁⟩ := resolution_lift_of_exact he2 (LinearMap.id - a₁ ∘ₗ b₁ - k₀ ∘ₗ e₁) (by
    ext x; simp [hb₁', ha₁', hk₀'])
  refine ⟨a₀, a₁, a₂, b₀, b₁, b₂, h₀, h₁, h₂, k₀, k₁, ha₁, ha₂, hb₁, hb₂, ?_, ?_, ?_⟩
  · rw [hh₁, sub_add_cancel]
  · rw [hh₂, sub_add_cancel]
  · rw [hk₁, sub_add_cancel]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PchernOf
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer.ChernClause

theorem pchern_of (hsep : ∀ {R : Type} [CommRing R] (A : Over (Sp R)) [GrpObj A], IsAbelianScheme A → A.left.IsSeparated)
 (hcharts : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (u : Unif F s σ), X.IsSeparated → ∀ {N : Type} (𝒰 : N → X.Opens), ⨆ i, 𝒰 i = ⊤ → ∃ (K : Charts F) (r : Real K s σ) (j : K.K → N), K.Rich ∧ (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') ∧ r.IsFor u ∧ ∀ k, ⊤ ≤ r.x k ⁻¹ᵁ 𝒰 (j k))
 (hpull : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X) (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ z : SecondDeRham s, IsChern (dp0 B) s M z → ∃ (i : K.Obj → M.ι) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) ∧ (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) ∧ (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ ((show ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C from ℓ.1) T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) ∧ r.coef.pull2 z = GlobalTheory.CatCoh.H2.mk K.Oc ℓ)
 (hframe : ∀ (A : Over (Sp ℂ)) [GrpObj A] {g : ℕ} (L : LB A.left) (u : HolUnif A L g) (M : LB A.left) (u' : HolUnif A M g), M.IsLB → u'.ex = u.ex → ∀ (H : Matrix (Fin g) (Fin g) ℂ) (χ : u'.Λ → ℂ), u'.IsAH H χ → ∀ (K : Charts (fibFam u)) (r : Real K (A.hom ≫ 𝟙 _) (algebraMap ℂ (Hol (fibFam u).V))), r.IsFor (fibUnif u) → ∀ (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∃ (fr : ∀ k, Hol (K.W k)) (a lg : u.Λ → ∀ k, Hol (K.W k)), (∀ k, IsUnit (fr k)) ∧ (∀ l k' k (h : K.le l k' k) (hh : ⊤ ≤ r.x k' ⁻¹ᵁ (M.U (j k') ⊓ M.U (j k))), fr k' = evalAt (r.x k') (M.U (j k') ⊓ M.U (j k)) hh (M.g (j k') (j k)).val * a l k' * Charts.sh h (fr k)) ∧ (∀ l k, IsUnit (a l k)) ∧ (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) ∧ (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') ∧ (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (algebraMap ℂ (Hol (fibFam u).V) ((Real.pi : ℂ) * ((m : Fin g → ℂ) ⬝ᵥ H.mulVec (star (l : Fin g → ℂ)))))) ∧ (∀ l m k, lg (l + m) k = lg l k + lg m k))
 (hlift : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {B : Type} [CommRing B] {X : Scheme.{0}} {s : X ⟶ Sp B} {σ : B →+* Hol F.V} (K : Charts F) (r : Real K s σ) (M : LB X), M.IsLB → ∀ (j : K.K → M.ι), (∀ k, ⊤ ≤ r.x k ⁻¹ᵁ M.U (j k)) → ∀ (fr : ∀ k, Hol (K.W k)) (a : Λ → ∀ k, Hol (K.W k)), (∀ k, IsUnit (fr k)) → (∀ l k' k (h : K.le l k' k) (hh : ⊤ ≤ r.x k' ⁻¹ᵁ (M.U (j k') ⊓ M.U (j k))), fr k' = evalAt (r.x k') (M.U (j k') ⊓ M.U (j k)) hh (M.g (j k') (j k)).val * a l k' * Charts.sh h (fr k)) → ∀ (i : K.Obj → M.ι), (∀ T, ⊤ ≤ (r.obj T).x ⁻¹ᵁ M.U (i T)) → ∀ (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C), (∀ (T T' : K.Obj) (φ : T ⟶ T') (hh : ⊤ ≤ (r.obj T').x ⁻¹ᵁ (M.U (i T') ⊓ M.U (i T))), Ideal.Quotient.mk T'.J (uu T T' φ) = evalAt (r.obj T').x (M.U (i T') ⊓ M.U (i T)) hh (M.g (i T') (i T)).val) → ∃ e : ∀ T : K.Obj, (T.C)ˣ, (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J))
 (halg : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) (a lg : Λ → ∀ k, Hol (K.W k)) (β : Λ → Λ → Hol F.V), (∀ l k, IsUnit (a l k)) → (∀ l k c, dw c (a l k) = dw c (lg l k) * a l k) → (∀ l m k'' k' (h : K.le m k'' k'), a (l + m) k'' = Charts.sh h (a l k') * a m k'') → (∀ l m k'' k' (h : K.le m k'' k'), Charts.sh h (lg l k') = lg l k'' + K.cst k'' (β l m)) → (∀ l m k, lg (l + m) k = lg l k + lg m k) → ∀ (e : ∀ T : K.Obj, (T.C)ˣ) (uu : ∀ T T' : K.Obj, (T ⟶ T') → T'.C) (ℓ : ∀ T T' T'' : K.Obj, (T ⟶ T') → (T' ⟶ T'') → T''.C), (∀ (T T' : K.Obj) (φ : T ⟶ T'), uu T T' φ * φ.φ (e T : T.C) * T'.ρ (a φ.deg T'.k) - (e T' : T'.C) ∈ T'.J) → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ ∈ T''.J ∧ dpExp T''.δ (ℓ T T' T'' φ ψ) * uu T T'' (φ ≫ ψ) = ψ.φ (uu T T' φ) * uu T' T'' ψ) → ∃ c : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), ℓ T T' T'' φ ψ = (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg))
 (hcup : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F) {n : ℕ} (p q : Fin n → Λ →+ Hol F.V) (ℓ : GlobalTheory.CatCoh.Z2 K.Oc) (c : GlobalTheory.CatCoh.C1 K.Oc) (β : Λ → Λ → Hol F.V), (∑ i, GlobalTheory.CatCoh.cup K.Oc (K.perCl (p i)) (K.perCl (q i))) = GlobalTheory.CatCoh.H2.mk K.Oc ℓ → (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), (show T''.C from ℓ.1 T T' T'' φ ψ) = (show T''.C from GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ) + algebraMap (Hol F.V) T''.C (β φ.deg ψ.deg)) → ∃ c' : GlobalTheory.CatCoh.C1 K.Oc, ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), GlobalTheory.CatCoh.d1 K.Oc c' T T' T'' φ ψ = algebraMap (Hol F.V) (K.Oc.obj T'') (∑ i, p i φ.deg * q i ψ.deg - β φ.deg ψ.deg))
 (hsym : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), (∀ c : GlobalTheory.CatCoh.C1 K.Oc, (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → c T T'' (φ ≫ ψ) = GlobalTheory.CatCoh.mp K.Oc ψ (c T T' φ) + c T' T'' ψ) → ∃ G : GlobalTheory.CatCoh.C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → c T T' φ = GlobalTheory.CatCoh.d0 K.Oc G T T' φ) → (∀ G : GlobalTheory.CatCoh.C0 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → GlobalTheory.CatCoh.mp K.Oc φ (G T) = G T') → ∃ r : Hol F.V, ∀ T, G T = algebraMap (Hol F.V) (K.Oc.obj T) r) → (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') → K.Rich → ∀ (β : Λ →+ Λ →+ Hol F.V) (c : GlobalTheory.CatCoh.C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), GlobalTheory.CatCoh.d1 K.Oc c T T' T'' φ ψ = algebraMap (Hol F.V) (K.Oc.obj T'') (β φ.deg ψ.deg)) → ∀ l m, β l m = β m l)
 (hah : ∀ {g : ℕ} (H : Matrix (Fin g) (Fin g) ℂ), H.IsHermitian → ∀ x y : Fin g → ℂ, (Real.pi : ℂ) * (y ⬝ᵥ H.mulVec (star x)) - Real.pi * (x ⬝ᵥ H.mulVec (star y)) = (((-1 : ℤˣ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) * ((x ⬝ᵥ H.mulVec (star y)).im : ℂ))
 (h1 : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → K.Based → ∀ (h : GlobalTheory.CatCoh.C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → h T T'' (φ ≫ ψ) = ψ.φ (h T T' φ) + h T' T'' ψ) → ∃ G : GlobalTheory.CatCoh.C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → h T T' φ = G T' - φ.φ (G T))
 (h0 : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → ∀ G : GlobalTheory.CatCoh.C0 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → G T' = φ.φ (G T)) → ∃ p : Hol F.V, ∀ T : K.Obj, G T = algebraMap (Hol F.V) T.C p) : PChern (-1) := by
  intro A _ g hA L u P hP M u' hM hex H χ ψ hAH hψ x x'
  obtain ⟨n, a, b, hc, rfl⟩ := hψ
  obtain ⟨K, r, j, hR, hS, hF, hj⟩ := hcharts (fibUnif u) (hsep A hA) M.U hM.cover
  have hB : K.Based := by
    obtain ⟨k, hk⟩ := hR.1 (0, 0) trivial
    exact ⟨k, fun z _ ↦ by rwa [Subsingleton.elim z 0]⟩
  obtain ⟨i, uu, ℓ, hi, huu, hℓ, hz⟩ := hpull K r M j hj _ hc
  obtain ⟨fr, af, lg, f1, f2, a1, a2, a3, a4, a5⟩ := hframe A L u M u' hM hex H χ hAH K r hF j hj
  obtain ⟨e, he⟩ := hlift K r M hM j hj fr af f1 f2 i hi uu huu
  let β : u.Λ → u.Λ → ℂ := fun l m ↦ (Real.pi : ℂ) * ((m : Fin g → ℂ) ⬝ᵥ H.mulVec (star (l : Fin g → ℂ)))
  obtain ⟨c, hcc⟩ := halg K af lg (fun l m ↦ algebraMap ℂ (Hol (fibFam u).V) (β l m)) a1 a2 a3 a4 a5 e uu ℓ.1 he hℓ
  let pr : primDR A → (u.Λ →+ Hol (fibFam u).V) := fun c ↦
    { toFun x := algebraMap ℂ (Hol (fibFam u).V) (P x c)
      map_zero' := by rw [map_zero, LinearMap.zero_apply, map_zero]
      map_add' x y := by rw [map_add, LinearMap.add_apply, map_add] }
  have hpr : ∀ c : primDR A, r.coef.pull1 c.1 = K.perCl (pr c) := fun c ↦ hP c K r hF
  obtain ⟨c', hc'⟩ := hcup K (fun k ↦ pr (a k)) (fun k ↦ pr (b k)) ℓ c
    (fun l m ↦ algebraMap ℂ (Hol (fibFam u).V) (β l m)) (by
      rw [← hz, map_sum]
      exact Finset.sum_congr rfl fun k _ ↦ by rw [GlobalTheory.CatCoh.CoefMap.pullCohomologyTwo_cup, hpr, hpr]) hcc
  let δ : u.Λ → u.Λ → ℂ := fun l m ↦ ∑ k, P l (a k) * P m (b k) - β l m
  have d1 : ∀ l l' m, δ (l + l') m = δ l m + δ l' m := fun l l' m ↦ by
    simp only [δ, β, map_add, LinearMap.add_apply, Submodule.coe_add, star_add, Matrix.mulVec_add, dotProduct_add,
      add_mul, Finset.sum_add_distrib]
    ring
  have d2 : ∀ l m m', δ l (m + m') = δ l m + δ l m' := fun l m m' ↦ by
    simp only [δ, β, map_add, LinearMap.add_apply, Submodule.coe_add, add_dotProduct,
      mul_add, Finset.sum_add_distrib]
    ring
  let β' : u.Λ →+ u.Λ →+ Hol (fibFam u).V := AddMonoidHom.mk'
    (fun l ↦ AddMonoidHom.mk' (fun m ↦ algebraMap ℂ (Hol (fibFam u).V) (δ l m)) fun m m' ↦ by rw [d2, map_add])
    fun l l' ↦ AddMonoidHom.ext fun m ↦ by
      change algebraMap ℂ (Hol (fibFam u).V) (δ (l + l') m) = algebraMap ℂ (Hol (fibFam u).V) (δ l m) + algebraMap ℂ (Hol (fibFam u).V) (δ l' m)
      rw [d1, map_add]
  have hs := hsym K (fun c hc ↦ h1 K hR hB c hc) (fun G hG ↦ h0 K hR G fun T T' φ h ↦ (hG T T' φ h).symm) hS hR β' c'
    (fun T T' T'' φ ψ ↦ by
      rw [hc']
      congr 1
      change _ = algebraMap ℂ (Hol (fibFam u).V) (δ φ.deg ψ.deg)
      simp only [δ, map_sub, map_sum, map_mul]
      rfl) x x'
  have hs' : δ x x' = δ x' x := by
    have := congrArg (Hol.ev (W := (fibFam u).V) 0 trivial) hs
    change Hol.ev (W := (fibFam u).V) 0 trivial (algebraMap ℂ _ (δ x x')) = Hol.ev (W := (fibFam u).V) 0 trivial (algebraMap ℂ _ (δ x' x)) at this
    simpa using this
  rw [wedgeForm_apply, ← hah H hAH.1 x x', Finset.sum_sub_distrib]
  simp only [δ, β] at hs'
  have e2 : ∑ k, P x (b k) * P x' (a k) = ∑ k, P x' (a k) * P x (b k) := Finset.sum_congr rfl fun k _ ↦ mul_comm _ _
  rw [e2]
  linear_combination hs'

theorem pchern : GlobalTheory.AnPer.PChern (-1) :=
  pchern_of @_root_.GlobalTheory.T.abelianScheme_isSeparated_of_affine_base @_root_.GlobalTheory.T.exists_translationClosed_charts_subordinate_to_cover @_root_.GlobalTheory.T.isCrystallineChern_on_analytic_thickenings @_root_.GlobalTheory.T.exists_frame_factorOfAutomorphy_log @_root_.GlobalTheory.T.exists_units_comparing_lifted_transitions_factor @_root_.GlobalTheory.T.log_cocycle_cohomologous_alt @_root_.GlobalTheory.T.cup_period_classes_sum_const @_root_.GlobalTheory.T.const_biadditive_coboundary_symmetric @GlobalTheory.pi_mul_hermitian_alternation @_root_.GlobalTheory.T.degZeroCocycle_exists_coboundary_of_rich_based @_root_.GlobalTheory.T.exists_holomorphic_param_of_degZero_compatible

end GlobalTheory.AnPer.ChernClause
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodHomPushEnd
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AnPer

theorem periodHom_push_end : PEnd := by
  intro A _ g hA L u P hP α _ M hM x x' hx
  have hsep : A.left.IsSeparated := by
    haveI : IsProper A.hom := hA.proper
    refine ⟨?_⟩
    rw [← terminal.comp_from A.hom]
    infer_instance
  have hΛ : ∀ l : u.Λ, M l ∈ u.Λ := fun l ↦ by
    rw [← u.ker, hM, (u.ker _).2 l.2, MonObj.one_comp]
  let N : u.Λ →+ u.Λ :=
    { toFun l := ⟨M l, hΛ l⟩
      map_zero' := Subtype.ext (map_zero M)
      map_add' a b := Subtype.ext (map_add M _ _) }
  obtain rfl : x' = N x := Subtype.ext hx
  refine LinearMap.ext fun c ↦ ?_
  have key := GlobalTheory.T.holomorphicPeriods_natural_along_covered_morphism (fibUnif u) (fibUnif u) hsep hsep id analyticOnNhd_id (fun _ h ↦ h) M N
    (fun _ _ _ ↦ rfl) (RingHom.id ℂ) α.left (homMor (dp0 ℂ) (𝟙 _) α).isMor (fun _ ↦ rfl)
    (fun p _ ↦ (congrArg Over.Hom.left (hM p.2)).symm) c.1 _ _ (hP c)
    (hP (primPull (dp0 ℂ) (𝟙 _) α c)) x
  exact congrArg (fun f : Hol (fibFam u).V ↦ f.1 ⟨0, trivial⟩) key

end GlobalTheory.AnPer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PieriRecursionUnique
section
open scoped Classical

namespace GlobalTheory

theorem pieri_recursion_zero (n : ℕ) (c : ℕ → ℂ) (D : (Fin n → ℕ) → ℂ)
    (hD : ∀ l, ¬ Antitone l → D l = 0)
    (hr : ∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), D (l + (fun i => if i ∈ J then 1 else 0)) = c j * D l)
    (h0 : D 0 = 0) : ∀ μ, D μ = 0 := by
  have main : ∀ s k (μ : Fin n → ℕ), ∑ i, μ i = s →
      n - (Finset.univ.filter (fun i => μ i ≠ 0)).card = k → D μ = 0 := by
    intro s
    refine Nat.strong_induction_on s ?_
    intro s ihs k
    refine Nat.strong_induction_on k ?_
    intro k ihk μ hs hk
    by_cases hμ : Antitone μ
    swap
    · exact hD μ hμ
    by_cases hz : μ = 0
    · subst hz; exact h0
    set J0 : Finset (Fin n) := Finset.univ.filter (fun i => μ i ≠ 0) with hJ0
    set l : Fin n → ℕ := fun i => μ i - 1 with hl
    have hla : Antitone l := fun a b hab => Nat.sub_le_sub_right (hμ hab) 1
    have hj : J0.card ≤ n := by simpa using Finset.card_le_univ J0
    have hlμ : l + (fun i => if i ∈ J0 then 1 else 0) = μ := by
      funext i
      simp only [Pi.add_apply, hl, hJ0, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with h <;> omega
    have hsum : ∀ J : Finset (Fin n),
        ∑ i, ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) i = ∑ i, l i + J.card := by
      intro J
      simp [Finset.sum_add_distrib, Finset.sum_boole]
    have hDl : D l = 0 := by
      have hlt : ∑ i, l i < s := by
        rw [← hs]
        obtain ⟨i, hi⟩ : ∃ i, μ i ≠ 0 := by
          by_contra h
          push_neg at h
          exact hz (funext h)
        exact Finset.sum_lt_sum (fun i _ => Nat.sub_le _ _)
          ⟨i, Finset.mem_univ _, by simp only [hl]; omega⟩
      exact ihs _ hlt _ l rfl rfl
    have hsingle : ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = J0.card),
        D (l + (fun i => if i ∈ J then 1 else 0)) = D (l + (fun i => if i ∈ J0 then 1 else 0)) := by
      refine Finset.sum_eq_single_of_mem J0 (by simp) ?_
      intro J hJ hne
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJ
      set ν : Fin n → ℕ := l + (fun i => if i ∈ J then 1 else 0) with hν
      by_cases hνa : Antitone ν
      swap
      · exact hD ν hνa
      have hnsub : ¬ J ⊆ J0 := fun h => hne (Finset.eq_of_subset_of_card_le h (by omega))
      obtain ⟨i, hiJ, hiJ0⟩ := Finset.not_subset.mp hnsub
      have hμi : μ i = 0 := by simpa [hJ0] using hiJ0
      have hνi : 1 ≤ ν i := by simp [hν, hiJ]
      have hsub : insert i J0 ⊆ Finset.univ.filter (fun k => ν k ≠ 0) := by
        intro k hk
        rw [Finset.mem_insert] at hk
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rcases hk with rfl | hk
        · omega
        · have hk' : μ k ≠ 0 := by simpa [hJ0] using hk
          have hki : k ≤ i := by
            by_contra h
            push_neg at h
            have := hμ h.le
            omega
          have := hνa hki
          omega
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_insert_of_notMem hiJ0] at hcard
      have hcn : (Finset.univ.filter (fun k => ν k ≠ 0)).card ≤ n := by
        simpa using Finset.card_le_univ (Finset.univ.filter (fun k => ν k ≠ 0))
      refine ihk (n - (Finset.univ.filter (fun k => ν k ≠ 0)).card) ?_ ν ?_ rfl
      · omega
      · have h1 := hsum J
        have h2 := hsum J0
        rw [hlμ] at h2
        rw [hν, h1, hJ, ← h2, hs]
    have hrec := hr l hla J0.card hj
    rw [hsingle, hDl, mul_zero, hlμ] at hrec
    exact hrec
  intro μ
  exact main _ _ μ rfl rfl

theorem pieri_recursion_unique : ∀ (n : ℕ) (c : ℕ → ℂ) (V U : (Fin n → ℕ) → ℂ),
    (∀ l, ¬ Antitone l → V l = 0) → (∀ l, ¬ Antitone l → U l = 0) →
    (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), V (l + (fun i => if i ∈ J then 1 else 0)) = c j * V l) →
    (∀ l, Antitone l → ∀ j ≤ n, ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter
      (fun J => J.card = j), U (l + (fun i => if i ∈ J then 1 else 0)) = c j * U l) →
    V 0 = U 0 → V = U := by
  intro n c V U hV hU hrV hrU h0
  have h := pieri_recursion_zero n c (fun l => V l - U l)
    (fun l hl => by simp [hV l hl, hU l hl])
    (fun l hl j hj => by
      simp only [Finset.sum_sub_distrib, hrV l hl j hj, hrU l hl j hj, mul_sub])
    (by simp [h0])
  funext μ
  exact sub_eq_zero.mp (h μ)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSectionsGroupSchemeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullback_sections_group_scheme : ∀ (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k mA : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))), IsBCBasis A L k bA → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) [GrpObj A'] (φA' : A'.left ⟶ A.left) (ψA : A'.left ⟶ (topS Rg ⊗ A).left), IsGrpPullback A' A t φA' → ψA ≫ (snd (topS Rg) A).left = φA' → ∀ (d : Fin mA → Γ(Sp R, ⊤)), (∀ (j : Fin 1 → L.ι) (x : A'.left), x ∈ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j → ∃ (W : A'.left.Opens) (hW : W ≤ LB.wchart L (fun _ : Fin 1 => ψA ≫ (snd (topS Rg) A).left) j), x ∈ W ∧ ∑ i, (A'.hom.appLE ⊤ W (by simp)).hom (d i) * (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) j) W (hW.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ j))).hom ((bA i).f j) = 0) → d = 0 := by
  first | (exact @GlobalTheory.HomFixIndep.pulled_basis_indep) | (exact GlobalTheory.HomFixIndep.pulled_basis_indep) | (intros; apply GlobalTheory.HomFixIndep.pulled_basis_indep  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOnePrescribedReAtIdempotentStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_norm_one_prescribed_re_at_idempotent : ∀ (R : Type) [CommRing R] (a b ε p q : R), ε * ε = ε → IsUnit a → IsUnit b → IsUnit (2 : R) → ε * (b - (p ^ 2 - a * q ^ 2)) = 0 → ∀ t : R, ∃ h : ℍ[R, a, b], nrm h = 1 ∧ ε * h.re = ε * t := by
  first | exact @GlobalTheory.quat_norm_one_re_at_idem | exact GlobalTheory.quat_norm_one_re_at_idem | (intros; apply GlobalTheory.quat_norm_one_re_at_idem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenAdelesStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quaternion_norm_one_trace_open_adeles : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ g : DA F a b, nrm g = 1 → ∀ W : Set (DA F a b), W ∈ 𝓝 g → ∃ O : Set (AF F), IsOpen O ∧ O.Nonempty ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by
  first | exact @GlobalTheory.QSA.traceOpen_adele | exact GlobalTheory.QSA.traceOpen_adele | (intros; apply GlobalTheory.QSA.traceOpen_adele <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightTranslateHarishChandraFiniteFormPropertiesStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rightTranslate_harishChandraFiniteForm_properties : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (L : Subgroup (GL (Fin a) (Af E))) (W : Submodule ℂ (Kinf E a → ℂ)) (X : Set (Module.End ℂ (Sm E a) → ℂ)) (S : Finset (Module.End ℂ (Sm E a) → ℂ)), X ⊆ ↑S → ∀ (N : ℕ), ∀ φ ∈ GlobalTheory.HCF.formsGL E a L W X N, ∀ (t : GL (Fin a) (Af E)) (κ : Kinf E a), (∀ γ g, (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ).1 (ratGL E a γ * g) = (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ).1 g) ∧ IsOpen {k | finRep E a k (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ) = rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ} ∧ ∀ (τ : E →+* ℂ) (u : ℂ), Polynomial.aeval (cap τ u) (∏ χ ∈ S, (Polynomial.X - Polynomial.C (χ (cap τ u))) ^ N) (rt E a (finGL E a t * infGL E a (Unitary.toUnits κ)) φ) = 0 := by
  first | exact @GlobalTheory.HCF.rt_translate_kill | exact GlobalTheory.HCF.rt_translate_kill | (intros; apply GlobalTheory.HCF.rt_translate_kill <;> assumption)
end

