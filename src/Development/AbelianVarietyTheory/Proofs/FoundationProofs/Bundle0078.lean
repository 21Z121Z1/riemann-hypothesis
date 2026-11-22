import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0063
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0064
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0065

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulSqrtNegOddPolynomialIdentity
section
open Polynomial PeriodPair

namespace GlobalTheory

lemma exists_monic_sq_eq_of_mul_eq_sq {D G P : ℂ[X]} (hD : D.Monic) (hc : IsCoprime D G)
    (h : D * G = P ^ 2) : ∃ h : ℂ[X], h.Monic ∧ D = h ^ 2 := by
  obtain ⟨d, hd⟩ := exists_associated_pow_of_mul_eq_pow' hc h
  have hd0 : d ≠ 0 := by
    rintro rfl
    exact hD.ne_zero (by simpa using hd.symm)
  refine ⟨normalize d, monic_normalize hd0, ?_⟩
  refine eq_of_monic_of_associated hD ((monic_normalize hd0).pow 2) ?_
  exact hd.symm.trans ((associated_normalize d).pow_pow)

theorem exists_mul_sqrt_neg_odd_polynomial_identity (L : PeriodPair) (α : ℂ) (m : ℕ)
    (k : Subfield ℂ) (hα2 : α ^ 2 = -(2 * (m : ℂ) + 1))
    (hα : ∀ l ∈ L.lattice, α * l ∈ L.lattice)
    (hind : (L.lattice.toAddSubgroup.map (AddMonoidHom.mulLeft α)).relIndex
      L.lattice.toAddSubgroup = 2 * m + 1)
    (h₂ : L.g₂ ∈ k) (h₃ : L.g₃ ∈ k) (hαk : α ∈ k)
    (hk : ∀ t ∉ L.lattice, α * t ∈ L.lattice → L.weierstrassP t ∈ k) :
    ∃ n h : ℂ[X], n.Monic ∧ h.Monic ∧ n.natDegree = 2 * m + 1 ∧ h.natDegree = m ∧
      IsCoprime n h ∧ (∀ i, n.coeff i ∈ k) ∧
      (∀ x, h.IsRoot x → ∃ t ∉ L.lattice, α * t ∈ L.lattice ∧ L.weierstrassP t = x) ∧
      (X ^ 3 + C (-L.g₂ / 4) * X + C (-L.g₃ / 4)) * (derivative n * h - 2 * n * derivative h) ^ 2 =
        n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * h ^ 4 + C (α ^ 6 * (-L.g₃ / 4)) * h ^ 6 := by
  have hα0 : α ≠ 0 := by
    rintro rfl
    have h0 : ((2 * m + 1 : ℕ) : ℂ) = 0 := by
      push_cast
      linear_combination hα2
    exact absurd (Nat.cast_eq_zero.mp h0) (by omega)
  obtain ⟨A, D, c1, -, c3, c4, c5, c6, c7, c8, c9⟩ :=
    exists_weierstrassP_mul_eq_div hα0 hα k h₂ h₃ hαk hk
  set F : ℂ[X] := X ^ 3 + C (-L.g₂ / 4) * X + C (-L.g₃ / 4) with hF
  set n : ℂ[X] := C (α ^ 2) * A with hn
  have hα20 : α ^ 2 ≠ 0 := pow_ne_zero 2 hα0
  have hFe : ∀ z ∉ L.lattice, F.eval (℘[L] z) = ℘'[L] z ^ 2 / 4 := by
    intro z hz
    rw [L.derivWeierstrassP_sq z hz]
    simp only [hF, eval_add, eval_mul, eval_pow, eval_X, eval_C]
    ring
  have hnD : IsCoprime n D := by
    rw [hn]
    exact (isCoprime_mul_unit_left_left (isUnit_C.mpr (IsUnit.mk0 _ hα20)) A D).mpr c5
  have key : F * (derivative n * D - n * derivative D) ^ 2 =
      D * (n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3) := by
    refine mul_left_cancel₀ c3.ne_zero (Polynomial.funext fun x ↦ ?_)
    obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
    by_cases h0 : D.eval (℘[L] z) = 0
    · simp [h0]
    have hz' := (c8 z hz).not.mp h0
    have e1 := derivWeierstrassP_mul_eq hα c9 hz' h0
    have e2 := L.derivWeierstrassP_sq _ hz'
    rw [c9 z hz'] at e2
    rw [eval_mul, eval_mul, eval_mul (p := D), hFe z hz]
    congr 1
    simp only [hn, derivative_mul, derivative_C, eval_add, eval_mul, eval_pow, eval_sub, eval_C,
      zero_mul, zero_add] at e1 ⊢
    have e3 := congrArg (· ^ 2) e1
    simp only [mul_pow] at e3
    rw [e2] at e3
    field_simp at e3
    field_simp
    linear_combination (-1 : ℂ) * e3
  have hDF : IsCoprime D F := by
    rw [Polynomial.isCoprime_iff_aeval_ne_zero_of_isAlgClosed ℂ ℂ]
    intro x
    obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
    by_contra! hc
    simp only [coe_aeval_eq_eval] at hc
    have h1 := (c8 z hz).mp hc.1
    have h2 : ℘'[L] z = 0 := by
      have := hc.2
      rw [hFe z hz] at this
      simpa using this
    rw [derivWeierstrassP_eq_zero_iff L hz] at h2
    refine hz ?_
    have h3 := sub_mem (neg_mem (hα _ h1)) (nsmul_mem h2 m)
    convert h3 using 1
    rw [nsmul_eq_mul]
    linear_combination z * hα2
  have hDG : IsCoprime D
      (n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3) := by
    have : n ^ 3 + C (α ^ 4 * (-L.g₂ / 4)) * n * D ^ 2 + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 3 =
        n ^ 3 + D * (C (α ^ 4 * (-L.g₂ / 4)) * n * D + C (α ^ 6 * (-L.g₃ / 4)) * D ^ 2) := by ring
    rw [this]
    exact (hnD.symm.pow_right).add_mul_left_right _
  obtain ⟨h, hm, hD⟩ := exists_monic_sq_eq_of_mul_eq_sq c3 (hDG.mul_right hDF)
    (P := F * (derivative n * D - n * derivative D)) (by linear_combination (-F) * key)
  have hdn : n.natDegree = 2 * m + 1 := by rw [hn, natDegree_C_mul hα20, c6, hind]
  refine ⟨n, h, ?_, hm, hdn, ?_, ?_, fun i ↦ ?_, fun x hx ↦ ?_, ?_⟩
  · rw [Monic, hn, leadingCoeff_mul, leadingCoeff_C, c4, mul_inv_cancel₀ hα20]
  · rw [c6, hind, hD, natDegree_pow] at c7
    omega
  · rw [hD] at hnD
    exact (IsCoprime.pow_right_iff (by norm_num)).mp hnD
  · rw [hn, coeff_C_mul]
    exact mul_mem (pow_mem hαk 2) (c1 i)
  · obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
    refine ⟨z, hz, (c8 z hz).mp ?_, rfl⟩
    rw [hD, eval_pow, hx.eq_zero]
    norm_num
  · refine mul_left_cancel₀ (pow_ne_zero 2 hm.ne_zero) ?_
    rw [hD, derivative_sq] at key
    have h2 : (C 2 : ℂ[X]) = 2 := rfl
    rw [h2] at key
    linear_combination key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPlaceOverJLineOfUpperHalfPlanePoint
section
open Matrix GlobalTheory.KZ
open Filter Topology

noncomputable section

namespace GlobalTheory.KZ.ValAt

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem nhdsNE_of_germ_eq {τ : ℂ} (hτ : τ ∈ Hs) {φ ψ : ℂ → ℂ} (h : (φ : Mero) = (ψ : Mero)) :
    φ =ᶠ[𝓝[≠] τ] ψ := by
  rw [Filter.Germ.coe_eq] at h
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h) τ hτ
  have h2 : Hs ∈ 𝓝[≠] τ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hτ)
  filter_upwards [h1, h2] with z hz hz'
  rcases hz with hz | hz
  · exact hz
  · exact absurd hz' hz

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ValAt.exists_rep (g : _root_.GlobalTheory.KZ.Mero) :
    ∃ φ : ℂ → ℂ, g = (φ : _root_.GlobalTheory.KZ.Mero) := by
  obtain ⟨φ, hφ⟩ := Quot.exists_rep g
  exact ⟨φ, hφ.symm⟩

def rep (X : Tower Ω ε) (x : X.K) : ℂ → ℂ := (exists_rep (X.an x)).choose

theorem rep_spec (X : Tower Ω ε) (x : X.K) : X.an x = (rep X x : Mero) := (exists_rep (X.an x)).choose_spec

def ord (X : Tower Ω ε) (τ : ℂ) (x : X.K) : WithTop ℤ := meromorphicOrderAt (rep X x) τ

theorem ord_eq (X : Tower Ω ε) {τ : ℂ} (hτ : τ ∈ Hs) {x : X.K} {φ : ℂ → ℂ} (h : X.an x = (φ : Mero)) :
    ord X τ x = meromorphicOrderAt φ τ :=
  meromorphicOrderAt_congr (nhdsNE_of_germ_eq hτ ((rep_spec X x).symm.trans h))

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private theorem an_eq_germ_rep (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (x : X.K) :
    X.an x = (_root_.GlobalTheory.KZ.ValAt.rep X x : _root_.GlobalTheory.KZ.Mero) :=
  (_root_.GlobalTheory.KZ.ValAt.exists_rep (X.an x)).choose_spec

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private theorem isOpen_upperHalfPlaneSet' : IsOpen _root_.GlobalTheory.KZ.Hs := by
  unfold _root_.GlobalTheory.KZ.Hs
  exact isOpen_lt continuous_const Complex.continuous_im

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private theorem eventuallyEq_nhdsNE_of_mero_coe_eq {φ ψ : ℂ → ℂ}
    (h : (φ : _root_.GlobalTheory.KZ.Mero) = ψ) {τ : ℂ} (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) :
    φ =ᶠ[𝓝[≠] τ] ψ := by
  have h' := (Filter.Germ.coe_eq.1 h : φ =ᶠ[codiscreteWithin _root_.GlobalTheory.KZ.Hs] ψ)
  rw [Filter.EventuallyEq, Filter.Eventually, mem_codiscreteWithin] at h'
  have hd := h' τ hτ
  rw [Filter.disjoint_principal_right] at hd
  filter_upwards [hd, nhdsWithin_le_nhds (isOpen_upperHalfPlaneSet'.mem_nhds hτ)] with z h1 h2
  by_contra hne
  exact h1 ⟨h2, hne⟩

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private theorem ord_eq_meromorphicOrderAt_of_an_eq_coe {φ : ℂ → ℂ} (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (x : X.K) (h : X.an x = (φ : _root_.GlobalTheory.KZ.Mero)) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) :
    _root_.GlobalTheory.KZ.ValAt.ord X τ x = meromorphicOrderAt φ τ := by
  unfold _root_.GlobalTheory.KZ.ValAt.ord
  rw [an_eq_germ_rep] at h
  exact meromorphicOrderAt_congr (eventuallyEq_nhdsNE_of_mero_coe_eq h hτ)

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private theorem isPreconnected_upperHalfPlaneSet : IsPreconnected _root_.GlobalTheory.KZ.Hs := by
  unfold _root_.GlobalTheory.KZ.Hs
  exact (convex_halfSpace_im_gt 0).isPreconnected

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private theorem eventually_ne_zero_nhdsNE_of_mero_coe_ne_zero {b : ℂ → ℂ}
    (hb : DifferentiableOn ℂ b _root_.GlobalTheory.KZ.Hs)
    (hb0 : (b : _root_.GlobalTheory.KZ.Mero) ≠ 0) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) : ∀ᶠ z in 𝓝[≠] τ, b z ≠ 0 := by
  have ha := hb.analyticOnNhd isOpen_upperHalfPlaneSet'
  rcases (ha τ hτ).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    apply hb0
    have hz := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_upperHalfPlaneSet hτ h
    rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
    exact Filter.eventually_of_mem (self_mem_codiscreteWithin _) hz
  · exact h

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private theorem exists_differentiableOn_rep_eventuallyEq_div (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (x : X.K) {τ : ℂ} (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) :
    ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a _root_.GlobalTheory.KZ.Hs ∧
      DifferentiableOn ℂ b _root_.GlobalTheory.KZ.Hs ∧
      _root_.GlobalTheory.KZ.ValAt.rep X x =ᶠ[𝓝[≠] τ] a / b := by
  obtain ⟨a, b, ha, hb, hb0, hab⟩ := X.an_mero x
  refine ⟨a, b, ha, hb, ?_⟩
  rw [an_eq_germ_rep, ← Filter.Germ.coe_mul] at hab
  filter_upwards [eventuallyEq_nhdsNE_of_mero_coe_eq hab hτ, eventually_ne_zero_nhdsNE_of_mero_coe_ne_zero hb hb0 hτ]
    with z h1 h2
  rw [Pi.div_apply, eq_div_iff h2]
  exact h1

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
private theorem meromorphicAt_rep_of_mem_upperHalfPlaneSet (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    (x : X.K) {τ : ℂ} (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) :
    MeromorphicAt (_root_.GlobalTheory.KZ.ValAt.rep X x) τ := by
  obtain ⟨a, b, ha, hb, h⟩ := exists_differentiableOn_rep_eventuallyEq_div X x hτ
  have ha' := (ha.analyticOnNhd isOpen_upperHalfPlaneSet' τ hτ).meromorphicAt
  have hb' := (hb.analyticOnNhd isOpen_upperHalfPlaneSet' τ hτ).meromorphicAt
  exact (ha'.div hb').congr h.symm

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ValAt.ord_mul (X : _root_.GlobalTheory.KZ.Tower Ω ε) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) (x y : X.K) :
    _root_.GlobalTheory.KZ.ValAt.ord X τ (x * y) =
      _root_.GlobalTheory.KZ.ValAt.ord X τ x + _root_.GlobalTheory.KZ.ValAt.ord X τ y := by
  rw [ord_eq_meromorphicOrderAt_of_an_eq_coe X (x * y)
    (φ := _root_.GlobalTheory.KZ.ValAt.rep X x * _root_.GlobalTheory.KZ.ValAt.rep X y) ?_ hτ]
  · exact meromorphicOrderAt_mul (meromorphicAt_rep_of_mem_upperHalfPlaneSet X x hτ)
      (meromorphicAt_rep_of_mem_upperHalfPlaneSet X y hτ)
  · rw [map_mul, Filter.Germ.coe_mul, ← an_eq_germ_rep,
      ← an_eq_germ_rep]

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ValAt.ord_add (X : _root_.GlobalTheory.KZ.Tower Ω ε) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) (x y : X.K) :
    min (_root_.GlobalTheory.KZ.ValAt.ord X τ x) (_root_.GlobalTheory.KZ.ValAt.ord X τ y) ≤
      _root_.GlobalTheory.KZ.ValAt.ord X τ (x + y) := by
  rw [ord_eq_meromorphicOrderAt_of_an_eq_coe X (x + y)
    (φ := _root_.GlobalTheory.KZ.ValAt.rep X x + _root_.GlobalTheory.KZ.ValAt.rep X y) ?_ hτ]
  · exact meromorphicOrderAt_add (meromorphicAt_rep_of_mem_upperHalfPlaneSet X x hτ)
      (meromorphicAt_rep_of_mem_upperHalfPlaneSet X y hτ)
  · rw [map_add, Filter.Germ.coe_add, ← an_eq_germ_rep,
      ← an_eq_germ_rep]

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ValAt.ord_const (X : _root_.GlobalTheory.KZ.Tower Ω ε)
    {τ : ℂ} (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) (c : Ω) :
    0 ≤ _root_.GlobalTheory.KZ.ValAt.ord X τ (algebraMap Ω X.K c) := by
  rw [ord_eq_meromorphicOrderAt_of_an_eq_coe X _ (X.an_c c) hτ]
  exact analyticAt_const.meromorphicOrderAt_nonneg

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ValAt.ord_one (X : _root_.GlobalTheory.KZ.Tower Ω ε) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) : _root_.GlobalTheory.KZ.ValAt.ord X τ 1 = 0 := by
  classical
  rw [ord_eq_meromorphicOrderAt_of_an_eq_coe X 1 (φ := fun _ => 1) (by rw [map_one]; rfl) hτ,
    meromorphicOrderAt_const]
  simp

open Matrix in
open Filter Topology in
variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} in
theorem _root_.GlobalTheory.KZ.ValAt.ord_add_ord_inv (X : _root_.GlobalTheory.KZ.Tower Ω ε) {τ : ℂ}
    (hτ : τ ∈ _root_.GlobalTheory.KZ.Hs) {x : X.K} (hx : x ≠ 0) :
    _root_.GlobalTheory.KZ.ValAt.ord X τ x + _root_.GlobalTheory.KZ.ValAt.ord X τ x⁻¹ = 0 := by
  rw [← _root_.GlobalTheory.KZ.ValAt.ord_mul X hτ, mul_inv_cancel₀ hx,
    _root_.GlobalTheory.KZ.ValAt.ord_one X hτ]

def place (X : Tower Ω ε) {τ : ℂ} (hτ : τ ∈ Hs) : ValuationSubring X.K where
  carrier := {x | 0 ≤ ord X τ x}
  mul_mem' {x y} hx hy := by
    show 0 ≤ ord X τ (x * y)
    rw [ord_mul X hτ]
    exact add_nonneg hx hy
  one_mem' := (ord_one X hτ).ge
  add_mem' {x y} hx hy := (le_min hx hy).trans (ord_add X hτ x y)
  zero_mem' := by simpa using ord_const X hτ 0
  neg_mem' {x} hx := by
    show 0 ≤ ord X τ (-x)
    have h := ord_const X hτ (-1)
    rw [map_neg, map_one] at h
    rw [← neg_one_mul, ord_mul X hτ]
    exact add_nonneg h hx
  mem_or_inv_mem' x := by
    by_cases hx : x = 0
    · left
      subst hx
      show 0 ≤ ord X τ 0
      simpa using ord_const X hτ 0
    · by_contra hc
      rw [not_or] at hc
      have h1 : ord X τ x < 0 := not_le.1 hc.1
      have h2 : ord X τ x⁻¹ < 0 := not_le.1 hc.2
      have h3 := ord_add_ord_inv X hτ hx
      have h4 : ord X τ x + ord X τ x⁻¹ ≤ ord X τ x + 0 := by gcongr
      rw [h3, add_zero] at h4
      exact absurd h1 (not_lt.2 h4)

theorem mem_place (X : Tower Ω ε) {τ : ℂ} (hτ : τ ∈ Hs) (x : X.K) : x ∈ place X hτ ↔ 0 ≤ ord X τ x := Iff.rfl

theorem exists_place {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (τ : ℂ) (hτ : τ ∈ Hs) :
    ∃ W : ValuationSubring X.K, X.OverY W ∧ ∀ x : X.K, W.valuation x = 1 →
      ∀ φ : ℂ → ℂ, X.an x = (φ : Mero) → meromorphicOrderAt φ τ = 0 := by
  refine ⟨place X hτ, ⟨fun c => ord_const X hτ c, ?_⟩, fun x hx φ hφ => ?_⟩
  · obtain ⟨φ, h, hφ⟩ := X.j_hol
    rw [mem_place, ord_eq X hτ h]
    exact (hφ.analyticOnNhd isOpen_Hs τ hτ).meromorphicOrderAt_nonneg
  · have h0 : x ≠ 0 := by
      rintro rfl
      simp at hx
    have h1 : 0 ≤ ord X τ x := (mem_place X hτ x).1 (((place X hτ).valuation_le_one_iff x).1 hx.le)
    have h2 : 0 ≤ ord X τ x⁻¹ := (mem_place X hτ _).1 (((place X hτ).valuation_le_one_iff _).1
      (by rw [map_inv₀, hx, inv_one]))
    have h3 := ord_add_ord_inv X hτ h0
    rw [← ord_eq X hτ hφ]
    refine le_antisymm ?_ h1
    calc ord X τ x = ord X τ x + 0 := (add_zero _).symm
      _ ≤ ord X τ x + ord X τ x⁻¹ := by gcongr
      _ = 0 := h3

end GlobalTheory.KZ.ValAt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQRootPolyOfFixedGeometricStabilizerStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (N : ℕ) (y : Ω), (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g y = y) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) ∧
    y = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
  first | exact @GlobalTheory.K5.span_fixed_ggeo_stab | exact GlobalTheory.K5.span_fixed_ggeo_stab | (intros; apply GlobalTheory.K5.span_fixed_ggeo_stab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsQRootPolyOfFixedGeometricStabilizerTauStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_qRoot_poly_of_fixed_geometric_stabilizer_tau : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ (N : ℕ) (z : Ω), (∀ g ∈ Ggeo p Ω ⊓ MulAction.stabilizer (Gal p Ω) (T.qq N), g z = z) →
  ∃ c : ℕ → Ω, (∀ j, ∀ g ∈ Ggeo p Ω, g (c j) = c j) ∧ z = ∑ j ∈ Finset.range (p ^ N), c j * T.qq N ^ j := by
  first | exact @GlobalTheory.K5.Span.span | exact GlobalTheory.K5.Span.span | (intros; apply GlobalTheory.K5.Span.span <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRootOfUnityCloseOfPowReducesOne
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory

open Polynomial

theorem exists_root_of_unity_close_of_pow_close : ∀ {Ω K : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] [Field K]
    [Algebra Ω K] (W : ValuationSubring K) (x : K) (N : ℕ), 0 < N → W.valuation (x ^ N - 1) < 1 →
    ∃ ζ : Ω, ζ ^ N = 1 ∧ W.valuation (x - algebraMap Ω K ζ) < 1 := by
  intro Ω K _ _ _ _ _ W x N hN hv
  classical
  set p : Polynomial Ω := X ^ N - C 1 with hp
  have hm : p.Monic := monic_X_pow_sub_C 1 hN.ne'
  have hs := (IsAlgClosed.splits p).eq_prod_roots_of_monic hm
  have hx : x ^ N - 1 = (p.roots.map (fun a => x - algebraMap Ω K a)).prod := by
    have := congrArg (Polynomial.aeval x) hs
    simpa [p, map_multiset_prod, Multiset.map_map, Function.comp_def] using this
  by_contra hcon
  push_neg at hcon
  refine (not_lt.mpr ?_) hv
  rw [hx, map_multiset_prod, Multiset.map_map]
  refine Multiset.one_le_prod_of_one_le ?_
  intro y hy
  obtain ⟨a, ha, rfl⟩ := Multiset.mem_map.mp hy
  have ha' : a ^ N = 1 := by
    have := (mem_roots hm.ne_zero).mp ha
    simpa [p, sub_eq_zero] using this
  exact hcon a ha'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSubringNoMonicFactorisationSpecialisationStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_subring_no_monic_factorisation_specialisation : ∀ {F : Type} [Field F] [IsAlgClosed F] (Φ : Polynomial (Polynomial F)), Φ.Monic → Irreducible Φ → ∃ s : Finset F, ∃ Ψ : Polynomial (Polynomial (Subring.closure (s : Set F))), Ψ.map (Polynomial.mapRingHom (Subring.closure (s : Set F)).subtype) = Φ ∧ ∀ (k : Type) [Field k] (φ : Subring.closure (s : Set F) →+* k) (A B : Polynomial (Polynomial k)), A.Monic → B.Monic → A * B = Ψ.map (Polynomial.mapRingHom φ) → A.natDegree = 0 ∨ B.natDegree = 0 := by
  first | exact @GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation | exact GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation | (intros; apply GlobalTheory.FactorCertificate.exists_subring_no_monic_factorisation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTendstoSlashEvaluationMatrixMulStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tendsto_slashEvaluationMatrix_mul : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → IsReps Γ s → (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) → (leadM M s w F).det ≠ 0 → ∃ U : ℍ → Matrix (Fin r) (Fin r) ℂ, Tendsto (fun τ => evM s w F τ * U τ) atImInfty (𝓝 (leadM M s w F)) ∧ Tendsto (fun τ => ModularForm.discriminant τ • U τ) atImInfty (𝓝 0) := by
  first | exact @GlobalTheory.OddFrame.exists_tendsto_evM_mul | exact GlobalTheory.OddFrame.exists_tendsto_evM_mul | (intros; apply GlobalTheory.OddFrame.exists_tendsto_evM_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpUpperInt
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ

theorem Tower.exp_upper_int {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (a b d : ℤ)
    (ha : 0 < a) (hd : 0 < d) (f : X.K) (r : ℚ) :
    (X.exp (X.sl (toGQ !![a, b; 0, d]) f)).coeff (r * a / d) = eOm ε (r * b / d) * (X.exp f).coeff r := by
  have hdet : (0 : ℤ) < (!![a, b; 0, d] : Matrix (Fin 2) (Fin 2) ℤ).det := by
    simp [Matrix.det_fin_two]; positivity
  have e : ∀ i j, ent (toGQ !![a, b; 0, d]) i j = ((!![a, b; 0, d] : Matrix (Fin 2) (Fin 2) ℤ) i j : ℚ) := by
    intro i j; rw [ent, toGQ, dif_pos hdet]; rfl
  have h := X.exp_upper (toGQ !![a, b; 0, d]) (by rw [e]; simp) f r
  simpa [e] using h

end GlobalTheory.KZ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FactorialLeTwoMulCardPermWithFixedPointStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.factorial_le_two_mul_card_perm_with_fixedPoint : ∀ (α : Type) [Fintype α] [DecidableEq α], Nonempty α → (Fintype.card α).factorial ≤ 2 * (Finset.univ.filter fun σ : Equiv.Perm α => ∃ i, σ i = i).card := by
  first | exact @GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed | exact GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed | (intros; apply GlobalTheory.BadShare.factorial_le_two_mul_card_perm_fixed <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalOfGammaLeStatement
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_modularForm_cuspForm_of_gamma_le : ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ → FiniteDimensional ℂ (ModularForm Γ k) ∧ FiniteDimensional ℂ (CuspForm Γ k) := by
  first | exact @GlobalTheory.OddFrame.finiteDimensional_of_Gamma_le | exact GlobalTheory.OddFrame.finiteDimensional_of_Gamma_le | (intros; apply GlobalTheory.OddFrame.finiteDimensional_of_Gamma_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FixedFieldAlmostEtaleOfMovesIntegersStatement
section
open GlobalTheory.AlmostEt
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fixedFieldAlmostEtale_of_moves_integers : ∀ (L : Type) [Field L] (v : Valuation L ℝ≥0) (G : Type) [Group G] [MulSemiringAction G L], (∀ (g : G) (x : L), v (g • x) = v x) → ∀ N : Subgroup G, N.Normal → N.FiniteIndex → (∀ σ : G, σ ∉ N → Moves v (Fix L N) σ) → AlmostSep v N := by
  first | exact @GlobalTheory.AlmostEt.almostSep_of_moves | exact GlobalTheory.AlmostEt.almostSep_of_moves | (intros; apply GlobalTheory.AlmostEt.almostSep_of_moves <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricGaloisDenseTauPowMulFixingQRootsStatement
section
open GlobalTheory.K5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometricGalois_dense_tau_pow_mul_fixing_qRoots : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
  ∀ (T : Tower p Ω) (τ : Gal p Ω), τ ∈ Ggeo p Ω → (∀ n, τ (T.qq n) = T.ζ n * T.qq n) →
  ∀ g ∈ Ggeo p Ω, ∀ S : Finset Ω, ∃ s : ℕ, ∃ h ∈ Ggeo p Ω ⊓ ⨅ n, Gn T n, ∀ x ∈ S, (τ ^ s * h) x = g x := by
  first | exact @GlobalTheory.K5.Dense.dense_tau_pow_mul | exact GlobalTheory.K5.Dense.dense_tau_pow_mul | (intros; apply GlobalTheory.K5.Dense.dense_tau_pow_mul <;> assumption)
end

