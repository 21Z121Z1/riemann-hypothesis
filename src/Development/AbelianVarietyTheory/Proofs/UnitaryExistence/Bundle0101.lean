import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.CoefficientSpaceWeights
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaLetterEquivConjugate
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeneralLinearGroupCharEqOneOfDetEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteNotIsUnitOneAddSmul
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.UnFree
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIdempotentSectionFamily
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0099
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0041
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0023
import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0030
import Development.AbelianVarietyTheory.Proofs.HeightProofs.NoCommonZeroIffOfSec
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.AdelicNormWeight
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0028
import Development.AbelianVarietyTheory.Counterexamples.LevelGroupExamples.ZeroNotAdmissibleOfRankPos
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0100
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.Bundle0001
import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.EqZeroOfMul
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LFCompare
open Polynomial

section Rat
variable (K : Type) [Field K] [CharZero K]

def ratFn : Subalgebra K (ℚ → K) where
  carrier := {f | ∃ p q : K[X], (∀ s : ℚ, q.eval (s : K) ≠ 0) ∧ ∀ s : ℚ, f s * q.eval (s : K) = p.eval (s : K)}
  mul_mem' := by
    rintro f g ⟨p, q, hq, h⟩ ⟨p', q', hq', h'⟩
    refine ⟨p * p', q * q', fun s => by rw [eval_mul]; exact mul_ne_zero (hq s) (hq' s), fun s => ?_⟩
    rw [eval_mul, eval_mul, ← h, ← h', Pi.mul_apply]; ring
  add_mem' := by
    rintro f g ⟨p, q, hq, h⟩ ⟨p', q', hq', h'⟩
    refine ⟨p * q' + p' * q, q * q', fun s => by rw [eval_mul]; exact mul_ne_zero (hq s) (hq' s), fun s => ?_⟩
    rw [eval_add, eval_mul, eval_mul, eval_mul, ← h, ← h', Pi.add_apply]; ring
  algebraMap_mem' a := ⟨C a, 1, fun s => by simp, fun s => by simp⟩

variable {K}

theorem const_mem (a : K) : (fun _ : ℚ => a) ∈ ratFn K := (ratFn K).algebraMap_mem a

theorem cast_mem : (fun s : ℚ => (s : K)) ∈ ratFn K := ⟨X, 1, fun s => by simp, fun s => by simp⟩

theorem inv_mem {f : ℚ → K} (hf : f ∈ ratFn K) (h0 : ∀ s, f s ≠ 0) : (fun s => (f s)⁻¹) ∈ ratFn K := by
  obtain ⟨p, q, hq, h⟩ := hf
  refine ⟨q, p, fun s => by rw [← h]; exact mul_ne_zero (h0 s) (hq s), fun s => ?_⟩
  rw [← h, ← mul_assoc, inv_mul_cancel₀ (h0 s), one_mul]

theorem zpow_mem {f : ℚ → K} (hf : f ∈ ratFn K) (h0 : ∀ s, f s ≠ 0) (e : ℤ) : (fun s => f s ^ e) ∈ ratFn K := by
  obtain ⟨m, rfl | rfl⟩ := e.eq_nat_or_neg
  · simp only [zpow_natCast]
    exact pow_mem hf m
  · simp only [zpow_neg, zpow_natCast, ← inv_pow]
    exact pow_mem (inv_mem hf h0) m

theorem eq_zero_of_mul {f g : ℚ → K} (hf : f ∈ ratFn K) (hg : g ∈ ratFn K) (h : ∀ s, f s * g s = 0) {s₀ : ℚ}
    (h0 : g s₀ ≠ 0) (s : ℚ) : f s = 0 := by
  obtain ⟨p, q, hq, hp⟩ := hf
  obtain ⟨p', q', hq', hp'⟩ := hg
  have hpp : p * p' = 0 := by
    refine Polynomial.eq_zero_of_infinite_isRoot _
      ((Set.infinite_range_of_injective (Rat.cast_injective (α := K))).mono ?_)
    rintro _ ⟨t, rfl⟩
    change eval _ _ = 0
    rw [eval_mul, ← hp, ← hp']
    linear_combination (eval (t : K) q * eval (t : K) q') * h t
  have hp0 : p' ≠ 0 := by
    rintro rfl
    exact mul_ne_zero h0 (hq' s₀) (by simpa using hp' s₀)
  have : p = 0 := (mul_eq_zero.1 hpp).resolve_right hp0
  subst this
  exact (mul_eq_zero.1 (by simpa using hp s)).resolve_right (hq s)

theorem scalar_eq {c v f₀ g₀ f₁ g₁ : ℚ → K} {N : ℕ} (hN : N ≠ 0) (hv : v ∈ ratFn K) (hf₀ : f₀ ∈ ratFn K)
    (hg₀ : g₀ ∈ ratFn K) (hf₁ : f₁ ∈ ratFn K) (hg₁ : g₁ ∈ ratFn K) (e₀ : ∀ s, f₀ s = c s * g₀ s)
    (e₁ : ∀ s, f₁ s = c s * g₁ s) (hpow : ∀ s, c s ^ N = v s ^ N) (h0 : c 0 = v 0) (hv0 : v 0 ≠ 0)
    (hg0 : g₀ 0 ≠ 0) (hg1 : g₁ 1 ≠ 0) : c 1 = v 1 := by
  have hvg : (fun s => v s * g₀ s) ∈ ratFn K := mul_mem hv hg₀
  have hS : (fun s => ∑ i ∈ Finset.range N, f₀ s ^ i * (v s * g₀ s) ^ (N - 1 - i)) ∈ ratFn K := by
    have := Subalgebra.sum_mem (ratFn K) (t := Finset.range N)
      (f := fun i => f₀ ^ i * (fun s => v s * g₀ s) ^ (N - 1 - i))
      fun i _ => mul_mem (pow_mem hf₀ i) (pow_mem hvg _)
    convert this using 1
    funext s
    simp
  have a₀ : ∀ s, f₀ s - v s * g₀ s = 0 := by
    refine eq_zero_of_mul (s₀ := 0) (sub_mem hf₀ hvg) hS (fun s => ?_) ?_
    · rw [mul_comm]
      refine (geom_sum₂_mul _ _ _).trans ?_
      rw [e₀, mul_pow, mul_pow, hpow, sub_self]
    · have : f₀ 0 = v 0 * g₀ 0 := by rw [e₀, h0]
      simp only [this]
      rw [geom_sum₂_self]
      exact mul_ne_zero (Nat.cast_ne_zero.2 hN) (pow_ne_zero _ (mul_ne_zero hv0 hg0))
  have a₁ : f₁ 1 - v 1 * g₁ 1 = 0 := by
    refine eq_zero_of_mul (s₀ := 0) (f := fun s => f₁ s - v s * g₁ s) (sub_mem hf₁ (mul_mem hv hg₁)) hg₀
      (fun s => ?_) hg0 1
    have := a₀ s
    rw [e₀] at this
    rw [e₁]
    linear_combination g₁ s * this
  rw [e₁] at a₁
  exact mul_right_cancel₀ hg1 (sub_eq_zero.1 a₁)

theorem det_mem {n : Type} [Fintype n] [DecidableEq n] {M : ℚ → Matrix n n K}
    (h : ∀ i j, (fun s => M s i j) ∈ ratFn K) : (fun s => (M s).det) ∈ ratFn K := by
  have := Subalgebra.sum_mem (ratFn K) (t := Finset.univ)
    (f := fun σ : Equiv.Perm n => (fun _ : ℚ => ((Equiv.Perm.sign σ : ℤ) : K)) * ∏ i, fun s => M s (σ i) i)
    fun σ _ => mul_mem (const_mem _) (Subalgebra.prod_mem _ fun i _ => h _ _)
  convert this using 1
  funext s
  simp [Matrix.det_apply']

theorem matInv_mem {n : Type} [Fintype n] [DecidableEq n] {M : ℚ → Matrix n n K}
    (h : ∀ i j, (fun s => M s i j) ∈ ratFn K) (h0 : ∀ s, (M s).det ≠ 0) (i j : n) :
    (fun s => (M s)⁻¹ i j) ∈ ratFn K := by
  have h1 : (fun s => (M s).adjugate i j) ∈ ratFn K := by
    simp only [Matrix.adjugate_apply]
    refine det_mem fun a b => ?_
    by_cases hab : a = j
    · subst hab
      simpa using const_mem _
    · simpa [Matrix.updateRow_ne hab] using h a b
  have := mul_mem (inv_mem (det_mem h) h0) h1
  convert this using 1
  funext s
  simp [Matrix.inv_def]

theorem aeval_mem {σ σ' ι : Type} [Fintype ι] (r : ℚ → σ → ι → K) (y : σ → ι → σ')
    (hr : ∀ x j, (fun s => r s x j) ∈ ratFn K) (P : MvPolynomial σ K) (ℓ : MvPolynomial σ' K →ₗ[K] K) :
    (fun s => ℓ (MvPolynomial.aeval (fun x => ∑ j, MvPolynomial.C (r s x j) * MvPolynomial.X (y x j)) P)) ∈
      ratFn K := by
  induction P using MvPolynomial.induction_on generalizing ℓ with
  | C a => simpa using const_mem _
  | add p q hp hq =>
    simp only [map_add]
    exact add_mem (hp ℓ) (hq ℓ)
  | mul_X p x hp =>
    have := Subalgebra.sum_mem (ratFn K) (t := Finset.univ) fun j _ =>
      mul_mem (hr x j) (hp (ℓ ∘ₗ LinearMap.mulRight K (MvPolynomial.X (y x j))))
    convert this using 1
    funext s
    simp only [map_mul, MvPolynomial.aeval_X, Finset.mul_sum, map_sum, Finset.sum_apply, Pi.mul_apply,
      LinearMap.comp_apply, LinearMap.mulRight_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_left_comm, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]

end Rat

theorem tele {M : Type} [CommMonoid M] (x : ℕ → M) (ν : ℕ → ℕ) (hν : Antitone ν) (m : ℕ) :
    (∏ i ∈ Finset.range m, (∏ b ∈ Finset.range (i + 1), x b) ^ (ν i - ν (i + 1))) *
      (∏ b ∈ Finset.range m, x b) ^ ν m = ∏ b ∈ Finset.range m, x b ^ ν b := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ, mul_assoc, ← pow_add, Nat.sub_add_cancel (hν (Nat.le_succ m)),
      Finset.prod_range_succ x, mul_pow, ← mul_assoc, ih, Finset.prod_range_succ]

theorem char_eq_one {F A n : Type} [Field F] [CharZero F] [CommGroup A] [Fintype n] [DecidableEq n]
    (ψ : GL n F →* A) (g : GL n F) (hg : (g : Matrix n n F).det = 1) : ψ g = 1 := by
  obtain ⟨L, L', D, hD, hM⟩ :=
    Matrix.SpecialLinearGroup.exists_list_transvec_mul_diagonal_mul_list_transvec ⟨(g : Matrix n n F), hg⟩
  let χ := ψ.comp (Matrix.SpecialLinearGroup.toGL (n := n) (R := F))
  have ht : ∀ t : Matrix.TransvectionStruct n F, χ t.toSpecialLinearGroup = 1 := by
    rintro ⟨i, j, hij, a⟩
    have hN : Matrix.single i j a * Matrix.single i j a = 0 := Matrix.single_mul_single_of_ne _ _ _ _ hij.symm _
    have := ddChar_unip_eq_one ψ _ hN (ddCharDiag (Pi.mulSingle i (Units.mk0 2 two_ne_zero))) 2 1
      (by
        ext a b
        by_cases h : i = a
        · subst h; simp [ddCharDiag_val]
        · simp [ddCharDiag_val, Matrix.single_apply, h])
      (by
        ext a b
        by_cases h : j = b
        · subst h; simp [ddCharDiag_val, Pi.mulSingle_eq_of_ne hij.symm]
        · simp [ddCharDiag_val, Matrix.single_apply, h])
      (by norm_num)
    rw [← this]
    exact congrArg ψ (Units.ext rfl)
  have hl : ∀ L : List (Matrix.TransvectionStruct n F),
      χ (L.map Matrix.TransvectionStruct.toSpecialLinearGroup).prod = 1 := fun L => by
    induction L with
    | nil => simp
    | cons t L ih => rw [List.map_cons, List.prod_cons, map_mul, ht, ih, one_mul]
  have hd : χ ⟨Matrix.diagonal D, hD⟩ = 1 :=
    ddChar_diag ψ _ (fun i j h => Matrix.diagonal_apply_ne D h) hD
  have := (congrArg χ hM).trans ((map_mul χ _ _).trans (congrArg₂ (· * ·) ((map_mul χ _ _).trans
    (congrArg₂ (· * ·) (hl L) hd)) (hl L')))
  have e : ψ g = χ ⟨(g : Matrix n n F), hg⟩ := congrArg ψ (Units.ext rfl)
  exact e.trans (this.trans (by simp))

section Cayley

open scoped Matrix

variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E] {n : ℕ}

theorem exists_curve (K : Type) [Field K] [CharZero K] (γ : Matrix (Fin n) (Fin n) E) (hγ : γᴴ * γ = 1)
    (h1 : IsUnit (1 + γ)) :
    ∃ Γ : ℚ → Matrix (Fin n) (Fin n) E, (∀ s, (Γ s)ᴴ * Γ s = 1) ∧ Γ 0 = 1 ∧ Γ 1 = γ ∧
      ∀ (σ : E →+* K) i j, (fun s => σ (Γ s i j)) ∈ ratFn K := by
  obtain ⟨w, hw⟩ := h1.exists_right_inv
  obtain ⟨hS, hS2⟩ := GenusSelfDual.cayley_skew (u := γ) hγ hw (mul_eq_one_comm.1 hw)
  generalize (1 - γ) * w = S at hS hS2
  have hs : ∀ s : ℚ, star (s • S) = -(s • S) := fun s => by rw [star_smul, hS, smul_neg]; rfl
  have hu : ∀ s : ℚ, IsUnit (1 + s • S).det := fun s =>
    (Matrix.isUnit_iff_isUnit_det _).1 (GenusSelfDual.isUnit_one_add_of_skew _ (hs s))
  refine ⟨fun s => 2 * (1 + s • S)⁻¹ - 1,
    fun s => GenusSelfDual.cayley_unitary (hs s) (Matrix.mul_nonsing_inv _ (hu s)), ?_, ?_, fun σ i j => ?_⟩
  · simp only [zero_smul, add_zero, inv_one]; norm_num
  · have h := Matrix.nonsing_inv_mul _ (hu 1)
    simp only [one_smul] at h ⊢
    have : (1 + S)⁻¹ * 2 = 1 + γ := by rw [← hS2, ← mul_assoc, h, one_mul]
    rw [two_mul, ← mul_two, this, add_sub_cancel_left]
  · have e : ∀ s : ℚ, σ.mapMatrix (1 + s • S)⁻¹ = (σ.mapMatrix (1 + s • S))⁻¹ := fun s =>
      (Matrix.inv_eq_right_inv (by rw [← map_mul, Matrix.mul_nonsing_inv _ (hu s), map_one])).symm
    have hm := matInv_mem (M := fun s : ℚ => σ.mapMatrix (1 + s • S)) (fun a b => by
      have := add_mem (const_mem (σ ((1 : Matrix (Fin n) (Fin n) E) a b))) (mul_mem cast_mem (const_mem (σ (S a b))))
      convert this using 1
      funext s
      simp [Rat.smul_def]) (fun s => by
        rw [← RingHom.map_det]; exact (_root_.map_ne_zero σ).2 (hu s).ne_zero) i j
    have := sub_mem (add_mem hm hm) (const_mem (σ ((1 : Matrix (Fin n) (Fin n) E) i j)))
    convert this using 1
    funext s
    simp only [Pi.sub_apply, Pi.add_apply, ← e]
    simp only [two_mul, Matrix.sub_apply, Matrix.add_apply, map_sub, map_add]
    rfl

theorem exists_scalar (γ : Matrix (Fin n) (Fin n) E) : ∃ z : E, star z * z = 1 ∧ IsUnit (1 + z • γ) := by
  obtain ⟨θ', h0, hθ⟩ := GenusSelfDual.exists_imaginary_integer E
  generalize (θ' : E) = θ at h0 hθ
  replace hθ : star θ = -θ := hθ
  have hc : ∀ k : ℤ, star (1 + k * θ) = 1 - k * θ := fun k => by
    rw [star_add, star_one, star_mul', star_intCast, hθ]; ring
  have hne : ∀ k : ℤ, 1 + k * θ ≠ 0 := fun k hk => by
    have := hc k
    rw [hk, star_zero] at this
    exact two_ne_zero (α := E) (by linear_combination hk - this)
  have hne' : ∀ k : ℤ, 1 - k * θ ≠ 0 := fun k => by
    rw [← hc]; exact star_ne_zero.2 (hne k)
  let f : ℤ → E := fun k => (1 - k * θ) / (1 + k * θ)
  have hf : Function.Injective f := fun a b hab => by
    rw [div_eq_div_iff (hne a) (hne b)] at hab
    have : (2 * θ : E) * (a - b) = 0 := by linear_combination -hab
    exact_mod_cast sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (mul_ne_zero two_ne_zero h0))
  obtain ⟨_, ⟨k, rfl⟩, hk⟩ := (Set.infinite_range_of_injective hf).exists_notMem_finite
    (GenusSelfDual.finite_not_isUnit_one_add_smul (RingHom.id E) γ)
  refine ⟨f k, ?_, not_not.1 hk⟩
  have := hc (-k)
  simp only [Int.cast_neg, neg_mul, ← sub_eq_add_neg, sub_neg_eq_add] at this
  simp only [f, star_div₀, hc, this]
  rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero (hne' k) (hne k))]

end Cayley

end GlobalTheory.LFCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCoeffFieldIdempotentCuttingPeriodSpaces
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompRat

open GlobalTheory.CompIdem ReciprocityTheory.ChartRestriction.G.TB.ValAt

theorem exists_indicator_function {X : Scheme.{0}} (U : Set X) (hU : IsClopen U) :
    ∃ e : Γ(X, ⊤), e * e = e ∧ ∀ x : Sp ℂ ⟶ X,
      (x (IsLocalRing.closedPoint ℂ) ∈ U → valAt' x ⊤ e = 1) ∧
      (x (IsLocalRing.closedPoint ℂ) ∉ U → valAt' x ⊤ e = 0) := by
  let V : Bool → X.Opens := fun b => match b with
    | true => ⟨U, hU.2⟩
    | false => ⟨Uᶜ, hU.1.isOpen_compl⟩
  let sf : ∀ b, Γ(X, V b) := fun b => match b with
    | true => 1
    | false => 0
  have hcov : (⊤ : X.Opens) ≤ iSup V := by
    intro x _
    rw [TopologicalSpace.Opens.mem_iSup]
    by_cases h : x ∈ U
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  have hsub : ∀ W : X.Opens, W = ⊥ → Subsingleton Γ(X, W) := by
    rintro _ rfl
    infer_instance
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf V sf := by
    intro a b
    cases a <;> cases b
    · simp [sf]
    · refine (hsub _ ?_).elim _ _
      ext x
      simp [V]
    · refine (hsub _ ?_).elim _ _
      ext x
      simp [V]
    · simp [sf]
  obtain ⟨e, he'⟩ : ∃ e : Γ(X, ⊤), ∀ b, X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op e = sf b :=
    (X.sheaf.existsUnique_gluing' V ⊤ (fun b => homOfLE le_top) hcov sf hcomp).exists
  have hpt : ∀ (x : Sp ℂ ⟶ X) (b : Bool), x (IsLocalRing.closedPoint ℂ) ∈ V b → ⊤ ≤ x ⁻¹ᵁ V b := by
    intro x b h z _
    rwa [Subsingleton.elim (α := PrimeSpectrum ℂ) z (IsLocalRing.closedPoint ℂ)]
  refine ⟨e, ?_, fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine X.sheaf.eq_of_locally_eq' V ⊤ (fun b => homOfLE le_top) hcov _ _ fun b => ?_
    show X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op (e * e) = X.presheaf.map (homOfLE (le_top : V b ≤ ⊤)).op e
    rw [map_mul, he']
    cases b <;> simp [sf]
  · refine (TB.ValAt.valAt'_res x le_top (hpt x true h) e).symm.trans ((congrArg (valAt' x _) (he' true)).trans ?_)
    exact TB.ValAt.valAt'_one x _ (hpt x true h)
  · refine (TB.ValAt.valAt'_res x le_top (hpt x false h) e).symm.trans ((congrArg (valAt' x _) (he' false)).trans ?_)
    exact (valHom x _ (hpt x false h)).map_zero

theorem eq_val_of_A_eq_one {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H}
    (σ : KA l →+* ℂ) (hσ : σ (baseKA l).ρ = H.rt0) (hA : l.A = 1) : σ = (KA l).val.toRingHom := by
  have hz : zeta l.A = 1 := by
    rw [hA, zeta, Nat.cast_one, div_one, Complex.exp_two_pi_mul_I]
  ext ⟨x, hx⟩
  show σ ⟨x, hx⟩ = x
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hσ
    · have : (⟨zeta l.A, IntermediateField.subset_adjoin _ _ (by simp)⟩ : KA l) = 1 := Subtype.ext hz
      exact (congrArg σ this).trans ((map_one σ).trans hz.symm)
  | algebraMap q => exact (map_ratCast σ q)
  | add x y hx hy h1 h2 => exact (map_add σ ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [h1, h2])
  | mul x y hx hy h1 h2 => exact (map_mul σ ⟨x, hx⟩ ⟨y, hy⟩).trans (by rw [h1, h2])
  | inv x hx h1 => exact (map_inv₀ σ ⟨x, hx⟩).trans (by rw [h1])

theorem exists_coeff_idempotent_functions :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (F : FamilyUnif Xo σ ty), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty → l.A = 1 → ∀ c₀ : Coeff l, ∃ c : Coeff l, c₀.F ≤ c.F ∧ ∀ i : Fin F.n, ∃ e : Γ(Xo.XF c, ⊤), e * e = e ∧ ∀ i' P, IsPeriod (F.Di i') ty P → ∀ x : Sp ℂ ⟶ Xo.XF c, x ≫ pullback.fst _ _ = F.u i' P → x ≫ pullback.snd _ _ = spMap c.F.val.toRingHom → valAt' x ⊤ e = if i' = i then 1 else 0 := by
  intro E _ _ _ H D l Xo σ₀ g ty F _ hσ _ hA c
  obtain rfl := eq_val_of_A_eq_one σ₀ hσ hA
  classical
  have := CompFin.quasiCompact_alt Xo
  have := Xo.smooth
  have : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  obtain ⟨S, hS, hrat⟩ := exists_rational_components (c.le.trans (coeff_le_algebraicClosure c)) Xo.s
  have := c.fin
  let b := Module.finBasis ℚ c.F
  obtain ⟨c', hc'⟩ := exists_coeff_containing E H l (S ∪ Finset.univ.image fun j => (b j : ℂ)) (by
    intro z hz
    rcases Finset.mem_union.1 hz with h | h
    · exact mem_algebraicClosure_iff.1 (hS z h)
    · obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 h
      exact mem_algebraicClosure_iff.1 (coeff_le_algebraicClosure c (b j).2))
  refine ⟨c', fun z hz => ?_, fun i => ?_⟩
  · have e := congrArg c.F.val (b.sum_repr ⟨z, hz⟩)
    rw [map_sum] at e
    have e' : z = _ := e.symm
    rw [e']
    refine sum_mem fun j _ => ?_
    rw [map_rat_smul]
    exact IntermediateField.smul_mem _
      (hc' _ (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))))
  have hr := hrat c'.F c'.le (coeff_le_algebraicClosure c') fun z hz => hc' z (Finset.mem_union_left _ hz)
  obtain ⟨t, ht, hcont⟩ := exists_index F
  have := CompFin.isNoetherian_XF Xo c'
  let σ : c'.F →+* ℂ := c'.F.val.toRingHom
  let s : Xo.XF c' ⟶ Sp c'.F := pullback.snd _ _
  let pr : Xo.XF c' ⟶ Xo.X := pullback.fst _ _
  have hover : ∀ p : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ → (p ≫ pr) ≫ Xo.s = spMap (KA l).val.toRingHom := by
    intro p hp
    rw [Category.assoc, pullback.condition, ← Category.assoc, hp, GlobalTheory.CompIdem.spMap_comp]
    rfl
  have hconst : ∀ p q : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ → q ≫ s = spMap σ →
      p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent (q (IsLocalRing.closedPoint ℂ)) →
      t (p ≫ pr) = t (q ≫ pr) := by
    intro p q hp hq hpq
    obtain ⟨r, hr1, hr2⟩ := hr (q (IsLocalRing.closedPoint ℂ))
    exact const_on_component σ s r hr1 (fun x => t (x ≫ pr))
      (fun m B y hB hy hh => hcont m B _ hB (fun b hb => hover _ (hy b hb)) (GlobalTheory.LocLift.isHolTo_comp_hom hh _))
      p q hp hq ((connectedComponent_eq hr2) ▸ hpq) hr2
  let U : Set (Xo.XF c') := {z | ∃ p : Sp ℂ ⟶ Xo.XF c', p ≫ s = spMap σ ∧
    p (IsLocalRing.closedPoint ℂ) ∈ connectedComponent z ∧ t (p ≫ pr) = i}
  have hUc : ∀ z w, w ∈ connectedComponent z → (w ∈ U ↔ z ∈ U) := by
    intro z w h
    simp only [U, Set.mem_setOf_eq, connectedComponent_eq h]
  have hU : IsClopen U := by
    refine ⟨⟨isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩, isOpen_iff_forall_mem_open.2 fun z hz => ?_⟩
    · exact ⟨connectedComponent z, fun w hw h => hz ((hUc z w hw).1 h),
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
    · exact ⟨connectedComponent z, fun w hw => (hUc z w hw).2 hz,
        isOpen_connectedComponent_of_noetherianSpace z, mem_connectedComponent⟩
  obtain ⟨e, h1, h2⟩ := exists_indicator_function U hU
  refine ⟨e, h1, fun i' P hP p hp1 hp => ?_⟩
  have hp' : t (p ≫ pr) = i' := by
    have : p ≫ pr = F.u i' P := hp1
    rw [this]
    exact ht i' P hP
  split_ifs with h
  · subst h
    exact (h2 p).1 ⟨p, hp, mem_connectedComponent, hp'⟩
  · refine (h2 p).2 ?_
    rintro ⟨q, hq, hqp, hqi⟩
    exact h (Fin.ext (hp'.symm.trans ((hconst q p hq hp hqp).symm.trans hqi)))

end GlobalTheory.CompRat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMemberDictionaryContextGoodEmbeddingStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_memberDictionaryContext_goodEmbedding : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (hr : V.rank = r) (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), IotaOK Dw V ι → 1 ≤ Dw.p + Dw.q → l.A = 1 → GoodEmb c σ → (∃ C : Ctx Xo c σ V r, C.OK ∧ C.ι = ι) ∧ (∀ C : Ctx Xo c σ V r, C.OK → GlobalTheory.FrameUnif.NegXi C.M) ∧ ∀ x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ, (∀ τ : D.host.E →+* ℂ, τ (H.rt : D.host.E) = H.rt0 → gram τ (-(Matrix.reindex (finCongr hr) (finCongr hr) V.gram)ᵀ) (x₀ τ) = Matrix.diagonal fun a : Fin r => ((sgn Dw.q (a : ℕ) : ℝ) : ℂ)) → ∃ C : Ctx Xo c σ V r, C.OK ∧ C.ι = ι ∧ C.x₀ = x₀ := by
  first | exact @GlobalTheory.Member.exists_ctx | exact GlobalTheory.Member.exists_ctx | (intros; apply GlobalTheory.Member.exists_ctx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueClassSumOfSeriesTotal
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ClassSumCompare

open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.AdelicNormWeight

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def flip {X K : Type} [Neg X] (φ : X → K) : X → K := fun x => φ (-x)

section Reps

variable {n : ℕ}

def ords {ι : Type} (J : Subgroup (UA E n)) (h : ι → UA E n) : ι → ℕ := fun i => Nat.card (stab J (h i))

def lats {ι : Type} (h : ι → UA E n) : ι → GenLat E n := fun i => latOf (h i)

end Reps

section Sums

variable {n : ℕ} {ι : Type} [Fintype ι] {T : Type} [AddCommGroup T] [Module c.F T]

variable {Xo c}

def coverCoeff (d : DeltaDat Xo c n) (φ : (Fin n → ConjQ Dw l) → c.F) (φδ : (Fin n → LaJ Xo c d) → c.F) :
    (Fin n → LevQ Dw d.l₂) → c.F :=
  fun q => d.eF.symm (phiHat d.c₂ (flip (coverDatum d φ φδ)) q)

def twist (d : DeltaDat Xo c n) (g : Rul d.Xo₂ d.c₂) : DeltaDat Xo c n := { d with cδ := d.cδ * g }

abbrev Tested {S : Type} [CommRing S] [Algebra c.F S] (y : FrPt Xo c S) : Prop :=
  FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y

variable (Xo c)

end Sums

end GlobalTheory.ClassSumCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ThetaPointsChangeLevelIsometryLinearMapStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaPoints_change_levelIsometry_linearMap : Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (F : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) (fun j => relab c σ (e j).1)) (r : ℕ) (M : ModelsOf F r) (k : Fin F.n) (T : ThetaData e F M k), ∀ b ∈ T.co ⁻¹' (M.X k).dom, ∀ b' ∈ T.co ⁻¹' (M.X k).dom, ∀ (κ κ' : ℂ) (y y' : FrPt Xo c (CAt σ)) (gam : (F.Di k).La ≃ₗ[𝓞 E] (F.Di k).La) (h₀ : Matrix (Fin g) (Fin g) ℂ), IsThetaPt T b κ y → IsThetaPt T b' κ' y' → ((∀ a b, (F.Di k).EF (gam a) (gam b) = (F.Di k).EF a b) ∧ (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) (F.Di k).La), ∃ v, gam a = a + l.M • v) ∧ (∀ a, ∃ v, gam a = a + l.A • v)) → (∀ a, T.Pf (T.co b') (gam a) = h₀ *ᵥ T.Pf (T.co b) a) → y'.x = y.x ∧ (∀ τ i, IsDerivAt0 (fun z => (F.ex k (T.Pf (T.co b)) z).left) (h₀⁻¹ *ᵥ Pi.single (e.symm ⟨τ, i⟩) 1) (y'.u τ i)) ∧ ∃ t₀ : (CAt σ)ˣ, SecBC (RingHom.id (CAt σ)) (t₀ : CAt σ) y.x y'.x y.s y'.s ∧ toC (t₀ : CAt σ) ^ 2 * (κ ^ 2 * (T.h b').det * h₀.det) = κ' ^ 2 * (T.h b).det := by
  first | exact @GlobalTheory.ThetaPtChg.thetaPt_change | exact GlobalTheory.ThetaPtChg.thetaPt_change | (intros; apply GlobalTheory.ThetaPtChg.thetaPt_change <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.WeightZeroSectionValueConjPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.PureType GlobalTheory.CompRat
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weightZeroSection_value_conj_point : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (σ : c.F →+* ℂ) (τ : ℂ ≃+* ℂ), ∀ f ∈ sec Xo c 0 0, ∀ (y : FrPt Xo c (CAt σ)) (y' : FrPt Xo c (CAt ((τ : ℂ →+* ℂ).comp σ))), y'.x = spMap (τ : ℂ →+* ℂ) ≫ y.x → Formalism.L2.PjFree.toC (evR Xo c f y') = τ (Formalism.L2.PjFree.toC (evR Xo c f y)) := by
  first | exact @GlobalTheory.WeightZeroValue.evR_conj | exact GlobalTheory.WeightZeroValue.evR_conj | (intros; apply GlobalTheory.WeightZeroValue.evR_conj <;> assumption)
end

