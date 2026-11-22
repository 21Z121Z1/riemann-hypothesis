import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0382
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0432
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0280
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0410
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub
import Formalism.LocalToGlobal.Divisibility.Tuples
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0049
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilRepresentationHeisenberg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0435
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0365
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0385
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FunctionFieldPlaceLocalIndexColength
section
open scoped IntermediateField Polynomial RatFunc
open GlobalTheory.Nef

set_option autoImplicit false

namespace GlobalTheory.Nef.LocalIndex

open GlobalTheory.Nef.OrdCalc

variable {k F : Type} [Field k] [Field F] [Algebra k F]

theorem const_le_one (v : Place k F) (c : k) : v.1 (algebraMap k F c) ≤ 1 := by
  by_cases hc : c = 0
  · simp [hc]
  · exact (v.2.2 c hc).le

theorem div_unif (v : Place k F) {π : F} (hπ : π ≠ 0) (h1 : ord v π = 1) {y : F}
    (hy : v.1 y < 1) : v.1 (π⁻¹ * y) ≤ 1 := by
  by_cases h0 : y = 0
  · simp [h0]
  have h2 := (le_one_iff v y h0).1 hy.le
  have h3 : ord v y ≠ 0 := fun h => hy.ne ((eq_one_iff v y h0).2 h)
  have h4 : ord v π⁻¹ = -1 := by
    have := ord_zpow v π (-1)
    rw [zpow_neg_one, h1] at this; simpa using this
  rw [le_one_iff v _ (mul_ne_zero (inv_ne_zero hπ) h0), ord_mul v _ _ (inv_ne_zero hπ) h0, h4]
  omega

theorem exists_residue (v : Place k F)
    (hres : ∀ x : F, v.1 x ≤ 1 → ∃ c : k, v.1 (x - algebraMap k F c) < 1) :
    ∃ f : F →ₗ[k] k, ∀ y, v.1 y ≤ 1 → f y = 0 → v.1 y < 1 := by
  let m : Submodule k F :=
    { carrier := {y | v.1 y < 1}
      add_mem' := fun {a b} ha hb => v.1.map_add_lt ha hb
      zero_mem' := by simp
      smul_mem' := fun c y hy => by
        show v.1 (c • y) < 1
        rw [Algebra.smul_def, map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' (const_le_one v c)) hy }
  have h1 : (1 : F) ∉ m := by
    show ¬ v.1 1 < 1
    simp
  obtain ⟨f, hf, hk⟩ := Submodule.exists_le_ker_of_notMem h1
  refine ⟨f, fun y hy h0 => ?_⟩
  obtain ⟨c, hc⟩ := hres y hy
  have h2 : f (y - algebraMap k F c) = 0 := hk hc
  rw [map_sub, h0, Algebra.algebraMap_eq_smul_one, map_smul, zero_sub, neg_eq_zero, smul_eq_mul,
    mul_eq_zero] at h2
  rcases h2 with h2 | h2
  · simpa [h2] using hc
  · exact absurd h2 hf

theorem mulVec_int (v : Place k F) {n : ℕ} (u : Matrix (Fin n) (Fin n) F) (x : Fin n → F)
    (hu : ∀ i j, v.1 (u i j) ≤ 1) (hx : ∀ i, v.1 (x i) ≤ 1) (i : Fin n) :
    v.1 (u.mulVec x i) ≤ 1 := by
  simp only [Matrix.mulVec, dotProduct]
  apply Valuation.map_sum_le
  intro j _
  rw [map_mul]
  exact mul_le_one' (hu i j) (hx j)

theorem exists_primitive (v : Place k F) {n : ℕ} (a : Matrix (Fin n) (Fin n) F) (hd : a.det ≠ 0)
    (hlt : v.1 a.det < 1) :
    ∃ (c : Fin n → F) (i : Fin n), c i = 1 ∧ (∀ l, v.1 (c l) ≤ 1) ∧ ∀ l, v.1 (a.mulVec c l) < 1 := by
  have hn : ¬ ∀ i j, v.1 (a⁻¹ i j) ≤ 1 := by
    intro h
    have h1 := (det_adj_int v n _ h).1
    have h2 : v.1 (a.det * a⁻¹.det) < 1 := by
      rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_right' h1) hlt
    rw [← Matrix.det_mul, Matrix.mul_nonsing_inv a (isUnit_iff_ne_zero.2 hd)] at h2
    simp at h2
  push Not at hn
  obtain ⟨i0, j, hj⟩ := hn
  have hb : (fun l => a⁻¹ l j) ≠ 0 := by
    intro h
    have := congrFun h i0
    simp only [Pi.zero_apply] at this
    rw [this] at hj
    simp at hj
  obtain ⟨i, hi, -, -, hmax⟩ := nrm_max v n _ hb
  have hvi : 1 < v.1 (a⁻¹ i j) := lt_of_lt_of_le hj (hmax i0)
  have hpos : 0 < v.1 (a⁻¹ i j) := lt_trans zero_lt_one hvi
  refine ⟨(a⁻¹ i j)⁻¹ • fun l => a⁻¹ l j, i, ?_, fun l => ?_, fun l => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ hi
  · simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀]
    rw [inv_mul_le_iff₀ hpos, mul_one]; exact hmax l
  · rw [Matrix.mulVec_smul]
    have e : a.mulVec (fun l => a⁻¹ l j) l = (1 : Matrix (Fin n) (Fin n) F) l j := by
      rw [← Matrix.mul_nonsing_inv a (isUnit_iff_ne_zero.2 hd)]; rfl
    simp only [Pi.smul_apply, smul_eq_mul, map_mul, map_inv₀, e]
    rw [inv_mul_lt_iff₀ hpos, mul_one]
    refine lt_of_le_of_lt ?_ hvi
    by_cases h : l = j <;> simp [Matrix.one_apply, h]

theorem exists_functional_inv_mulVec_integral_of_order (v : Place k F)
    (hres : ∀ x : F, v.1 x ≤ 1 → ∃ c : k, v.1 (x - algebraMap k F c) < 1) (n N : ℕ) :
    ∀ a : Matrix (Fin n) (Fin n) F, a.det ≠ 0 → (∀ i j, v.1 (a i j) ≤ 1) → ord v a.det = N →
      ∃ φ : (Fin n → F) →ₗ[k] (Fin N → k), ∀ x : Fin n → F, (∀ i, v.1 (x i) ≤ 1) → φ x = 0 →
        ∀ i, v.1 (a⁻¹.mulVec x i) ≤ 1 := by
  induction N with
  | zero =>
    intro a hd ha hN
    have hu : Unimod v a := ⟨ha, (eq_one_iff v _ hd).2 (by simpa using hN)⟩
    exact ⟨0, fun x hx _ i => mulVec_int v _ x (unimod_mul_inv v n a a hu hu).2.1 hx i⟩
  | succ N ih =>
    intro a hd ha hN
    obtain ⟨π, hπ, hπ1⟩ := exists_unif v
    obtain ⟨f, hf⟩ := exists_residue v hres
    have hlt : v.1 a.det < 1 := lt_of_le_of_ne (det_adj_int v n a ha).1 (fun h => by
      have := (eq_one_iff v _ hd).1 h
      omega)
    obtain ⟨c, i, hci, hc, hac⟩ := exists_primitive v a hd hlt
    set T : Matrix (Fin n) (Fin n) F := (1 : Matrix (Fin n) (Fin n) F).updateCol i (π⁻¹ • c) with hT
    have hTd : T.det = π⁻¹ := by
      rw [hT, ← Matrix.cramer_apply, Matrix.cramer_one]; simp [hci]
    have h4 : ord v π⁻¹ = -1 := by
      have := ord_zpow v π (-1)
      rw [zpow_neg_one, hπ1] at this; simpa using this
    have hd' : (a * T).det ≠ 0 := by
      rw [Matrix.det_mul, hTd]; exact mul_ne_zero hd (inv_ne_zero hπ)
    have ha' : ∀ l j, v.1 ((a * T) l j) ≤ 1 := by
      intro l j
      by_cases h : j = i
      · have e : (a * T) l j = π⁻¹ * a.mulVec c l := by
          subst h
          simp only [hT, Matrix.mul_apply, Matrix.updateCol_self, Matrix.mulVec, dotProduct,
            Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
          exact Finset.sum_congr rfl fun _ _ => by ring
        rw [e]; exact div_unif v hπ hπ1 (hac l)
      · have e : (a * T) l j = a l j := by
          conv_rhs => rw [← Matrix.mul_one a]
          simp only [hT, Matrix.mul_apply, Matrix.updateCol_ne h]
        rw [e]; exact ha l j
    have hN' : ord v (a * T).det = N := by
      rw [Matrix.det_mul, hTd, ord_mul v _ _ hd (inv_ne_zero hπ), hN, h4]; push_cast; ring
    obtain ⟨φ, hφ⟩ := ih (a * T) hd' ha' hN'
    let ψ : (Fin n → F) →ₗ[k] k :=
      f ∘ₗ (LinearMap.proj i) ∘ₗ ((Matrix.mulVecLin (a * T)⁻¹).restrictScalars k)
    refine ⟨LinearMap.pi fun j => Fin.cases ψ (fun j => (LinearMap.proj j) ∘ₗ φ) j,
      fun x hx h0 l => ?_⟩
    have h1 : φ x = 0 := funext fun j => by simpa using congrFun h0 j.succ
    have h2 : f ((a * T)⁻¹.mulVec x i) = 0 := by simpa [ψ] using congrFun h0 0
    have hy := hφ x hx h1
    have hyi := div_unif v hπ hπ1 (hf _ (hy i) h2)
    have e : a⁻¹ = T * (a * T)⁻¹ := by
      rw [Matrix.mul_inv_rev, ← Matrix.mul_assoc,
        Matrix.mul_nonsing_inv T (isUnit_iff_ne_zero.2 (hTd ▸ inv_ne_zero hπ)), Matrix.one_mul]
    rw [e, ← Matrix.mulVec_mulVec]
    generalize (a * T)⁻¹.mulVec x = y at hy hyi
    simp only [Matrix.mulVec, dotProduct]
    apply Valuation.map_sum_le
    intro j _
    by_cases h : j = i
    · subst h
      have e2 : T l j * y j = c l * (π⁻¹ * y j) := by
        simp only [hT, Matrix.updateCol_self, Pi.smul_apply, smul_eq_mul]; ring
      rw [e2, map_mul]
      exact mul_le_one' (hc l) hyi
    · rw [map_mul]
      refine mul_le_one' ?_ (hy j)
      simp only [hT, Matrix.updateCol_ne h]
      by_cases h' : l = j <;> simp [Matrix.one_apply, h']

end GlobalTheory.Nef.LocalIndex

open GlobalTheory.Nef.OrdCalc GlobalTheory.Nef.LocalIndex in

theorem GlobalTheory.Nef.local_index : ∀ (k F : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field F] [Algebra k F], IsFF k F →
  ∀ (v : Place k F) (n : ℕ) (h : Matrix (Fin n) (Fin n) F), h.det ≠ 0 → (∀ i j, v.1 (h⁻¹ i j) ≤ 1) → ∃ (N : ℕ) (φ : (Fin n → F) →ₗ[k] (Fin N → k)), (N : ℤ) = -ord v h.det ∧ ∀ x : Fin n → F, (∀ i, v.1 (x i) ≤ 1) → φ x = 0 → ∀ i, v.1 (h.mulVec x i) ≤ 1 := by
  intro k F _ _ _ _ _ hF v n h hd hi
  have e : h⁻¹.det = h.det⁻¹ := by rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
  have hd' : h⁻¹.det ≠ 0 := e ▸ inv_ne_zero hd
  have h0 := (le_one_iff v _ hd').1 (det_adj_int v n _ hi).1
  have h1 : ord v h⁻¹.det = -ord v h.det := by
    have := ord_zpow v h.det (-1)
    rw [zpow_neg_one] at this; rw [e, this]; ring
  obtain ⟨N, hN⟩ := Int.eq_ofNat_of_zero_le h0
  obtain ⟨φ, hφ⟩ := exists_functional_inv_mulVec_integral_of_order v (GlobalTheory.T.functionFieldPlace_isDVR_and_residue_eq_ground k F hF v).2 n N h⁻¹ hd' hi hN
  rw [Matrix.nonsing_inv_nonsing_inv h (isUnit_iff_ne_zero.2 hd)] at hφ
  exact ⟨N, φ, by rw [← hN, h1], hφ⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoTermIteratedFDerivSummableBound
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

noncomputable section

namespace GlobalTheory.HeckeTwo

theorem fTerm_deriv_summable_bound : ∀ (F : Type) [Field F] [NumberField F] [NumberField.IsTotallyReal F] (𝔞 𝔟 : Frac F),
  ∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ,
    ∃ u : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) × NZ (𝔞 : FractionalIdeal (𝓞 F)⁰ F) → ℝ, Summable u ∧
      ∀ p, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (fun z : Emb F → ℂ => fTerm σ z p.1.out.1 p.2.1) z‖ ≤ u p := by
  intro F _ _ _ 𝔞 𝔟 K hK hKH L hL hLU n
  obtain ⟨m, hm⟩ := GlobalTheory.T.norm_iteratedFDeriv_fTerm_le_of_isCompact F K hK hKH L hL hLU n
  obtain ⟨C₀, -, hC₀⟩ := GlobalTheory.T.exists_balanced_unit_multiple_totallyReal F
  obtain ⟨N, hN⟩ := GlobalTheory.T.summable_heckeBalancedLatticeDoubleSum F 𝔞 𝔟 C₀ m
  obtain ⟨C, hC⟩ := hm N
  choose ε hε using fun c : Quotient (unitRel (𝔟 : FractionalIdeal (𝓞 F)⁰ F)) => hC₀ c.out.1 c.out.2.2
  refine ⟨fun p => C * ∏ τ : Emb F, (|τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)| + |τ (((ε p.1 : 𝓞 F) : F) * p.1.out.1)|⁻¹) ^ m /
          (1 + |τ p.2.1 * τ p.1.out.1|) ^ N, (hN ε hε).mul_left C, ?_⟩
  rintro ⟨c, ν⟩ σ hσ z hz
  have hee : (((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) * ((ε c : 𝓞 F) : F) = 1 := unit_inv_mul (ε c)
  have hfun : (fun z : Emb F → ℂ => fTerm σ z c.out.1 ν.1) =
      fun z => fTerm σ z (((ε c : 𝓞 F) : F) * c.out.1) (((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1) := by
    funext z
    have hb : c.out.1 = ((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * (((ε c : 𝓞 F) : F) * c.out.1) := by
      rw [← mul_assoc, hee, one_mul]
    conv_lhs => rw [hb]
    exact GlobalTheory.T.heckeEisensteinFourierTerm_move_unit F σ z _ _ (ε c)⁻¹
  have hb0 : ((ε c : 𝓞 F) : F) * c.out.1 ≠ 0 := mul_ne_zero (right_ne_zero_of_mul_eq_one hee) c.out.2.2
  have hν0 : ((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1 ≠ 0 := mul_ne_zero (left_ne_zero_of_mul_eq_one hee) ν.2.2
  dsimp only
  rw [hfun]
  refine (hC σ hσ z hz _ _ hb0 hν0).trans (le_of_eq ?_)
  congr 1
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 := congrArg τ hee
  rw [map_mul, map_one] at h1
  have h2 : τ (((((ε c)⁻¹ : (𝓞 F)ˣ) : 𝓞 F) : F) * ν.1) * τ (((ε c : 𝓞 F) : F) * c.out.1) = τ ν.1 * τ c.out.1 := by
    rw [map_mul, map_mul]; linear_combination (τ ν.1 * τ c.out.1) * h1
  rw [h2]

end GlobalTheory.HeckeTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormsIntegrallyEquivalentAlmostAll
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.ProdStep

theorem mem_span_prod {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] (a₁ : A₁) (a₂ : A₂) (x : A₁ × A₂) :
    x ∈ Ideal.span {((a₁, a₂) : A₁ × A₂)} ↔ x.1 ∈ Ideal.span {a₁} ∧ x.2 ∈ Ideal.span {a₂} := by
  simp only [Ideal.mem_span_singleton']
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨⟨c.1, rfl⟩, ⟨c.2, rfl⟩⟩
  · rintro ⟨⟨c₁, h₁⟩, ⟨c₂, h₂⟩⟩
    exact ⟨(c₁, c₂), Prod.ext h₁ h₂⟩

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap, ← Functor.map_comp, ← Spec.map_comp]

theorem prodStep : ∀ (q : ℕ) (B A₁ A₂ : Type) [CommRing B] [CommRing A₁] [CommRing A₂] [Algebra B A₁] [Algebra B A₂] (f : B) (I J : Ideal B) (n i : ℤ) (y : Ht q (sp B) n i), IsCoprime I J → (∀ a : A₁, ∃ b : B, a - algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f}) → (∀ b : B, algebraMap B A₁ b ∈ Ideal.span {algebraMap B A₁ f} ↔ b ∈ I) → (∀ a : A₂, ∃ b : B, a - algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f}) → (∀ b : B, algebraMap B A₂ b ∈ Ideal.span {algebraMap B A₂ f} ↔ b ∈ J) → pull _ (spMap (algebraMap B A₁)) _ _ y = 0 → pull _ (spMap (algebraMap B A₂)) _ _ y = 0 → (∀ a : A₁ × A₂, ∃ b : B, a - algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f}) ∧ (∀ b : B, algebraMap B (A₁ × A₂) b ∈ Ideal.span {algebraMap B (A₁ × A₂) f} ↔ b ∈ I ⊓ J) ∧ pull _ (spMap (algebraMap B (A₁ × A₂))) _ _ y = 0 := by
  intro q B A₁ A₂ _ _ _ _ _ f I J n i y hIJ hs₁ hk₁ hs₂ hk₂ hy₁ hy₂
  have hf : algebraMap B (A₁ × A₂) f = (algebraMap B A₁ f, algebraMap B A₂ f) := rfl
  refine ⟨?_, ?_, ?_⟩
  · intro a
    obtain ⟨u, hu, v, hv, huv⟩ := Ideal.isCoprime_iff_exists.1 hIJ
    obtain ⟨b₁, hb₁⟩ := hs₁ a.1
    obtain ⟨b₂, hb₂⟩ := hs₂ a.2
    refine ⟨b₁ * v + b₂ * u, ?_⟩
    rw [hf, mem_span_prod]
    constructor
    · have e : a.1 - algebraMap B A₁ (b₁ * v + b₂ * u) = (a.1 - algebraMap B A₁ b₁) + algebraMap B A₁ ((b₁ - b₂) * u) := by
        have : b₁ * v + b₂ * u = b₁ - (b₁ - b₂) * u := by linear_combination b₁ * huv
        rw [this, map_sub]; ring
      show a.1 - algebraMap B A₁ (b₁ * v + b₂ * u) ∈ _
      rw [e]
      exact Ideal.add_mem _ hb₁ ((hk₁ _).2 (I.mul_mem_left _ hu))
    · have e : a.2 - algebraMap B A₂ (b₁ * v + b₂ * u) = (a.2 - algebraMap B A₂ b₂) + algebraMap B A₂ ((b₂ - b₁) * v) := by
        have : b₁ * v + b₂ * u = b₂ - (b₂ - b₁) * v := by linear_combination b₂ * huv
        rw [this, map_sub]; ring
      show a.2 - algebraMap B A₂ (b₁ * v + b₂ * u) ∈ _
      rw [e]
      exact Ideal.add_mem _ hb₂ ((hk₂ _).2 (J.mul_mem_left _ hv))
  · intro b
    rw [hf, mem_span_prod, Ideal.mem_inf]
    exact and_congr (hk₁ b) (hk₂ b)
  · have hbij := GlobalTheory.EtC.ProdCoh.ht_prod_bijective q A₁ A₂ n i
    apply hbij.1
    have e₁ : (RingHom.fst A₁ A₂).comp (algebraMap B (A₁ × A₂)) = algebraMap B A₁ := by ext; rfl
    have e₂ : (RingHom.snd A₁ A₂).comp (algebraMap B (A₁ × A₂)) = algebraMap B A₂ := by ext; rfl
    simp only [map_zero]
    rw [← pull_comp, ← pull_comp, ← spMap_comp, ← spMap_comp, e₁, e₂, hy₁, hy₂]

end GlobalTheory.EtC.ProdStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyTrivialOfTermsDegreeZeroStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hypercohomology_trivial_of_terms_degreeZero : ∀ (R : Type) [CommRing R] (K M : Cx R) [K.IsStrictlyLE 0], (∀ p n : ℤ, p ≤ 0 → Subsingleton (CohomologyClass (sgl (K.X p)) M n)) → ∀ n : ℤ, Subsingleton (CohomologyClass K M n) := by
  first | exact @GlobalTheory.nullHtpy_stair | exact GlobalTheory.nullHtpy_stair | (intros; apply GlobalTheory.nullHtpy_stair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdFMapAlgebraMap
section
noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV Formalism.UG

namespace GlobalTheory.LKTorus

variable (L : Type) [Field L] [NumberField L]

def simTA (c : L →ₐ[ℚ] L) : Subgroup (AfE ℚ L)ˣ where
  carrier := {x | ∃ t : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ, x * conjId c x = idF ℚ L t}
  one_mem' := ⟨1, by simp⟩
  mul_mem' := by
    rintro x y ⟨s, hs⟩ ⟨t, ht⟩
    refine ⟨s * t, ?_⟩
    rw [map_mul, map_mul, ← hs, ← ht]
    exact mul_mul_mul_comm x y (conjId c x) (conjId c y)
  inv_mem' := by
    rintro x ⟨s, hs⟩
    refine ⟨s⁻¹, ?_⟩
    rw [map_inv, map_inv, ← hs, mul_inv]

def ratT (c : L →ₐ[ℚ] L) : Subgroup (simTA L c) :=
  ((simT ℚ c).map (ratId ℚ L)).subgroupOf (simTA L c)

theorem ratId_mem_simTA (c : L →ₐ[ℚ] L) {a : Lˣ} (ha : a ∈ simT ℚ c) : ratId ℚ L a ∈ simTA L c := by
  obtain ⟨t, ht⟩ := ha
  refine ⟨Units.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom t, ?_⟩
  apply Units.ext
  simp only [Units.val_mul, ratId, conjId, idF, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
    RingHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  simp only [inclE, sigR, Algebra.TensorProduct.includeLeftRingHom_apply, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    Algebra.TensorProduct.includeRight_apply]
  rw [ht, Algebra.algebraMap_eq_smul_one (A := L), Algebra.algebraMap_eq_smul_one (A := FiniteAdeleRing (𝓞 ℚ) ℚ),
    TensorProduct.smul_tmul]

theorem conjId_ratId (c : L →ₐ[ℚ] L) (a : Lˣ) :
    conjId c (ratId ℚ L a) = ratId ℚ L (Units.map (c : L →+* L).toMonoidHom a) := by
  apply Units.ext
  simp [conjId, ratId, sigR, inclE]

theorem idF_map_algebraMap (r : ℚˣ) :
    idF ℚ L (Units.map (algebraMap ℚ (FiniteAdeleRing (𝓞 ℚ) ℚ)).toMonoidHom r) =
      ratId ℚ L (Units.map (algebraMap ℚ L).toMonoidHom r) := by
  apply Units.ext
  simp only [idF, ratId, inclE, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe, RingHom.coe_coe,
    AlgHom.toRingHom_eq_coe, Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.includeLeftRingHom_apply]
  rw [Algebra.algebraMap_eq_smul_one (A := L), Algebra.algebraMap_eq_smul_one (A := FiniteAdeleRing (𝓞 ℚ) ℚ),
    TensorProduct.smul_tmul]

theorem sigR_mem_RInt (c : L →ₐ[ℚ] L) {y : AfE ℚ L} (hy : y ∈ RInt ℚ L) :
    sigR c (FiniteAdeleRing (𝓞 ℚ) ℚ) y ∈ RInt ℚ L := by
  have hle : RInt ℚ L ≤ (RInt ℚ L).comap (sigR c (FiniteAdeleRing (𝓞 ℚ) ℚ)) := by
    refine (Subring.closure_le).2 ?_
    rintro g (⟨⟨e, ⟨b, rfl⟩⟩, rfl⟩ | ⟨d, rfl⟩)
    · refine Subring.subset_closure (Or.inl ⟨⟨c (algebraMap (𝓞 L) L b), ⟨RingOfIntegers.mapRingHom (c : L →+* L) b, ?_⟩⟩, ?_⟩)
      · rfl
      · simp [sigR]
    · refine Subring.subset_closure (Or.inr ⟨d, ?_⟩)
      simp [sigR]
  exact hle hy

theorem conjId_mem_intU (c : L →ₐ[ℚ] L) {k : (AfE ℚ L)ˣ} (hk : k ∈ intU ℚ L) : conjId c k ∈ intU ℚ L := by
  rw [intU, Submonoid.mem_units_iff] at hk ⊢
  refine ⟨sigR_mem_RInt L c hk.1, ?_⟩
  rw [← map_inv]
  exact sigR_mem_RInt L c hk.2

theorem idF_mem_intU {u : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (hu : (u : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ intAd ℚ)
    (hu' : ((u⁻¹ : (FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ intAd ℚ) : idF ℚ L u ∈ intU ℚ L := by
  rw [intU, Submonoid.mem_units_iff]
  refine ⟨Subring.subset_closure (Or.inr ⟨⟨_, hu⟩, rfl⟩), ?_⟩
  rw [← map_inv]
  exact Subring.subset_closure (Or.inr ⟨⟨_, hu'⟩, rfl⟩)

end GlobalTheory.LKTorus
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveEtaleSheafOfLinearMapsFromModule
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem homSh_injective (R : Type) [CommRing R] (J : Shv R) [Injective J] (M : ModuleCat.{1} (ULift.{1} R)) [Projective M] :
    Injective ((homSh J).obj (op M)) := by
  obtain ⟨e, -, hX⟩ := GlobalTheory.T.exists_sheafHom_linearMapsSheaf_curry_equiv R J
  haveI : Module.Projective (ULift.{1} R) M := (IsProjective.iff_projective (P := M)).2 ‹_›
  constructor
  intro X Y g i _
  have surj : Function.Surjective (Linear.leftComp (ULift.{1} R) J i) :=
    fun k => ⟨Injective.factorThru k i, Injective.comp_factorThru k i⟩
  obtain ⟨h', hh'⟩ := Module.projective_lifting_property _ (e X M g) surj
  refine ⟨(e Y M).symm h', ?_⟩
  apply (e X M).injective
  rw [hX, Equiv.apply_symm_apply, hh']

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormNormalizedHeisenbergIntertwinerStatement
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariantForm_normalizedHeisenbergIntertwiner : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → (∀ x y, ‖γ x y‖ = 1) → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ (φ : X →ₗ[R] X), (∀ x y, γ (φ x) (φ y) = γ x y) → SelfDual γ (A.map φ) → idx A (A.map φ) ≠ 0 → ∀ T : M →ₗ[ℂ] M, (∀ x v, T (W x v) = W (φ x) (T v)) → (∀ e, Fixes W A e → T e = normOp lam W A (A.map φ) e) → ∀ B : M →ₗ[ℂ] M →ₗ⋆[ℂ] ℂ, (∀ x u v, B (W x u) (W x v) = B u v) → ∀ u v, B (T u) (T v) = B u v := by
  first | exact @GlobalTheory.FinWeil.invForm_intertwiner | exact GlobalTheory.FinWeil.invForm_intertwiner | (intros; apply GlobalTheory.FinWeil.invForm_intertwiner <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFieldMonicRootsTensorFractionRingStrictlyHenseStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isField_monicRoots_tensor_fractionRing_strictlyHenselian : ∀ (A O : Type) [CommRing A] [IsDomain A] [CommRing O] [Algebra A O], AIC A → SH O → IndEt A O → IsField (O ⊗[A] FractionRing A) ∧ AIC (O ⊗[A] FractionRing A) := by
  first | (exact @GlobalTheory.isField_aic_tensor_fractionRing_of_strictlyHenselian) | (exact GlobalTheory.isField_aic_tensor_fractionRing_of_strictlyHenselian) | (intros; apply GlobalTheory.isField_aic_tensor_fractionRing_of_strictlyHenselian  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralModularFamilyValueDivPeriodPow
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF IsTauOf)

namespace GlobalTheory.QFam

theorem isIntegral_value_div (ι : Type) [Fintype ι] (act : ι → SL(2, ℤ) → ι) (w N : ℕ)
    (f : ι → ℍ → ℂ) (R : Subring ℂ) (τ₀ : ℍ) (Ω : ℂ) (hN : 0 < N) (hact : ActBij act)
    (hf : IsFam act w f) (hq : ∀ i, QAll (· ∈ R) N (f i)) (hj : IsIntegral R (jT τ₀))
    (hΩ : Ω ^ 12 = DD τ₀) (i : ι) : IsIntegral R (f i τ₀ / Ω ^ w) := by
  have hq' : ∀ i, QAll (· ∈ (integralClosure R ℂ).toSubring) N (f i) := fun i => by
    obtain ⟨a, ha, haR⟩ := hq i
    exact ⟨a, ha, fun n => (integralClosure R ℂ).algebraMap_mem ⟨a n, haR n⟩⟩
  have hs := GlobalTheory.T.esymm_pow_twelve_div_discriminant_mem_subring ι act w N f (integralClosure R ℂ).toSubring τ₀ hN hact hf hq' hj
  have h1 : IsIntegral (integralClosure R ℂ) (f i τ₀ ^ 12 / DD τ₀ ^ w) :=
    GlobalTheory.T.isIntegral_of_esymm_mem_subring ι (integralClosure R ℂ).toSubring (fun i => f i τ₀ ^ 12 / DD τ₀ ^ w) hs i
  have h2 : IsIntegral R (f i τ₀ ^ 12 / DD τ₀ ^ w) := isIntegral_trans _ h1
  have h3 : (f i τ₀ / Ω ^ w) ^ 12 = f i τ₀ ^ 12 / DD τ₀ ^ w := by
    rw [div_pow, ← hΩ, ← pow_mul, ← pow_mul, mul_comm]
  exact IsIntegral.of_pow (n := 12) (by norm_num) (h3 ▸ h2)

end GlobalTheory.QFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenIsIrreducibleComponentOfRationalPointSmootStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_isIrreducible_componentOfRationalPoint_smooth : ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k)) (e : Spec (CommRingCat.of k) ⟶ X), Smooth f → e ≫ f = 𝟙 _ → IsOpen {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} ∧ IsIrreducible {x : X | x ∈ connectedComponentIn (f ⁻¹' {f x}) (e (f x))} := by
  first | exact @GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field | exact GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field | (intros; apply GlobalTheory.isOpen_and_isIrreducible_sectionComponent_of_smooth_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSubgroupOfSiegelAndOppositeNhdsStatement
section
open MeasureTheory Matrix GlobalTheory.KSp GlobalTheory.SplitUnitary
open GlobalTheory.WeilM (UG IsQuad IsHerm ResEtaPow)
open GlobalTheory.SplitWeil (SB nabs)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_subgroup_of_siegel_and_opposite_nhds : ∀ (F : Type) [Field F] [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (E : Type) [Field E] [Algebra F E] [TopologicalSpace E] [IsModuleTopology F E] (c : E →ₐ[F] E) (δ : E) (hE : IsQuad c δ) (ν : Type) [Fintype ν] [DecidableEq ν] (U : Subgroup (UG c (stdJ ν E))), (∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → g ∈ U) → (∀ᶠ g in nhds (1 : UG c (stdJ ν E)), g ∈ sieg c ν → (weyl c ν)⁻¹ * g * weyl c ν ∈ U) → IsOpen (U : Set (UG c (stdJ ν E))) := by
  first | exact @GlobalTheory.KSp.isOpen_of_sieg_of_opp | exact GlobalTheory.KSp.isOpen_of_sieg_of_opp | (intros; apply GlobalTheory.KSp.isOpen_of_sieg_of_opp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerLiftedCocycleImageEqPicardClassStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.KumPic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummerLiftedCocycle_image_eq_picardClass : ∀ (C : Shv ℤ) (qb : C ⟶ Gm) (E : Spc) (L : E ⟶ ofCat (glCat 1)) (a : Cocycle ((chains ℤ).obj E) (sgl C) 1), (∀ (U : Scheme.{0}) (x : Sx E 1 U), ∃ c : Sec C U, Sec.map qb c = unitSec (lineUnit L x) ∧ ev a.1 1 0 (by simp) U x = Sec.map (sglι C) c) → HK.post ℤ _ qb 1 (CohomologyClass.mk (zcomp a (Cocycle.ofHom (resAug C)) (add_zero 1))) = picClass L := by
  first | (exact @GlobalTheory.EtC.KumPic.PostVal.post_eq_picClass) | (exact GlobalTheory.EtC.KumPic.PostVal.post_eq_picClass) | (intros; apply GlobalTheory.EtC.KumPic.PostVal.post_eq_picClass  <;> assumption)
end

