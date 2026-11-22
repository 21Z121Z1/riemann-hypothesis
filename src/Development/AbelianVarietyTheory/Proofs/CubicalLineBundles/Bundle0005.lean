import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.EigenNorm

variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ)

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_add_left (z z' w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (z + z') w = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w + _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z' w := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, add_dotProduct]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_add_right (z w w' : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z (w + w') = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w + _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w' := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_add, Matrix.mulVec_add, dotProduct_add]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_smul_left (r : ℂ) (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm (r • z) w = r * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, smul_dotProduct, smul_eq_mul]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_smul_right (r : ℂ) (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z (r • w) = starRingEnd ℂ r * _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  rfl

theorem hermForm_sum_left {κ : Type*} (s : Finset κ) (z : κ → Fin g → ℂ) (w : Fin g → ℂ) :
    hermForm Hm (∑ i ∈ s, z i) w = ∑ i ∈ s, hermForm Hm (z i) w := by
  simp [hermForm, sum_dotProduct]

theorem hermForm_sum_right {κ : Type*} (s : Finset κ) (z : Fin g → ℂ) (w : κ → Fin g → ℂ) :
    hermForm Hm z (∑ i ∈ s, w i) = ∑ i ∈ s, hermForm Hm z (w i) := by
  simp [hermForm, star_sum, Matrix.mulVec_sum, dotProduct_sum]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory NumberField in
variable {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) in
theorem _root_.GlobalTheory.EigenNorm.hermForm_conj (hH : Hm.IsHermitian) (z w : Fin g → ℂ) :
    _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm w z = starRingEnd ℂ (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm Hm z w) := by
  simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.hermForm, dotProduct, Matrix.mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h := congrFun (congrFun hH i) j
  simp only [Matrix.conjTranspose_apply] at h
  rw [← h]
  simp [Pi.star_apply, Complex.star_def]
  ring

theorem eq_zero_of_sum_embedding_mul {E : Type} [Field E] [NumberField E] (f : (E →+* ℂ) → ℂ)
    (hf : ∀ s : 𝓞 E, ∑ τ : E →+* ℂ, τ (s : E) * f τ = 0) (τ : E →+* ℂ) : f τ = 0 := by
  have hinj : Function.Injective
      (fun τ : E →+* ℂ => ((τ.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* ℂ) : 𝓞 E →* ℂ)) := by
    intro τ₁ τ₂ h12
    refine IsFractionRing.ringHom_ext (A := 𝓞 E) fun s => ?_
    exact DFunLike.congr_fun h12 s
  have hli := (linearIndependent_monoidHom (𝓞 E) ℂ).comp _ hinj
  refine Fintype.linearIndependent_iff.1 hli f ?_ τ
  funext s
  simpa [mul_comm] using hf s

theorem conj_eq_neg_of_sq {ρ : ℂ} {d : ℕ} (hd : d ≠ 0) (h : ρ ^ 2 = -(d : ℂ)) : starRingEnd ℂ ρ = -ρ := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have h1 := congrArg Complex.re h
  have h2 := congrArg Complex.im h
  simp [pow_two] at h1 h2
  have h3 : ρ.re * ρ.im = 0 := by linarith [mul_comm ρ.re ρ.im]
  have h4 : ρ.re = 0 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact h
    · rw [h] at h1; nlinarith [mul_self_nonneg ρ.re]
  apply Complex.ext <;> simp [h4]

theorem hermForm_eigen :
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian →
  ∀ (L : Type) [AddCommGroup L] [Module (𝓞 E) L] (h : L → L → E) (ρ : ℂ) (c : ℝ) (x : (E →+* ℂ) → L →+ (Fin g → ℂ)),
  ρ ^ 2 = -(H.d : ℂ) → (∀ a b e, h (a + b) e = h a e + h b e) → (∀ (s : 𝓞 E) a e, h (s • a) e = s * h a e) →
  (∀ a b, h b a = IsCMField.complexConj E (h a b)) →
  (∀ τ (s : 𝓞 E) a, x τ (s • a) = τ (s : E) • x τ a) → (∀ τ, τ (H.rt : E) ≠ ρ → x τ = 0) →
  (∀ a, hermForm Hm (∑ τ, x τ a) (∑ τ, x τ a) = c * ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = ρ), τ (h a a)) →
  ∀ τ τ' a b, τ (H.rt : E) = ρ → hermForm Hm (x τ a) (x τ' b) = open Classical in if τ' = τ then c * τ (h a b) else 0 := by
  intro E _ _ _ H g Hm hH L _ _ h ρ c x hρ hadd hsmul hsymm hx hx0 hq τ τ' a b hτ
  classical
  have hd : H.d ≠ 0 := H.d_prime.ne_zero
  have hρc := conj_eq_neg_of_sq hd hρ
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    apply hd
    have : (H.d : ℂ) = 0 := by simpa using hρ.symm
    exact_mod_cast this
  have hconj : ∀ (σ : E →+* ℂ) a b, σ (h b a) = starRingEnd ℂ (σ (h a b)) := fun σ a b => by
    rw [hsymm a b, IsCMField.complexEmbedding_complexConj]
  have haddr : ∀ (σ : E →+* ℂ) e a b, σ (h e (a + b)) = σ (h e a) + σ (h e b) := fun σ e a b => by
    rw [hconj σ (a + b) e, hconj σ a e, hconj σ b e, hadd, map_add, map_add]
  have hsmulr : ∀ (σ : E →+* ℂ) (s : 𝓞 E) e a, σ (h e (s • a)) = starRingEnd ℂ (σ s) * σ (h e a) :=
    fun σ s e a => by rw [hconj σ (s • a) e, hconj σ a e, hsmul, map_mul, map_mul]
  set Ψ := Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = ρ) with hΨ
  let D : L → L → ℂ := fun a b =>
    hermForm Hm (∑ τ, x τ a) (∑ τ, x τ b) - c * ∑ τ ∈ Ψ, τ (h a b)
  have hD0 : ∀ a, D a a = 0 := fun a => sub_eq_zero.2 (hq a)
  have hDc : ∀ a b, D b a = starRingEnd ℂ (D a b) := fun a b => by
    simp only [D, map_sub, map_mul, map_sum, Complex.conj_ofReal, ← hconj]
    rw [hermForm_conj Hm hH]
  have hDl : ∀ a b e, D (a + b) e = D a e + D b e := fun a b e => by
    simp only [D, map_add, hadd, Finset.sum_add_distrib, hermForm_add_left]; ring
  have hDr : ∀ e a b, D e (a + b) = D e a + D e b := fun e a b => by
    simp only [D, map_add, haddr, Finset.sum_add_distrib, hermForm_add_right]; ring
  have hDpol : ∀ a b, D a b + starRingEnd ℂ (D a b) = 0 := fun a b => by
    have := hD0 (a + b)
    rw [hDl, hDr, hDr, hD0, hD0, hDc a b] at this
    linear_combination this
  have hDrt : ∀ a b, D (H.rt • a) b = ρ * D a b := fun a b => by
    have h1 : ∑ τ, x τ (H.rt • a) = ρ • ∑ τ, x τ a := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl fun σ _ => ?_
      by_cases hσ : σ (H.rt : E) = ρ
      · rw [hx, hσ]
      · simp [hx0 σ hσ]
    have h2 : ∑ τ ∈ Ψ, τ (h (H.rt • a) b) = ρ * ∑ τ ∈ Ψ, τ (h a b) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun σ hσ => ?_
      rw [hsmul, map_mul, (Finset.mem_filter.1 hσ).2]
    simp only [D]
    rw [h1, h2, hermForm_smul_left]; ring
  have hD : ∀ a b, D a b = 0 := fun a b => by
    have h1 := hDpol a b
    have h2 := hDpol (H.rt • a) b
    rw [hDrt, map_mul, hρc] at h2
    have h3 : ρ * (2 * D a b) = 0 := by linear_combination h2 + ρ * h1
    simpa [hρ0] using h3
  have hstep : ∀ b, hermForm Hm (x τ a) (∑ σ, x σ b) = c * τ (h a b) := fun b => by
    have := eq_zero_of_sum_embedding_mul
      (fun σ : E →+* ℂ => hermForm Hm (x σ a) (∑ σ, x σ b) -
        if σ (H.rt : E) = ρ then (c : ℂ) * σ (h a b) else 0) (fun s => ?_) τ
    · simpa [hτ, sub_eq_zero] using this
    have h1 := hD (s • a) b
    simp only [D, hΨ] at h1
    rw [hermForm_sum_left, Finset.sum_filter, Finset.mul_sum, ← Finset.sum_sub_distrib] at h1
    refine Eq.trans (Finset.sum_congr rfl fun σ _ => ?_) h1
    rw [hx, hermForm_smul_left, hsmul, map_mul]
    split_ifs <;> ring
  have := eq_zero_of_sum_embedding_mul
    (fun σ : E →+* ℂ => starRingEnd ℂ (hermForm Hm (x τ a) (x σ b) -
      if σ = τ then (c : ℂ) * τ (h a b) else 0)) (fun s => ?_) τ'
  · rw [map_eq_zero, sub_eq_zero] at this
    convert this
  have h1 := hstep (s • b)
  rw [hermForm_sum_right, hsmulr] at h1
  simp only [hx, hermForm_smul_right] at h1
  have h2 : ∑ σ : E →+* ℂ, starRingEnd ℂ (σ (s : E)) * (hermForm Hm (x τ a) (x σ b) -
      if σ = τ then (c : ℂ) * τ (h a b) else 0) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib, h1, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have h3 := congrArg (starRingEnd ℂ) h2
  simpa only [map_sum, map_mul, Complex.conj_conj, map_zero] using h3

end GlobalTheory.EigenNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SpecialisationNumberFieldAndCountableValues
section
namespace GlobalTheory

theorem exists_algHom_isAlgebraic_of_finiteType (F A L : Type*) [Field F] [CommRing A]
    [Nontrivial A] [Algebra F A] [Algebra.FiniteType F A] [Field L] [IsAlgClosed L] [Algebra F L] :
    ∃ φ : A →ₐ[F] L, ∀ x, IsAlgebraic F (φ x) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)
  refine ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] L).comp (Ideal.Quotient.mkₐ F m), fun x => ?_⟩
  exact (Algebra.IsAlgebraic.isAlgebraic (R := F) (Ideal.Quotient.mkₐ F m x)).algHom
    (IsAlgClosed.lift : (A ⧸ m) →ₐ[F] L)

theorem _root_.GlobalTheory.exists_ringHom_extend_of_finiteType (F A L : Type*) [Field F] [CommRing A]
    [Nontrivial A] [Algebra F A] [Algebra.FiniteType F A] [Field L] [IsAlgClosed L]
    (σ : F →+* L) : ∃ φ : A →+* L, ∀ x, φ (algebraMap F A x) = σ x := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)
  letI : Algebra F L := σ.toAlgebra
  let ψ : (A ⧸ m) →ₐ[F] L := IsAlgClosed.lift
  refine ⟨ψ.toRingHom.comp (Ideal.Quotient.mk m), fun x => ?_⟩
  have h1 : Ideal.Quotient.mk m (algebraMap F A x) = algebraMap F (A ⧸ m) x := rfl
  simp only [RingHom.comp_apply, h1, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rfl

theorem exists_fg_subalgebra_over {k L : Type*} [Field k] [Field L] [Algebra k L]
    (F : IntermediateField k L) (R : Subalgebra k L) (hR : R.FG) (u : L) :
    ∃ A : Subalgebra F L, Algebra.FiniteType F A ∧ R ≤ A.restrictScalars k ∧ u ∈ A := by
  classical
  obtain ⟨s, rfl⟩ := hR
  refine ⟨Algebra.adjoin F (↑(insert u s) : Set L), ?_, ?_, ?_⟩
  · exact (Subalgebra.fg_iff_finiteType _).1 ⟨_, rfl⟩
  · refine Algebra.adjoin_le fun x hx => ?_
    have : x ∈ Algebra.adjoin F (↑(insert u s) : Set L) :=
      Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))
    exact this
  · exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_insert_self _ _))

private lemma exists_algHom_extend_of_fg_ne_zero {k L M : Type*} [Field k] [Field L] [Algebra k L]
    [Field M] [IsAlgClosed M] [Algebra k M] (F : IntermediateField k L) (σ : F →ₐ[k] M)
    (R : Subalgebra k L) (hR : R.FG) (r : R) (hr : r ≠ 0) :
    ∃ ρ : R →ₐ[k] M, (∀ (x : R) (hx : (x : L) ∈ F), ρ x = σ ⟨x, hx⟩) ∧ ρ r ≠ 0 := by
  classical
  obtain ⟨s, hs⟩ := hR
  have hrL : (r : L) ≠ 0 := fun h => hr (Subtype.ext h)
  obtain ⟨A, hA⟩ : ∃ A : Subalgebra F L, A = Algebra.adjoin F ↑(insert ((r : L)⁻¹) s) := ⟨_, rfl⟩
  haveI : Algebra.FiniteType F A :=
    (Subalgebra.fg_iff_finiteType A).1 ⟨insert ((r : L)⁻¹) s, hA.symm⟩
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.exists_ringHom_extend_of_finiteType F A M σ.toRingHom
  have hgen : ∀ y ∈ insert ((r : L)⁻¹) s, y ∈ A := fun y hy => by
    rw [hA]; exact Algebra.subset_adjoin (Finset.mem_coe.2 hy)
  have hle : ∀ x ∈ R, x ∈ A := by
    intro x hx
    rw [← hs] at hx
    have hsub : Algebra.adjoin k (s : Set L) ≤ A.restrictScalars k :=
      Algebra.adjoin_le fun y hy => (Subalgebra.mem_restrictScalars k).2
        (hgen y (Finset.mem_insert_of_mem (Finset.mem_coe.1 hy)))
    exact (Subalgebra.mem_restrictScalars k).1 (hsub hx)
  let ι : R →+* A :=
    { toFun := fun x => ⟨x, hle x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ => Subtype.ext (by simp) }
  have hι : ∀ (x : R) (hx : (x : L) ∈ F), ι x = algebraMap F A ⟨x, hx⟩ :=
    fun _ _ => Subtype.ext rfl
  have hcomm : ∀ a : k, φ (ι (algebraMap k R a)) = algebraMap k M a := by
    intro a
    have h1 : ι (algebraMap k R a) = algebraMap F A (algebraMap k F a) := Subtype.ext (by
      change algebraMap k L a = algebraMap F L (algebraMap k F a)
      exact IsScalarTower.algebraMap_apply k F L a)
    rw [h1, hφ]
    exact σ.commutes a
  refine ⟨{ toRingHom := φ.comp ι, commutes' := hcomm }, fun x hx => ?_, ?_⟩
  · show φ (ι x) = σ ⟨x, hx⟩
    rw [hι x hx, hφ]
    rfl
  · have hinv : ι r * ⟨(r : L)⁻¹, hgen _ (Finset.mem_insert_self _ _)⟩ = 1 :=
      Subtype.ext (by simp [ι, hrL])
    have := congrArg φ hinv
    rw [map_mul, map_one] at this
    exact left_ne_zero_of_mul_eq_one this

theorem _root_.GlobalTheory.exists_specialisation_finite {k L : Type*} [Field k] [Field L]
    [Algebra k L] [IsAlgClosed L] (R : Subalgebra k L) (hR : R.FG) (r : R) (hr : r ≠ 0) :
    ∃ (K₁ : IntermediateField k L) (ρ : R →ₐ[k] K₁), FiniteDimensional k K₁ ∧ ρ r ≠ 0 ∧
      ∀ c : R, IsAlgebraic k c → (ρ c : L) = c := by
  classical
  haveI : IsAlgClosed (algebraicClosure k L) := IsAlgClosure.isAlgClosed k
  obtain ⟨ρ₁, hfix, hr₁⟩ :=
    exists_algHom_extend_of_fg_ne_zero (algebraicClosure k L) (AlgHom.id k _) R hR r hr
  let ρ₀ : R →ₐ[k] L := (algebraicClosure k L).val.comp ρ₁
  have halg : ∀ x : R, IsAlgebraic k (ρ₀ x) := fun x => mem_algebraicClosure_iff.1 (ρ₁ x).2
  haveI : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).1 hR
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := k) (A := R)
  haveI : Finite (ρ₀ '' (t : Set R)) := (t.finite_toSet.image _).to_subtype
  have hfin : FiniteDimensional k (IntermediateField.adjoin k (ρ₀ '' (t : Set R))) :=
    IntermediateField.finiteDimensional_adjoin fun y hy => by
      obtain ⟨x, -, rfl⟩ := hy
      exact (halg x).isIntegral
  have hmem : ∀ x : R, ρ₀ x ∈ IntermediateField.adjoin k (ρ₀ '' (t : Set R)) := by
    intro x
    have hx : x ∈ Algebra.adjoin k (t : Set R) := by rw [ht]; exact Algebra.mem_top
    have h1 : ρ₀ x ∈ Algebra.adjoin k (ρ₀ '' (t : Set R)) := by
      rw [← AlgHom.map_adjoin]; exact ⟨x, hx, rfl⟩
    exact IntermediateField.algebra_adjoin_le_adjoin k _ h1
  refine ⟨IntermediateField.adjoin k (ρ₀ '' (t : Set R)),
    { toFun := fun x => ⟨ρ₀ x, hmem x⟩
      map_one' := Subtype.ext (map_one ρ₀)
      map_mul' := fun x y => Subtype.ext (map_mul ρ₀ x y)
      map_zero' := Subtype.ext (map_zero ρ₀)
      map_add' := fun x y => Subtype.ext (map_add ρ₀ x y)
      commutes' := fun a => Subtype.ext (ρ₀.commutes a) }, hfin, fun h => hr₁ ?_, fun c hc => ?_⟩
  · have h' : ρ₀ r = 0 := congrArg Subtype.val h
    exact Subtype.ext h'
  · have hcL : (c : L) ∈ algebraicClosure k L := mem_algebraicClosure_iff.2 (hc.algHom R.val)
    show ((ρ₁ c : algebraicClosure k L) : L) = c
    rw [hfix c hcL]
    rfl

theorem exists_algHom_apply_eq_of_transcendental {k L : Type*} [Field k] [Field L] [Algebra k L]
    [IsAlgClosed L] (R : Subalgebra k L) (hR : R.FG) (c : R) (hc : Transcendental k (c : L))
    (t : L) (ht : Transcendental k t) : ∃ ρ : R →ₐ[k] L, ρ c = t := by
  let F : IntermediateField k L := IntermediateField.adjoin k {(c : L)}
  let σ : F →ₐ[k] L := (IntermediateField.val _).comp
    ((RatFunc.algEquivOfTranscendental t ht).toAlgHom.comp
      (RatFunc.algEquivOfTranscendental (c : L) hc).symm.toAlgHom)
  have hσ : σ (IntermediateField.AdjoinSimple.gen k (c : L)) = t := by
    change ((RatFunc.algEquivOfTranscendental t ht)
      ((RatFunc.algEquivOfTranscendental (c : L) hc).symm
        (IntermediateField.AdjoinSimple.gen k (c : L))) : L) = t
    rw [RatFunc.algEquivOfTranscendental_symm_gen, RatFunc.algEquivOfTranscendental_X]
  obtain ⟨A, hA, hRA, -⟩ := exists_fg_subalgebra_over F R hR 0
  obtain ⟨φ, hφ⟩ := exists_ringHom_extend_of_finiteType F A L σ.toRingHom
  let ι : R →+* A :=
    { toFun := fun x => ⟨x.1, hRA x.2⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  refine ⟨{ φ.comp ι with commutes' := fun a => ?_ }, ?_⟩
  · exact (hφ (algebraMap k F a)).trans (σ.commutes a)
  · exact (hφ (IntermediateField.AdjoinSimple.gen k (c : L))).trans hσ

theorem _root_.GlobalTheory.specialisation_numberField_and_countable_values :
    ∀ (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (R : Subalgebra k ℂ), R.FG →
    ∀ (c r : R), r ≠ 0 →
    (∃ (K₁ : IntermediateField k ℂ) (ρ : R →ₐ[k] K₁), FiniteDimensional k K₁ ∧ ρ r ≠ 0 ∧
      (IsAlgebraic k c → (ρ c : ℂ) = c)) ∧
    (∀ S : Set ℂ, S.Countable → (∀ ρ : R →ₐ[k] ℂ, ρ c ∈ S) → IsAlgebraic k c) := by
  intro k _ R hR c r hr
  refine ⟨?_, fun S hS hρ => ?_⟩
  · obtain ⟨K₁, ρ, hfin, hr₁, hfix⟩ := _root_.GlobalTheory.exists_specialisation_finite R hR r hr
    exact ⟨K₁, ρ, hfin, hr₁, hfix c⟩
  by_contra hc
  have hct : Transcendental k (c : ℂ) := fun h =>
    hc ((isAlgebraic_algHom_iff R.val Subtype.val_injective).1 h)
  have key : ∀ z : ℂ, Transcendental ℚ z → z ∈ S := by
    intro z hz
    have hzk : Transcendental k z := fun h => hz (h.restrictScalars ℚ)
    let e₁ := RatFunc.algEquivOfTranscendental (c : ℂ) hct
    let e₂ := RatFunc.algEquivOfTranscendental z hzk
    let σ : IntermediateField.adjoin k {(c : ℂ)} →ₐ[k] ℂ :=
      (IntermediateField.adjoin k {z}).val.comp (e₂.toAlgHom.comp e₁.symm.toAlgHom)
    have hcmem : (c : ℂ) ∈ IntermediateField.adjoin k {(c : ℂ)} :=
      IntermediateField.mem_adjoin_simple_self k (c : ℂ)
    have hσ : σ ⟨c, hcmem⟩ = z := by
      have h1 : e₁.symm ⟨c, hcmem⟩ = RatFunc.X := by
        rw [AlgEquiv.symm_apply_eq]
        exact Subtype.ext (RatFunc.algEquivOfTranscendental_X (c : ℂ) hct).symm
      show ((e₂ (e₁.symm ⟨c, hcmem⟩) : IntermediateField.adjoin k {z}) : ℂ) = z
      rw [h1]
      exact RatFunc.algEquivOfTranscendental_X z hzk
    obtain ⟨ρ, hfix, -⟩ :=
      exists_algHom_extend_of_fg_ne_zero (IntermediateField.adjoin k {(c : ℂ)}) σ R hR 1 one_ne_zero
    have h := hρ ρ
    rwa [hfix c hcmem, hσ] at h
  have hcover : (Set.univ : Set ℂ) ⊆ S ∪ {z | IsAlgebraic ℚ z} := fun z _ => by
    by_cases h : IsAlgebraic ℚ z
    · exact Or.inr h
    · exact Or.inl (key z h)
  exact not_countable_complex ((hS.union (Algebraic.countable ℚ ℂ)).mono hcover)

end GlobalTheory
end

