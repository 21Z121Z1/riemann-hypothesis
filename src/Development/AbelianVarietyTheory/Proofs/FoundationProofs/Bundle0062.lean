import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0047
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0048

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLatticeAdelicMatrixIntegralTranslate
section
open scoped Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory.AdelicMatLat

variable (E : Type) [Field E] [NumberField E]

def intAdeles : Subring (FiniteAdeleRing (𝓞 E) E) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers E}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem (v.adicCompletionIntegers E)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem (v.adicCompletionIntegers E)
  neg_mem' ha v := neg_mem (ha v)

theorem mem_intAdeles {a : FiniteAdeleRing (𝓞 E) E} :
    a ∈ intAdeles E ↔ ∀ v, a v ∈ v.adicCompletionIntegers E := Iff.rfl

theorem algebraMap_mem_iff (x : E) :
    algebraMap E (FiniteAdeleRing (𝓞 E) E) x ∈ intAdeles E ↔ ∃ r : 𝓞 E, (r : E) = x := by
  rw [mem_intAdeles, ← GlobalTheory.AdLat.mem_adelicIdeal_one_iff_integral,
    GlobalTheory.Idele.algebraMap_mem_adelicIdeal (GlobalTheory.AdLat.one_ne_zero_fracIdeal E),
    FractionalIdeal.mem_one_iff]

theorem exists_nat_denom (x : E) : ∃ d : ℕ, 0 < d ∧ ∃ r : 𝓞 E, (r : E) = d * x := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 E) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
  refine ⟨Ideal.absNorm (Ideal.span {b}), Nat.pos_of_ne_zero ?_, c * a, ?_⟩
  · simpa [Ideal.absNorm_eq_zero_iff] using hb0
  · have h1 : ((Ideal.absNorm (Ideal.span {b}) : ℕ) : E) =
        algebraMap (𝓞 E) E c * algebraMap (𝓞 E) E b := by
      rw [← map_mul, hc, map_natCast]
    have h2 : algebraMap (𝓞 E) E b ≠ 0 := by
      simpa using hb0
    rw [h1]
    change algebraMap (𝓞 E) E (c * a) = _
    rw [map_mul]
    field_simp

theorem exists_nat_mul_mem (a : FiniteAdeleRing (𝓞 E) E) :
    ∃ d : ℕ, 0 < d ∧ (d : FiniteAdeleRing (𝓞 E) E) * a ∈ intAdeles E := by
  obtain ⟨x, b, hb, rfl⟩ := GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul E 1 one_pos a
  obtain ⟨d, hd, r, hr⟩ := exists_nat_denom E x
  refine ⟨d, hd, ?_⟩
  rw [mul_add, one_smul]
  refine add_mem ?_ (mul_mem (natCast_mem _ d) hb)
  rw [← map_natCast (algebraMap E (FiniteAdeleRing (𝓞 E) E)), ← map_mul, algebraMap_mem_iff]
  exact ⟨r, hr⟩

theorem exists_nat_mul_mem_family {ι : Type} [Fintype ι] (a : ι → FiniteAdeleRing (𝓞 E) E) :
    ∃ d : ℕ, 0 < d ∧ ∀ i, (d : FiniteAdeleRing (𝓞 E) E) * a i ∈ intAdeles E := by
  classical
  choose d hd h using fun i => exists_nat_mul_mem E (a i)
  refine ⟨∏ i, d i, Finset.prod_pos fun i _ => hd i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Nat.cast_mul, mul_assoc]
  exact mul_mem (natCast_mem _ _) (h i)

variable {E} {n : ℕ}

def lat (β : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) : Submodule (𝓞 E) (Fin n → E) where
  carrier := {x | ∀ j, ∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β k j ∈ intAdeles E}
  add_mem' {x y} hx hy j := by
    simpa only [Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib] using add_mem (hx j) (hy j)
  zero_mem' j := by simp
  smul_mem' c x hx j := by
    have h : algebraMap E (FiniteAdeleRing (𝓞 E) E) (c : E) ∈ intAdeles E :=
      (algebraMap_mem_iff E _).2 ⟨c, rfl⟩
    have h2 := mul_mem h (hx j)
    rw [Finset.mul_sum] at h2
    convert h2 using 2 with k
    rw [← mul_assoc, ← map_mul]
    rfl

theorem mem_lat {β : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)} {x : Fin n → E} :
    x ∈ lat β ↔
      ∀ j, ∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β k j ∈ intAdeles E := Iff.rfl

theorem span_lat (β : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    Submodule.span E (lat β : Set (Fin n → E)) = ⊤ := by
  classical
  obtain ⟨d, hd, h⟩ := exists_nat_mul_mem_family E (fun p : Fin n × Fin n => β p.1 p.2)
  rw [eq_top_iff, ← (Pi.basisFun E (Fin n)).span_eq, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  have hm : (Pi.single i (d : E) : Fin n → E) ∈ lat β := by
    intro j
    rw [Finset.sum_eq_single i (by intro k _ hk; simp [Pi.single_eq_of_ne hk]) (by simp)]
    simpa using h (i, j)
  have hd' : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have he : Pi.basisFun E (Fin n) i = (d : E)⁻¹ • (Pi.single i (d : E) : Fin n → E) := by
    rw [Pi.basisFun_apply, ← Pi.single_smul, smul_eq_mul, inv_mul_cancel₀ hd']
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span hm)

theorem fg_lat (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) : (lat β.1).FG := by
  classical
  obtain ⟨d, hd, h⟩ := exists_nat_mul_mem_family E (fun p : Fin n × Fin n => β⁻¹.1 p.1 p.2)
  have hd' : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hle : lat β.1 ≤ Submodule.span (𝓞 E)
      (Set.range fun i : Fin n => (Pi.single i (d : E)⁻¹ : Fin n → E)) := by
    intro x hx
    have h1 : ∀ j, ∃ r : 𝓞 E, (r : E) = d * x j := by
      intro j
      rw [← algebraMap_mem_iff]
      have h2 : algebraMap E (FiniteAdeleRing (𝓞 E) E) (d * x j) =
          ∑ l, (∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β.1 k l) *
            ((d : FiniteAdeleRing (𝓞 E) E) * β⁻¹.1 l j) := by
        have h3 : ((fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k)) ᵥ* β.1) ᵥ* β⁻¹.1 =
            fun k => algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) := by
          rw [Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
        rw [map_mul, map_natCast, ← congrFun h3 j]
        simp only [Matrix.vecMul, dotProduct]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun l _ => mul_left_comm _ _ _
      rw [h2]
      exact sum_mem fun l _ => mul_mem (hx l) (h (l, j))
    choose r hr using h1
    have h4 : x = ∑ i, r i • (Pi.single i (d : E)⁻¹ : Fin n → E) := by
      ext j
      rw [Finset.sum_apply, Finset.sum_eq_single j
        (by intro k _ hk; simp [Pi.single_eq_of_ne hk.symm]) (by simp)]
      rw [Pi.smul_apply, Pi.single_eq_same]
      change x j = (r j : E) * (d : E)⁻¹
      rw [hr]
      field_simp
    rw [h4]
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI := isNoetherian_span_of_finite (𝓞 E)
    (Set.finite_range fun i : Fin n => (Pi.single i (d : E)⁻¹ : Fin n → E))
  exact Submodule.FG.of_le_of_isNoetherian hle

theorem isLattice_lat (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) :
    Submodule.IsLattice E (lat β.1) := ⟨fg_lat β, span_lat β.1⟩

theorem inv_mul_mem (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)) (M : ℕ) (δ : GL (Fin n) E)
    (hδ : ∀ x ∈ lat β.1, ∃ y : Fin n → 𝓞 E, (M : E) • x = (fun i => (y i : E)) ᵥ* δ.1)
    (i j : Fin n) :
    (M : FiniteAdeleRing (𝓞 E) E) *
      (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j ∈ intAdeles E := by
  classical
  obtain ⟨d₁, hd₁, h₁⟩ := exists_nat_mul_mem_family E (fun p : Fin n × Fin n => β.1 p.1 p.2)
  obtain ⟨d₂, hd₂, h₂⟩ := exists_nat_mul_mem_family E
    (fun p : Fin n × Fin n => algebraMap E (FiniteAdeleRing (𝓞 E) E) (δ⁻¹.1 p.1 p.2))
  choose x b hb hx using fun k => GlobalTheory.AdLat.exists_eq_algebraMap_add_nsmul E (d₁ * d₂)
    (Nat.mul_pos hd₁ hd₂) (β⁻¹.1 i k)
  have hxl : x ∈ lat β.1 := by
    intro l
    have h3 : ∑ k, algebraMap E (FiniteAdeleRing (𝓞 E) E) (x k) * β.1 k l =
        (β⁻¹.1 * β.1) i l - ∑ k, ((d₂ : FiniteAdeleRing (𝓞 E) E) * b k) *
          ((d₁ : FiniteAdeleRing (𝓞 E) E) * β.1 k l) := by
      rw [Matrix.mul_apply, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hx k, nsmul_eq_mul, Nat.cast_mul]
      ring
    rw [h3, Units.inv_mul]
    refine sub_mem ?_ (sum_mem fun k _ => mul_mem (mul_mem (natCast_mem _ _) (hb k)) (h₁ (k, l)))
    rw [Matrix.one_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  obtain ⟨y, hy⟩ := hδ x hxl
  have h4 : (y j : E) = ∑ k, (M : E) * x k * δ⁻¹.1 k j := by
    have h5 : ((M : E) • x) ᵥ* δ⁻¹.1 = fun i => (y i : E) := by
      rw [hy, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
    rw [← congrFun h5 j]
    rfl
  have h6 : (M : FiniteAdeleRing (𝓞 E) E) *
      (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j =
      algebraMap E (FiniteAdeleRing (𝓞 E) E) (y j : E) +
        ∑ k, ((M : FiniteAdeleRing (𝓞 E) E) * ((d₁ : FiniteAdeleRing (𝓞 E) E) * b k)) *
          ((d₂ : FiniteAdeleRing (𝓞 E) E) *
            algebraMap E (FiniteAdeleRing (𝓞 E) E) (δ⁻¹.1 k j)) := by
    rw [h4, map_sum, Matrix.mul_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hx k, nsmul_eq_mul, Nat.cast_mul, Matrix.map_apply, map_mul, map_mul, map_natCast]
    ring
  rw [h6]
  exact add_mem ((algebraMap_mem_iff E _).2 ⟨y j, rfl⟩) (sum_mem fun k _ =>
    mul_mem (mul_mem (natCast_mem _ _) (mul_mem (natCast_mem _ _) (hb k))) (h₂ (k, j)))

theorem exists_lattice_integral : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (β : GL (Fin n) (FiniteAdeleRing (𝓞 E) E)), ∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ ∧ ∀ (M : ℕ) (δ : GL (Fin n) E), (∀ i, δ.1 i ∈ Λ) → (∀ x ∈ Λ, ∃ y : Fin n → 𝓞 E, (M : E) • x = (fun i => (y i : E)) ᵥ* δ.1) → ∀ (i j : Fin n) (v : HeightOneSpectrum (𝓞 E)), (δ.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E)) * β.1) i j v ∈ v.adicCompletionIntegers E ∧ ((M : FiniteAdeleRing (𝓞 E) E) * (β⁻¹.1 * δ⁻¹.1.map (algebraMap E (FiniteAdeleRing (𝓞 E) E))) i j) v ∈ v.adicCompletionIntegers E := by
  intro E _ _ n β
  refine ⟨lat β.1, isLattice_lat β, fun M δ h1 h2 i j v => ⟨?_, inv_mul_mem β M δ h2 i j v⟩⟩
  rw [Matrix.mul_apply]
  exact h1 i j v

end GlobalTheory.AdelicMatLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMapConstEqOfIsAlgClosed
section
open scoped MatrixGroups
open Polynomial

namespace GlobalTheory.K4

theorem exists_map_const_eq_of_isAlgClosed {Ω L : Type} [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω]
    [Algebra.IsAlgebraic ℚ Ω] [Field L] (i : Ω →+* L) (σ : L →+* L) (c : Ω) : ∃ c' : Ω, σ (i c) = i c' := by
  letI : Algebra Ω L := i.toAlgebra
  obtain ⟨p, hp, h0⟩ : IsIntegral ℚ c := (Algebra.IsAlgebraic.isAlgebraic c).isIntegral
  have e : (σ.comp i).comp (algebraMap ℚ Ω) = i.comp (algebraMap ℚ Ω) := RingHom.ext_rat _ _
  have hint : IsIntegral Ω (σ (i c)) := by
    refine ⟨p.map (algebraMap ℚ Ω), hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    show p.eval₂ (i.comp (algebraMap ℚ Ω)) ((σ.comp i) c) = 0
    rw [← e, ← Polynomial.hom_eval₂, h0, map_zero]
  obtain ⟨c', hc'⟩ := minpoly.mem_range_of_degree_eq_one Ω (σ (i c))
    (IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hint))
  exact ⟨c', hc'.symm⟩

theorem isIntegral_map_of_map_range {R L : Type} [CommRing R] [Field L] [Algebra R L] (σ : L →+* L)
    (h : ∀ r : R, ∃ r' : R, σ (algebraMap R L r) = algebraMap R L r') {x : L} (hx : IsIntegral R x) :
    IsIntegral R (σ x) := by
  obtain ⟨p, hp, h0⟩ := hx
  have hl : p.map (σ.comp (algebraMap R L)) ∈ Polynomial.lifts (algebraMap R L) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    obtain ⟨r', hr'⟩ := h (p.coeff n)
    exact ⟨r', by rw [Polynomial.coeff_map, RingHom.comp_apply, hr']⟩
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl (hp.map _)
  refine ⟨q, hqm, ?_⟩
  rw [← Polynomial.eval_map, hq, Polynomial.eval_map, ← Polynomial.hom_eval₂, h0, map_zero]

theorem map_mem_ringOfIntegers_of_fix_mdl :
    ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra ℚ Ω] [Algebra.IsAlgebraic ℚ Ω] (ε : Ω →+* ℂ)
      (X : GlobalTheory.KZ.Tower Ω ε) (Γ' : Subgroup SL(2, ℤ)) (S : Subgroup (Ω ≃ₐ[ℚ] Ω)),
      letI := GlobalTheory.K4.algPoly X Γ'
      letI := GlobalTheory.K4.algMdl X Γ' S
      ∀ (σ : GlobalTheory.K4.lev X Γ' ≃ₐ[GlobalTheory.K4.mdl X Γ' S] GlobalTheory.K4.lev X Γ') (x : GlobalTheory.K4.lev X Γ'),
        x ∈ FunctionField.ringOfIntegers Ω (GlobalTheory.K4.lev X Γ') →
          σ x ∈ FunctionField.ringOfIntegers Ω (GlobalTheory.K4.lev X Γ') := by
  intro Ω _ _ _ _ ε X Γ' S
  letI := GlobalTheory.K4.algPoly X Γ'
  letI := GlobalTheory.K4.algMdl X Γ' S
  intro σ x hx
  have hj : σ ⟨X.jK, jK_mem_lev X Γ'⟩ = ⟨X.jK, jK_mem_lev X Γ'⟩ :=
    σ.commutes (⟨X.jK, jK_mem_mdl X Γ' S⟩ : mdl X Γ' S)
  have key : ∀ P : Polynomial Ω, ∃ Q : Polynomial Ω, σ (jPoly X Γ' P) = jPoly X Γ' Q := by
    intro P
    induction P using Polynomial.induction_on' with
    | add P P' hP hP' =>
      obtain ⟨Q, hQ⟩ := hP
      obtain ⟨Q', hQ'⟩ := hP'
      exact ⟨Q + Q', by rw [map_add, map_add, hQ, hQ', map_add]⟩
    | monomial n c =>
      obtain ⟨c', hc'⟩ := exists_map_const_eq_of_isAlgClosed (levConst X Γ') (σ : lev X Γ' →+* lev X Γ') c
      refine ⟨Polynomial.monomial n c', ?_⟩
      simp only [jPoly, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_monomial, map_mul, map_pow]
      rw [hj, ← hc']
      rfl
  exact isIntegral_map_of_map_range (R := Polynomial Ω) (σ : lev X Γ' →+* lev X Γ') key hx

end GlobalTheory.K4
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulLinearIndependentAlgebraicOverPadicInte
section
open GlobalTheory.K5

namespace GlobalTheory.K5.ReprInd

theorem aux {R Ω : Type*} [CommRing R] [IsDomain R] [AddCommGroup Ω] [Module R Ω] (P : Ω → Prop) :
    ∀ (m : ℕ) (a : Fin m → Ω) (f : Fin m → R), (∀ i, P (a i)) →
      ∃ (n : ℕ) (a' : Fin n → Ω) (f' : Fin n → R) (g : R), (∀ i, P (a' i)) ∧
        LinearIndependent R a' ∧ g ≠ 0 ∧ g • (∑ i, f i • a i) = ∑ i, f' i • a' i := by
  intro m
  induction m with
  | zero =>
    intro a f _
    refine ⟨0, a, f, 1, by simp, linearIndependent_empty_type, one_ne_zero, by simp⟩
  | succ m ih =>
    intro a f hP
    by_cases hli : LinearIndependent R a
    · exact ⟨m + 1, a, f, 1, hP, hli, one_ne_zero, one_smul _ _⟩
    · obtain ⟨c, hc, k, hk⟩ := Fintype.not_linearIndependent_iff.mp hli
      obtain ⟨n, a', f', g, hP', hli', hg, heq⟩ := ih (fun j => a (k.succAbove j))
        (fun j => c k * f (k.succAbove j) - f k * c (k.succAbove j)) (fun j => hP _)
      refine ⟨n, a', f', g * c k, hP', hli', mul_ne_zero hg hk, ?_⟩
      have key : c k • (∑ i, f i • a i) =
          ∑ j : Fin m, (c k * f (k.succAbove j) - f k * c (k.succAbove j)) • a (k.succAbove j) := by
        have h1 : c k • (∑ i, f i • a i) = c k • (∑ i, f i • a i) - f k • (∑ i, c i • a i) := by
          rw [hc, smul_zero, sub_zero]
        rw [h1, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib,
          Fin.sum_univ_succAbove _ k]
        simp only [smul_smul, ← sub_smul]
        rw [mul_comm (f k) (c k), sub_self, zero_smul, zero_add]
      rw [mul_smul, key, heq]

theorem main {R Ω : Type*} [CommRing R] [IsDomain R] [Field Ω] [Algebra R Ω] (P : Ω → Prop) :
    ∀ y ∈ Submodule.span R {x : Ω | P x},
    ∃ (n : ℕ) (a : Fin n → Ω) (f : Fin n → R) (g : R), (∀ i, P (a i)) ∧
      LinearIndependent R a ∧ g ≠ 0 ∧
      algebraMap R Ω g * y = ∑ i, algebraMap R Ω (f i) * a i := by
  intro y hy
  obtain ⟨m, f, a, rfl⟩ := Submodule.mem_span_set'.mp hy
  obtain ⟨n, a', f', g, hP', hli', hg, heq⟩ := aux P m (fun i => (a i : Ω)) f (fun i => (a i).2)
  refine ⟨n, a', f', g, hP', hli', hg, ?_⟩
  simpa only [Algebra.smul_def] using heq

end GlobalTheory.K5.ReprInd

theorem GlobalTheory.K5.algSpan_reprInd : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ y ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp p x},
    ∃ (n : ℕ) (a : Fin n → Ω) (f : Fin n → O0 p) (g : O0 p), (∀ i, IsAlgZp p (a i)) ∧
      LinearIndependent (O0 p) a ∧ g ≠ 0 ∧
      algebraMap (O0 p) Ω g * y = ∑ i, algebraMap (O0 p) Ω (f i) * a i := by
  intro p _ Ω _ _ _
  exact GlobalTheory.K5.ReprInd.main (fun x => IsAlgZp p x)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMulMemSpanAlgebraicOverPadicIntegers
section
noncomputable section

namespace GlobalTheory.K5.ReprSpan

open Polynomial

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem isAlgZp_one : IsAlgZp p (1 : Ω) :=
  ⟨X - C 1, X_sub_C_ne_zero 1, by simp⟩

theorem isAlgZp_mul {x y : Ω} (hx : IsAlgZp p x) (hy : IsAlgZp p y) : IsAlgZp p (x * y) := by
  letI : Algebra ℤ_[p] Ω := Algebra.compHom Ω (algebraMap ℤ_[p] (O0 p))
  haveI : IsScalarTower ℤ_[p] (O0 p) Ω := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have key : ∀ z : Ω, IsAlgZp p z ↔ IsAlgebraic ℤ_[p] z := fun z => by
    simp only [IsAlgZp, IsAlgebraic, aeval_map_algebraMap]
  rw [key] at hx hy ⊢
  exact hx.mul hy

variable (p Ω) in

def algZpMonoid : Submonoid Ω where
  carrier := {x | IsAlgZp p x}
  one_mem' := isAlgZp_one
  mul_mem' := isAlgZp_mul

theorem mem_adjoin_iff (z : Ω) :
    z ∈ Algebra.adjoin (O0 p) {x : Ω | IsAlgZp p x} ↔
      z ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp p x} := by
  rw [← Subalgebra.mem_toSubmodule, Algebra.adjoin_eq_span]
  have hcl : (Submonoid.closure {x : Ω | IsAlgZp p x} : Set Ω) = {x | IsAlgZp p x} := by
    rw [show {x : Ω | IsAlgZp p x} = (algZpMonoid p Ω : Set Ω) from rfl, Submonoid.closure_eq]
  rw [hcl]

theorem exists_mul_mem_span : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω →
    ∀ b ∈ Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x}),
    ∃ g : O0 p, g ≠ 0 ∧ algebraMap (O0 p) Ω g * b ∈ Submodule.span (O0 p) {x : Ω | IsAlgZp p x} := by
  intro p _ Ω _ _ h b hb
  set B := Algebra.adjoin (O0 p) {x : Ω | IsAlgZp p x} with hBdef
  let S : Subfield Ω :=
    { carrier := {b | ∃ g : O0 p, g ≠ 0 ∧ algebraMap (O0 p) Ω g * b ∈ B}
      zero_mem' := ⟨1, one_ne_zero, by rw [mul_zero]; exact B.zero_mem⟩
      one_mem' := ⟨1, one_ne_zero, by rw [map_one, mul_one]; exact B.one_mem⟩
      add_mem' := by
        rintro a c ⟨g, hg, ha⟩ ⟨g', hg', hc⟩
        refine ⟨g * g', mul_ne_zero hg hg', ?_⟩
        have e : algebraMap (O0 p) Ω (g * g') * (a + c) =
            algebraMap (O0 p) Ω g' * (algebraMap (O0 p) Ω g * a) +
              algebraMap (O0 p) Ω g * (algebraMap (O0 p) Ω g' * c) := by
          rw [map_mul]; ring
        rw [e]
        exact B.add_mem (B.mul_mem (B.algebraMap_mem _) ha) (B.mul_mem (B.algebraMap_mem _) hc)
      mul_mem' := by
        rintro a c ⟨g, hg, ha⟩ ⟨g', hg', hc⟩
        refine ⟨g * g', mul_ne_zero hg hg', ?_⟩
        have e : algebraMap (O0 p) Ω (g * g') * (a * c) =
            (algebraMap (O0 p) Ω g * a) * (algebraMap (O0 p) Ω g' * c) := by
          rw [map_mul]; ring
        rw [e]
        exact B.mul_mem ha hc
      neg_mem' := by
        rintro a ⟨g, hg, ha⟩
        exact ⟨g, hg, by rw [mul_neg]; exact B.neg_mem ha⟩
      inv_mem' := by
        rintro a ⟨g, hg, ha⟩
        by_cases ha0 : a = 0
        · exact ⟨1, one_ne_zero, by rw [ha0, inv_zero, mul_zero]; exact B.zero_mem⟩
        have hg0 : algebraMap (O0 p) Ω g ≠ 0 := fun e => hg (h.inj (by rw [e, map_zero]))
        have hy0 : algebraMap (O0 p) Ω g * a ≠ 0 := mul_ne_zero hg0 ha0
        let y : B := ⟨algebraMap (O0 p) Ω g * a, ha⟩
        have halg : IsAlgebraic (O0 p) y :=
          (isAlgebraic_algHom_iff B.val Subtype.val_injective).1 (h.alg.isAlgebraic _)
        have hnz : y ∈ nonZeroDivisors B :=
          mem_nonZeroDivisors_of_ne_zero (fun e => hy0 (congrArg Subtype.val e))
        obtain ⟨r, hr, s, hs⟩ := halg.exists_nonzero_dvd hnz
        have hs' : algebraMap (O0 p) Ω r = algebraMap (O0 p) Ω g * a * (s : Ω) := by
          have := congrArg Subtype.val hs
          simpa [y] using this
        refine ⟨r, hr, ?_⟩
        have e : algebraMap (O0 p) Ω r * a⁻¹ = algebraMap (O0 p) Ω g * (s : Ω) := by
          rw [hs']; field_simp
        show algebraMap (O0 p) Ω r * a⁻¹ ∈ B
        rw [e]
        exact B.mul_mem (B.algebraMap_mem g) s.2 }
  have hle : Subfield.closure (Set.range (algebraMap (O0 p) Ω) ∪ {x | IsAlgZp p x}) ≤ S := by
    rw [Subfield.closure_le]
    rintro x (⟨c, rfl⟩ | hx)
    · exact ⟨1, one_ne_zero, by rw [map_one, one_mul]; exact B.algebraMap_mem c⟩
    · exact ⟨1, one_ne_zero, by rw [map_one, one_mul]; exact Algebra.subset_adjoin hx⟩
  obtain ⟨g, hg, hgb⟩ := hle hb
  exact ⟨g, hg, (mem_adjoin_iff _).1 hgb⟩

end GlobalTheory.K5.ReprSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FactorialLeTwoMulCardPermWithFixedPoint
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

theorem two_mul_numDerangements_succ_le (n : ℕ) :
    2 * numDerangements (n + 1) ≤ (n + 1).factorial := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simp [numDerangements]
  | more n h1 h2 =>
    have e : numDerangements (n + 2 + 1)
        = (n + 1 + 1) * (numDerangements (n + 1) + numDerangements (n + 1 + 1)) :=
      numDerangements_add_two (n + 1)
    have f1 : (n + 2 + 1).factorial = (n + 2 + 1) * (n + 1 + 1).factorial :=
      Nat.factorial_succ _
    have f2 : (n + 1 + 1).factorial = (n + 1 + 1) * (n + 1).factorial :=
      Nat.factorial_succ _
    rw [e, f1]
    have := Nat.mul_le_mul_left (n + 1 + 1) (Nat.add_le_add h1 h2)
    nlinarith

theorem factorial_le_two_mul_card_perm_fixed :
    ∀ (α : Type) [Fintype α] [DecidableEq α], Nonempty α →
      (Fintype.card α).factorial ≤
        2 * (Finset.univ.filter fun σ : Equiv.Perm α => ∃ i, σ i = i).card := by
  intro α _ _ hne
  have hsum := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Equiv.Perm α)))
    (fun σ : Equiv.Perm α => ∃ i, σ i = i)
  rw [Finset.card_univ, Fintype.card_perm] at hsum
  have hd : (Finset.univ.filter fun σ : Equiv.Perm α => ¬ ∃ i, σ i = i).card
      = numDerangements (Fintype.card α) := by
    rw [← card_derangements_eq_numDerangements α, ← Fintype.card_subtype]
    refine Fintype.card_congr (Equiv.subtypeEquivRight fun σ => ?_)
    simp [derangements]
  obtain ⟨n, hn⟩ : ∃ n, Fintype.card α = n + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  have h := two_mul_numDerangements_succ_le n
  rw [← hn] at h
  omega

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteDimensionalOfGammaLe
section
open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem finiteDimensional_of_Gamma_le :
    ∀ (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (k : ℤ), 0 < M → CongruenceSubgroup.Gamma M ≤ Γ →
      FiniteDimensional ℂ (ModularForm Γ k) ∧ FiniteDimensional ℂ (CuspForm Γ k) := by
  intro M Γ k hM hle
  exact GlobalTheory.HeckeFamilyMatrices.finiteDimensional_modularForm_cuspForm Γ k (finiteIndex_of_Gamma_le hM hle)

end GlobalTheory.OddFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankCocycleExtensionLeOrderThreeRelationAddStatement
section
open GlobalTheory.HeckeFamilyMatrices.CocBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_cocycleExtension_le_orderThreeRelation_add : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s t : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → s ^ 2 = t ^ 3 → Subgroup.closure ({s, t} : Set G) = ⊤ → FiniteDimensional ℂ E → FiniteDimensional ℂ (relThree Γ ρ t) → FiniteDimensional ℂ (extn Γ ρ s) ∧ Module.finrank ℂ (extn Γ ρ s) ≤ Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ E := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_extn_le | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_extn_le | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_extn_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankCocyclesAddTwistedInvariantLeExtensionStatement
section
open GlobalTheory.HeckeFamilyMatrices.CocBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_cocycles_add_twistedInvariant_le_extension : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (s : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → s ^ 4 = 1 → FiniteDimensional ℂ (extn Γ ρ s) → FiniteDimensional ℂ (cocyc Γ ρ) ∧ Module.finrank ℂ (cocyc Γ ρ) + Module.finrank ℂ (twInv Γ s (ρ s)) ≤ Module.finrank ℂ (extn Γ ρ s) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_cocyc_add_twInv_le_extn | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_cocyc_add_twInv_le_extn | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_cocyc_add_twInv_le_extn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankOrderThreeRelationAddTwistedInvariantLeStatement
section
open GlobalTheory.HeckeFamilyMatrices.CocBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_orderThreeRelation_add_twistedInvariant_le : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (ρ : G → E →ₗ[ℂ] E) (t : G), (∀ g h v, ρ (g * h) v = ρ h (ρ g v)) → (∀ v, ρ 1 v = v) → t ^ 6 = 1 → FiniteDimensional ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) → FiniteDimensional ℂ (relThree Γ ρ t) ∧ Module.finrank ℂ (relThree Γ ρ t) + Module.finrank ℂ (twInv Γ t (ρ t)) ≤ Module.finrank ℂ (twInv Γ (t ^ 3) (ρ (t ^ 3))) := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_relThree_add_finrank_twInv_le | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_relThree_add_finrank_twInv_le | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_relThree_add_finrank_twInv_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinrankTwistedLeftInvariantMulOfFreeActionStatement
section
open GlobalTheory.HeckeFamilyMatrices.CocBound
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_twistedLeftInvariant_mul_of_free_action : ∀ {G : Type} [Group G] {E : Type} [AddCommGroup E] [Module ℂ E] (Γ : Subgroup G) (g : G) (A : E →ₗ[ℂ] E) (m : ℕ), Γ.FiniteIndex → FiniteDimensional ℂ E → 0 < m → g ^ m = 1 → A ^ m = 1 → (∀ (x : G) (k : ℕ), 0 < k → k < m → x * g ^ k * x⁻¹ ∉ Γ) → FiniteDimensional ℂ (twInv Γ g A) ∧ Module.finrank ℂ (twInv Γ g A) * m = Γ.index * Module.finrank ℂ E := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free | exact GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free | (intros; apply GlobalTheory.HeckeFamilyMatrices.CocBound.finrank_twInv_mul_of_free <;> assumption)
end

