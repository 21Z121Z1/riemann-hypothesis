import Mathlib

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SmithZeroOne
section
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.smith_zero_one :
    ∀ {A : Type} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {F V : Type} [Field F] [Algebra A F] [IsFractionRing A F] [AddCommGroup V] [Module F V] [Module A V] [IsScalarTower A F V] [Module.Finite F V] (ϖ : A) (Y Z : Submodule A V), Irreducible ϖ → Submodule.IsLattice F Z → Y ≤ Z → maximalIdeal A • Z ≤ Y → ∃ (b : Module.Basis (Fin (Module.finrank F V)) F V) (S : Finset (Fin (Module.finrank F V))), Z = Submodule.span A (Set.range b) ∧ Y = Submodule.span A (Set.range fun i => if i ∈ S then ϖ • b i else b i) := by
  intro A _ _ _ F V _ _ _ _ _ _ _ _ ϖ Y Z hϖ hZ hYZ hmY
  classical
  haveI := hZ
  have hfr : Module.finrank A Z = Module.finrank F V := by
    apply Module.finrank_eq_of_rank_eq
    rw [Submodule.IsLattice.rank' F Z, Module.finrank_eq_rank]
  let b0 : Module.Basis (Fin (Module.finrank F V)) A Z := Module.finBasisOfFinrankEq A Z hfr
  let N : Submodule A Z := Y.comap Z.subtype
  have hϖm : ϖ ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
  have hN : ∀ z : Z, ϖ • z ∈ N := fun z => hmY (Submodule.smul_mem_smul hϖm z.2)
  have hrk : Module.finrank A N = Module.finrank A Z := by
    apply le_antisymm (Submodule.finrank_le N)
    let g : Z →ₗ[A] N := (ϖ • LinearMap.id : Z →ₗ[A] Z).codRestrict N (fun z => hN z)
    apply LinearMap.finrank_le_finrank_of_injective (f := g)
    intro x y hxy
    have h1 : ϖ • x = ϖ • y := congrArg Subtype.val hxy
    exact smul_right_injective _ hϖ.ne_zero h1
  obtain ⟨b', a, ab', hab⟩ := Submodule.exists_smith_normal_form_of_rank_eq b0 hrk
  have hdiv : ∀ i, a i ∣ ϖ := by
    intro i
    let x : N := ⟨ϖ • b' i, hN _⟩
    have hx : (x : Z) = ∑ j, (ab'.repr x j * a j) • b' j := by
      have h := congrArg Subtype.val (ab'.sum_repr x)
      rw [← h, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Submodule.coe_smul, hab, mul_smul]
    have := congrArg (fun m => b'.repr m i) hx
    simp [x, Finsupp.single_apply, Finset.sum_apply'] at this
    exact ⟨ab'.repr x i, by rw [this, mul_comm]⟩
  let B := b'.extendOfIsLattice F
  let S : Finset (Fin (Module.finrank F V)) := Finset.univ.filter fun i => ¬ IsUnit (a i)
  refine ⟨B, S, ?_, ?_⟩
  · have h1 : Submodule.map Z.subtype (⊤ : Submodule A Z) = Z := by simp
    rw [← h1, ← b'.span_eq, Submodule.map_span, ← Set.range_comp]
    congr 2
    ext i
    simp [B]
  · have hY : Y = Submodule.map Z.subtype N := by
      rw [Submodule.map_comap_subtype]
      exact (inf_eq_right.2 hYZ).symm
    have hNs : Submodule.map N.subtype (⊤ : Submodule A N) = N := by simp
    have hv : Y = Submodule.span A (Set.range fun i => a i • B i) := by
      rw [hY, ← hNs, ← ab'.span_eq, Submodule.map_span, Submodule.map_span, ← Set.image_comp,
        ← Set.range_comp]
      congr 2
      ext i
      simp [B, hab]
    have hu : ∀ i, ∃ u : Aˣ, a i • B i = (u : A) • (if i ∈ S then ϖ • B i else B i) := by
      intro i
      obtain ⟨c, hc⟩ := hdiv i
      by_cases hai : IsUnit (a i)
      · refine ⟨hai.unit, ?_⟩
        have : i ∉ S := by simp [S, hai]
        simp [this]
      · have hcu : IsUnit c := by
          rcases hϖ.isUnit_or_isUnit hc with h | h
          · exact absurd h hai
          · exact h
        have : i ∈ S := by simp [S, hai]
        refine ⟨hcu.unit⁻¹, ?_⟩
        rw [if_pos this, smul_smul, hc]
        congr 1
        rw [mul_comm (a i) c, ← mul_assoc]
        simp
    rw [hv]
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨u, hu'⟩ := hu i
      show a i • B i ∈ _
      rw [hu']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      obtain ⟨u, hu'⟩ := hu i
      have : (if i ∈ S then ϖ • B i else B i) = ((u⁻¹ : Aˣ) : A) • (a i • B i) := by
        rw [hu', smul_smul]
        simp
      show (if i ∈ S then ϖ • B i else B i) ∈ _
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SqrtOneAdd
section
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.sqrt_one_add :
    ∀ {B : Type} [CommRing B] (I : Ideal B) [HenselianRing B I] (a : B), IsUnit (2 : B) → a - 1 ∈ I → ∃ α : Bˣ, (α : B) ^ 2 = a ∧ (α : B) - 1 ∈ I := by
  intro B _ I _ a h2 ha
  have hmon : (X ^ 2 - C a : B[X]).Monic := by
    apply Polynomial.monic_X_pow_sub_C
    norm_num
  obtain ⟨α, hroot, hα⟩ := HenselianRing.is_henselian (X ^ 2 - C a) hmon 1
    (by
      have : (X ^ 2 - C a : B[X]).eval 1 = -(a - 1) := by simp <;> ring
      rw [this]
      exact I.neg_mem ha)
    (by
      have : (derivative (X ^ 2 - C a : B[X])).eval 1 = 2 := by
        simp only [derivative_sub, derivative_X_pow, derivative_C, eval_sub, eval_mul, eval_C,
          eval_pow, eval_one, eval_zero]
        norm_num
      rw [this]
      exact h2.map _)
  have hu : IsUnit α := by
    have hj := HenselianRing.jac (I := I) hα
    rw [Ideal.mem_jacobson_bot] at hj
    have := hj 1
    simpa using this
  refine ⟨hu.unit, ?_, ?_⟩
  · simp only [IsUnit.unit_spec]
    have := hroot
    simp [Polynomial.IsRoot] at this
    exact sub_eq_zero.mp this
  · simpa using hα
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TopNilDefs
section
noncomputable section

open Filter

namespace UpperTheory.V.AlgebraTools

section TopNil

variable {R M κ : Type} [CommRing R] [AddCommGroup M] [Module R M]

def topNil (I : Ideal R) (T : κ → Module.End R M) : Submodule R M where
  carrier := {m | ∀ i (j : ℕ), ∀ᶠ r : ℕ in atTop, (T i ^ r) m ∈ (I ^ j • ⊤ : Submodule R M)}
  add_mem' ha hb i j := ((ha i j).and (hb i j)).mono fun _ h => by
    rw [map_add]; exact add_mem h.1 h.2
  zero_mem' _ _ := Eventually.of_forall fun _ => by rw [map_zero]; exact zero_mem _
  smul_mem' c _ h i j := (h i j).mono fun _ h => by
    rw [map_smul]; exact Submodule.smul_mem _ c h

theorem mem_topNil {I : Ideal R} {T : κ → Module.End R M} {m : M} :
    m ∈ topNil I T ↔ ∀ i (j : ℕ), ∀ᶠ r : ℕ in atTop, (T i ^ r) m ∈ (I ^ j • ⊤ : Submodule R M) := Iff.rfl

theorem mem_topNil_iff_exists {I : Ideal R} {T : κ → Module.End R M} {m : M} :
    m ∈ topNil I T ↔ ∀ i (j : ℕ), ∃ r : ℕ, (T i ^ r) m ∈ (I ^ j • ⊤ : Submodule R M) := by
  rw [mem_topNil]
  refine forall₂_congr fun i j => ⟨fun h => h.exists, fun ⟨r, hr⟩ => ?_⟩
  filter_upwards [eventually_ge_atTop r] with s hs
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hs
  rw [add_comm r t, pow_add, Module.End.mul_apply]
  have hle : (I ^ j • ⊤ : Submodule R M).map (T i ^ t) ≤ I ^ j • ⊤ := by
    rw [Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top
  exact hle ⟨_, hr, rfl⟩

end TopNil

section Split

open Polynomial

variable {R : Type} [CommRing R] (P : R[X]) (n : ℕ)

def splitIdeal : Ideal (MvPolynomial (Fin n) R) :=
  Ideal.span (Set.range fun k : ℕ =>
    (∏ i : Fin n, (X - C (MvPolynomial.X i : MvPolynomial (Fin n) R)) - P.map MvPolynomial.C).coeff k)

abbrev SplitAlg : Type := MvPolynomial (Fin n) R ⧸ splitIdeal P n

def SplitAlg.root (i : Fin n) : SplitAlg P n := Ideal.Quotient.mk _ (MvPolynomial.X i)

theorem SplitAlg.prod_root :
    ∏ i : Fin n, (X - C (SplitAlg.root P n i)) = P.map (algebraMap R (SplitAlg P n)) := by
  have h2 : (∏ i : Fin n, (X - C (MvPolynomial.X i : MvPolynomial (Fin n) R)) -
      P.map MvPolynomial.C).map (Ideal.Quotient.mk (splitIdeal P n)) = 0 := by
    ext k
    rw [coeff_map, coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.subset_span ⟨k, rfl⟩
  rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, sub_eq_zero] at h2
  simp only [Polynomial.map_sub, map_X, map_C] at h2
  exact h2

def SplitAlg.lift {A : Type} [CommRing A] [Algebra R A] (a : Fin n → A)
    (h : ∏ i : Fin n, (X - C (a i)) = P.map (algebraMap R A)) : SplitAlg P n →ₐ[R] A :=
  Ideal.Quotient.liftₐ _ (MvPolynomial.aeval a) fun x hx => by
    refine (Ideal.span_le (I := RingHom.ker (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] A))).2 ?_ hx
    rintro _ ⟨k, rfl⟩
    have h2 : (∏ i : Fin n, (X - C (MvPolynomial.X i : MvPolynomial (Fin n) R)) - P.map MvPolynomial.C).map
        (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] A).toRingHom = 0 := by
      rw [Polynomial.map_sub, Polynomial.map_prod, Polynomial.map_map, sub_eq_zero]
      have h3 : (MvPolynomial.aeval a : MvPolynomial (Fin n) R →ₐ[R] A).toRingHom.comp MvPolynomial.C =
          algebraMap R A := RingHom.ext fun r => by simp
      rw [h3, ← h]
      simp
    have h4 := congrArg (fun q => q.coeff k) h2
    simp only [coeff_map, coeff_zero] at h4
    exact h4

theorem SplitAlg.lift_root {A : Type} [CommRing A] [Algebra R A] (a : Fin n → A)
    (h : ∏ i : Fin n, (X - C (a i)) = P.map (algebraMap R A)) (i : Fin n) :
    SplitAlg.lift P n a h (SplitAlg.root P n i) = a i := by
  show MvPolynomial.aeval a (MvPolynomial.X i) = a i
  exact MvPolynomial.aeval_X a i

theorem SplitAlg.hom_ext {A : Type} [CommRing A] [Algebra R A] {f g : SplitAlg P n →ₐ[R] A}
    (h : ∀ i, f (SplitAlg.root P n i) = g (SplitAlg.root P n i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  exact h i

end Split

end UpperTheory.V.AlgebraTools
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TriProdZero
section
open Polynomial Matrix IsLocalRing TensorProduct

theorem UpperTheory.V.AlgebraTools.tri_prod_zero :
    ∀ {R : Type} [CommRing R] {n : ℕ} (u : Fin n → Matrix (Fin n) (Fin n) R), (∀ k i j, j < i → u k i j = 0) → (∀ k, u k k k = 0) → (List.ofFn u).prod = 0 := by
  intro R _ n u h1 h2
  have key : ∀ m, m ≤ n → ∀ i j : Fin n, j.val < m →
      ((List.ofFn u).take m).prod i j = 0 := by
    intro m
    induction m with
    | zero => intro _ i j hj; exact absurd hj (Nat.not_lt_zero _)
    | succ m ih =>
      intro hm i j hj
      have hlen : m < (List.ofFn u).length := by
        rw [List.length_ofFn]; omega
      rw [List.prod_take_succ _ _ hlen, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l.val < m
      · rw [ih (by omega) i l hl, zero_mul]
      · have hu : (List.ofFn u)[m] = u ⟨m, by omega⟩ := by
          simp
        rw [hu]
        by_cases hjl : j < l
        · rw [h1 _ _ _ hjl, mul_zero]
        · have hjl' : l.val ≤ j.val := Fin.le_def.mp (not_lt.mp hjl)
          have e1 : l = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
          have e2 : j = ⟨m, by omega⟩ := Fin.ext (by simp; omega)
          rw [e1, e2, h2, mul_zero]
  ext i j
  have := key n le_rfl i j j.isLt
  rw [List.take_of_length_le (by simp)] at this
  simpa using this
end

