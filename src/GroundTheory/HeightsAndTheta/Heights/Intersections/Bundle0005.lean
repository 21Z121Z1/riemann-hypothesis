import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PRelBaseChange
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial TensorProduct

theorem RelBaseChange.aeval_map {F F' : Type} [Field F] [Field F'] [Algebra F F'] {σ τ : Type}
    (g : σ → MvPolynomial τ F) (p : MvPolynomial σ F) :
    aeval (fun s => MvPolynomial.map (algebraMap F F') (g s)) (MvPolynomial.map (algebraMap F F') p) =
      MvPolynomial.map (algebraMap F F') (aeval g p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p s hp => simp only [map_mul, hp, map_X, aeval_X]

theorem RelBaseChange.proof : RelBaseChange.Statement := by
  intro F F' _ _ _ σ τ g
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro p hp
    rw [RingHom.mem_ker] at hp
    rw [Ideal.mem_comap, RingHom.mem_ker]
    erw [RelBaseChange.aeval_map g p, hp, map_zero]
  · intro x hx
    rw [RingHom.mem_ker] at hx
    let Φ : MvPolynomial σ F →ₗ[F] MvPolynomial τ F := (aeval g).toLinearMap
    let eσ := MvPolynomial.algebraTensorAlgEquiv (σ := σ) F F'
    let eτ := MvPolynomial.algebraTensorAlgEquiv (σ := τ) F F'
    have key : ∀ y : F' ⊗[F] MvPolynomial σ F,
        eτ (AlgebraTensorModule.lTensor F' F' Φ y) =
          aeval (fun s => MvPolynomial.map (algebraMap F F') (g s)) (eσ y) := by
      intro y
      induction y with
      | zero => simp
      | add y z hy hz => simp only [map_add, hy, hz]
      | tmul a p =>
        simp only [AlgebraTensorModule.lTensor_tmul, eσ, eτ, algebraTensorAlgEquiv_tmul, map_smul,
          RelBaseChange.aeval_map, Φ, AlgHom.toLinearMap_apply]
    have hy : eσ.symm x ∈ LinearMap.ker (AlgebraTensorModule.lTensor F' F' Φ) := by
      rw [LinearMap.mem_ker]
      apply eτ.injective
      rw [key, AlgEquiv.apply_symm_apply, hx, map_zero]
    rw [Module.Flat.ker_lTensor_eq] at hy
    obtain ⟨z, hz⟩ := hy
    have hx' : x = eσ (AlgebraTensorModule.lTensor F' F' (LinearMap.ker Φ).subtype z) := by
      rw [hz, AlgEquiv.apply_symm_apply]
    rw [hx']
    clear hz hx'
    induction z with
    | zero => simp
    | add y z hy hz => rw [map_add, map_add]; exact Ideal.add_mem _ hy hz
    | tmul a k =>
      simp only [AlgebraTensorModule.lTensor_tmul, Submodule.coe_subtype, eσ,
        algebraTensorAlgEquiv_tmul, MvPolynomial.smul_eq_C_mul]
      refine Ideal.mul_mem_left _ _ (Ideal.mem_map_of_mem _ ?_)
      rw [RingHom.mem_ker]
      exact k.2

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PTrdegAdjoinFrac
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

theorem TrdegAdjoinFrac.proof : TrdegAdjoinFrac.Statement := by
  intro D _ _ _ E _ _ _ _ s hinj
  set A := Algebra.adjoin ℤ
    (Set.range (fun d : D => algebraMap (FractionRing D) E (algebraMap D (FractionRing D) d)) ∪ s) with hA
  set B := Algebra.adjoin (FractionRing D) s with hB
  have hmem : ∀ c : D, algebraMap (FractionRing D) E (algebraMap D (FractionRing D) c) ∈ A :=
    fun c => Algebra.subset_adjoin (Or.inl ⟨c, rfl⟩)
  have hs : ∀ x ∈ s, x ∈ A := fun x hx => Algebra.subset_adjoin (Or.inr hx)
  have hAB : ∀ x ∈ A, x ∈ B := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨d, rfl⟩ | hy
      · exact B.algebraMap_mem _
      · exact Algebra.subset_adjoin hy
    | algebraMap n => rw [eq_intCast]; exact intCast_mem B n
    | add y z _ _ hy hz => exact B.add_mem hy hz
    | mul y z _ _ hy hz => exact B.mul_mem hy hz

  have key : ∀ x ∈ B, ∃ d : D, d ≠ 0 ∧
      algebraMap (FractionRing D) E (algebraMap D (FractionRing D) d) * x ∈ A := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact ⟨1, one_ne_zero, by simpa using hs x hx⟩
    | algebraMap r =>
      obtain ⟨⟨a, m⟩, h⟩ := IsLocalization.surj (nonZeroDivisors D) r
      refine ⟨m, nonZeroDivisors.ne_zero m.2, ?_⟩
      rw [← map_mul, mul_comm, h]
      exact hmem a
    | add x y _ _ hx hy =>
      obtain ⟨d, hd, hdx⟩ := hx
      obtain ⟨e, he, hey⟩ := hy
      refine ⟨d * e, mul_ne_zero hd he, ?_⟩
      have : algebraMap (FractionRing D) E (algebraMap D (FractionRing D) (d * e)) * (x + y) =
          algebraMap (FractionRing D) E (algebraMap D (FractionRing D) e) *
              (algebraMap (FractionRing D) E (algebraMap D (FractionRing D) d) * x) +
            algebraMap (FractionRing D) E (algebraMap D (FractionRing D) d) *
              (algebraMap (FractionRing D) E (algebraMap D (FractionRing D) e) * y) := by
        simp only [map_mul]; ring
      rw [this]
      exact A.add_mem (A.mul_mem (hmem e) hdx) (A.mul_mem (hmem d) hey)
    | mul x y _ _ hx hy =>
      obtain ⟨d, hd, hdx⟩ := hx
      obtain ⟨e, he, hey⟩ := hy
      refine ⟨d * e, mul_ne_zero hd he, ?_⟩
      have : algebraMap (FractionRing D) E (algebraMap D (FractionRing D) (d * e)) * (x * y) =
          (algebraMap (FractionRing D) E (algebraMap D (FractionRing D) d) * x) *
            (algebraMap (FractionRing D) E (algebraMap D (FractionRing D) e) * y) := by
        simp only [map_mul]; ring
      rw [this]
      exact A.mul_mem hdx hey

  have hZD : @FaithfulSMul ℤ D Algebra.toSMul := (faithfulSMul_iff_algebraMap_injective ℤ D).2 hinj
  have tZDΦ : @IsScalarTower ℤ D (FractionRing D) Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have h1 : Algebra.trdeg ℤ D = Algebra.trdeg ℤ (FractionRing D) := by
    have e := trdeg_add_eq ℤ D (A := FractionRing D)
    have := IsLocalization.isAlgebraic (FractionRing D) (nonZeroDivisors D)
    rw [trdeg_eq_zero (R := D) (A := FractionRing D), add_zero] at e
    exact e

  have : FaithfulSMul (FractionRing D) B :=
    (faithfulSMul_iff_algebraMap_injective (FractionRing D) B).2 (algebraMap (FractionRing D) B).injective
  have hZΦ : @FaithfulSMul ℤ (FractionRing D) Algebra.toSMul := by
    refine (faithfulSMul_iff_algebraMap_injective ℤ (FractionRing D)).2 ?_
    have : algebraMap ℤ (FractionRing D) = (algebraMap D (FractionRing D)).comp (algebraMap ℤ D) :=
      RingHom.ext_int _ _
    rw [this]
    exact (IsFractionRing.injective D (FractionRing D)).comp hinj
  have tZΦB : @IsScalarTower ℤ (FractionRing D) B Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have h2 : Algebra.trdeg ℤ (FractionRing D) + Algebra.trdeg (FractionRing D) B = Algebra.trdeg ℤ B :=
    trdeg_add_eq ℤ (FractionRing D) (A := B)

  let f : A →+* B :=
    { toFun := fun a => ⟨a, hAB a a.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let : Algebra A B := f.toAlgebra
  have tZAB : @IsScalarTower ℤ A B Algebra.toSMul Algebra.toSMul Algebra.toSMul :=
    IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  have hZE : Function.Injective (algebraMap ℤ E) := by
    have : algebraMap ℤ E = ((algebraMap (FractionRing D) E).comp
        (algebraMap D (FractionRing D))).comp (algebraMap ℤ D) := RingHom.ext_int _ _
    rw [this]
    exact (algebraMap (FractionRing D) E).injective.comp
      ((IsFractionRing.injective D (FractionRing D)).comp hinj)
  have hZA : @FaithfulSMul ℤ A Algebra.toSMul := by
    refine (faithfulSMul_iff_algebraMap_injective ℤ A).2 ?_
    intro m n hmn
    exact hZE (congrArg (fun a : A => (a : E)) hmn)
  have : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2 (by
    intro a b h
    exact Subtype.ext (congrArg Subtype.val h :))
  have : Algebra.IsAlgebraic A B := by
    refine ⟨fun z => ?_⟩
    obtain ⟨d, hd, hdz⟩ := key z z.2
    have hne : algebraMap (FractionRing D) E (algebraMap D (FractionRing D) d) ≠ 0 := by
      rw [map_ne_zero_iff _ (algebraMap (FractionRing D) E).injective,
        map_ne_zero_iff _ (IsFractionRing.injective D (FractionRing D))]
      exact hd
    have hy : algebraMap A B ⟨_, hmem d⟩ ∈ nonZeroDivisors B := by
      refine mem_nonZeroDivisors_of_ne_zero ?_
      intro h0
      exact hne (congrArg Subtype.val h0 :)
    refine IsAlgebraic.of_mul hy (isAlgebraic_algebraMap _) ?_
    have : algebraMap A B ⟨_, hmem d⟩ * z = algebraMap A B ⟨_, hdz⟩ := Subtype.ext rfl
    rw [this]
    exact isAlgebraic_algebraMap _
  have h3 : Algebra.trdeg ℤ A = Algebra.trdeg ℤ B := by
    have e := trdeg_add_eq ℤ A (A := B)
    rw [trdeg_eq_zero (R := A) (A := B), add_zero] at e
    exact e
  rw [h3, ← h2, h1]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsFibreLocal
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MeasureTheory MvPolynomial ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

def momentPoly {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (w : Ω → ℝ)
    (Q : MvPolynomial (Fin 3) (Ω → ℝ)) : MvPolynomial (Fin 3) ℝ :=
  ∑ m ∈ Q.support, monomial m (∫ p, w p * coeff m Q p ∂μ)

def dotPoly {Ω : Type*} (n : Ω → S2) : MvPolynomial (Fin 3) (Ω → ℝ) :=
  ∑ i, X i * C (fun p => (n p : E3) i)

def fibreMomentPoly (k : ℕ) : MvPolynomial (Fin 3) ℝ :=
  momentPoly (sphereMeasure.prod sphereMeasure)
    (fun p : S2 × S2 => (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (p.1 : E3) (p.2 : E3)) / 2))
    (aeval ![dotPoly Prod.fst, dotPoly Prod.snd] (dgPoly k))

def pushMomentPoly (k : ℕ) : MvPolynomial (Fin 3) ℝ :=
  (-(2 * (k : ℝ) - 1)) • momentPoly sphereMeasure (fun _ => 1) (dotPoly id ^ (2 * k - 2))

def FibreLocal.Statement : Prop :=
  (∀ (k : ℕ) (a : E3),
    ∫ n₁ : S2, ∫ n₂ : S2, (1 / 2 : ℝ) * Real.log ((1 - inner ℝ (n₁ : E3) (n₂ : E3)) / 2) *
        eval ![inner ℝ a (n₁ : E3), inner ℝ a (n₂ : E3)] (dgPoly k) ∂sphereMeasure ∂sphereMeasure =
      -kappa k * inner ℝ a a ^ (k - 1)) ∧
  (∀ (k : ℕ) (B : Type) [CommRing B] [Algebra ℝ B] (a : Fin 3 → B),
    aeval a (fibreMomentPoly k) = algebraMap ℝ B (-kappa k) * (∑ i, a i ^ 2) ^ (k - 1)) ∧
  (∀ k : ℕ, 1 ≤ k → ∀ a : E3,
    -(2 * (k : ℝ) - 1) * ∫ n : S2, inner ℝ a (n : E3) ^ (2 * k - 2) ∂sphereMeasure =
      -(inner ℝ a a ^ (k - 1))) ∧
  (∀ k : ℕ, 1 ≤ k → ∀ (B : Type) [CommRing B] [Algebra ℝ B] (a : Fin 3 → B),
    aeval a (pushMomentPoly k) = -(∑ i, a i ^ 2) ^ (k - 1)) ∧
  ∀ k : ℕ, kappa k = (1 / 2) * ∑ j ∈ Finset.range k, (1 : ℝ) / (2 * j + 1)

end

end GroundTheory.Heights₂.Heights.Inter
end

