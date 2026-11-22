import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagForms
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0010
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.InhDivCycleOfSuppEmpty
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0026
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PDiagRelevant
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI

noncomputable section

namespace DiagonalRelevant

theorem X_mem_ker_iff {K : Type} {ι : K → Type} {Φ : Type} [Field Φ] (c : (Σ k, ι k) → Φ)
    (p : Σ k, ι k) :
    (X p : MvPolynomial (Σ k, ι k) ℤ) ∈ RingHom.ker (T.multiConeMap c) ↔ c p = 0 := by
  rw [RingHom.mem_ker]
  unfold T.multiConeMap
  rw [eval₂Hom_X', mul_eq_zero, C_eq_zero]
  simp [X_ne_zero]

theorem lineVal_ne_zero {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {Φ : Type} [Field Φ]
    [Algebra Ω Φ] (e : Module.Basis (Fin 2) Ω E) {ψ : E →ₗ[Ω] Ω} (hψ : ψ ≠ 0) {a : Φ}
    (ha : Transcendental Ω a) : T.lineVal e ψ a ≠ 0 := by
  intro h
  unfold T.lineVal at h
  by_cases h1 : ψ (e 1) = 0
  · apply hψ
    refine e.ext fun q => ?_
    fin_cases q
    · simp only [h1, map_zero, mul_zero, add_zero] at h
      simpa using (map_eq_zero_iff _ (algebraMap Ω Φ).injective).1 h
    · simpa using h1
  · apply ha
    have h1' : algebraMap Ω Φ (ψ (e 1)) ≠ 0 := (map_ne_zero _).2 h1
    have : a = algebraMap Ω Φ (-(ψ (e 0)) / ψ (e 1)) := by
      rw [map_div₀, map_neg, eq_div_iff h1']
      linear_combination h
    rw [this]
    exact isAlgebraic_algebraMap _

end DiagonalRelevant

open DiagonalRelevant DiagonalForms in

theorem DiagRelevant.proof : DiagRelevant.Statement := by
  intro Ω _ ι ν κ _ _ _ E _ _ Φ _ _ x B e φ δ _ hgen hdet ⟨i, hi⟩ a ha
  have hmap : ∀ y : Ω, y ≠ 0 → algebraMap Ω Φ y ≠ 0 := fun y hy => (map_ne_zero _).2 hy
  obtain ⟨u, hu, w, hw, huw⟩ := exists_detE_ne B i hi e
  obtain ⟨l, hl⟩ : ∃ l, δ l ≠ 0 := by
    by_contra! h
    exact huw ((Submodule.mem_bot _).1 ((Submodule.span_le (p := ⊥)).2
      (by rintro _ ⟨l, rfl⟩; simp [h l]) ((hdet i hi).2 u hu w hw)))
  obtain ⟨ψ₀, hψ₀, ψ₁, -, hne⟩ := exists_dual_pair B i hi e
  obtain ⟨k, hk⟩ : ∃ k, φ k ≠ 0 := by
    by_contra! h
    obtain ⟨c, -, hc⟩ := hgen i hi ψ₀ hψ₀
    exact hne (by simp [hc, h])
  have hv : T.lineVal e (φ k) (a 0) ≠ 0 := lineVal_ne_zero e hk (ha.transcendental 0)
  intro blk
  cases blk with
  | base => exact ⟨i, fun h => hmap _ hi ((X_mem_ker_iff _ _).1 h)⟩
  | det => exact ⟨l, fun h => hmap _ hl ((X_mem_ker_iff _ _).1 h)⟩
  | line0 => exact ⟨k, fun h => hv ((X_mem_ker_iff _ _).1 h)⟩
  | line1 => exact ⟨k, fun h => hv ((X_mem_ker_iff _ _).1 h)⟩

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagFibre
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Linear

variable {K : Type} {ι : K → Type} {N1 n : ℕ}

def flagFibreBlocksEquiv : FibreBlock (Sum.inl : K → K ⊕ Fin (n - 1)) ≃ Fin (n - 1) where
  toFun k := match k with
    | ⟨.inl k, h⟩ => (h ⟨k, rfl⟩).elim
    | ⟨.inr j, _⟩ => j
  invFun j := ⟨.inr j, by rintro ⟨k, hk⟩; cases hk⟩
  left_inv k := by
    match k with
    | ⟨.inl k, h⟩ => exact (h ⟨k, rfl⟩).elim
    | ⟨.inr j, _⟩ => rfl
  right_inv _ := rfl

def flagCompound {F : Type} [Field F] (B : Matrix (Fin n) (Fin N1) F) :
    ∀ k : FibreBlock (Sum.inl : K → K ⊕ Fin (n - 1)),
      fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl k → PluckerBlocks n n (flagFibreBlocksEquiv k) → F
  | ⟨.inl k, h⟩ => (h ⟨k, rfl⟩).elim
  | ⟨.inr _, _⟩ => fun S S' => (B.submatrix (S'.1.orderEmbOfFin S'.2) (S.1.orderEmbOfFin S.2)).det

theorem fibreDeg_flag (a : K ⊕ Fin (n - 1) → ℤ) :
    fibreDeg Sum.inl a = (fun j => a (Sum.inr j)) ∘ (flagFibreBlocksEquiv (K := K) (n := n)) := by
  funext k
  match k with
  | ⟨.inl k, h⟩ => exact (h ⟨k, rfl⟩).elim
  | ⟨.inr _, _⟩ => rfl

theorem flagMinor_mul {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (B' : Matrix (Fin n) (Fin N1) R)
    (j : Fin (n - 1)) (S : PluckerBlocks N1 n j) :
    flagMinor (M * B') j S = ∑ S' : PluckerBlocks n n j,
      flagMinor M j S' * (B'.submatrix (S'.1.orderEmbOfFin S'.2) (S.1.orderEmbOfFin S.2)).det := by
  unfold flagMinor
  rw [Matrix.submatrix_mul M B' _ id _ Function.bijective_id, CauchyBinet.proof]
  rfl

end Linear

section Compound

variable {F : Type} [Field F] {N1 n : ℕ}

theorem exists_mul_eq_one (B : Matrix (Fin n) (Fin N1) F) (hB : LinearIndependent F B.row) :
    ∃ C : Matrix (Fin N1) (Fin n) F, B * C = 1 := by
  have hinj : Function.Injective (Matrix.vecMulLinear B) := Matrix.vecMul_injective_iff.2 hB
  obtain ⟨g, hg⟩ := (Matrix.vecMulLinear B).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 hinj)
  refine ⟨Matrix.of fun c b => g (Pi.single c 1) b, ?_⟩
  ext i b
  have hrow : Matrix.vecMulLinear B (Pi.single i 1) = B i := by
    ext c
    simp [Matrix.vecMul, dotProduct, Pi.single_apply]
  have h1 := LinearMap.congr_fun hg (Pi.single i 1)
  rw [LinearMap.comp_apply, hrow, LinearMap.id_apply] at h1
  have h2 : ∑ c, B i c • (Pi.single c 1 : Fin N1 → F) = B i := by
    ext x
    simp [Finset.sum_apply, Pi.single_apply]
  calc (B * Matrix.of fun c b => g (Pi.single c 1) b) i b = ∑ c, B i c * g (Pi.single c 1) b := by
        simp [Matrix.mul_apply]
    _ = g (B i) b := by
        conv_rhs => rw [← h2]
        simp [map_sum, Finset.sum_apply, map_smul]
    _ = (1 : Matrix (Fin n) (Fin n) F) i b := by
        rw [h1, Matrix.one_apply, Pi.single_apply]
        exact if_congr eq_comm rfl rfl

theorem det_one_submatrix {m : ℕ} (S' S'' : {S : Finset (Fin n) // S.card = m}) :
    ((1 : Matrix (Fin n) (Fin n) F).submatrix (S'.1.orderEmbOfFin S'.2) (S''.1.orderEmbOfFin S''.2)).det =
      if S' = S'' then 1 else 0 := by
  split_ifs with h
  · subst h
    rw [Matrix.submatrix_one _ (S'.1.orderEmbOfFin S'.2).injective, Matrix.det_one]
  · have hsub : ¬ S'.1 ⊆ S''.1 := fun hs =>
      h (Subtype.ext (Finset.eq_of_subset_of_card_le hs (by rw [S'.2, S''.2])))
    obtain ⟨x, hx, hx'⟩ := Finset.not_subset.1 hsub
    have hr : x ∈ Set.range (S'.1.orderEmbOfFin S'.2) := by rw [Finset.range_orderEmbOfFin]; exact hx
    obtain ⟨r, hr⟩ := hr
    refine Matrix.det_eq_zero_of_row_eq_zero r fun c => ?_
    rw [Matrix.submatrix_apply, Matrix.one_apply_ne]
    intro he
    apply hx'
    rw [← hr, he]
    exact Finset.orderEmbOfFin_mem _ _ _

theorem compound_mul_eq {m : ℕ} (B : Matrix (Fin n) (Fin N1) F) (C : Matrix (Fin N1) (Fin n) F) (hBC : B * C = 1)
    (S' S'' : {S : Finset (Fin n) // S.card = m}) :
    ∑ S : {S : Finset (Fin N1) // S.card = m},
        (C.submatrix (S.1.orderEmbOfFin S.2) (S''.1.orderEmbOfFin S''.2)).det *
          (B.submatrix (S'.1.orderEmbOfFin S'.2) (S.1.orderEmbOfFin S.2)).det =
      if S' = S'' then 1 else 0 := by
  rw [← det_one_submatrix S' S'', ← hBC,
    Matrix.submatrix_mul B C _ id _ Function.bijective_id, CauchyBinet.proof]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem compound_injective {m : ℕ} (B : Matrix (Fin n) (Fin N1) F) (hB : LinearIndependent F B.row) :
    Function.Injective (Matrix.of fun (S : {S : Finset (Fin N1) // S.card = m})
      (S' : {S : Finset (Fin n) // S.card = m}) =>
        (B.submatrix (S'.1.orderEmbOfFin S'.2) (S.1.orderEmbOfFin S.2)).det).mulVec := by
  obtain ⟨C, hBC⟩ := exists_mul_eq_one B hB
  let D : Matrix {S : Finset (Fin n) // S.card = m} {S : Finset (Fin N1) // S.card = m} F :=
    Matrix.of fun S'' S => (C.submatrix (S.1.orderEmbOfFin S.2) (S''.1.orderEmbOfFin S''.2)).det
  have hD : D * (Matrix.of fun (S : {S : Finset (Fin N1) // S.card = m})
      (S' : {S : Finset (Fin n) // S.card = m}) =>
        (B.submatrix (S'.1.orderEmbOfFin S'.2) (S.1.orderEmbOfFin S.2)).det) = 1 := by
    ext S'' S'
    have hc : (if S'' = S' then (1 : F) else 0) = if S' = S'' then 1 else 0 := if_congr eq_comm rfl rfl
    rw [Matrix.mul_apply, Matrix.one_apply, hc, ← compound_mul_eq B C hBC S' S'']
    rfl
  intro x y hxy
  have := congrArg D.mulVec hxy
  rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hD, Matrix.one_mulVec, Matrix.one_mulVec] at this

theorem flagCompound_injective {K : Type} {ι : K → Type} (B : Matrix (Fin n) (Fin N1) F)
    (hB : LinearIndependent F B.row) (k : FibreBlock (Sum.inl : K → K ⊕ Fin (n - 1))) :
    Function.Injective (Matrix.of (flagCompound (ι := ι) B k)).mulVec := by
  match k with
  | ⟨.inl k, h⟩ => exact (h ⟨k, rfl⟩).elim
  | ⟨.inr j, _⟩ => exact compound_injective (m := j + 1) B hB

end Compound

section Fibre

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {N1 n : ℕ}

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem fibreIdeal_flag (P : Ideal (MRing ι)) [hP : P.IsPrime] (B : Matrix (Fin n) (Fin N1) (FnField P)) :
    fibreIdeal Sum.inl (flagGenFibre P hP B) =
      (flagIdealOver (FnField P) n).comap
        (blockLinSubst (flagFibreBlocksEquiv (K := K)) (flagCompound (ι := ι) B)).toRingHom := by
  show RingHom.ker (aeval (fun q : Σ k : FibreBlock (Sum.inl : K → K ⊕ Fin (n - 1)),
      fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl k =>
        algebraMap (MvPolynomial (Fin n × Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n × Fin n) (FnField P)))
          (flagMap P B (X ⟨q.1.1, q.2⟩))) :
      MRingOver (FnField P) (fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl) →ₐ[FnField P]
        FractionRing (MvPolynomial (Fin n × Fin n) (FnField P))) = _
  have key : ∀ f, aeval (fun q : Σ k : FibreBlock (Sum.inl : K → K ⊕ Fin (n - 1)),
      fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl k =>
        algebraMap (MvPolynomial (Fin n × Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n × Fin n) (FnField P)))
          (flagMap P B (X ⟨q.1.1, q.2⟩))) f =
      algebraMap (MvPolynomial (Fin n × Fin n) (FnField P)) (FractionRing (MvPolynomial (Fin n × Fin n) (FnField P)))
        (aeval (fun q : Σ j, PluckerBlocks n n j => flagMinor (genMat (FnField P) n) q.1 q.2)
          (blockLinSubst (flagFibreBlocksEquiv (K := K)) (flagCompound (ι := ι) B) f)) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a =>
      rw [aeval_C, show (C a : MRingOver (FnField P) (fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl)) =
        algebraMap (FnField P) _ a from rfl, AlgHom.commutes, AlgHom.commutes]
      exact IsScalarTower.algebraMap_apply _ _ _ a
    | add p q hp hq => rw [map_add, hp, hq, map_add, map_add, map_add]
    | mul_X p q hp =>
      rw [map_mul, hp, map_mul, map_mul, map_mul]
      congr 1
      rw [aeval_X, blockLinSubst, aeval_X]
      obtain ⟨⟨k, hk⟩, S⟩ := q
      match k, hk, S with
      | .inl k, h, _ => exact (h ⟨k, rfl⟩).elim
      | .inr j, h, S =>
        congr 1
        rw [flagMap, eval₂Hom_X']
        refine (flagMinor_mul (genMat (FnField P) n) (B.map C) j S).trans ?_
        simp only [map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq]
        refine Finset.sum_congr rfl fun S' _ => ?_
        exact (mul_comm _ _).trans
          (congrArg (· * flagMinor (genMat (FnField P) n) j S') (RingHom.map_det C _).symm)
  ext f
  simp only [flagIdealOver, RingHom.mem_ker, Ideal.mem_comap, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [key, map_eq_zero_iff _ (IsFractionRing.injective _ _)]

omit [Fintype K] [∀ k, Fintype (ι k)] in

theorem charZero_fnField (P : Ideal (MRing ι)) [P.IsPrime] (hP : IsHorizontal P) : CharZero (FnField P) := by
  refine charZero_of_inj_zero fun m hm => ?_
  have h1 : algebraMap (MRing ι ⧸ P) (FnField P) (Ideal.Quotient.mk P (C (m : ℤ))) = 0 := by
    simpa using hm
  rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem] at h1
  have h2 : (m : ℤ) ∈ P.comap (C : ℤ →+* MRing ι) := h1
  rw [hP, Ideal.mem_bot] at h2
  exact_mod_cast h2

theorem map_flagMinor (F F' : Type) [Field F] [Field F'] [Algebra F F'] (j : Fin (n - 1)) (S : PluckerBlocks n n j) :
    MvPolynomial.map (algebraMap F F') (flagMinor (genMat F n) j S) = flagMinor (genMat F' n) j S := by
  unfold flagMinor
  rw [RingHom.map_det]
  congr 1
  ext a b
  simp [genMat]

theorem flagIdealOver_map (hRel : RelBaseChange.Statement) (F F' : Type) [Field F] [Field F'] [Algebra F F'] :
    (flagIdealOver F n).map (MvPolynomial.map (algebraMap F F')) = flagIdealOver F' n := by
  unfold flagIdealOver
  rw [hRel F F']
  simp only [map_flagMinor]

end Fibre

theorem FlagFibre.proof
    (hEU : ∀ (K : Type) [Fintype K] (F : Type) [Field F] (ι : K → Type) [∀ k, Fintype (ι k)],
      ExistsUniqueStatement F ι)
    (hBC : ∀ (K : Type) [Fintype K] (F F' : Type) [Field F] [Field F'] [Algebra F F'] (ι : K → Type)
      [∀ k, Fintype (ι k)], BaseChangeStatement F F' ι)
    (hLin : LinEmbed.Statement) (hDim : FlagDim.Statement) (hRel : RelBaseChange.Statement) :
    FlagFibre.Statement := by
  intro K _ ι _ N1 t n P d c m B hP _ hB J₀ hJ₀
  have : P.IsPrime := hP.2.1.1
  have : CharZero (FnField P) := charZero_fnField P hP.2.2.1
  obtain ⟨J, hJ, -⟩ := hEU _ (FnField P) (fibreIdx (FlagBundleBlocks ι N1 n) Sum.inl)
  obtain ⟨J₁, hJ₁, -⟩ := hEU _ (FnField P) (PluckerBlocks n n)
  refine ⟨J, hJ, fun a => ?_⟩
  have hfib : fibreIdeal Sum.inl (flagGenFibre P hP.2.1.1 B) =
      (flagIdealOver (FnField P) n).comap
        (blockLinSubst (flagFibreBlocksEquiv (K := K)) (flagCompound (ι := ι) B)).toRingHom :=
    fibreIdeal_flag P B
  have hdeg : (fun j => fibreDeg Sum.inl (a j)) =
      fun j => (fun j' => a j (Sum.inr j')) ∘ (flagFibreBlocksEquiv (K := K) (n := n)) :=
    funext fun j => fibreDeg_flag (a j)
  have h1 : J (fibreIdeal Sum.inl (flagGenFibre P hP.2.1.1 B)) (flagDim n) (fun j => fibreDeg Sum.inl (a j)) =
      J₁ (flagIdealOver (FnField P) n) (flagDim n) (fun j j' => a j (Sum.inr j')) := by
    rw [hfib, hdeg]
    exact hLin (FnField P) (Fin (n - 1)) _ (PluckerBlocks n n) _ flagFibreBlocksEquiv (flagCompound B)
      (flagCompound_injective B hB.1) J₁ J hJ₁ hJ _ _ _ (hDim _ n)
  rw [h1]
  have h2 := hBC _ ℚ (FnField P) (PluckerBlocks n n) J₀ J₁ hJ₀ hJ₁ (flagIdealQ n) (flagDim n)
    (fun j j' => a j (Sum.inr j')) (hDim ℚ n)
  have := flagIdealOver_isPrime (FnField P) n
  rw [h2, flagIdealQ_eq, flagIdealOver_map hRel, Ideal.minimalPrimes_eq_subsingleton_self,
    finsum_mem_singleton, inh_multAt_self]
  simp

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagMinorsBaseChange
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

namespace FlagMinorsBaseChange

theorem flagMinor_mul_const_mem {F : Type} [Field F] {σ : Type} {n m p : ℕ}
    (M : Matrix (Fin n) (Fin m) (MvPolynomial σ F)) (D : Matrix (Fin m) (Fin p) F)
    (N : Matrix (Fin n) (Fin p) (MvPolynomial σ F)) (hN : ∀ a b, N a b = ∑ k, M a k * C (D k b))
    (j : Fin (n - 1)) (S : PluckerBlocks p n j) :
    flagMinor N j S ∈
      Algebra.adjoin F (Set.range fun q : Σ j, PluckerBlocks m n j => flagMinor M q.1 q.2) := by
  have hle : (j : ℕ) + 1 ≤ n := by have := j.2; omega
  have hsplit : N.submatrix (Fin.castLE hle) (S.1.orderEmbOfFin S.2) =
      (M.submatrix (Fin.castLE hle) id : Matrix (Fin ((j : ℕ) + 1)) (Fin m) (MvPolynomial σ F)) *
        ((D.map (C : F → MvPolynomial σ F)).submatrix id (S.1.orderEmbOfFin S.2) :
          Matrix (Fin m) (Fin ((j : ℕ) + 1)) (MvPolynomial σ F)) := by
    ext a b
    rw [Matrix.submatrix_apply, hN, Matrix.mul_apply]
    rfl
  unfold flagMinor
  rw [hsplit, GroundTheory.Heights₂.Heights.CauchyBinet.proof]
  refine Subalgebra.sum_mem _ fun I _ => Subalgebra.mul_mem _ ?_ ?_
  · apply Algebra.subset_adjoin
    exact ⟨⟨j, I⟩, rfl⟩
  · have h : rowsOf ((D.map (C : F → MvPolynomial σ F)).submatrix id (S.1.orderEmbOfFin S.2)) I =
        (RingHom.mapMatrix (C : F →+* MvPolynomial σ F))
          (D.submatrix (I.1.orderEmbOfFin I.2) (S.1.orderEmbOfFin S.2)) := by
      ext a b
      rfl
    rw [h, ← RingHom.map_det]
    exact Subalgebra.algebraMap_mem _ _

theorem exists_mul_eq_one {F : Type} [Field F] {n N1 : ℕ} (B : Matrix (Fin n) (Fin N1) F)
    (hB : LinearIndependent F B) : ∃ D : Matrix (Fin N1) (Fin n) F, B * D = 1 := by
  have hinj : Function.Injective B.vecMul := Matrix.vecMul_injective_iff.mpr hB
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective B.vecMulLinear
    (LinearMap.ker_eq_bot.mpr hinj)
  refine ⟨(LinearMap.toMatrix' g).transpose, ?_⟩
  rw [Matrix.ext_iff_vecMul]
  intro v
  rw [← Matrix.vecMul_vecMul, Matrix.vecMul_transpose, LinearMap.toMatrix'_mulVec, Matrix.vecMul_one]
  exact congrFun (congrArg DFunLike.coe hg) v

end FlagMinorsBaseChange

theorem FlagMinorsBaseChange.proof : FlagMinorsBaseChange.Statement := by
  intro F _ n N1 B hB
  apply le_antisymm
  · rw [Algebra.adjoin_le_iff]
    rintro _ ⟨q, rfl⟩
    exact FlagMinorsBaseChange.flagMinor_mul_const_mem (genMat F n) B _ (fun a b => rfl) q.1 q.2
  · obtain ⟨D, hD⟩ := FlagMinorsBaseChange.exists_mul_eq_one B hB
    have e : ∀ l b, ∑ k, B l k * D k b = (1 : Matrix (Fin n) (Fin n) F) l b := fun l b => by
      rw [← Matrix.mul_apply, hD]
    rw [Algebra.adjoin_le_iff]
    rintro _ ⟨q, rfl⟩
    refine FlagMinorsBaseChange.flagMinor_mul_const_mem _ D (genMat F n) ?_ q.1 q.2
    intro a b
    show X (a, b) = ∑ k, (∑ l, X (a, l) * C (B l k)) * C (D k b)
    symm
    simp_rw [Finset.sum_mul, mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← map_sum, e, Matrix.one_apply]
    simp

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PLocRingChartLoc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem LocRingChartLoc.proof : LocRingChartLoc.Statement := by
  classical
  intro K _ ι _ P W hP hW hPW hrel
  let L := FractionRing (MRing ι ⧸ P)
  let q : MRing ι →+* L := (algebraMap (MRing ι ⧸ P) L).comp (Ideal.Quotient.mk P)
  have hq : ∀ f, f ∉ W → q f ≠ 0 := fun f hf h => hf (hPW (by
    rwa [RingHom.comp_apply, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h))
  have hnz : ∀ v, v ∉ W → Ideal.Quotient.mk P v ∈ nonZeroDivisors (MRing ι ⧸ P) := fun v hv =>
    mem_nonZeroDivisors_of_ne_zero fun h => hv (hPW (Ideal.Quotient.eq_zero_iff_mem.mp h))

  have hfrac : ∀ u v a, IsMultiHomog u a → IsMultiHomog v a → v ∉ W → q u / q v ∈ locRing P W := by
    intro u v a hu hv hvW
    refine Subring.subset_closure ⟨u, v, a, hnz v hvW, hvW, hu, hv, ?_⟩
    rw [IsFractionRing.mk'_eq_div]
    rfl
  choose c hc using hrel

  let g : (Σ k, ι k) → L := fun p => q (X p) / q (X ⟨p.1, c p.1⟩)
  let B : Subring L := Subring.closure (Set.range g)
  have hTB : Subring.closure ((Finset.univ.image g : Finset L) : Set L) = B := by
    rw [Finset.coe_image, Finset.coe_univ, Set.image_univ]
  have hBS : B ≤ locRing P W := Subring.closure_le.mpr (by
    rintro _ ⟨p, rfl⟩
    exact hfrac _ _ _ (AvoidRing.isMultiHomog_X p.1 p.2) (AvoidRing.isMultiHomog_X p.1 (c p.1)) (hc p.1))
  let θ : MRing ι →+* L := eval₂Hom (Int.castRingHom L) g
  have hθB : ∀ f, θ f ∈ B := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C r => rw [eval₂Hom_C, eq_intCast]; exact intCast_mem _ r
    | add f₁ f₂ h₁ h₂ => rw [map_add]; exact add_mem h₁ h₂
    | mul_X f p hf => rw [map_mul, eval₂Hom_X']; exact mul_mem hf (Subring.subset_closure ⟨p, rfl⟩)

  have hkey : ∀ u a, IsMultiHomog u a → q u = θ u * q (∏ k, X ⟨k, c k⟩ ^ a k) := by
    intro u a hu
    conv_lhs => rw [u.as_sum]
    conv_rhs => rw [u.as_sum]
    rw [map_sum, map_sum, Finset.sum_mul, map_prod]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hT : ∏ k, q (X ⟨k, c k⟩ ^ a k) = ∏ p : Σ k, ι k, q (X ⟨p.1, c p.1⟩) ^ m p := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ => ?_
      show q (X ⟨k, c k⟩ ^ a k) = ∏ y, q (X ⟨k, c k⟩) ^ m ⟨k, y⟩
      rw [map_pow, Finset.prod_pow_eq_pow_sum, hu m hm k]
    have hθm : θ (monomial m (coeff m u)) = ((coeff m u : ℤ) : L) * ∏ p, g p ^ m p := by
      rw [show θ _ = eval₂ (Int.castRingHom L) g _ from rfl, eval₂_monomial, eq_intCast,
        Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    have hqm : q (monomial m (coeff m u)) = ((coeff m u : ℤ) : L) * ∏ p, q (X p) ^ m p := by
      rw [monomial_eq, map_mul, map_finsuppProd, Finsupp.prod_fintype _ _ (fun _ => by simp)]
      simp only [map_pow]
      congr 1
      exact eq_intCast (q.comp C) _
    rw [hT, hθm, hqm, mul_assoc, ← Finset.prod_mul_distrib]
    congr 1
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← mul_pow]
    congr 1
    exact (div_mul_cancel₀ _ (hq _ (hc p.1))).symm
  refine ⟨Finset.univ.image g, hTB ▸ hBS, fun z hz => ?_⟩
  rw [hTB]
  obtain ⟨u, v, a, hu, hv, hvW, hzv⟩ := LocRingFrac.proof K ι P W hP hW hPW z hz
  have hTW := AvoidRing.coordProd_not_mem hW c hc a
  have hu' := hkey u a hu
  have hv' := hkey v a hv
  have hinv := hfrac _ v a (AvoidRing.isMultiHomog_coordProd c a) hv hvW
  have hθv : θ v ≠ 0 := fun h => hq v hvW (by rw [hv', h, zero_mul])
  refine ⟨θ u, hθB u, θ v, hθB v, hθv, ?_, ?_⟩
  · have he : (θ v)⁻¹ = q (∏ k, X ⟨k, c k⟩ ^ a k) / q v := by
      rw [eq_div_iff (hq v hvW), hv', ← mul_assoc, inv_mul_cancel₀ hθv, one_mul]
    rw [he]
    exact hinv
  · apply mul_right_cancel₀ (hq _ hTW)
    rw [mul_assoc, ← hv', ← hu']
    exact hzv

end

end GroundTheory.Heights₂.Heights.Inter
end

