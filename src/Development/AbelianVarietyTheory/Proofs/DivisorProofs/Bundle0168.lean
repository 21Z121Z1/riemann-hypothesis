import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0071
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuotientEigenDifference
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0072

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerAevalTruncatedPolynomialPresentationStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_aeval_truncatedPolynomial_presentation : ∀ (n : ℕ), 0 < n → ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra B A] (d : ℕ) (x : Fin d → A) (b : Fin d → B), (∀ i, x i ^ n = algebraMap B A (b i)) → LinearIndependent B (fun a : Fin d → Fin n => ∏ i, x i ^ (a i : ℕ)) → RingHom.ker (MvPolynomial.aeval x : MvPolynomial (Fin d) B →ₐ[B] A) = Ideal.span (Set.range fun i : Fin d => (MvPolynomial.X i ^ n - MvPolynomial.C (b i) : MvPolynomial (Fin d) B)) := by
  first | exact @GlobalTheory.ker_aeval_truncated | exact GlobalTheory.ker_aeval_truncated | (intros; apply GlobalTheory.ker_aeval_truncated <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerInfMapLeMapMulKerOfFlatTargetStatement
section
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ker_inf_map_le_map_mul_ker_of_flat_target : ∀ (B P A : Type) [CommRing B] [CommRing P] [CommRing A] [Algebra B P] [Algebra B A] [Module.Flat B A] (Ψ : P →ₐ[B] A), Function.Surjective Ψ → ∀ I : Ideal B, RingHom.ker Ψ ⊓ I.map (algebraMap B P) ≤ I.map (algebraMap B P) * RingHom.ker Ψ := by
  first | exact @GlobalTheory.ker_inf_map_le_map_mul_ker_of_flat | exact GlobalTheory.ker_inf_map_le_map_mul_ker_of_flat | (intros; apply GlobalTheory.ker_inf_map_le_map_mul_ker_of_flat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerSmulLeIdealSmulOfFreeStatement
section
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_smul_of_smul_eq_zero_of_free : ∀ (Λ : Type) [CommRing Λ] (t : Λ), (∀ x : Λ, t * x = 0 → x ∈ Ideal.span {t}) → ∀ (M : Type 1) [AddCommGroup M] [Module Λ M], Module.Free Λ M → ∀ m : M, t • m = 0 → m ∈ Ideal.span {t} • (⊤ : Submodule Λ M) := by
  first | exact @GlobalTheory.ker_smul_le_ideal_smul_of_free | exact GlobalTheory.ker_smul_le_ideal_smul_of_free | (intros; apply GlobalTheory.ker_smul_le_ideal_smul_of_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrullIntersectionIdealLocalFormStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.krull_intersection_ideal_local_form : ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (I a a' : Ideal B), (∀ e : ℕ, a ≤ a' ⊔ I ^ (e + 1)) → ∃ r ∈ I, ∀ x ∈ a, (1 - r) * x ∈ a' := by
  first | exact @GlobalTheory.krull_inter_ideal_local | exact GlobalTheory.krull_inter_ideal_local | (intros; apply GlobalTheory.krull_inter_ideal_local <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovMatrixConjEqOfCharpolyEq
section
open Matrix Polynomial

noncomputable section

namespace GlobalTheory.LeviDesc.Krylov

theorem pow_dim_eq_neg_sum_charpoly_coeff {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) :
    y ^ r = - ∑ k : Fin r, y.charpoly.coeff k • y ^ (k : ℕ) := by
  have h := Matrix.aeval_self_charpoly y
  have hm := (Matrix.charpoly_monic y).as_sum
  have hd : y.charpoly.natDegree = r := by simpa using Matrix.charpoly_natDegree_eq_dim y
  rw [hd] at hm
  rw [hm] at h
  simp [map_sum, Algebra.smul_def] at h
  rw [Fin.sum_univ_eq_sum_range (fun k => y.charpoly.coeff k • y ^ k)]
  simp only [Algebra.smul_def]
  exact eq_neg_of_add_eq_zero_left h

def companion {F : Type} [Field F] (r : ℕ) (p : F[X]) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i j => if (j : ℕ) + 1 < r then (if (i : ℕ) = (j : ℕ) + 1 then 1 else 0) else - p.coeff i

theorem mul_krylov_eq {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (e : Fin r → F) :
    y * krylov y e = krylov y e * companion r y.charpoly := by
  ext i j
  have hl : (y * krylov y e) i j = (y ^ ((j : ℕ) + 1) *ᵥ e) i := by
    rw [pow_succ', ← Matrix.mulVec_mulVec]
    simp [Matrix.mul_apply, krylov_apply, Matrix.mulVec, dotProduct]
  rw [hl, Matrix.mul_apply]
  by_cases hj : (j : ℕ) + 1 < r
  · simp only [companion, Matrix.of_apply, hj, if_true]
    rw [Finset.sum_eq_single (⟨(j : ℕ) + 1, hj⟩ : Fin r)]
    · simp [krylov_apply]
    · intro k _ hk
      have : (k : ℕ) ≠ (j : ℕ) + 1 := fun h => hk (Fin.ext h)
      simp [this]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hr : (j : ℕ) + 1 = r := by omega
    simp only [companion, Matrix.of_apply, hj, if_false]
    rw [hr, pow_dim_eq_neg_sum_charpoly_coeff y, Matrix.neg_mulVec, Matrix.sum_mulVec]
    simp [krylov_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.mulVec, dotProduct, Matrix.smul_apply, smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring

theorem krylov_inv_mul_mul_krylov {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F)
    (e : Fin r → F) (h : IsUnit (krylov y e).det) :
    (krylov y e)⁻¹ * y * krylov y e = companion r y.charpoly := by
  rw [Matrix.mul_assoc, mul_krylov_eq, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ h, Matrix.one_mul]

theorem krylov_conj_eq_of_charpoly_eq {F : Type} [Field F] {r : ℕ} (y y' : Matrix (Fin r) (Fin r) F)
    (e e' : Fin r → F) (hχ : y.charpoly = y'.charpoly) (h : IsUnit (krylov y e).det)
    (h' : IsUnit (krylov y' e').det) :
    (krylov y e)⁻¹ * y * krylov y e = (krylov y' e')⁻¹ * y' * krylov y' e' := by
  rw [krylov_inv_mul_mul_krylov y e h, krylov_inv_mul_mul_krylov y' e' h', hχ]

end GlobalTheory.LeviDesc.Krylov
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAevalValuationDvrStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_aeval_valuation_dvr : ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V] [IsLocalHom (algebraMap T V)],
    Function.Injective (algebraMap T V) →
    ∀ (γ : V) (ϖ u : T) (k : ℕ), Irreducible ϖ → IsUnit u → IsUnit (k : T) → 0 < k →
    γ ^ k = algebraMap T V u →
    ∀ h : Polynomial T, Polynomial.aeval γ h = 0 ∨
      ∃ (a : ℕ) (h' c : Polynomial T), IsUnit (Polynomial.aeval γ c) ∧ IsUnit (Polynomial.aeval γ h') ∧
        Polynomial.aeval γ c * Polynomial.aeval γ h = algebraMap T V ϖ ^ a * Polynomial.aeval γ h' := by
  first | (exact @GlobalTheory.kummer_valuation) | (exact GlobalTheory.kummer_valuation) | (intros; apply GlobalTheory.kummer_valuation  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerAlgebraFiniteProjectiveFaithfullyFlat
section
open scoped TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.KummerAlg

open MvPolynomial

theorem smul_comm_of_invertible {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L]
    [Module.Invertible B L] (ψ : L →ₗ[B] B) (e ℓ : L) : ψ e • ℓ = ψ ℓ • e := by
  let T : L ⊗[B] L →ₗ[B] L := TensorProduct.lift ((LinearMap.lsmul B L).compl₁₂ ψ LinearMap.id)
  have h := congrArg T (Module.Invertible.tmul_comm (R := B) (m₁ := e) (m₂ := ℓ))
  simpa [T] using h

variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {q : ℕ}

def intersection_update_fsHerm_neg_one (φ : MultilinearMap B (fun _ : Fin (q + 1) => L) B) (e : L) : L →ₗ[B] B :=
  φ.toLinearMap (fun _ => e) 0

theorem position_apply (φ : MultilinearMap B (fun _ : Fin (q + 1) => L) B) (e ℓ : L) :
    intersection_update_fsHerm_neg_one φ e ℓ = φ (Function.update (fun _ => e) 0 ℓ) := rfl

theorem position_self (φ : MultilinearMap B (fun _ : Fin (q + 1) => L) B) (e : L) :
    intersection_update_fsHerm_neg_one φ e e = φ (fun _ => e) := by
  rw [position_apply, Function.update_eq_self]

theorem pow_mul_eq_mul_prod_position [Module.Invertible B L]
    (φ : MultilinearMap B (fun _ : Fin (q + 1) => L) B) (e : L) (ℓ : Fin (q + 1) → L) :
    φ (fun _ => e) ^ (q + 1) * φ ℓ = φ (fun _ => e) * ∏ i, intersection_update_fsHerm_neg_one φ e (ℓ i) := by
  have h1 : φ (fun i => φ (fun _ => e) • ℓ i) = φ (fun _ => e) ^ (q + 1) * φ ℓ := by
    rw [MultilinearMap.map_smul_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul]
  have h2 : φ (fun i => intersection_update_fsHerm_neg_one φ e (ℓ i) • e) = (∏ i, intersection_update_fsHerm_neg_one φ e (ℓ i)) * φ (fun _ => e) := by
    rw [MultilinearMap.map_smul_univ, smul_eq_mul]
  have h3 : (fun i => φ (fun _ => e) • ℓ i) = (fun i => intersection_update_fsHerm_neg_one φ e (ℓ i) • e) := by
    funext i
    rw [← position_self φ e]
    exact smul_comm_of_invertible (intersection_update_fsHerm_neg_one φ e) e (ℓ i)
  rw [← h1, h3, h2, mul_comm]

theorem algebraMap_mul_gen (φ : MultilinearMap B (fun _ : Fin (q + 1) => L) B) (e ℓ : L) :
    algebraMap B (Alg φ) (φ (fun _ => e)) * gen φ ℓ =
      algebraMap B (Alg φ) (intersection_update_fsHerm_neg_one φ e ℓ) * gen φ e := by
  have hA := prod_gen φ (fun _ => e)
  have hB := prod_gen φ (Function.update (fun _ => e) 0 ℓ)
  rw [Fin.prod_univ_succ] at hA hB
  simp only [Function.update_self, ne_eq, Fin.succ_ne_zero, not_false_eq_true,
    Function.update_of_ne] at hB
  rw [position_apply, ← hB, ← hA]
  ring

end GlobalTheory.KummerAlg

namespace GlobalTheory.KummerAlg
open MvPolynomial
variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {q : ℕ}

theorem algHom_ext_of_isUnit (φ : MultilinearMap B (fun _ : Fin (q + 1) => L) B) (e : L)
    {R : Type} [CommRing R] [Algebra B R] (hu : IsUnit (algebraMap B R (φ (fun _ => e))))
    {g₁ g₂ : Alg φ →ₐ[B] R} (h : g₁ (gen φ e) = g₂ (gen φ e)) : g₁ = g₂ := by
  refine Ideal.Quotient.algHom_ext B (MvPolynomial.algHom_ext fun ℓ => ?_)
  change g₁ (gen φ ℓ) = g₂ (gen φ ℓ)
  have k₁ := congrArg g₁ (algebraMap_mul_gen φ e ℓ)
  have k₂ := congrArg g₂ (algebraMap_mul_gen φ e ℓ)
  simp only [map_mul, AlgHom.commutes] at k₁ k₂
  apply hu.mul_left_cancel
  rw [k₁, k₂, h]

def liftRoot [Module.Invertible B L] (φ : MultilinearMap B (fun _ : Fin (q + 1) => L) B) (e : L)
    {R : Type} [CommRing R] [Algebra B R] (hu : IsUnit (algebraMap B R (φ (fun _ => e))))
    (x : R) (hx : x ^ (q + 1) = algebraMap B R (φ (fun _ => e))) : Alg φ →ₐ[B] R :=
  Ideal.Quotient.liftₐ (ideal φ)
    (MvPolynomial.aeval fun ℓ => algebraMap B R (intersection_update_fsHerm_neg_one φ e ℓ) * ↑hu.unit⁻¹ * x) <| by
    intro a ha
    have hle : ideal φ ≤ RingHom.ker (MvPolynomial.aeval (R := B) fun ℓ : L =>
        algebraMap B R (intersection_update_fsHerm_neg_one φ e ℓ) * ↑hu.unit⁻¹ * x) := ?_
    · exact hle ha
    refine Ideal.span_le.2 ?_
    rintro r ((⟨⟨a, b⟩, rfl⟩ | ⟨⟨c, a⟩, rfl⟩) | ⟨ℓ, rfl⟩)
    · simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        map_sub, aeval_X, map_add]
      ring
    · simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        map_sub, map_mul, aeval_X, aeval_C, map_smul, smul_eq_mul]
      ring
    · simp only [SetLike.mem_coe, RingHom.mem_ker, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
        map_sub, map_prod, aeval_X, aeval_C]
      rw [sub_eq_zero, Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
        Finset.prod_const, Finset.card_univ, Fintype.card_fin, hx]
      have key := congrArg (algebraMap B R) (pow_mul_eq_mul_prod_position φ e ℓ)
      simp only [map_mul, map_pow, map_prod] at key
      set u := hu.unit
      have hu' : (u : R) = algebraMap B R (φ (fun _ => e)) := rfl
      rw [← hu'] at key ⊢
      have hv : (↑u⁻¹ : R) ^ (q + 1) * (u : R) ^ (q + 1) = 1 := by
        rw [← mul_pow, Units.inv_mul, one_pow]
      apply (u ^ (q + 1)).isUnit.mul_right_cancel
      rw [Units.val_pow_eq_pow_val]
      calc (∏ i, algebraMap B R (intersection_update_fsHerm_neg_one φ e (ℓ i))) * ↑u⁻¹ ^ (q + 1) * ↑u * ↑u ^ (q + 1)
          = (↑u * ∏ i, algebraMap B R (intersection_update_fsHerm_neg_one φ e (ℓ i))) * (↑u⁻¹ ^ (q + 1) * ↑u ^ (q + 1)) := by ring
        _ = algebraMap B R (φ ℓ) * ↑u ^ (q + 1) := by rw [hv, mul_one, ← key]; ring

theorem liftRoot_gen [Module.Invertible B L] (φ : MultilinearMap B (fun _ : Fin (q + 1) => L) B)
    (e : L) {R : Type} [CommRing R] [Algebra B R] (hu : IsUnit (algebraMap B R (φ (fun _ => e))))
    (x : R) (hx : x ^ (q + 1) = algebraMap B R (φ (fun _ => e))) :
    liftRoot φ e hu x hx (gen φ e) = x := by
  have h0 : liftRoot φ e hu x hx (gen φ e) =
      MvPolynomial.aeval (fun ℓ => algebraMap B R (intersection_update_fsHerm_neg_one φ e ℓ) * ↑hu.unit⁻¹ * x) (X e) := rfl
  rw [h0, aeval_X, position_self]
  have : algebraMap B R (φ (fun _ => e)) * ↑hu.unit⁻¹ = 1 := by
    exact hu.mul_val_inv
  rw [this, one_mul]

end GlobalTheory.KummerAlg

namespace GlobalTheory.KummerAlg
open MvPolynomial
variable {B : Type} [CommRing B] {L : Type} [AddCommGroup L] [Module B L] {q : ℕ}

theorem smul_top_ne_top [Module.Invertible B L]
    (φ : MultilinearMap B (fun _ : Fin (q + 1) => L) B) (m : Ideal B) [hm : m.IsMaximal]
    (e : L) (he : φ (fun _ => e) ∉ m) : m • (⊤ : Submodule B (Alg φ)) ≠ ⊤ := by
  letI : Field (B ⧸ m) := Ideal.Quotient.field m
  let K := AlgebraicClosure (B ⧸ m)
  have hK : ∀ b : B, algebraMap B K b = algebraMap (B ⧸ m) K (Ideal.Quotient.mk m b) := fun b =>
    IsScalarTower.algebraMap_apply B (B ⧸ m) K b
  have hu : IsUnit (algebraMap B K (φ (fun _ => e))) := by
    rw [hK, isUnit_iff_ne_zero, ne_eq, map_eq_zero_iff _ (algebraMap (B ⧸ m) K).injective,
      Ideal.Quotient.eq_zero_iff_mem]
    exact he
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap B K (φ (fun _ => e)))
    (Nat.succ_pos q)
  let g := liftRoot φ e hu x hx
  intro htop
  have hle : m • (⊤ : Submodule B (Alg φ)) ≤ Submodule.comap g.toLinearMap ⊥ := by
    refine Submodule.smul_le.2 fun r hr n _ => ?_
    rw [Submodule.mem_comap, Submodule.mem_bot, AlgHom.toLinearMap_apply, map_smul,
      Algebra.smul_def, hK, (Ideal.Quotient.eq_zero_iff_mem).2 hr, map_zero, zero_mul]
  have h1 : (1 : Alg φ) ∈ Submodule.comap g.toLinearMap ⊥ := hle (by rw [htop]; exact Submodule.mem_top)
  simp only [Submodule.mem_comap, AlgHom.toLinearMap_apply, map_one, Submodule.mem_bot] at h1
  exact one_ne_zero h1

def awayEquiv [Module.Invertible B L] (φ : MultilinearMap B (fun _ : Fin (q + 1) => L) B) (e : L) :
    Localization.Away (φ (fun _ => e)) ⊗[B] Alg φ ≃ₐ[Localization.Away (φ (fun _ => e))]
      AdjoinRoot (Polynomial.X ^ (q + 1) - Polynomial.C
        (algebraMap B (Localization.Away (φ (fun _ => e))) (φ (fun _ => e)))) := by
  set f := φ (fun _ => e)
  set Bf := Localization.Away f
  set P : Polynomial Bf := Polynomial.X ^ (q + 1) - Polynomial.C (algebraMap B Bf f)
  set A := AdjoinRoot P
  set T := Bf ⊗[B] Alg φ
  have hfu : IsUnit (algebraMap B Bf f) := IsLocalization.Away.algebraMap_isUnit f
  have huA : IsUnit (algebraMap B A f) := by
    rw [IsScalarTower.algebraMap_apply B Bf A]; exact hfu.map _
  have huT : IsUnit (algebraMap B T f) := by
    rw [IsScalarTower.algebraMap_apply B Bf T]; exact hfu.map _
  have hxA : AdjoinRoot.root P ^ (q + 1) = algebraMap B A f := by
    have h := AdjoinRoot.eval₂_root P
    simp only [P, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h
    rw [IsScalarTower.algebraMap_apply B Bf A]
    exact sub_eq_zero.1 h
  have hxT : P.eval₂ (algebraMap Bf T) ((1 : Bf) ⊗ₜ[B] gen φ e : T) = 0 := by
    simp only [P, Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C]
    rw [sub_eq_zero, Algebra.TensorProduct.tmul_pow, one_pow, ← IsScalarTower.algebraMap_apply,
      ← Algebra.TensorProduct.includeRight.commutes]
    congr 1
    have := prod_gen φ (fun _ => e)
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
    exact this
  let fwd : T →ₐ[Bf] A := Algebra.TensorProduct.lift (Algebra.ofId Bf A)
    (liftRoot φ e huA (AdjoinRoot.root P) hxA) (fun _ _ => Commute.all _ _)
  let bwd : A →ₐ[Bf] T := AdjoinRoot.liftAlgHom P (Algebra.ofId Bf T) ((1 : Bf) ⊗ₜ[B] gen φ e) hxT
  have hf : fwd ((1 : Bf) ⊗ₜ[B] gen φ e) = AdjoinRoot.root P := by
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]
    exact liftRoot_gen φ e huA _ hxA
  have hb : bwd (AdjoinRoot.root P) = (1 : Bf) ⊗ₜ[B] gen φ e := AdjoinRoot.liftAlgHom_root _ _ _ _
  refine AlgEquiv.ofAlgHom fwd bwd ?_ ?_
  · exact AdjoinRoot.algHom_ext (by simp only [AlgHom.comp_apply, hb, hf, AlgHom.id_apply])
  · refine Algebra.TensorProduct.ext (Subsingleton.elim _ _) ?_
    exact algHom_ext_of_isUnit φ e huT (by
      simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars', Algebra.TensorProduct.includeRight_apply,
        hf, hb, AlgHom.id_apply])

theorem away_finite_projective [Module.Invertible B L]
    (φ : MultilinearMap B (fun _ : Fin (q + 1) => L) B) (e : L) :
    Module.Finite (Localization.Away (φ (fun _ => e))) (Localization.Away (φ (fun _ => e)) ⊗[B] Alg φ) ∧
    Module.Projective (Localization.Away (φ (fun _ => e))) (Localization.Away (φ (fun _ => e)) ⊗[B] Alg φ) := by
  set Bf := Localization.Away (φ (fun _ => e))
  have hmon : (Polynomial.X ^ (q + 1) - Polynomial.C (algebraMap B Bf (φ (fun _ => e)))).Monic :=
    Polynomial.monic_X_pow_sub_C _ (Nat.succ_ne_zero q)
  let pb := AdjoinRoot.powerBasis' hmon
  haveI := Module.Free.of_basis pb.basis
  haveI := Module.Finite.of_basis pb.basis
  let eq := (awayEquiv φ e).toLinearEquiv
  exact ⟨Module.Finite.equiv eq.symm, Module.Projective.of_equiv eq.symm⟩

end GlobalTheory.KummerAlg

namespace GlobalTheory.KummerAlg

theorem finite_projective_faithfullyFlat : ∀ (B : Type) [CommRing B] (L : Type) [AddCommGroup L]
    [Module B L] [Module.Invertible B L] (q : ℕ) (φ : MultilinearMap B (fun _ : Fin q => L) B),
    0 < q → (∀ p : Ideal B, p.IsPrime → ∃ e : L, φ (fun _ => e) ∉ p) →
    Module.Finite B (GlobalTheory.KummerAlg.Alg φ) ∧ Module.Projective B (GlobalTheory.KummerAlg.Alg φ) ∧
      Module.FaithfullyFlat B (GlobalTheory.KummerAlg.Alg φ) := by
  intro B _ L _ _ _ q φ hq hφ
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  let s : Set B := Set.range (fun e : L => φ (fun _ => e))
  have hs : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hsm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨e, he⟩ := hφ m hm.isPrime
    exact he (hsm (Ideal.subset_span ⟨e, rfl⟩))
  let F : s → Type := fun g => Localization.Away g.1 ⊗[B] Alg φ
  let ϕ : ∀ g : s, Alg φ →ₗ[B] F g := fun g => TensorProduct.mk B (Localization.Away g.1) (Alg φ) 1
  have hfp : ∀ g : s, Module.Finite (Localization.Away g.1) (F g) ∧
      Module.Projective (Localization.Away g.1) (F g) := by
    rintro ⟨_, e, rfl⟩
    exact away_finite_projective φ e
  haveI (g : s) : Module.Finite (Localization.Away g.1) (F g) := (hfp g).1
  haveI (g : s) : Module.Projective (Localization.Away g.1) (F g) := (hfp g).2
  haveI (g : s) : IsLocalizedModule (Submonoid.powers g.1) (ϕ g) :=
    (isLocalizedModule_iff_isBaseChange (Submonoid.powers g.1) (Localization.Away g.1) (ϕ g)).2
      (TensorProduct.isBaseChange B (Alg φ) (Localization.Away g.1))
  haveI (g : s) : Module.Flat B (F g) := by
    haveI : Module.Flat B (Localization.Away g.1) := IsLocalization.flat _ (Submonoid.powers g.1)
    haveI : Module.Flat (Localization.Away g.1) (F g) := Module.Flat.of_projective
    exact Module.Flat.trans B (Localization.Away g.1) (F g)
  haveI : Module.FinitePresentation B (Alg φ) :=
    Module.FinitePresentation.of_localizationSpan' s hs (Mₚ := F)
      (Rₚ := fun g : s => Localization.Away g.1) ϕ
      fun _ => Module.finitePresentation_of_projective _ _
  haveI : Module.Flat B (Alg φ) :=
    Module.flat_of_isLocalized_span B (Alg φ) s hs F ϕ fun _ => inferInstance
  refine ⟨inferInstance, Module.Flat.projective_of_finitePresentation, ?_⟩
  constructor
  intro m hm
  obtain ⟨e, he⟩ := hφ m hm.isPrime
  exact smul_top_ne_top φ m e he

end GlobalTheory.KummerAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerResidueMemAdjoinUnitStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_residue_mem_adjoin_unit : ∀ (T V : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [Algebra T V] [IsLocalHom (algebraMap T V)],
    Function.Injective (algebraMap T V) →
    ∀ (α γ : V) (ϖ : T) (m : ℕ), Irreducible ϖ → 0 < m → IsUnit γ →
    α ^ m = γ * algebraMap T V ϖ →
    (∀ h : Polynomial T, Polynomial.aeval γ h = 0 ∨
      ∃ (a : ℕ) (h' c : Polynomial T), IsUnit (Polynomial.aeval γ c) ∧ IsUnit (Polynomial.aeval γ h') ∧
        Polynomial.aeval γ c * Polynomial.aeval γ h = algebraMap T V ϖ ^ a * Polynomial.aeval γ h') →
    (∀ v : V, ∃ f g : Polynomial T, Polynomial.aeval α g ≠ 0 ∧ Polynomial.aeval α g * v = Polynomial.aeval α f) →
    ∀ v : V, IsLocalRing.residue V v ∈
      IntermediateField.adjoin (IsLocalRing.ResidueField T) {IsLocalRing.residue V γ} := by
  first | (exact @GlobalTheory.kummer_residue_mem_adjoin) | (exact GlobalTheory.kummer_residue_mem_adjoin) | (intros; apply GlobalTheory.kummer_residue_mem_adjoin  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KummerUniformiserAdjoinRootTensorIsReducedStatement
section
open IsLocalRing
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kummer_uniformiser_adjoinRoot_tensor_isReduced : ∀ (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D],
    Nonempty (D ≃ₐ[S] AdjoinRoot (Polynomial.X ^ e - Polynomial.C π)) → Irreducible π → IsUnit (e : S) →
    IsReduced (TensorProduct S D L) := by
  first | (exact @GlobalTheory.kummer_uniformiser_tensor_isReduced) | (exact GlobalTheory.kummer_uniformiser_tensor_isReduced) | (intros; apply GlobalTheory.kummer_uniformiser_tensor_isReduced  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LambdaMonomialCoeffDualNumberProductEq
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A

namespace GlobalTheory.PsCo.Cw2a

theorem t_exL_dual : T_exL_dual := by
  intro n L m a
  exact GlobalTheory.coeff_allOnes_prod_one_add_mul (σ := EntIdx n) m a

end GlobalTheory.PsCo.Cw2a
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDetRelationOfLsmulShift
section
open scoped NNReal

namespace GlobalTheory

open GlobalTheory.IndefiniteRowSideFullHecke.QuotientEigenDifference

theorem addVal_inv_pow_mul {C : Type} [Field C] (w : Valuation C ℝ≥0) (ℓ : C)
    (h0 : 0 < w ℓ) (h1 : w ℓ < 1) {d c : C} (hd : d ≠ 0) (hc : c ≠ 0) (n : ℕ) :
    addVal w ℓ (d⁻¹ ^ n * c) = addVal w ℓ c - (n : ℝ) * addVal w ℓ d := by
  have hwd : ((w d : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (w.ne_zero_iff.2 hd)
  have hwc : ((w c : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (w.ne_zero_iff.2 hc)
  have hl : Real.log ((w ℓ : ℝ≥0) : ℝ) ≠ 0 := by
    refine (Real.log_neg ?_ ?_).ne
    · exact_mod_cast h0
    · exact_mod_cast h1
  unfold addVal
  rw [map_mul, map_pow, map_inv₀]
  push_cast
  rw [Real.log_mul (pow_ne_zero _ (inv_ne_zero hwd)) hwc, Real.log_pow, Real.log_inv]
  field_simp
  ring

theorem detRel_of_detRel_lsmul (C : Type) [Field C] (w : Valuation C ℝ≥0) (ℓ : C)
    (h0 : 0 < w ℓ) (h1 : w ℓ < 1) (p q : ℕ) (F : Submodule C (Fin (p + q) → C))
    (X0 : Submodule w.valuationSubring (Fin (p + q) → C))
    (L : Submodule w.valuationSubring ((Fin (p + q) → C) ⧸ F))
    (M : Submodule w.valuationSubring (Fin (p + q) → C)) (y : ℝ) (d : w.valuationSubring)
    (hd : d ≠ 0)
    (h : DetRel w ℓ F (X0.map (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d)) L M y) :
    DetRel w ℓ F X0 L M (y - ((p + q : ℕ) : ℝ) * addVal w ℓ (d : C)) := by
  obtain ⟨x, u, m, c, hx, hu, hm, hmF, ⟨hc0, hcy⟩, hdet⟩ := h
  have hdC : (d : C) ≠ 0 := fun e => hd (Subtype.ext e)
  have hsm : ∀ v : Fin (p + q) → C, d • v = (d : C) • v := fun v => rfl
  have hinj : Function.Injective (LinearMap.lsmul w.valuationSubring (Fin (p + q) → C) d) := by
    intro a b hab
    simp only [LinearMap.lsmul_apply, hsm] at hab
    exact smul_right_injective _ hdC hab
  refine ⟨fun i => (d : C)⁻¹ • x i, u, m, (d : C)⁻¹ ^ (p + q) * c, ⟨?_, ?_⟩, hu, hm, hmF,
    ⟨mul_ne_zero (pow_ne_zero _ (inv_ne_zero hdC)) hc0, ?_⟩, ?_⟩
  · exact hx.1.units_smul (fun _ => Units.mk0 _ (inv_ne_zero hdC))
  · apply Submodule.map_injective_of_injective hinj
    rw [← hx.2, Submodule.map_span, ← Set.range_comp]
    congr 2
    funext i
    simp [hsm, smul_smul, hdC]
  · rw [addVal_inv_pow_mul w ℓ h0 h1 hdC hc0, hcy]
  · have : Matrix.of (fun i => (d : C)⁻¹ • x i) = (d : C)⁻¹ • Matrix.of x := by
      ext i j; simp
    rw [this, Matrix.det_smul, Fintype.card_fin, hdet, mul_assoc]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeFormIdealDualVectorIntegralStatement
section
open NumberField
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_form_ideal_dual_vector_integral : ∀ {F V : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V], Module.finrank F V = 2 → ∀ (B : LinearMap.BilinForm F V), (∀ z, B z z = 0) → ∀ (L : Set V), (0 : V) ∈ L → (∀ x ∈ L, ∀ x' ∈ L, x + x' ∈ L) → (∀ (a : 𝓞 F), ∀ x ∈ L, (a : F) • x ∈ L) →
    ∀ (J : FractionalIdeal (𝓞 F)⁰ F), J ≠ 0 → (∀ z ∈ L, ∀ w ∈ L, B z w ∈ J) →
    (∀ t ∈ J, t ∈ Submodule.span (𝓞 F) {t | ∃ z ∈ L, ∃ w ∈ L, t = B z w}) →
    ∀ {v : V}, v ≠ 0 → ∃ I : FractionalIdeal (𝓞 F)⁰ F, I ≠ 0 ∧ ∀ a : F, a ∈ I ↔ a • v ∈ L := by
  first | exact @GlobalTheory.exists_fractionalIdeal_smul_mem_lattice_of_alternating | exact GlobalTheory.exists_fractionalIdeal_smul_mem_lattice_of_alternating | (intros; apply GlobalTheory.exists_fractionalIdeal_smul_mem_lattice_of_alternating <;> assumption)
end

