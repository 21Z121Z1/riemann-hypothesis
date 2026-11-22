import Mathlib
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.IrreducibleCharacterSeries.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0458
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0460
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableLatticeEqZpowStdInertCompletion
section
open IsDedekindDomain NumberField
open scoped Matrix

namespace GlobalTheory.LocLatInert

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem exists_unit_of_inert (σ : K →+* K) (hσ : ∀ x, σ (σ x) = x)
    (hv : ∀ x, Valued.v (σ x) = Valued.v x)
    (hx : ∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) :
    ∃ u : K, σ u * u = 1 ∧ Valued.v u ≤ 1 ∧ Valued.v (σ u) ≤ 1 ∧ 1 - u ≠ 0 ∧
      Valued.v (1 - u)⁻¹ ≤ 1 := by
  obtain ⟨x, hx1, hx2⟩ := hx

  have hvx : Valued.v x = 1 := by
    refine le_antisymm hx1 ?_
    calc (1 : WithZero (Multiplicative ℤ)) = Valued.v (σ x - x) := hx2.symm
      _ ≤ max (Valued.v (σ x)) (Valued.v x) := Valuation.map_sub _ _ _
      _ = Valued.v x := by rw [hv, max_self]
  have hx0 : x ≠ 0 := by
    intro h0; rw [h0, map_zero] at hvx; exact zero_ne_one hvx
  have hsx0 : σ x ≠ 0 := by
    intro h0; rw [← hv, h0, map_zero] at hvx; exact zero_ne_one hvx
  have hd : x - σ x ≠ 0 := by
    intro h0
    rw [← neg_sub, h0, neg_zero, map_zero] at hx2
    exact zero_ne_one hx2
  have hvd : Valued.v (x - σ x) = 1 := by rw [← neg_sub, Valuation.map_neg, hx2]

  refine ⟨σ x * x⁻¹, ?_, ?_, ?_, ?_, ?_⟩
  · rw [map_mul, map_inv₀, hσ]
    field_simp
  · rw [map_mul, map_inv₀, hv, hvx, inv_one, mul_one]
  · rw [map_mul, map_mul, map_inv₀, hσ, map_inv₀, hv, hvx, inv_one, mul_one]
  · rw [sub_ne_zero]
    intro h
    apply hd
    have : x = σ x := by
      field_simp at h
      exact h
    rw [← this, sub_self]
  · have e : (1 - σ x * x⁻¹)⁻¹ = x * (x - σ x)⁻¹ := by
      field_simp
    rw [e, map_mul, map_inv₀, hvx, hvd]
    simp

theorem single_mem_of_mem (σ : K →+* K) {n : ℕ} (L : AddSubgroup (Fin n → K))
    (hO : ∀ a : K, Valued.v a ≤ 1 → ∀ w ∈ L, a • w ∈ L)
    (hU : ∀ U : GL (Fin n) K, U ∈ Formalism.UG.UJ σ 1 → (∀ i j, Valued.v (U.1 i j) ≤ 1) →
      (∀ i j, Valued.v ((U⁻¹).1 i j) ≤ 1) → ∀ w ∈ L, U.1 *ᵥ w ∈ L)
    (u : K) (hu : σ u * u = 1) (hu1 : Valued.v u ≤ 1) (hu2 : Valued.v (σ u) ≤ 1)
    (hu3 : 1 - u ≠ 0) (hu4 : Valued.v (1 - u)⁻¹ ≤ 1)
    (w : Fin n → K) (hw : w ∈ L) (i : Fin n) : Pi.single i (w i) ∈ L := by

  have hdd : ∀ j, Function.update (1 : Fin n → K) i u j * Function.update (1 : Fin n → K) i (σ u) j = 1 := by
    intro j
    by_cases hj : j = i
    · rw [hj, Function.update_self, Function.update_self, mul_comm, hu]
    · rw [Function.update_of_ne hj, Function.update_of_ne hj, Pi.one_apply, mul_one]
  let D : GL (Fin n) K :=
    ⟨Matrix.diagonal (Function.update 1 i u), Matrix.diagonal (Function.update 1 i (σ u)),
      by rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; exact congrArg _ (funext hdd),
      by
        rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
        exact congrArg _ (funext fun j => by rw [mul_comm]; exact hdd j)⟩
  have hDU : D ∈ Formalism.UG.UJ σ 1 := by
    simp only [Formalism.UG.UJ, Formalism.UG.cT]
    show ((Matrix.diagonal (Function.update (1 : Fin n → K) i u)).map σ)ᵀ * 1 *
      Matrix.diagonal (Function.update (1 : Fin n → K) i u) = 1
    rw [Matrix.diagonal_map (map_zero σ), Matrix.diagonal_transpose, Matrix.mul_one,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext j
    by_cases hj : j = i
    · rw [hj, Function.update_self, hu]
    · rw [Function.update_of_ne hj, Pi.one_apply, map_one, mul_one]
  have hent : ∀ (c : K), Valued.v c ≤ 1 → ∀ a b,
      Valued.v (Matrix.diagonal (Function.update (1 : Fin n → K) i c) a b) ≤ 1 := by
    intro c hc a b
    rw [Matrix.diagonal_apply]
    split_ifs
    · by_cases ha : a = i
      · rw [ha, Function.update_self]; exact hc
      · rw [Function.update_of_ne ha, Pi.one_apply, map_one]
    · rw [map_zero]; exact zero_le
  have hDw := hU D hDU (hent u hu1) (hent (σ u) hu2) w hw

  have e1 : (D : Matrix (Fin n) (Fin n) K) *ᵥ w - w = Pi.single i ((u - 1) * w i) := by
    funext j
    show (Matrix.diagonal (Function.update (1 : Fin n → K) i u) *ᵥ w) j - w j = _
    rw [Matrix.mulVec_diagonal]
    by_cases hj : j = i
    · rw [hj, Function.update_self, Pi.single_eq_same]; ring
    · rw [Function.update_of_ne hj, Pi.single_eq_of_ne hj, Pi.one_apply, one_mul, sub_self]
  have hsub : Pi.single i ((u - 1) * w i) ∈ L := e1 ▸ L.sub_mem hDw hw

  have hc : Valued.v (-(1 - u)⁻¹) ≤ 1 := by rw [Valuation.map_neg]; exact hu4
  have hfin := hO _ hc _ hsub
  convert hfin using 1
  funext j
  by_cases hj : j = i
  · rw [hj, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul]
    field_simp
    ring
  · rw [Pi.smul_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, smul_zero]

theorem single_mem_swap (σ : K →+* K) {n : ℕ} (L : AddSubgroup (Fin n → K))
    (hU : ∀ U : GL (Fin n) K, U ∈ Formalism.UG.UJ σ 1 → (∀ i j, Valued.v (U.1 i j) ≤ 1) →
      (∀ i j, Valued.v ((U⁻¹).1 i j) ≤ 1) → ∀ w ∈ L, U.1 *ᵥ w ∈ L)
    (i j : Fin n) (t : K) (h : Pi.single i t ∈ L) : Pi.single j t ∈ L := by

  have hPP : (Equiv.swap i j).permMatrix K * (Equiv.swap i j).permMatrix K = 1 := by
    rw [← Matrix.permMatrix_mul, Equiv.swap_mul_self, Matrix.permMatrix_one]
  let P : GL (Fin n) K := ⟨(Equiv.swap i j).permMatrix K, (Equiv.swap i j).permMatrix K, hPP, hPP⟩
  have hmap : ((Equiv.swap i j).permMatrix K).map σ = (Equiv.swap i j).permMatrix K := by
    ext a b
    simp only [Matrix.map_apply, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs
    · exact map_one σ
    · exact map_zero σ
  have hPU : P ∈ Formalism.UG.UJ σ 1 := by
    simp only [Formalism.UG.UJ, Formalism.UG.cT]
    show (((Equiv.swap i j).permMatrix K).map σ)ᵀ * 1 * (Equiv.swap i j).permMatrix K = 1
    rw [hmap, Matrix.transpose_permMatrix, Matrix.mul_one, ← Matrix.permMatrix_mul, mul_inv_cancel,
      Matrix.permMatrix_one]
  have hent : ∀ a b, Valued.v (((Equiv.swap i j).permMatrix K) a b) ≤ 1 := by
    intro a b
    simp only [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply]
    split_ifs
    · rw [map_one]
    · rw [map_zero]; exact zero_le
  have hP := hU P hPU hent hent _ h

  have e : (P : Matrix (Fin n) (Fin n) K) *ᵥ Pi.single i t = Pi.single j t := by
    show (Equiv.swap i j).permMatrix K *ᵥ Pi.single i t = Pi.single j t
    rw [Matrix.permMatrix_mulVec]
    funext a
    simp only [Function.comp_apply, Pi.single_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_left]
  exact e ▸ hP

end GlobalTheory.LocLatInert

namespace GlobalTheory.LocLatInert

variable {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]

theorem set_classify (I : Set K) (hmul : ∀ a : K, Valued.v a ≤ 1 → ∀ t ∈ I, a * t ∈ I)
    (N : K) (hN : N ≠ 0) (hNI : N ∈ I) (hb : ∀ t ∈ I, Valued.v (N * t) ≤ 1) :
    ∃ M : ℤ, ∀ t, t ∈ I ↔ Valued.v t ≤ WithZero.exp M := by
  have hvN : Valued.v N ≠ 0 := (Valuation.ne_zero_iff _).2 hN

  let S : Set ℤ := {m | ∃ t ∈ I, Valued.v t = WithZero.exp m}
  have hS : S.Nonempty := ⟨WithZero.log (Valued.v N), N, hNI, (WithZero.exp_log hvN).symm⟩
  have hbdd : BddAbove S := by
    refine ⟨-WithZero.log (Valued.v N), ?_⟩
    rintro m ⟨t, ht, hvt⟩
    have h1 := hb t ht
    rw [map_mul, hvt, ← WithZero.exp_log hvN, ← WithZero.exp_add, ← WithZero.exp_zero,
      WithZero.exp_le_exp] at h1
    omega

  obtain ⟨t0, ht0, hvt0⟩ : sSup S ∈ S := Int.csSup_mem hS hbdd
  refine ⟨sSup S, fun t => ⟨fun ht => ?_, fun ht => ?_⟩⟩
  · by_cases h0 : t = 0
    · rw [h0, map_zero]; exact zero_le
    · have hvt : Valued.v t ≠ 0 := (Valuation.ne_zero_iff _).2 h0
      rw [← WithZero.exp_log hvt, WithZero.exp_le_exp]
      exact le_csSup hbdd ⟨t, ht, (WithZero.exp_log hvt).symm⟩
  · have ht00 : t0 ≠ 0 := by
      intro h0; rw [h0, map_zero] at hvt0; exact WithZero.exp_ne_zero hvt0.symm
    have e : t = (t * t0⁻¹) * t0 := by field_simp
    rw [e]
    refine hmul _ ?_ t0 ht0
    rw [map_mul, map_inv₀, hvt0]
    calc Valued.v t * (WithZero.exp (sSup S))⁻¹
        ≤ WithZero.exp (sSup S) * (WithZero.exp (sSup S))⁻¹ := by gcongr
      _ = 1 := mul_inv_cancel₀ WithZero.exp_ne_zero

end GlobalTheory.LocLatInert

namespace GlobalTheory.LocLatInert

theorem stable_lattice_eq_zpow_std : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (σ : P.adicCompletion E →+* P.adicCompletion E), (∀ x, σ (σ x) = x) → (∀ x, Valued.v (σ x) = Valued.v x) → (∃ x, Valued.v x ≤ 1 ∧ Valued.v (σ x - x) = 1) → ∀ (ϖ : P.adicCompletion E), Valued.v ϖ = WithZero.exp (-1 : ℤ) → ∀ (n : ℕ) (L : AddSubgroup (Fin n → P.adicCompletion E)) (N : P.adicCompletion E), N ≠ 0 → (∀ a : P.adicCompletion E, Valued.v a ≤ 1 → ∀ w ∈ L, a • w ∈ L) → (∀ w : Fin n → P.adicCompletion E, (∀ i, Valued.v (w i) ≤ 1) → N • w ∈ L) → (∀ w ∈ L, ∀ i, Valued.v (N * w i) ≤ 1) → (∀ U : GL (Fin n) (P.adicCompletion E), U ∈ Formalism.UG.UJ σ 1 → (∀ i j, Valued.v (U.1 i j) ≤ 1) → (∀ i j, Valued.v ((U⁻¹).1 i j) ≤ 1) → ∀ w ∈ L, U.1 *ᵥ w ∈ L) → ∃ k : ℤ, ∀ w, w ∈ L ↔ ∀ i, Valued.v (ϖ ^ k * w i) ≤ 1 := by
  intro E _ _ P σ hσ hv hx ϖ hϖ n L N hN hO hN' hb hU
  obtain ⟨u, hu, hu1, hu2, hu3, hu4⟩ := exists_unit_of_inert σ hσ hv hx
  rcases Nat.eq_zero_or_pos n with rfl | hn
  ·
    refine ⟨0, fun w => ⟨fun _ i => i.elim0, fun _ => ?_⟩⟩
    have hw : w = 0 := funext fun i => i.elim0
    rw [hw]
    exact L.zero_mem
  ·
    let i0 : Fin n := ⟨0, hn⟩
    let I : Set (P.adicCompletion E) := {t | Pi.single i0 t ∈ L}
    have hIall : ∀ (i : Fin n) t, Pi.single i t ∈ L ↔ t ∈ I := fun i t =>
      ⟨single_mem_swap σ L hU i i0 t, single_mem_swap σ L hU i0 i t⟩
    have hmul : ∀ a : P.adicCompletion E, Valued.v a ≤ 1 → ∀ t ∈ I, a * t ∈ I := by
      intro a ha t ht
      have e : Pi.single i0 (a * t) = a • (Pi.single i0 t : Fin n → P.adicCompletion E) := by
        funext j
        by_cases hj : j = i0
        · rw [hj, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul]
        · rw [Pi.smul_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, smul_zero]
      show Pi.single i0 (a * t) ∈ L
      rw [e]
      exact hO a ha _ ht
    have hNI : N ∈ I := by
      have h1 := hN' (Pi.single i0 1) fun i => by
        by_cases hi : i = i0
        · rw [hi, Pi.single_eq_same, map_one]
        · rw [Pi.single_eq_of_ne hi, map_zero]; exact zero_le
      have e : N • (Pi.single i0 1 : Fin n → P.adicCompletion E) = Pi.single i0 N := by
        funext j
        by_cases hj : j = i0
        · rw [hj, Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, smul_eq_mul, mul_one]
        · rw [Pi.smul_apply, Pi.single_eq_of_ne hj, Pi.single_eq_of_ne hj, smul_zero]
      show Pi.single i0 N ∈ L
      rw [← e]
      exact h1
    have hbI : ∀ t ∈ I, Valued.v (N * t) ≤ 1 := fun t ht => by
      have h1 := hb _ ht i0
      rwa [Pi.single_eq_same] at h1
    obtain ⟨M, hM⟩ := set_classify I hmul N hN hNI hbI

    have key : ∀ t : P.adicCompletion E, Valued.v (ϖ ^ M * t) ≤ 1 ↔ Valued.v t ≤ WithZero.exp M := by
      intro t
      rw [map_mul, map_zpow₀, hϖ, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg_one]
      constructor
      · intro h
        calc Valued.v t = WithZero.exp M * (WithZero.exp (-M) * Valued.v t) := by
              rw [← mul_assoc, ← WithZero.exp_add, add_neg_cancel, WithZero.exp_zero, one_mul]
          _ ≤ WithZero.exp M * 1 := by gcongr
          _ = WithZero.exp M := mul_one _
      · intro h
        calc WithZero.exp (-M) * Valued.v t ≤ WithZero.exp (-M) * WithZero.exp M := by gcongr
          _ = 1 := by rw [← WithZero.exp_add, neg_add_cancel, WithZero.exp_zero]
    refine ⟨M, fun w => ⟨fun hw i => ?_, fun hw => ?_⟩⟩
    · exact (key (w i)).2 ((hM (w i)).1
        ((hIall i (w i)).1 (single_mem_of_mem σ L hO hU u hu hu1 hu2 hu3 hu4 w hw i)))
    · rw [← Finset.univ_sum_single w]
      exact L.sum_mem fun i _ => (hIall i (w i)).2 ((hM (w i)).2 ((key (w i)).1 (hw i)))

end GlobalTheory.LocLatInert
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarCoeffEisensteinSeriesReversePoly
section
noncomputable section

open Polynomial CategoryTheory

namespace GlobalTheory.SerConj

open Formalism.IrreducibleCountingLemmas.TYPES

section Tensor

variable {ι : Type} {V W : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]

def semiMap (σ : ℂ →+* ℂ) (j : ∀ i, V i →+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v) :
    PiTensorProduct ℂ V →+ PiTensorProduct ℂ W :=
  PiTensorProduct.liftAddHom (fun p => σ p.1 • PiTensorProduct.tprod ℂ fun i => j i (p.2 i))
    (fun r f i hf => by
      rw [MultilinearMap.map_coord_zero _ i (by simp [hf]), smul_zero])
    (fun f => by simp)
    (fun r f i m₁ m₂ => by
      have e : ∀ m : V i, (fun k => j k (Function.update f i m k)) =
          Function.update (fun k => j k (f k)) i (j i m) := fun m =>
        funext fun k => Function.apply_update (fun k => j k) f i m k
      simp only [e, map_add, MultilinearMap.map_update_add, smul_add])
    (fun r r' f => by simp [add_smul])
    (fun r f i r' => by
      have e : ∀ m : V i, (fun k => j k (Function.update f i m k)) =
          Function.update (fun k => j k (f k)) i (j i m) := fun m =>
        funext fun k => Function.apply_update (fun k => j k) f i m k
      simp only [e, hj, MultilinearMap.map_update_smul, Function.update_eq_self, map_mul, smul_smul, mul_comm])

theorem semiMap_tprod (σ : ℂ →+* ℂ) (j : ∀ i, V i →+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v)
    (a : ℂ) (f : ∀ i, V i) :
    semiMap σ j hj (a • PiTensorProduct.tprod ℂ f) = σ a • PiTensorProduct.tprod ℂ fun i => j i (f i) := by
  rw [← PiTensorProduct.tprodCoeff_eq_smul_tprod]
  rfl

theorem semiMap_smul (σ : ℂ →+* ℂ) (j : ∀ i, V i →+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v)
    (a : ℂ) (x : PiTensorProduct ℂ V) : semiMap σ j hj (a • x) = σ a • semiMap σ j hj x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f => rw [smul_smul, semiMap_tprod, semiMap_tprod, smul_smul, map_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, smul_add]

theorem semiMap_map (σ : ℂ →+* ℂ) (j : ∀ i, V i →+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v)
    (A : ∀ i, V i →ₗ[ℂ] V i) (B : ∀ i, W i →ₗ[ℂ] W i) (h : ∀ i v, j i (A i v) = B i (j i v))
    (x : PiTensorProduct ℂ V) :
    semiMap σ j hj (PiTensorProduct.map A x) = PiTensorProduct.map B (semiMap σ j hj x) := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [map_smul, PiTensorProduct.map_tprod, semiMap_tprod, semiMap_tprod, map_smul, PiTensorProduct.map_tprod]
    simp only [h]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem symm_smul {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (σ : ℂ ≃+* ℂ)
    (j : A ≃+ B) (hj : ∀ (a : ℂ) v, j (a • v) = σ a • j v) (a : ℂ) (w : B) :
    j.symm (a • w) = σ.symm a • j.symm w := by
  apply j.injective
  rw [hj]; simp

theorem semiMap_injective (σ : ℂ ≃+* ℂ) (j : ∀ i, V i ≃+ W i) (hj : ∀ i (a : ℂ) v, j i (a • v) = σ a • j i v) :
    Function.Injective (semiMap σ.toRingHom (fun i => (j i).toAddMonoidHom) hj) := by
  refine Function.LeftInverse.injective
    (g := semiMap σ.symm.toRingHom (fun i => (j i).symm.toAddMonoidHom) fun i => symm_smul σ (j i) (hj i)) fun x => ?_
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine (congrArg _ (semiMap_tprod _ _ _ r f)).trans ((semiMap_tprod _ _ _ _ _).trans ?_)
    simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end Tensor

section Conj

variable {Γ : Type} [Group Γ]

def bcEquiv (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) : τ ≃+ bc σ τ :=
  (Module.finBasis ℂ τ).equivFun.toAddEquiv.trans (AddEquiv.piCongrRight fun _ => σ.toAddEquiv)

theorem bcEquiv_smul (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (a : ℂ) (v : τ) :
    bcEquiv σ τ (a • v) = σ a • bcEquiv σ τ v := by
  refine funext fun i => ?_
  change σ ((Module.finBasis ℂ τ).repr (a • v) i) = σ a * σ ((Module.finBasis ℂ τ).repr v i)
  simp

theorem bcEquiv_ρ (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (γ : Γ) (v : τ) :
    bcEquiv σ τ (τ.ρ γ v) = (bc σ τ).ρ γ (bcEquiv σ τ v) := by
  refine funext fun i => ?_
  change σ ((Module.finBasis ℂ τ).repr (τ.ρ γ v) i) =
    (((LinearMap.toMatrix (Module.finBasis ℂ τ) (Module.finBasis ℂ τ) (τ.ρ γ)).map σ).mulVec
      fun k => σ ((Module.finBasis ℂ τ).repr v k)) i
  rw [← LinearMap.toMatrix_mulVec_repr (Module.finBasis ℂ τ) (Module.finBasis ℂ τ)]
  simp [Matrix.mulVec, dotProduct]

theorem character_bc (σ : ℂ ≃+* ℂ) (τ : FDRep ℂ Γ) (γ : Γ) : (bc σ τ).character γ = σ (τ.character γ) :=
  trace_bcRepr σ τ.ρ γ

theorem simple_bc [Fintype Γ] (σ : ℂ ≃+* ℂ) {τ : FDRep ℂ Γ} (h : Simple τ) : Simple (bc σ τ) := by
  rw [FDRep.simple_iff_char_is_norm_one] at h ⊢
  simp only [character_bc]
  rw [← map_natCast σ, ← h, map_sum]
  simp only [map_mul]

variable {K : Type} [Field K] [Fintype K] [DecidableEq K] {ι : Type} [Fintype ι] [DecidableEq ι]

theorem isCuspidal_bc (σ : ℂ ≃+* ℂ) {τ : FDRep ℂ (GL ι K)} (h : IsCuspidal K τ) : IsCuspidal K (bc σ τ) := by
  intro s b hb hs w hw
  obtain ⟨v, rfl⟩ := (bcEquiv σ τ).surjective w
  rw [h s b hb hs v fun u hu => (bcEquiv σ τ).injective ((bcEquiv_ρ σ τ u v).trans (hw u hu)), map_zero]

theorem isConstituent_bc (σ : ℂ ≃+* ℂ) {s : ℕ} (b : ι → Fin s) (lam : ∀ c : Fin s, FDRep ℂ (GL {i // b i = c} K))
    {τ : FDRep ℂ (GL ι K)} (h : IsConstituent τ (hcRep K b lam)) :
    IsConstituent (bc σ τ) (hcRep K b fun c => bc σ (lam c)) := by
  obtain ⟨φ, hφ, hne⟩ := h
  let J := semiMap σ.toRingHom (fun c => (bcEquiv σ (lam c)).toAddMonoidHom) fun c => bcEquiv_smul σ (lam c)
  have hJ : Function.Injective J := semiMap_injective σ _ _
  let ψ : bc σ τ →ₗ[ℂ] hcSpace K b fun c => bc σ (lam c) :=
    { toFun := fun w => ⟨fun x => J ((φ ((bcEquiv σ τ).symm w)).1 x), fun p x => by
        refine (congrArg J ((φ ((bcEquiv σ τ).symm w)).2 p x)).trans ?_
        exact semiMap_map _ _ _ _ _ (fun c v => bcEquiv_ρ σ (lam c) _ v) _⟩
      map_add' := fun w w' => by
        ext x
        simp
      map_smul' := fun a w => by
        ext x
        change J ((φ ((bcEquiv σ τ).symm (a • w))).1 x) = a • J ((φ ((bcEquiv σ τ).symm w)).1 x)
        rw [symm_smul σ _ (bcEquiv_smul σ τ), map_smul]
        refine (semiMap_smul _ _ _ _ _).trans ?_
        simp [J] }
  refine ⟨ψ, fun γ => ?_, fun h0 => hne ?_⟩
  · refine LinearMap.ext fun w => Subtype.ext (funext fun x => ?_)
    obtain ⟨v, rfl⟩ := (bcEquiv σ τ).surjective w
    change J ((φ ((bcEquiv σ τ).symm ((bc σ τ).ρ γ (bcEquiv σ τ v)))).1 x) =
      J ((φ ((bcEquiv σ τ).symm (bcEquiv σ τ v))).1 (x * γ))
    rw [← bcEquiv_ρ, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
    have := LinearMap.congr_fun (hφ γ) v
    rw [LinearMap.comp_apply] at this
    rw [this]
    rfl
  · refine LinearMap.ext fun v => Subtype.ext (funext fun x => hJ ?_)
    have := congrFun (congrArg Subtype.val (LinearMap.congr_fun h0 (bcEquiv σ τ v))) x
    change J ((φ ((bcEquiv σ τ).symm (bcEquiv σ τ v))).1 x) = 0 at this
    rw [AddEquiv.symm_apply_apply] at this
    rw [this]
    exact (map_zero J).symm

end Conj

section Label

variable {K : Type} [Field K]

theorem normRev_prod {α : Type} (s : Finset α) (P : α → K[X]) :
    C ((∏ c ∈ s, P c).coeff 0)⁻¹ * (∏ c ∈ s, P c).reverse = ∏ c ∈ s, C ((P c).coeff 0)⁻¹ * (P c).reverse := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [reverse]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, ← ih, mul_coeff_zero, mul_inv, C_mul, reverse_mul_of_domain]
    ring

theorem normRev_normRev {f : K[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    C ((C (f.coeff 0)⁻¹ * f.reverse).coeff 0)⁻¹ * (C (f.coeff 0)⁻¹ * f.reverse).reverse = f := by
  have h1 : (C (f.coeff 0)⁻¹ * f.reverse).coeff 0 ≠ 0 := by
    rw [coeff_C_mul, coeff_zero_reverse, hm.leadingCoeff, mul_one]
    exact inv_ne_zero h0
  refine GlobalTheory.DualLabel.eq_of_rootsBar_eq (GlobalTheory.DualLabel.monic_normRev h1) hm ?_
  rw [GlobalTheory.DualLabel.rootsBar_normRev (GlobalTheory.DualLabel.monic_normRev h0) h1, GlobalTheory.DualLabel.rootsBar_normRev hm h0,
    Multiset.map_map]
  simp

variable [Fintype K] [DecidableEq K] {Cv : LabelConv K}

theorem hasLabelO_conj (O : LabelMap K Cv) (hO : LabelMapEquivariant O) {ι : Type} [Fintype ι] [DecidableEq ι]
    {τ : FDRep ℂ (GL ι K)} {f : K[X]} (h : HasLabelO O τ f) :
    HasLabelO O (bc (starRingAut : ℂ ≃+* ℂ) τ) (C (f.coeff 0)⁻¹ * f.reverse) := by
  obtain ⟨s, b, lam, hb, hl, hc, rfl⟩ := h
  refine ⟨s, b, fun c => bc starRingAut (lam c), hb, fun c => ⟨simple_bc _ (hl c).1, isCuspidal_bc _ (hl c).2⟩,
    isConstituent_bc _ b lam hc, ?_⟩
  rw [normRev_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  have hd : 1 ≤ Fintype.card {i // b i = c} := by
    obtain ⟨i, hi⟩ := hb c
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  refine (GlobalTheory.DualLabel.lab_dual O hO _ _ _ hd (Formalism.L2.PT.simple_transp _ (hl c).1)
    (Formalism.L2.PT.isCuspidal_transp _ (hl c).2) (Formalism.L2.PT.simple_transp _ (simple_bc _ (hl c).1))
    (Formalism.L2.PT.isCuspidal_transp _ (isCuspidal_bc _ (hl c).2)) fun γ => ?_).symm
  change (transp _ (bc starRingAut (lam c))).character γ = (transp _ (lam c)).character γ⁻¹
  rw [Formalism.L2.PT.character_transp, Formalism.L2.PT.character_transp, character_bc, map_inv]
  exact PI.SerBridgeGLW.conjugate_character_formula _ _ _

end Label

theorem star_coeff_eSerO : ∀ {g : ℕ} [Fact g.Prime] {C : Formalism.IrreducibleCountingLemmas.TYPES.LabelConv (ZMod g)}
    (O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) C), Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant O →
    ∀ (r : ℕ) (f : Polynomial (ZMod g)), f.Monic → f.coeff 0 ≠ 0 → ∀ x,
      star ((Formalism.L2.NT.eSerO O r f).coeff x) =
        (Formalism.L2.NT.eSerO O r (Polynomial.C (f.coeff 0)⁻¹ * f.reverse)).coeff x := by
  intro g _ Cv O hO r f hm h0 x
  classical
  let S : MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) ≃+ MonoidAlgebra ℂ (GL (Fin r) (ZMod g)) :=
    MonoidAlgebra.mapAddEquiv _ (starRingAut : ℂ ≃+* ℂ).toAddEquiv
  have hS : ∀ z y, (S z).coeff y = star (z.coeff y) := fun z y => MonoidAlgebra.coeff_mapAddEquiv _ _ _
  have hSS : ∀ z, S (S z) = z := fun z => by
    ext y
    rw [hS, hS, star_star]
  have hz : ∀ τ : FDRep ℂ (GL (Fin r) (ZMod g)), zIdem (bc starRingAut τ) = S (zIdem τ) := fun τ => by
    ext y
    rw [hS]
    exact (galoisConjCentralIdempotent _ starRingAut τ y).symm
  rw [← hS]
  congr 2
  unfold Formalism.L2.NT.eSerO
  rw [S.map_finsum]
  refine finsum_eq_of_bijective S S.bijective fun z => ?_
  have hiff : (∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = z ∧ HasLabelO O τ f) ↔
      ∃ τ : FDRep ℂ (GL (Fin r) (ZMod g)), Simple τ ∧ zIdem τ = S z ∧
        HasLabelO O τ (C (f.coeff 0)⁻¹ * f.reverse) := by
    constructor
    · rintro ⟨τ, h1, h2, h3⟩
      exact ⟨_, simple_bc _ h1, by rw [hz, h2], hasLabelO_conj O hO h3⟩
    · rintro ⟨τ, h1, h2, h3⟩
      have h4 := hasLabelO_conj O hO h3
      rw [normRev_normRev hm h0] at h4
      exact ⟨_, simple_bc _ h1, by rw [hz, h2, hSS], h4⟩
  rw [finsum_eq_if, finsum_eq_if, ← hiff]
  split_ifs
  · rfl
  · exact map_zero S

end GlobalTheory.SerConj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubsingletonHypercohomologyOfLocallyExactOnSuppoStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.subsingleton_hypercohomology_of_locallyExact_on_support : ∀ (R : Type) [CommRing R] (E : Spc) (C : Cx R) [C.IsKInjective], (∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → ∀ (n : ℤ) (b : Sec (C.X n) U), Sec.map (C.d n (n + 1)) b = 0 → Loc U fun V g => ∃ a : Sec (C.X (n - 1)) V, Sec.map (C.d (n - 1) n) a = Sec.res g b) → ∀ n, Subsingleton (CohomologyClass ((chains R).obj E) C n) := by
  first | (exact @GlobalTheory.EtC.subsingleton_of_locExact_supp) | (exact GlobalTheory.EtC.subsingleton_of_locExact_supp) | (intros; apply GlobalTheory.EtC.subsingleton_of_locExact_supp  <;> assumption)
end

