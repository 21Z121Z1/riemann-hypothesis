import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0586
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import ReciprocityTheory.DualLattices.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0593
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0594
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0590

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockTriVecMulEqSinglePred
section
noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open Formalism.L2.DIV Module Matrix

theorem eq_one_off_mul {F : Type} [Field F] {r : ℕ} (S : Fin r → Prop) (M N : Matrix (Fin r) (Fin r) F)
    (hM : ∀ i j, ¬ (S i ∧ S j) → M i j = (1 : Matrix (Fin r) (Fin r) F) i j)
    (hN : ∀ i j, ¬ (S i ∧ S j) → N i j = (1 : Matrix (Fin r) (Fin r) F) i j) :
    ∀ i j, ¬ (S i ∧ S j) → (M * N) i j = (1 : Matrix (Fin r) (Fin r) F) i j := by
  intro i j hij
  by_cases hi : S i
  · have hj : ¬ S j := fun h => hij ⟨hi, h⟩
    have e : (M * N) i j = (M * (1 : Matrix (Fin r) (Fin r) F)) i j := by
      simp only [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => by rw [hN a j fun h => hj h.2]
    rw [e, Matrix.mul_one, hM i j hij]
  · have e : (M * N) i j = ((1 : Matrix (Fin r) (Fin r) F) * N) i j := by
      simp only [Matrix.mul_apply]
      exact Finset.sum_congr rfl fun a _ => by rw [hM i a fun h => hi h.1]
    rw [e, Matrix.one_mul, hN i j hij]

theorem exists_gl_vecMul_eq_single_of_ne {F : Type} [Field F] {r : ℕ} (S : Fin r → Prop) (c : Fin r) (hc : S c)
    (l : Fin r → F) (hl : l c ≠ 0) (hS : ∀ i, l i ≠ 0 → S i) :
    ∃ h : GL (Fin r) F, (∀ i j, ¬ (S i ∧ S j) → (h : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) ∧
      Matrix.vecMul l (h : Matrix (Fin r) (Fin r) F) = Pi.single c 1 := by
  set e : Fin r → F := Pi.single c 1 with he
  set A : Matrix (Fin r) (Fin r) F := vecMulVec e (l - e) with hA
  have hd : (l - e) ⬝ᵥ e = l c - 1 := by simp [he]
  have hAA : A * A = (l c - 1) • A := by
    rw [hA, vecMulVec_mul_vecMulVec, hd, vecMulVec_smul]
  have h1 : (1 - (l c)⁻¹ • A) * (1 + A) = 1 := by
    rw [sub_mul, one_mul, smul_mul_assoc, mul_add, mul_one, hAA]
    have : A + (l c - 1) • A = l c • A := by rw [sub_smul, one_smul]; abel
    rw [this, smul_smul, inv_mul_cancel₀ hl, one_smul]; abel
  refine ⟨⟨1 - (l c)⁻¹ • A, 1 + A, h1, mul_eq_one_comm.mp h1⟩, ?_, ?_⟩
  · intro i j hij
    have : A i j = 0 := by
      rw [hA, vecMulVec_apply]
      by_cases hi : i = c
      · have hj : ¬ S j := fun h => hij ⟨hi ▸ hc, h⟩
        have hlj : l j = 0 := by
          by_contra h
          exact hj (hS j h)
        have hjc : j ≠ c := fun h => hj (h ▸ hc)
        simp [he, hlj, hjc]
      · simp [he, hi]
    simp [this]
  · have hv : Matrix.vecMul l A = l c • (l - e) := by
      rw [hA, vecMul_vecMulVec]
      simp [he]
    show Matrix.vecMul l (1 - (l c)⁻¹ • A) = e
    rw [vecMul_sub, vecMul_one, vecMul_smul, hv, smul_smul, inv_mul_cancel₀ hl, one_smul]
    abel

theorem exists_gl_vecMul_eq_single {F : Type} [Field F] {r : ℕ} (S : Fin r → Prop) (c : Fin r) (hc : S c)
    (l : Fin r → F) (hl : l ≠ 0) (hS : ∀ i, l i ≠ 0 → S i) :
    ∃ h : GL (Fin r) F, (∀ i j, ¬ (S i ∧ S j) → (h : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) ∧
      Matrix.vecMul l (h : Matrix (Fin r) (Fin r) F) = Pi.single c 1 := by
  by_cases hlc : l c = 0
  swap
  · exact exists_gl_vecMul_eq_single_of_ne S c hc l hlc hS
  obtain ⟨a, ha⟩ := Function.ne_iff.mp hl
  have ha : l a ≠ 0 := ha
  have hac : a ≠ c := fun h => ha (h ▸ hlc)
  have h1 : transvection a c (1 : F) * transvection a c (-1 : F) = 1 := by
    rw [transvection_mul_transvection_same a c hac, add_neg_cancel, transvection_zero]
  let t : GL (Fin r) F := ⟨transvection a c 1, transvection a c (-1), h1, mul_eq_one_comm.mp h1⟩
  have hv : ∀ j, Matrix.vecMul l (transvection a c (1 : F)) j = l j + if j = c then l a else 0 := by
    intro j
    rw [transvection, vecMul_add, vecMul_one, Pi.add_apply]
    congr 1
    by_cases hj : j = c
    · subst hj
      simp [vecMul, dotProduct, Matrix.single_apply]
    · simp [vecMul, dotProduct, Matrix.single_apply, hj, Ne.symm hj]
  obtain ⟨h, hh1, hh2⟩ := exists_gl_vecMul_eq_single_of_ne S c hc (Matrix.vecMul l (transvection a c (1 : F)))
    (by rw [hv]; simpa [hlc] using ha)
    (by
      intro i hi
      by_cases hic : i = c
      · exact hic ▸ hc
      · rw [hv] at hi
        exact hS i (by simpa [hic] using hi))
  refine ⟨t * h, ?_, ?_⟩
  · refine eq_one_off_mul S (transvection a c (1 : F)) _ ?_ hh1
    intro i j hij
    have : ¬ (a = i ∧ c = j) := fun h => hij ⟨h.1 ▸ hS a ha, h.2 ▸ hc⟩
    simp [transvection, Matrix.single_apply, this]
  · rw [← hh2, vecMul_vecMul]
    rfl

theorem exists_blockTri_vecMul_eq_single : ∀ (F : Type) [Field F] (r : ℕ) (b : Fin r → ℕ), Monotone b → ∀ (k k' : Fin r), k'.val + 1 = k.val → ∀ l : Fin r → F, l ≠ 0 → (∀ i, l i ≠ 0 → i < k ∧ b i = b k) → ∃ h : blockTri (κ := F) b, (∀ i j, ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k) ∧ Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = Pi.single k' 1 := by
  intro F _ r b hb k k' hk l hl hS
  have hk' : k' < k ∧ b k' = b k := by
    obtain ⟨a, ha⟩ := Function.ne_iff.mp hl
    obtain ⟨h1, h2⟩ := hS a ha
    have h3 : k' < k := by rw [Fin.lt_def]; omega
    have h4 : a ≤ k' := by rw [Fin.lt_def] at h1; rw [Fin.le_def]; omega
    exact ⟨h3, le_antisymm (hb h3.le) (h2 ▸ hb h4)⟩
  obtain ⟨h, h1, h2⟩ := exists_gl_vecMul_eq_single (fun i => i < k ∧ b i = b k) k' hk' l hl hS
  refine ⟨⟨h, ?_⟩, ?_, h2⟩
  · have : (h : Matrix (Fin r) (Fin r) F).BlockTriangular b := by
      intro i j hij
      rw [h1 i j (fun hh => by rw [hh.1.2, hh.2.2] at hij; exact lt_irrefl _ hij)]
      exact Matrix.one_apply_ne (fun e => by rw [e] at hij; exact lt_irrefl _ hij)
    exact this
  · intro i j hij
    by_contra hn
    exact hij (h1 i j fun hh => hn ⟨hh.1.1, hh.2.1⟩)

end GlobalTheory.FinGL.LeviWh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColumnCharacterEigenSubmoduleNeBot
section
noncomputable section

namespace GlobalTheory.FinGL.LeviWh

open GlobalTheory.FinGL Formalism.L2.DIV Module

theorem exists_eigenvector_of_stable {F : Type} [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1)
    {ι : Type} [Fintype ι] [DecidableEq ι] {V : Type} [AddCommGroup V] [Module ℂ V]
    (T : (ι → F) → V →ₗ[ℂ] V) (h0 : T 0 = LinearMap.id) (hT : ∀ x x' v, T x (T x' v) = T (x + x') v)
    (W : Submodule ℂ V) (hW : ∀ x, ∀ v ∈ W, T x v ∈ W) (hne : W ≠ ⊥) :
    ∃ l : ι → F, ∃ w ∈ W, w ≠ 0 ∧ ∀ x, T x w = ψ (∑ i, l i * x i) • w := by
  classical
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff W).1 hne
  let w : (ι → F) → V := fun l => ∑ x : ι → F, ψ (-∑ i, l i * x i) • T x v
  have hprim := AddChar.IsPrimitive.of_ne_one hψ
  have hs : ∀ x : ι → F, x ≠ 0 → ∑ l : ι → F, ψ (-∑ i, l i * x i) = 0 := by
    intro x hx
    have e : ∀ l : ι → F, ψ (-∑ i, l i * x i) = ∏ i, ψ (l i * (-x i)) := by
      intro l
      rw [← Finset.sum_neg_distrib]
      simp only [mul_neg]
      induction (Finset.univ : Finset ι) using Finset.induction_on with
      | empty => simp
      | insert a s ha ih => rw [Finset.sum_insert ha, Finset.prod_insert ha, AddChar.map_add_eq_mul, ih]
    simp only [e]
    rw [← Fintype.piFinset_univ, ← Finset.prod_univ_sum (fun _ => Finset.univ) (fun i t => ψ (t * (-x i)))]
    obtain ⟨i, hi⟩ := Function.ne_iff.1 hx
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    have := AddChar.sum_mulShift (ψ := ψ) (-x i) hprim
    rw [if_neg (by simpa using hi)] at this
    simpa using this
  have hsum : ∑ l, w l = (Fintype.card (ι → F) : ℂ) • v := by
    simp only [w]
    rw [Finset.sum_comm, Finset.sum_eq_single (0 : ι → F)]
    · simp [h0, Nat.cast_smul_eq_nsmul, -Fintype.card_pi]
    · intro x _ hx
      rw [← Finset.sum_smul, hs x hx, zero_smul]
    · simp
  have hex : ∃ l, w l ≠ 0 := by
    by_contra hc
    push Not at hc
    rw [Finset.sum_eq_zero fun l _ => hc l] at hsum
    rcases smul_eq_zero.1 hsum.symm with h | h
    · exact (Nat.cast_ne_zero.2 Fintype.card_ne_zero) h
    · exact hv0 h
  obtain ⟨l, hl⟩ := hex
  refine ⟨l, w l, W.sum_mem fun x _ => W.smul_mem _ (hW x v hv), hl, fun x => ?_⟩
  simp only [w, map_sum, map_smul, hT, Finset.smul_sum, smul_smul]
  refine Fintype.sum_equiv (Equiv.addLeft x) _ _ fun z => ?_
  simp only [Equiv.coe_addLeft, ← AddChar.map_add_eq_mul, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  congr 2
  ring

variable {F : Type} [Field F] {r : ℕ}

def colMat (k : Fin r) (x : Fin r → F) : Matrix (Fin r) (Fin r) F :=
  Matrix.of fun i j => if i < k ∧ j = k then x i else 0

theorem colMat_mul_apply (k : Fin r) (x : Fin r → F) (M : Matrix (Fin r) (Fin r) F) (i j : Fin r) :
    (colMat k x * M) i j = if i < k then x i * M k j else 0 := by
  rw [Matrix.mul_apply, Finset.sum_eq_single k]
  · by_cases h : i < k <;> simp [colMat, h]
  · intro m _ hm
    simp [colMat, hm]
  · simp

theorem one_add_colMat_mul (k : Fin r) (x x' : Fin r → F) :
    (1 + colMat k x) * (1 + colMat k x') = 1 + colMat k (x + x') := by
  have : colMat k x * colMat k x' = 0 := by
    ext i j
    rw [colMat_mul_apply]
    simp [colMat]
  have h2 : colMat k (x + x') = colMat k x + colMat k x' := by
    ext i j
    simp only [colMat, Matrix.of_apply, Matrix.add_apply, Pi.add_apply]
    split_ifs <;> simp
  rw [h2, add_mul, mul_add, mul_add, this]
  simp only [one_mul, mul_one]
  abel

theorem colMat_zero (k : Fin r) : colMat k (0 : Fin r → F) = 0 := by
  ext i j
  simp [colMat]

def colGL (k : Fin r) (x : Fin r → F) : GL (Fin r) F where
  val := 1 + colMat k x
  inv := 1 + colMat k (-x)
  val_inv := by rw [one_add_colMat_mul]; simp [colMat_zero]
  inv_val := by rw [one_add_colMat_mul]; simp [colMat_zero]

theorem colGL_mem_unip (k : Fin r) (x : Fin r → F) : colGL k x ∈ unip F r := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · have hij' : j < i := hij
    have : ¬ (i < k ∧ j = k) := fun h => by
      obtain ⟨h1, rfl⟩ := h
      exact lt_asymm h1 hij'
    simp [colGL, colMat, this, Matrix.one_apply_ne hij'.ne']
  · have : ¬ (i < k ∧ i = k) := fun h => h.1.ne h.2
    simp [colGL, colMat, this]

def colEl {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x : Fin r → F) : blockTri (κ := F) b :=
  ⟨colGL k x, fun i j hij => (colGL_mem_unip k x).1 (show j < i from hb.reflect_lt hij)⟩

theorem colEl_val {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x : Fin r → F) :
    ((colEl hb k x : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = 1 + colMat k x := rfl

theorem colEl_mul {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x x' : Fin r → F) :
    colEl hb k x * colEl hb k x' = colEl hb k (x + x') :=
  Subtype.ext (Units.ext (one_add_colMat_mul k x x'))

theorem colEl_zero {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) : colEl hb k (0 : Fin r → F) = 1 :=
  Subtype.ext (Units.ext (by rw [colEl_val, colMat_zero]; simp))

theorem colEl_neg_mul {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x : Fin r → F) {u : blockTri (κ := F) b}
    (hu : u ∈ colSet F b k.val)
    (hx : ∀ i, i < k → x i = ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k) :
    colEl hb k (-x) * u ∈ colSet F b (k.val + 1) ∧
      edgeSum (blkEdge b) ((colEl hb k (-x) * u : blockTri (κ := F) b) : GL (Fin r) F) =
        edgeSum (fun i j => blkEdge b i j ∧ k < j) (u : GL (Fin r) F) := by
  have e : ∀ i j, (((colEl hb k (-x) * u : blockTri (κ := F) b) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
      ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j +
        if i < k then -x i * ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) k j else 0 := by
    intro i j
    rw [Subgroup.coe_mul, Units.val_mul, colEl_val, add_mul, one_mul, Matrix.add_apply, colMat_mul_apply]
    rfl
  have hc : ∀ i j : Fin r, j.val < k.val + 1 →
      (((colEl hb k (-x) * u : blockTri (κ := F) b) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
        (1 : Matrix (Fin r) (Fin r) F) i j := by
    intro i j hj
    rw [e]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | h
    · rw [hu.2 i j h, hu.2 k j h, Matrix.one_apply_ne (i := k) (j := j) (fun h' => by simp [h'] at h)]
      simp
    · obtain rfl : j = k := Fin.ext h
      rw [hu.1.2 j]
      rcases lt_trichotomy i j with h' | h' | h'
      · rw [if_pos h', hx i h', Matrix.one_apply_ne h'.ne]; ring
      · subst h'; simp [hu.1.2 i]
      · rw [if_neg (lt_asymm h'), hu.1.1 (show j.val < i.val from h'), Matrix.one_apply_ne h'.ne']; simp
  refine ⟨⟨(unip F r).mul_mem (colGL_mem_unip k (-x)) hu.1, hc⟩, ?_⟩
  unfold edgeSum
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  by_cases hij : blkEdge b i j
  · have h1 := hij.1
    by_cases hk : k < j
    · have : ¬ i < k := by rw [Fin.lt_def] at hk ⊢; omega
      rw [if_pos hij, if_pos ⟨hij, hk⟩, e, if_neg this, add_zero]
    · rw [if_pos hij, if_neg (fun h => hk h.2), hc i j (by rw [Fin.lt_def] at hk; omega),
        Matrix.one_apply_ne (fun h' => by simp [h'] at h1)]
  · rw [if_neg hij, if_neg (fun h => hij h.1)]

theorem mul_colEl_val {b : Fin r → ℕ} (hb : Monotone b) (k : Fin r) (x : Fin r → F) {u : blockTri (κ := F) b}
    (hu : u ∈ colSet F b (k.val + 1)) (i j : Fin r) :
    (((u * colEl hb k x : blockTri (κ := F) b) : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j =
      ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j + if i < k ∧ j = k then x i else 0 := by
  rw [Subgroup.coe_mul, Units.val_mul, colEl_val, mul_add, mul_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  have : ∀ m, ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i m * colMat k x m j =
      (1 : Matrix (Fin r) (Fin r) F) i m * colMat k x m j := by
    intro m
    by_cases hm : m < k
    · rw [hu.2 i m (by rw [Fin.lt_def] at hm; omega)]
    · simp [colMat, hm]
  simp only [this]
  rw [← Matrix.mul_apply, one_mul]
  rfl

theorem colEl_stable {V : Type} [AddCommGroup V] [Module ℂ V] (ψ : AddChar F ℂ) {b : Fin r → ℕ} (hb : Monotone b)
    (σ : Representation ℂ (blockTri (κ := F) b) V) (k : Fin r) (x : Fin r → F) (v : V)
    (hv : v ∈ eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F)))) :
    σ (colEl hb k x) v ∈ eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) := by
  rw [mem_eig] at hv ⊢
  intro u hu
  have hu' : u ∈ colSet F b k.val := ⟨hu.1, fun i j hj => hu.2 i j (by omega)⟩
  have hm : u * colEl hb k x ∈ colSet F b k.val := by
    refine ⟨(unip F r).mul_mem hu.1 (colGL_mem_unip k x), fun i j hj => ?_⟩
    rw [mul_colEl_val hb k x hu, hu.2 i j (by omega), if_neg (fun h => by simp [h.2] at hj), add_zero]
  obtain ⟨h1, h2⟩ := colEl_neg_mul hb k x hm (fun i hi => by
    rw [mul_colEl_val hb k x hu, hu.2 i k (by omega), if_pos ⟨hi, rfl⟩, Matrix.one_apply_ne hi.ne, zero_add])
  obtain ⟨-, h3⟩ := colEl_neg_mul hb k 0 hu' (fun i hi => by
    rw [hu.2 i k (by omega), Matrix.one_apply_ne hi.ne]; rfl)
  rw [neg_zero, colEl_zero, one_mul] at h3
  have h4 : edgeSum (fun i j => blkEdge b i j ∧ k < j) ((u * colEl hb k x : blockTri (κ := F) b) : GL (Fin r) F) =
      edgeSum (fun i j => blkEdge b i j ∧ k < j) (u : GL (Fin r) F) := by
    unfold edgeSum
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs with h
    · rw [mul_colEl_val hb k x hu, if_neg (fun h' => h.2.ne' h'.2), add_zero]
    · rfl
  have h5 := hv _ h1
  rw [h2, h4, ← h3] at h5
  have h6 : u * colEl hb k x = colEl hb k x * (colEl hb k (-x) * (u * colEl hb k x)) := by
    rw [← mul_assoc (colEl hb k x), colEl_mul, add_neg_cancel, colEl_zero, one_mul]
  rw [← Module.End.mul_apply, ← map_mul, h6, map_mul, Module.End.mul_apply, h5, map_smul]

theorem exists_colChar_eig_ne_bot : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V), Monotone b → (∀ p : blockTri (κ := F) b, (∀ i j, b i = b j → ((p : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j = (1 : Matrix (Fin r) (Fin r) F) i j) → σ p = 1) → ∀ k : Fin r, eig σ (colSet F b (k.val + 1)) (fun p => ψ (edgeSum (blkEdge b) (p : GL (Fin r) F))) ≠ ⊥ → ∃ l : Fin r → F, (∀ i, l i ≠ 0 → i < k ∧ b i = b k) ∧ eig σ (colSet F b k.val) (colChar ψ b k l) ≠ ⊥ := by
  intro F _ _ ψ hψ r V _ _ b σ hb hinf k hne
  obtain ⟨l, w, hw, hw0, hl⟩ := exists_eigenvector_of_stable ψ hψ (fun x => σ (colEl hb k x))
    (by rw [colEl_zero, map_one]; rfl)
    (fun x x' v => by rw [← Module.End.mul_apply, ← map_mul, colEl_mul]) _
    (fun x v hv => colEl_stable ψ hb σ k x v hv) hne
  refine ⟨l, fun i hi => ?_, (Submodule.ne_bot_iff _).2 ⟨w, ?_, hw0⟩⟩
  · by_contra hc
    refine AddChar.IsPrimitive.of_ne_one hψ hi (AddChar.ext _ _ fun t => ?_)
    have h1 : σ (colEl hb k (Pi.single i t)) = 1 := by
      refine hinf _ fun a c hac => ?_
      rw [colEl_val, Matrix.add_apply, add_eq_left]
      simp only [colMat, Matrix.of_apply]
      split_ifs with h
      · refine Pi.single_eq_of_ne (fun h' => hc ?_) _
        rw [← h', hac, h.2]
        exact ⟨h.2 ▸ h.1, rfl⟩
      · rfl
    have h2 := hl (Pi.single i t)
    rw [h1, Finset.sum_eq_single i (fun a _ ha => by simp [ha]) (by simp), Pi.single_eq_same] at h2
    have h3 : (ψ (l i * t) - 1) • w = 0 := by rw [sub_smul, ← h2]; simp
    have h4 := (smul_eq_zero.1 h3).resolve_right hw0
    simpa [sub_eq_zero] using h4
  · rw [mem_eig] at hw ⊢
    intro u hu
    set x : Fin r → F := fun i => ((u : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i k with hx
    obtain ⟨h1, h2⟩ := colEl_neg_mul hb k x hu (fun i _ => rfl)
    have h5 := hw _ h1
    rw [h2] at h5
    have h6 : u = colEl hb k x * (colEl hb k (-x) * u) := by
      rw [← mul_assoc (colEl hb k x), colEl_mul, add_neg_cancel, colEl_zero, one_mul]
    calc σ u w = σ (colEl hb k x) (σ (colEl hb k (-x) * u) w) := by
          rw [← Module.End.mul_apply, ← map_mul, ← h6]
      _ = _ := by
          rw [h5, map_smul, hl x, smul_smul, colChar, AddChar.map_add_eq_mul, mul_comm]

end GlobalTheory.FinGL.LeviWh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCycPerfd
section
set_option autoImplicit false

noncomputable section

open Ideal WittVector

namespace GlobalTheory.PerfdCompletion

theorem t_complete (p : ℕ) (A : Type) [CommRing A] :
    IsAdicComplete (span {(p : AdicCompletion (span {(p : A)}) A)})
      (AdicCompletion (span {(p : A)}) A) := by
  have h := AdicCompletion.isAdicComplete (R := A) (I := span {(p : A)}) (M := A)
    (Submodule.fg_span_singleton _)
  rw [← IsAdicComplete.map_algebraMap_iff (S := AdicCompletion (span {(p : A)}) A)] at h
  simpa [Ideal.map_span] using h

section Closed

theorem exists_pow_eq {A : Type} (K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [IsAlgClosed K]
    [Algebra A K] [IsFractionRing A K] (x : A) {n : ℕ} (hn : 0 < n) : ∃ y : A, y ^ n = x := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap A K x) hn
  have hi : IsIntegral A z := ⟨Polynomial.X ^ n - Polynomial.C x,
    Polynomial.monic_X_pow_sub_C x hn.ne', by simp [hz]⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).1 hi
  exact ⟨y, IsFractionRing.injective A K (by rw [map_pow, hy, hz])⟩

theorem dvd_of_dvd_pow {A : Type} (K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K]
    [Algebra A K] [IsFractionRing A K] {a π x : A} {m : ℕ} (hm : 0 < m) (hπ : π ^ m = a) (h0 : π ≠ 0)
    (h : a ∣ x ^ m) : π ∣ x := by
  obtain ⟨b, hb⟩ := h
  have hπK : algebraMap A K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective A K)).2 h0
  set z := algebraMap A K x / algebraMap A K π
  have hz : z ^ m = algebraMap A K b := by
    have ha : algebraMap A K a ≠ 0 := by rw [← hπ, map_pow]; exact pow_ne_zero _ hπK
    rw [div_pow, div_eq_iff (pow_ne_zero _ hπK), ← map_pow, ← map_pow, hπ, hb, map_mul, mul_comm]
  have hi : IsIntegral A z := ⟨Polynomial.X ^ m - Polynomial.C b,
    Polynomial.monic_X_pow_sub_C b hm.ne', by simp [hz]⟩
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := K)).1 hi
  refine ⟨y, IsFractionRing.injective A K ?_⟩
  rw [map_mul, hy, mul_div_cancel₀ _ hπK]

end Closed

theorem exists_cycPerfd : ∀ (p : ℕ) [Fact p.Prime] (A K : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [Field K] [IsAlgClosed K] [CharZero K] [Algebra A K] [IsFractionRing A K], ¬ IsUnit (p : A) → ∀ ζ : ℕ → A, (∀ n, IsPrimitiveRoot (ζ n) (p ^ n)) → (∀ n, ζ (n + 1) ^ p = ζ n) → ∃ (S : GlobalTheory.Published.CycPerfd p) (e : AdicCompletion (Ideal.span {(p : A)}) A ≃+* S.R), ∀ n, GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta S.ε n = e (algebraMap A _ (ζ n)) := by
  intro p _ A K _ _ _ _ _ _ _ _ hpA ζ hζ hζs
  have hp0 : (p : A) ≠ 0 := by
    intro h
    have h' := congrArg (algebraMap A K) h
    rw [map_natCast, map_zero, Nat.cast_eq_zero] at h'
    exact (Fact.out : p.Prime).ne_zero h'
  have hreg : IsSMulRegular A (p : A) := fun x y h => mul_left_cancel₀ hp0 h
  obtain ⟨hsurj, hker⟩ := GlobalTheory.T.adic_completion_quotient_ker_eq p A hreg
  set R := AdicCompletion (span {(p : A)}) A
  set φ := (Ideal.Quotient.mk (span {(p : R)})).comp (algebraMap A R) with hφ
  have hnu : ¬IsUnit (p : R) := by
    intro h
    have h1 : IsUnit (Ideal.Quotient.mk (span {(p : R)}) (p : R)) := h.map _
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (mem_span_singleton_self _), isUnit_zero_iff] at h1
    have h2 : (1 : A) ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_one]; exact h1.symm
    rw [hker, mem_span_singleton] at h2
    exact hpA (isUnit_of_dvd_one h2)
  haveI : Fact ¬IsUnit (p : R) := ⟨hnu⟩
  haveI : IsAdicComplete (span {(p : R)}) R := t_complete p A
  set z : ℕ → R := fun n => algebraMap A R (ζ n) with hzdef
  have hz : ∀ n, z (n + 1) ^ p = z n := fun n => by simp only [hzdef, ← map_pow, hζs]
  set ε : PreTilt R p := ReciprocityTheory.PGsh.ofRoots z hz with hεdef
  have hroot : (GlobalTheory.Sandwich.root : PreTilt R p → PreTilt R p) =
      ⇑(_root_.frobeniusEquiv (PreTilt R p) p).symm := rfl
  have hzeta : ∀ n, GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta ε n = z n := by
    intro n
    have := ReciprocityTheory.PGsh.untilt_eq_of_coeff (GlobalTheory.Sandwich.root^[n] ε) (fun k => z (n + k))
      (fun k => hz (n + k)) (fun k => by
        rw [hroot, ← PreTilt.coeff_def, PreTilt.coeff_iterate_frobeniusEquiv_symm, PreTilt.coeff_def,
          ReciprocityTheory.PGsh.coeff_ofRoots, add_comm])
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta] using this
  have hzeta0 : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta ε 0 = 1 := by
    rw [hzeta 0, hzdef]
    have h1 : ζ 0 = 1 := by simpa using (hζ 0)
    simp [h1]
  have hfrob : Function.Surjective (_root_.frobenius (ModP R p) p) := by
    intro c
    obtain ⟨x, rfl⟩ := hsurj c
    obtain ⟨y, hy⟩ := exists_pow_eq K x (Fact.out : p.Prime).pos
    exact ⟨φ y, by rw [frobenius_def, ← map_pow, hy]⟩

  have hroots : ∀ x : A, ∃ y : A, y ^ p = x := fun x => exists_pow_eq K x (Fact.out : p.Prime).pos
  choose r hr using hroots
  let π : ℕ → A := fun n => Nat.rec (p : A) (fun _ y => r y) n
  have hπs : ∀ n, π (n + 1) ^ p = π n := fun n => hr _
  have hπpow : ∀ n, π n ^ (p ^ n) = p := by
    intro n
    induction n with
    | zero => simp [π]
    | succ n ih => rw [pow_succ', pow_mul, hπs, ih]
  have hπ0 : ∀ n, π n ≠ 0 := fun n h => hp0 (by rw [← hπpow n, h, zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)])
  have hdiv : ∀ (n : ℕ) (x : A), (p : A) ∣ x ^ (p ^ n) → π n ∣ x := fun n x h =>
    dvd_of_dvd_pow K (pow_pos (Fact.out : p.Prime).pos n) (hπpow n) (hπ0 n) h
  obtain ⟨pflat, hpf, hpdiv⟩ := GlobalTheory.T.perfectoid_tower_surjective p A R (algebraMap A R) hp0 hsurj hker π rfl hπs hdiv
  have hregR := GlobalTheory.T.isSMulRegular_adicCompletion p A hreg

  set f : PreTilt R p := (_root_.frobeniusEquiv (PreTilt R p) p).symm (GlobalTheory.Sandwich.root ε) with hf
  have hfp : f ^ p = GlobalTheory.Sandwich.root ε := frobeniusEquiv_symm_pow_p (PreTilt R p) p _
  have hfu : PreTilt.untilt f = z 2 := by
    rw [← hzeta 2]
    simp [GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.zeta, hf, hroot]
  have hass : Associated ((PreTilt.untilt f - 1) ^ (p * (p - 1))) (p : R) := by
    have h := GlobalTheory.associated_primitiveRoot_sub_one_pow_totient_prime_pow (k := 1)
      (Fact.out : p.Prime) (hζ 2)
    rw [Nat.totient_prime_pow_succ (Fact.out : p.Prime), pow_one] at h
    have h2 := h.map (algebraMap A R)
    rw [map_pow, map_sub, map_one, map_natCast] at h2
    rw [hfu]; exact h2
  have hdivξ : ∀ c : PreTilt R p, PreTilt.coeff 0 c = 0 → WittVector.constantCoeff (GlobalTheory.Sandwich.xi ε) ∣ c := by
    intro c hc
    rw [GlobalTheory.T.constantCoeff_xi_eq_root_sub_one_pow, ← hfp]
    exact GlobalTheory.T.tilt_untilt_divides_pow p R hregR pflat f hpf hpdiv hass c hc
  have hθξ : fontaineTheta R p (GlobalTheory.Sandwich.xi ε) = 0 := by
    have h1 : PreTilt.untilt (GlobalTheory.Sandwich.root ε) = z 1 := by
      rw [← hzeta 1]; rfl
    rw [GlobalTheory.Sandwich.xi, map_sum]
    simp only [map_pow, fontaineTheta_teichmuller, h1]
    have h2 : ∑ i ∈ Finset.range p, z 1 ^ i = algebraMap A R (∑ i ∈ Finset.range p, ζ 1 ^ i) := by
      simp [hzdef]
    have h3 : ∑ i ∈ Finset.range p, ζ 1 ^ i = 0 := by
      have := (hζ 1).geom_sum_eq_zero (by simpa using (Fact.out : p.Prime).one_lt)
      simpa using this
    rw [h2, h3, map_zero]
  refine ⟨⟨R, hregR, ε, hzeta0, surjective_fontaineTheta hfrob,
    GlobalTheory.T.ker_fontaineTheta_eq_span_of_distinguished p R hregR _ hθξ hdivξ⟩, RingEquiv.refl _, fun n => ?_⟩
  exact hzeta n

end GlobalTheory.PerfdCompletion
end
end

