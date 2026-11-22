import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0108
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0100

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitTZpow
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

noncomputable section

namespace GlobalTheory.CompanionTheory.PerfBC

def unitT (R : Type) [CommRing R] : (R[T;T⁻¹])ˣ where
  val := LaurentPolynomial.T 1
  inv := LaurentPolynomial.T (-1)
  val_inv := by rw [← LaurentPolynomial.T_add]; simp
  inv_val := by rw [← LaurentPolynomial.T_add]; simp

theorem bc_laur : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K] (i : A[T;T⁻¹] →ₐ[A] B) (f g : A), Pf p A → Pf p K → PQ p (i : A[T;T⁻¹] →+* B) (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g}) → ∃ i₁ : K[T;T⁻¹] →+* B ⊗[A] K, PQ p i₁ (Ideal.span {LaurentPolynomial.C (algebraMap A K f) - LaurentPolynomial.T 1 * LaurentPolynomial.C (algebraMap A K g)}) ∧ (∀ a, i₁ (LaurentPolynomial.C a) = (1 : B) ⊗ₜ[A] a) ∧ ∀ n : ℤ, i₁ (LaurentPolynomial.T n) = i (LaurentPolynomial.T n) ⊗ₜ[A] (1 : K) := by
  intro p _ A _ B _ _ K _ _ i f g hA hK hPQ
  let j : A[T;T⁻¹] →+* K[T;T⁻¹] :=
    AddMonoidAlgebra.liftNCRingHom ((LaurentPolynomial.C : K →+* K[T;T⁻¹]).comp (algebraMap A K))
      (AddMonoidAlgebra.of K ℤ) (fun _ _ => Commute.all _ _)
  let i₁ : K[T;T⁻¹] →+* B ⊗[A] K :=
    AddMonoidAlgebra.liftNCRingHom
      (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom
      (((Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] K).comp
        (i : A[T;T⁻¹] →+* B)).toMonoidHom.comp (AddMonoidAlgebra.of A ℤ))
      (fun _ _ => Commute.all _ _)
  have hi1 : ∀ (n : ℤ) (k : K), i₁ (AddMonoidAlgebra.single n k) =
      ((1 : B) ⊗ₜ[A] k) * (i (LaurentPolynomial.T n) ⊗ₜ[A] (1 : K)) := by
    intro n k
    exact AddMonoidAlgebra.liftNC_single _ _ n k
  have hj1 : ∀ (n : ℤ) (a : A), j (AddMonoidAlgebra.single n a) =
      LaurentPolynomial.C (algebraMap A K a) * LaurentPolynomial.T n := by
    intro n a
    exact AddMonoidAlgebra.liftNC_single _ _ n a
  have hC : ∀ a, i₁ (LaurentPolynomial.C a) = (1 : B) ⊗ₜ[A] a := by
    intro a
    have h1 := hi1 0 a
    rw [LaurentPolynomial.T_zero, map_one, ← Algebra.TensorProduct.one_def, mul_one] at h1
    exact h1
  have hT : ∀ n : ℤ, i₁ (LaurentPolynomial.T n) = i (LaurentPolynomial.T n) ⊗ₜ[A] (1 : K) := by
    intro n
    have h1 := hi1 n 1
    rw [← Algebra.TensorProduct.one_def, one_mul] at h1
    exact h1
  have hjC : ∀ a, j (LaurentPolynomial.C a) = LaurentPolynomial.C (algebraMap A K a) := by
    intro a
    have h1 := hj1 0 a
    rw [LaurentPolynomial.T_zero, mul_one] at h1
    exact h1
  have hjT : ∀ n : ℤ, j (LaurentPolynomial.T n) = LaurentPolynomial.T n := by
    intro n
    have h1 := hj1 n 1
    rw [map_one, map_one, one_mul] at h1
    exact h1
  have hiC : ∀ a, i (LaurentPolynomial.C a) = algebraMap A B a := by
    intro a
    rw [← AlgHom.commutes i a, LaurentPolynomial.algebraMap_apply, Algebra.algebraMap_self_apply]
  have hcomp : (LaurentPolynomial.C : K →+* K[T;T⁻¹]).comp (algebraMap A K) =
      j.comp (algebraMap A A[T;T⁻¹]) := by
    ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, LaurentPolynomial.algebraMap_apply,
      Algebra.algebraMap_self_apply, hjC]
  have hgen : Subring.closure (Set.range (LaurentPolynomial.C : K →+* K[T;T⁻¹]) ∪ Set.range j) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    refine LaurentPolynomial.induction_on' q ?_ ?_
    · intro a b ha hb
      exact Subring.add_mem _ ha hb
    · intro n a
      exact Subring.mul_mem _ (Subring.subset_closure (Or.inl ⟨a, rfl⟩))
        (Subring.subset_closure (Or.inr ⟨LaurentPolynomial.T n, hjT n⟩))
  have hij : ∀ s, i₁ (j s) = i s ⊗ₜ[A] (1 : K) := by
    intro s
    refine LaurentPolynomial.induction_on' s ?_ ?_
    · intro a b ha hb
      rw [map_add, map_add, ha, hb, map_add, TensorProduct.add_tmul]
    · intro n a
      rw [map_mul, map_mul, hjC, hjT, map_mul, hC, hT, hiC, Algebra.TensorProduct.tmul_mul_tmul,
        one_mul, mul_one, ← Algebra.smul_def, TensorProduct.smul_tmul,
        ← Algebra.algebraMap_eq_smul_one]
  have hmap : (Ideal.span {LaurentPolynomial.C f - LaurentPolynomial.T 1 * LaurentPolynomial.C g} :
      Ideal A[T;T⁻¹]).map j = Ideal.span {LaurentPolynomial.C (algebraMap A K f) -
        LaurentPolynomial.T 1 * LaurentPolynomial.C (algebraMap A K g)} := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_mul, hjC, hjC, hjT]
  refine ⟨i₁, ?_, hC, hT⟩
  rw [← hmap]
  exact GlobalTheory.T.perfect_tensor_generated_lift p A A[T;T⁻¹] B K K[T;T⁻¹] i _ LaurentPolynomial.C j i₁ hA hK hPQ hcomp hgen
    hC hij

end GlobalTheory.CompanionTheory.PerfBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerBlockEmbeddingConj
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Conj

variable {K : Type} [Field K]

theorem blkEmb_mul_apply {d j : ℕ} (hj : j ≤ d) (A : Matrix (Fin j) (Fin j) K)
    (M : Matrix (Fin d) (Fin d) K) (i l : Fin d) :
    (blkEmb K d j A * M) i l =
      if h : (i : ℕ) < j then ∑ k : Fin j, A ⟨i, h⟩ k * M (Fin.castLE hj k) l else M i l := by
  rw [Matrix.mul_apply]
  by_cases h : (i : ℕ) < j
  · rw [dif_pos h]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
    · intro a ha
      have ha' : ¬ (a : ℕ) < j := fun hlt => ha ⟨⟨a, hlt⟩, by ext; simp⟩
      have hne : i ≠ a := fun e => ha' (e ▸ h)
      simp [blkEmb, ha', hne]
    · intro k
      simp [blkEmb, h]
  · rw [dif_neg h, Finset.sum_eq_single i]
    · simp [blkEmb, h]
    · intro a _ ha
      simp [blkEmb, h, Ne.symm ha]
    · simp

theorem mul_blkEmb_apply {d j : ℕ} (hj : j ≤ d) (B : Matrix (Fin j) (Fin j) K)
    (M : Matrix (Fin d) (Fin d) K) (i l : Fin d) :
    (M * blkEmb K d j B) i l =
      if h : (l : ℕ) < j then ∑ k : Fin j, M i (Fin.castLE hj k) * B k ⟨l, h⟩ else M i l := by
  rw [Matrix.mul_apply]
  by_cases h : (l : ℕ) < j
  · rw [dif_pos h]
    symm
    refine Fintype.sum_of_injective (Fin.castLE hj) (Fin.castLE_injective hj) _ _ ?_ ?_
    · intro a ha
      have ha' : ¬ (a : ℕ) < j := fun hlt => ha ⟨⟨a, hlt⟩, by ext; simp⟩
      have hne : a ≠ l := fun e => ha' (e ▸ h)
      simp [blkEmb, ha', hne]
    · intro k
      simp [blkEmb, h]
  · rw [dif_neg h, Finset.sum_eq_single l]
    · simp [blkEmb, h]
    · intro a _ ha
      simp [blkEmb, h, ha]
    · simp

theorem conj_apply_ge {d j : ℕ} (hj : j ≤ d) (A B : Matrix (Fin j) (Fin j) K)
    (M : Matrix (Fin d) (Fin d) K) (i l : Fin d) (hl : j ≤ (l : ℕ)) :
    (blkEmb K d j A * M * blkEmb K d j B) i l =
      if h : (i : ℕ) < j then ∑ k : Fin j, A ⟨i, h⟩ k * M (Fin.castLE hj k) l else M i l := by
  rw [mul_blkEmb_apply hj, dif_neg (not_lt.2 hl), blkEmb_mul_apply hj]

theorem conj_apply_lt {d j : ℕ} (hj : j ≤ d) (A B : Matrix (Fin j) (Fin j) K) (hAB : A * B = 1)
    (M : Matrix (Fin d) (Fin d) K)
    (hM : ∀ i l : Fin d, (l : ℕ) < j → M i l = if i = l then 1 else 0)
    (i l : Fin d) (hl : (l : ℕ) < j) :
    (blkEmb K d j A * M * blkEmb K d j B) i l = if i = l then 1 else 0 := by
  rw [mul_blkEmb_apply hj, dif_pos hl]
  simp_rw [blkEmb_mul_apply hj]
  by_cases h : (i : ℕ) < j
  · simp only [dif_pos h]
    have inner : ∀ k : Fin j, ∑ m : Fin j, A ⟨i, h⟩ m * M (Fin.castLE hj m) (Fin.castLE hj k)
        = A ⟨i, h⟩ k := by
      intro k
      rw [Finset.sum_eq_single k]
      · rw [hM _ _ (by simp)]
        simp
      · intro m _ hm
        rw [hM _ _ (by simp), if_neg (fun e => hm (Fin.castLE_injective hj e))]
        simp
      · simp
    simp_rw [inner]
    have := congrFun (congrFun hAB ⟨i, h⟩) ⟨l, hl⟩
    rw [Matrix.mul_apply] at this
    rw [this, Matrix.one_apply]
    by_cases e : i = l
    · simp [e]
    · have e' : ¬ ((⟨i, h⟩ : Fin j) = ⟨l, hl⟩) := fun q => e (Fin.ext (by simpa using q))
      simp [e, e']
  · simp only [dif_neg h]
    have hne : i ≠ l := fun e => h (e ▸ hl)
    rw [if_neg hne]
    refine Finset.sum_eq_zero fun k _ => ?_
    have hk : i ≠ Fin.castLE hj k := fun e => h (by rw [e]; simp)
    rw [hM _ _ (by simp), if_neg hk]
    simp

theorem col_lt {d j : ℕ} {u : GL (Fin d) K} (hu : u ∈ patSet K (colGe d j)) (i l : Fin d)
    (hl : (l : ℕ) < j) : (u : Matrix (Fin d) (Fin d) K) i l = if i = l then 1 else 0 := by
  by_cases e : i = l
  · rw [if_pos e]
    exact (hu i l).1 e
  · rw [if_neg e]
    exact (hu i l).2 e (fun c => absurd c.2 (not_le.2 hl))

theorem conj_mem {d j : ℕ} (hj : j ≤ d) (g : GL (Fin j) K) (h : GL (Fin d) K)
    (h1 : (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K))
    (h2 : ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K))
    {u : GL (Fin d) K} (hu : u ∈ patSet K (colGe d j)) :
    h * u * h⁻¹ ∈ patSet K (colGe d j) := by
  have hgg : (g : Matrix (Fin j) (Fin j) K) * ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have key : ((h * u * h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blkEmb K d j (g : Matrix (Fin j) (Fin j) K) * (u : Matrix (Fin d) (Fin d) K) *
        blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) := by
    rw [Units.val_mul, Units.val_mul, h1, h2]
  intro i l
  rw [key]
  by_cases hl : (l : ℕ) < j
  · rw [conj_apply_lt hj _ _ hgg _ (fun a b hb => col_lt hu a b hb) i l hl]
    exact ⟨fun e => if_pos e, fun e _ => if_neg e⟩
  · have hl' : j ≤ (l : ℕ) := not_lt.1 hl
    rw [conj_apply_ge hj _ _ _ i l hl']
    constructor
    · intro e
      have hi : ¬ (i : ℕ) < j := by rw [e]; exact hl
      rw [dif_neg hi]
      exact (hu i l).1 e
    · intro e hc
      have hlt : ¬ i < l := fun q => hc ⟨q, hl'⟩
      have hi : ¬ (i : ℕ) < j := fun q => hlt (by
        rw [Fin.lt_def]; omega)
      rw [dif_neg hi]
      exact (hu i l).2 e (fun c => hlt c.1)

theorem sum_colGeR {d j : ℕ} (hj : j < d) (r : Fin j → K) (M : Matrix (Fin d) (Fin d) K) :
    ∑ i, ∑ l, colGeR K d j r i l * M i l =
      ∑ i, ∑ l, colGeE K d (j + 1) i l * M i l +
        ∑ k : Fin j, r k * M (Fin.castLE hj.le k) ⟨j, hj⟩ := by
  simp only [colGeR, add_mul, Finset.sum_add_distrib]
  congr 1
  symm
  refine Fintype.sum_of_injective (Fin.castLE hj.le) (Fin.castLE_injective hj.le) _ _ ?_ ?_
  · intro a ha
    have ha' : ¬ (a : ℕ) < j := fun hlt => ha ⟨⟨a, hlt⟩, by ext; simp⟩
    refine Finset.sum_eq_zero fun l _ => ?_
    simp [ha']
  · intro k
    rw [Finset.sum_eq_single (⟨j, hj⟩ : Fin d)]
    · simp
    · intro l _ hl
      have : ¬ (l : ℕ) = j := fun e => hl (Fin.ext e)
      simp [this]
    · simp

theorem sum_colGeE_congr {d j : ℕ} (X U : Matrix (Fin d) (Fin d) K)
    (hXU : ∀ i l : Fin d, j ≤ (i : ℕ) → j ≤ (l : ℕ) → X i l = U i l) :
    ∑ i, ∑ l, colGeE K d (j + 1) i l * X i l = ∑ i, ∑ l, colGeE K d (j + 1) i l * U i l := by
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases c : (l : ℕ) = i + 1 ∧ j + 1 ≤ (l : ℕ)
  · rw [hXU i l (by omega) (by omega)]
  · have e : colGeE K d (j + 1) i l = 0 := if_neg c
    rw [e, zero_mul, zero_mul]

theorem patChar_conj {d j : ℕ} (hj : j < d) (ψ₀ : AddChar K ℂ) (g : GL (Fin j) K)
    (h : GL (Fin d) K) (r : Fin j → K)
    (h1 : (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K))
    (h2 : ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K))
    (u : GL (Fin d) K) :
    patChar (colGeR K d j r) ψ₀ (h * u * h⁻¹) =
      patChar (colGeR K d j (Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K))) ψ₀ u := by
  have key : ((h * u * h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
      blkEmb K d j (g : Matrix (Fin j) (Fin j) K) * (u : Matrix (Fin d) (Fin d) K) *
        blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) := by
    rw [Units.val_mul, Units.val_mul, h1, h2]
  unfold patChar
  congr 1
  rw [sum_colGeR hj, sum_colGeR hj, key]
  congr 1
  · refine sum_colGeE_congr _ _ fun i l hi hl => ?_
    rw [conj_apply_ge hj.le _ _ _ i l hl, dif_neg (not_lt.2 hi)]
  · have : ∀ k : Fin j, (blkEmb K d j (g : Matrix (Fin j) (Fin j) K) *
        (u : Matrix (Fin d) (Fin d) K) *
        blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K)) (Fin.castLE hj.le k) ⟨j, hj⟩
        = ∑ m : Fin j, (g : Matrix (Fin j) (Fin j) K) k m *
          (u : Matrix (Fin d) (Fin d) K) (Fin.castLE hj.le m) ⟨j, hj⟩ := by
      intro k
      rw [conj_apply_ge hj.le _ _ _ _ _ (le_refl j), dif_pos (by simp)]
      rfl
    simp_rw [this, Finset.mul_sum, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun k _ => ?_
    ring

theorem wh_colGeR_conj : ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ) (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ) (g : GL (Fin j) K) (h : GL (Fin d) K) (r : Fin j → K),
    j < d → (∀ x y, χ (x * y * x⁻¹) = χ y) →
    (h : Matrix (Fin d) (Fin d) K) = blkEmb K d j (g : Matrix (Fin j) (Fin j) K) →
    ((h⁻¹ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = blkEmb K d j ((g⁻¹ : GL (Fin j) K) : Matrix (Fin j) (Fin j) K) →
    wh (colGe d j) (colGeR K d j r) ψ₀ χ = wh (colGe d j) (colGeR K d j (Matrix.vecMul r (g : Matrix (Fin j) (Fin j) K))) ψ₀ χ := by
  intro K _ _ _ d j ψ₀ χ g h r hj hχ h1 h2
  have hN : ∀ u : GL (Fin d) K, h * u * h⁻¹ ∈ patSet K (colGe d j) ↔ u ∈ patSet K (colGe d j) := by
    intro u
    refine ⟨fun hu => ?_, conj_mem hj.le g h h1 h2⟩
    have := conj_mem hj.le g⁻¹ h⁻¹ h2 (by rw [inv_inv, inv_inv]; exact h1) hu
    have e : h⁻¹ * (h * u * h⁻¹) * (h⁻¹)⁻¹ = u := by group
    rwa [e] at this
  unfold wh
  congr 1
  rw [← Equiv.sum_comp (MulAut.conj h).toEquiv]
  refine Finset.sum_congr rfl fun u _ => ?_
  have e : (MulAut.conj h).toEquiv u = h * u * h⁻¹ := rfl
  rw [e]
  by_cases hu : u ∈ patSet K (colGe d j)
  · rw [if_pos ((hN u).2 hu), if_pos hu, patChar_conj hj ψ₀ g h r h1 h2 u, hχ]
  · rw [if_neg (fun q => hu ((hN u).1 q)), if_neg hu]

end GlobalTheory.CompanionTheory.TyFin.ColStep.Conj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerColumnRecursion
section
open ReciprocityTheory.Ty.Fin GlobalTheory.CompanionTheory.TyFin.ColStep

noncomputable section

namespace GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

def colEntries {d j : ℕ} (hj : j < d) (u : GL (Fin d) K) : Fin j → K :=
  fun i => (u : Matrix (Fin d) (Fin d) K) ⟨i, i.2.trans hj⟩ ⟨j, hj⟩

theorem sum_dite_col {d j : ℕ} (hj : j < d) (r : Fin j → K) (M : Matrix (Fin d) (Fin d) K) :
    ∑ i : Fin d, ∑ l : Fin d, (if h : (l : ℕ) = j ∧ (i : ℕ) < j then r ⟨i, h.2⟩ else 0) * M i l =
      ∑ i : Fin j, r i * M ⟨i, i.2.trans hj⟩ ⟨j, hj⟩ := by
  have inner : ∀ i : Fin d, ∑ l : Fin d, (if h : (l : ℕ) = j ∧ (i : ℕ) < j then r ⟨i, h.2⟩ else 0) * M i l =
      if h : (i : ℕ) < j then r ⟨i, h⟩ * M i ⟨j, hj⟩ else 0 := by
    intro i
    rw [Finset.sum_eq_single ⟨j, hj⟩]
    · by_cases h : (i : ℕ) < j
      · rw [dif_pos ⟨rfl, h⟩, dif_pos h]
      · rw [dif_neg (fun h' => h h'.2), dif_neg h, zero_mul]
    · intro l _ hl
      have hl' : ¬ ((l : ℕ) = j ∧ (i : ℕ) < j) := fun h => hl (Fin.ext h.1)
      rw [dif_neg hl', zero_mul]
    · intro h
      exact absurd (Finset.mem_univ _) h
  simp only [inner]
  rw [show (∑ i : Fin d, if h : (i : ℕ) < j then r ⟨i, h⟩ * M i ⟨j, hj⟩ else 0) =
      ∑ i ∈ (Finset.univ : Finset (Fin j)).map (Fin.castLEEmb hj.le),
        (if h : (i : ℕ) < j then r ⟨i, h⟩ * M i ⟨j, hj⟩ else 0) from ?_]
  · rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Fin.castLEEmb_apply, Fin.val_castLE, dif_pos i.2]
    rfl
  · symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hij : ¬ (i : ℕ) < j := by
      intro h
      apply hi
      exact Finset.mem_map.mpr ⟨⟨i, h⟩, Finset.mem_univ _, Fin.ext rfl⟩
    rw [dif_neg hij]

theorem patChar_colGeR {d j : ℕ} (hj : j < d) (r : Fin j → K) (ψ₀ : AddChar K ℂ) (u : GL (Fin d) K) :
    patChar (colGeR K d j r) ψ₀ u =
      patChar (colGeE K d (j + 1)) ψ₀ u * ψ₀ (∑ i, r i * colEntries hj u i) := by
  unfold patChar
  rw [← AddChar.map_add_eq_mul]
  congr 1
  rw [show (∑ i, r i * colEntries hj u i) =
      ∑ i : Fin j, r i * (u : Matrix (Fin d) (Fin d) K) ⟨i, i.2.trans hj⟩ ⟨j, hj⟩ from rfl,
    ← sum_dite_col hj r (u : Matrix (Fin d) (Fin d) K), ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l _
  unfold colGeR
  ring

theorem mem_patSet_succ_iff {d j : ℕ} (hj : j < d) (u : GL (Fin d) K) :
    u ∈ patSet K (colGe d (j + 1)) ↔ u ∈ patSet K (colGe d j) ∧ colEntries hj u = 0 := by
  simp only [patSet, Set.mem_setOf_eq, colGe]
  constructor
  · intro h
    refine ⟨fun i l => ⟨(h i l).1, fun hne hn => (h i l).2 hne (fun hc => hn ⟨hc.1, by
      have h2 := hc.2; omega⟩)⟩, ?_⟩
    funext i
    have hi2 := i.2
    have hi : (⟨i, i.2.trans hj⟩ : Fin d) ≠ ⟨j, hj⟩ := by
      intro h'
      have h3 := congrArg Fin.val h'
      simp only [Fin.val_mk] at h3
      omega
    exact (h _ _).2 hi (fun hc => by
      have h2 := hc.2
      simp only [Fin.val_mk] at h2
      omega)
  · rintro ⟨h, hc⟩ i l
    refine ⟨(h i l).1, fun hne hn => ?_⟩
    by_cases hlj : (l : ℕ) = j ∧ i < l
    · have h3 : (i : ℕ) < l := hlj.2
      have hij : (i : ℕ) < j := by omega
      have h4 := congrFun hc ⟨i, hij⟩
      have hl : l = ⟨j, hj⟩ := Fin.ext hlj.1
      subst hl
      exact h4
    · apply (h i l).2 hne
      rintro ⟨h1, h2⟩
      apply hn
      refine ⟨h1, ?_⟩
      have h5 : (l : ℕ) ≠ j := fun h3 => hlj ⟨h3, h1⟩
      omega

theorem wh_colGe_succ_eq_sum (K : Type) [Field K] [Fintype K] [DecidableEq K] (d j : ℕ)
    (ψ₀ : AddChar K ℂ) (χ : GL (Fin d) K → ℂ) (hj : j < d)
    (hc : (patSet K (colGe d j)).ncard = Fintype.card K ^ j * (patSet K (colGe d (j + 1))).ncard)
    (ho : ∀ x : Fin j → K, (∑ r : Fin j → K, (ψ₀ (∑ i, r i * x i))⁻¹) =
      if x = 0 then (Fintype.card K : ℂ) ^ j else 0) :
    wh (colGe d (j + 1)) (colGeE K d (j + 1)) ψ₀ χ =
      ∑ r : Fin j → K, wh (colGe d j) (colGeR K d j r) ψ₀ χ := by
  classical
  have hq : (Fintype.card K : ℂ) ^ j ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hN : ((patSet K (colGe d j)).ncard : ℂ)⁻¹ * (Fintype.card K : ℂ) ^ j =
      ((patSet K (colGe d (j + 1))).ncard : ℂ)⁻¹ := by
    rw [hc, Nat.cast_mul, Nat.cast_pow, mul_inv, mul_comm (((Fintype.card K : ℂ) ^ j)⁻¹), mul_assoc,
      inv_mul_cancel₀ hq, mul_one]
  have hu : ∀ u : GL (Fin d) K, (∑ r : Fin j → K, if u ∈ patSet K (colGe d j) then
      (patChar (colGeR K d j r) ψ₀ u)⁻¹ * χ u else 0) =
      (Fintype.card K : ℂ) ^ j * (if u ∈ patSet K (colGe d (j + 1)) then
        (patChar (colGeE K d (j + 1)) ψ₀ u)⁻¹ * χ u else 0) := by
    intro u
    by_cases hP : u ∈ patSet K (colGe d j)
    · rw [Finset.sum_congr rfl (fun r _ => if_pos hP)]
      simp only [patChar_colGeR hj, mul_inv]
      rw [show (∑ r : Fin j → K, (patChar (colGeE K d (j + 1)) ψ₀ u)⁻¹ *
          (ψ₀ (∑ i, r i * colEntries hj u i))⁻¹ * χ u) =
          ((patChar (colGeE K d (j + 1)) ψ₀ u)⁻¹ * χ u) *
            ∑ r : Fin j → K, (ψ₀ (∑ i, r i * colEntries hj u i))⁻¹ by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _
        ring]
      rw [ho (colEntries hj u)]
      by_cases hx : colEntries hj u = 0
      · have hmem : u ∈ patSet K (colGe d (j + 1)) := (mem_patSet_succ_iff hj u).mpr ⟨hP, hx⟩
        rw [if_pos hx, if_pos hmem]
        ring
      · have hmem : u ∉ patSet K (colGe d (j + 1)) := fun h => hx ((mem_patSet_succ_iff hj u).mp h).2
        rw [if_neg hx, if_neg hmem]
        ring
    · have hmem : u ∉ patSet K (colGe d (j + 1)) := fun h => hP ((mem_patSet_succ_iff hj u).mp h).1
      rw [if_neg hmem, mul_zero]
      exact Finset.sum_eq_zero (fun r _ => if_neg hP)
  unfold wh
  rw [← Finset.mul_sum, Finset.sum_comm]
  simp only [hu]
  rw [← Finset.mul_sum, ← mul_assoc, hN]

end GlobalTheory.CompanionTheory.TyFin.ColStep.Fourier
end
end

