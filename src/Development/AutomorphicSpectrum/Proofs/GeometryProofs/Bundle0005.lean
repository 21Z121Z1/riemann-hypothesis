import Mathlib

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericLuDecompositionUnique
section
open Matrix

namespace GlobalTheory.CompanionTheory.GenericLU

theorem affine_form_ne_zero {K L : Type} [Field K] [Field L] [Algebra K L] {n : ℕ}
    (a : K) (b : Fin n → K) (x : Fin n → L) (hx : AlgebraicIndependent K x)
    (hab : a ≠ 0 ∨ ∃ j, b j ≠ 0) :
    algebraMap K L a + ∑ j, algebraMap K L (b j) * x j ≠ 0 := by
  classical
  intro h
  let P : MvPolynomial (Fin n) K :=
    MvPolynomial.C a + ∑ j, MvPolynomial.C (b j) * MvPolynomial.X j
  have hP : MvPolynomial.aeval x P = 0 := by
    simpa [P, map_add, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.aeval_X] using h
  have hP0 : P = 0 := by
    have := (injective_iff_map_eq_zero (MvPolynomial.aeval x : MvPolynomial (Fin n) K →ₐ[K] L)).mp hx
    exact this P hP
  rcases hab with ha | ⟨j, hj⟩
  · apply ha
    have := congrArg (MvPolynomial.coeff 0) hP0
    simpa [P, MvPolynomial.coeff_add, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_C, MvPolynomial.coeff_X'] using this
  · apply hj
    have := congrArg (MvPolynomial.coeff (Finsupp.single j 1)) hP0
    have hne : (0 : Fin n →₀ ℕ) ≠ Finsupp.single j 1 :=
      (Finsupp.single_ne_zero.mpr one_ne_zero).symm
    simpa [P, hne, MvPolynomial.coeff_add, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
      MvPolynomial.coeff_C, MvPolynomial.coeff_X', Finsupp.single_left_inj, Finsupp.single_eq_single_iff] using this

theorem schur_det_ne_zero {F : Type} [Field F] {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) F)
    (x : Fin n → F) (hA : A.det ≠ 0) (q : Fin (n + 1) → F)
    (hq : ∀ i, q i = A i 0 + ∑ k, A i k.succ * x k) (h0 : q 0 ≠ 0) :
    (Matrix.of fun i j : Fin n => A i.succ j.succ - q i.succ / q 0 * A 0 j.succ).det ≠ 0 := by
  intro hdet
  obtain ⟨y, hy, hSy⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  set t : F := -(∑ j, A 0 j.succ * y j) / q 0 with ht
  apply hA
  refine Matrix.exists_mulVec_eq_zero_iff.mp
    ⟨Fin.cons t (fun k => y k + t * x k), ?_, ?_⟩
  · intro hz
    have h1 : t = 0 := by simpa using congrFun hz 0
    apply hy
    funext k
    have := congrFun hz k.succ
    simpa [h1] using this
  · have key : ∀ i, (A *ᵥ (Fin.cons t (fun k => y k + t * x k) : Fin (n + 1) → F)) i
        = t * q i + ∑ k, A i k.succ * y k := by
      intro i
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, hq,
        mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      have : ∀ k, A i k.succ * (t * x k) = t * (A i k.succ * x k) := fun k => by ring
      simp only [this]
      ring
    funext i
    rw [key]
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [ht, Pi.zero_apply]
      field_simp
      ring
    · have h := congrFun hSy i
      simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.zero_apply, sub_mul,
        Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum] at h
      simp only [ht, Pi.zero_apply]
      field_simp at h ⊢
      linear_combination h

theorem lu_step {L : Type} [Field L] {n : ℕ} (M : Matrix (Fin (n + 1)) (Fin (n + 1)) L)
    (hM : M 0 0 ≠ 0) (v' w' : Matrix (Fin n) (Fin n) L)
    (hsch : ∀ i j, M i.succ j.succ - M i.succ 0 / M 0 0 * M 0 j.succ = (v' * w') i j)
    (h1 : ∀ k, v' k k = 1) (h2 : ∀ l k, l < k → v' l k = 0)
    (h3 : ∀ l k, k < l → w' l k = 0) (h4 : ∀ k, w' k k ≠ 0) :
    ∃ v w : Matrix (Fin (n + 1)) (Fin (n + 1)) L, M = v * w ∧ (∀ k, v k k = 1) ∧
      (∀ l k, l < k → v l k = 0) ∧ (∀ l k, k < l → w l k = 0) ∧ ∀ k, w k k ≠ 0 := by
  let v : Matrix (Fin (n + 1)) (Fin (n + 1)) L := fun i j =>
    Fin.cases (Fin.cases 1 (fun _ => 0) j)
      (fun i' => Fin.cases (M i'.succ 0 / M 0 0) (fun j' => v' i' j') j) i
  let w : Matrix (Fin (n + 1)) (Fin (n + 1)) L := fun i j =>
    Fin.cases (Fin.cases (M 0 0) (fun j' => M 0 j'.succ) j)
      (fun i' => Fin.cases 0 (fun j' => w' i' j') j) i
  have v00 : v 0 0 = 1 := rfl
  have v0s : ∀ j, v 0 (Fin.succ j) = 0 := fun _ => rfl
  have vs0 : ∀ i, v (Fin.succ i) 0 = M i.succ 0 / M 0 0 := fun _ => rfl
  have vss : ∀ i j, v (Fin.succ i) (Fin.succ j) = v' i j := fun _ _ => rfl
  have w00 : w 0 0 = M 0 0 := rfl
  have w0s : ∀ j, w 0 (Fin.succ j) = M 0 j.succ := fun _ => rfl
  have ws0 : ∀ i, w (Fin.succ i) 0 = 0 := fun _ => rfl
  have wss : ∀ i j, w (Fin.succ i) (Fin.succ j) = w' i j := fun _ _ => rfl
  refine ⟨v, w, ?_, ?_, ?_, ?_, ?_⟩
  · ext i j
    rw [Matrix.mul_apply, Fin.sum_univ_succ]
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [v00, v0s, w00]
    · simp [v00, v0s, w0s]
    · simp [vs0, vss, w00, ws0]
      field_simp
    · have := hsch i j
      rw [Matrix.mul_apply] at this
      simp only [vs0, vss, w0s, wss]
      rw [← this]
      ring
  · intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · exact v00
    · rw [vss]; exact h1 k
  · intro l k
    refine Fin.cases ?_ (fun l => ?_) l <;> refine Fin.cases ?_ (fun k => ?_) k
    · intro h; exact absurd h (lt_irrefl _)
    · intro _; exact v0s k
    · intro h; exact absurd h (Fin.not_lt_zero _)
    · intro h; rw [vss]; exact h2 l k (Fin.succ_lt_succ_iff.mp h)
  · intro l k
    refine Fin.cases ?_ (fun l => ?_) l <;> refine Fin.cases ?_ (fun k => ?_) k
    · intro h; exact absurd h (lt_irrefl _)
    · intro h; exact absurd h (Fin.not_lt_zero _)
    · intro _; exact ws0 l
    · intro h; rw [wss]; exact h3 l k (Fin.succ_lt_succ_iff.mp h)
  · intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · rw [w00]; exact hM
    · rw [wss]; exact h4 k

theorem generic_lu_decomposition_exists (n : ℕ) : ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    (A : Matrix (Fin n) (Fin n) K) (u : Matrix (Fin n) (Fin n) L), A.det ≠ 0 →
    (∀ k, u k k = 1) → (∀ l k, l < k → u l k = 0) →
    AlgebraicIndependent K (fun q : {lk : Fin n × Fin n // lk.2 < lk.1} => u q.1.1 q.1.2) →
    ∃ v w : Matrix (Fin n) (Fin n) L, A.map (algebraMap K L) * u = v * w ∧ (∀ k, v k k = 1) ∧
      (∀ l k, l < k → v l k = 0) ∧ (∀ l k, k < l → w l k = 0) ∧ ∀ k, w k k ≠ 0 := by
  induction n with
  | zero =>
    intro K L _ _ _ A u _ _ _ _
    exact ⟨0, 0, Subsingleton.elim _ _, fun k => k.elim0, fun l => l.elim0, fun l => l.elim0,
      fun k => k.elim0⟩
  | succ n ih =>
    intro K L _ _ _ A u hA hdiag hup hind
    let x : Fin n → L := fun i => u i.succ 0
    let u' : Matrix (Fin n) (Fin n) L := fun i j => u i.succ j.succ
    let y : {lk : Fin n × Fin n // lk.2 < lk.1} → L := fun q => u' q.1.1 q.1.2
    let idx : {lk : Fin n × Fin n // lk.2 < lk.1} ⊕ Fin n →
        {lk : Fin (n + 1) × Fin (n + 1) // lk.2 < lk.1} :=
      Sum.elim (fun q => ⟨(q.1.1.succ, q.1.2.succ), Fin.succ_lt_succ_iff.mpr q.2⟩)
        (fun i => ⟨(i.succ, 0), Fin.succ_pos i⟩)
    have hidx : Function.Injective idx := by
      rintro (s | i) (s' | i') hh
      · have e : (s.1.1.succ, s.1.2.succ) = (s'.1.1.succ, s'.1.2.succ) :=
          congrArg Subtype.val hh
        exact congrArg Sum.inl (Subtype.ext (Prod.ext
          (Fin.succ_injective _ (congrArg Prod.fst e))
          (Fin.succ_injective _ (congrArg Prod.snd e))))
      · have e : (s.1.1.succ, s.1.2.succ) = (i'.succ, (0 : Fin (n + 1))) :=
          congrArg Subtype.val hh
        exact absurd (congrArg Prod.snd e) (Fin.succ_ne_zero _)
      · have e : (i.succ, (0 : Fin (n + 1))) = (s'.1.1.succ, s'.1.2.succ) :=
          congrArg Subtype.val hh
        exact absurd (congrArg Prod.snd e).symm (Fin.succ_ne_zero _)
      · have e : (i.succ, (0 : Fin (n + 1))) = (i'.succ, (0 : Fin (n + 1))) :=
          congrArg Subtype.val hh
        exact congrArg Sum.inr (Fin.succ_injective _ (congrArg Prod.fst e))
    have hsum : AlgebraicIndependent K (Sum.elim y x) := by
      have := hind.comp idx hidx
      convert this using 1
      funext s
      rcases s with q | i <;> rfl
    obtain ⟨hx, hy⟩ := AlgebraicIndependent.sumElim_iff.mp hsum
    have hy' : AlgebraicIndependent (IntermediateField.adjoin K (Set.range x)) y :=
      IntermediateField.algebraicIndependent_adjoin_iff.mpr hy
    let K₁ := IntermediateField.adjoin K (Set.range x)
    let xs : Fin n → K₁ := fun i => ⟨x i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
    let A₁ : Matrix (Fin (n + 1)) (Fin (n + 1)) K₁ := A.map (algebraMap K K₁)
    let q : Fin (n + 1) → K₁ := fun i => A₁ i 0 + ∑ k, A₁ i k.succ * xs k
    have hA₁ : A₁.det ≠ 0 := by
      have : A₁.det = algebraMap K K₁ A.det := by
        simpa [A₁] using (RingHom.map_det (algebraMap K K₁) A).symm
      rw [this]
      exact (map_ne_zero _).mpr hA
    let M : Matrix (Fin (n + 1)) (Fin (n + 1)) L := A.map (algebraMap K L) * u
    have hcoe : ∀ i j, algebraMap K₁ L (A₁ i j) = algebraMap K L (A i j) := fun i j =>
      (IsScalarTower.algebraMap_apply K K₁ L (A i j)).symm
    have hxs : ∀ k, algebraMap K₁ L (xs k) = x k := fun _ => rfl
    have hM0 : ∀ i, M i 0 = algebraMap K₁ L (q i) := by
      intro i
      simp only [M, q, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.map_apply, hdiag, map_add,
        map_sum, map_mul, hcoe, hxs, mul_one]
      rfl
    have hMs : ∀ i j, M i j.succ = ∑ k, algebraMap K L (A i k.succ) * u' k j := by
      intro i j
      simp only [M, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.map_apply]
      rw [hup 0 j.succ (Fin.succ_pos j)]
      simp [u']
    have hp : M 0 0 ≠ 0 := by
      have hne : A 0 0 ≠ 0 ∨ ∃ j, A 0 (Fin.succ j) ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        apply hA
        apply Matrix.det_eq_zero_of_row_eq_zero 0
        intro j
        refine Fin.cases hcon.1 hcon.2 j
      have := affine_form_ne_zero (A 0 0) (fun j => A 0 j.succ) x hx hne
      have h2 : M 0 0 = algebraMap K L (A 0 0) + ∑ j, algebraMap K L (A 0 j.succ) * x j := by
        simp only [M, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.map_apply, hdiag, mul_one]
        rfl
      rwa [h2]
    have hq0 : q 0 ≠ 0 := by
      intro h
      apply hp
      rw [hM0, h, map_zero]
    let S : Matrix (Fin n) (Fin n) K₁ :=
      Matrix.of fun i j : Fin n => A₁ i.succ j.succ - q i.succ / q 0 * A₁ 0 j.succ
    have hS : S.det ≠ 0 := schur_det_ne_zero A₁ xs hA₁ q (fun _ => rfl) hq0
    obtain ⟨v', w', hvw, h1, h2, h3, h4⟩ := ih K₁ L S u' hS (fun k => hdiag k.succ)
      (fun l k h => hup l.succ k.succ (Fin.succ_lt_succ_iff.mpr h)) hy'
    refine lu_step M hp v' w' ?_ h1 h2 h3 h4
    intro i j
    rw [← hvw, Matrix.mul_apply, hMs, hMs, hM0, hM0, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [S, Matrix.map_apply, Matrix.of_apply, map_sub, map_mul, map_div₀, hcoe]
    ring

theorem generic_lu : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (n : ℕ)
    (A : Matrix (Fin n) (Fin n) K) (u : Matrix (Fin n) (Fin n) L), A.det ≠ 0 →
    (∀ k, u k k = 1) → (∀ l k, l < k → u l k = 0) →
    AlgebraicIndependent K (fun q : {lk : Fin n × Fin n // lk.2 < lk.1} => u q.1.1 q.1.2) →
    ∃ v w : Matrix (Fin n) (Fin n) L, A.map (algebraMap K L) * u = v * w ∧ (∀ k, v k k = 1) ∧
      (∀ l k, l < k → v l k = 0) ∧ (∀ l k, k < l → w l k = 0) ∧ ∀ k, w k k ≠ 0 := by
  intro K L _ _ _ n
  exact generic_lu_decomposition_exists n K L

end GlobalTheory.CompanionTheory.GenericLU
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralOverLocalizationScaled
section
namespace GlobalTheory.CompanionTheory.Ggeo.ClearDenominators

open Polynomial

theorem exists_common_denominator {o K : Type} [CommRing o] [Field K] [Algebra o K]
    (A : Subalgebra o K) (R : Subring K)
    (hfrac : ∀ r ∈ R, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ r = u / v)
    (s : Finset K) (hs : ∀ x ∈ s, x ∈ R) :
    ∃ w ∈ A, w ≠ 0 ∧ w⁻¹ ∈ R ∧ ∀ x ∈ s, w * x ∈ A := by
  classical
  revert hs
  refine Finset.induction_on s ?_ ?_
  · intro _
    refine ⟨1, one_mem A, one_ne_zero, ?_, ?_⟩
    · rw [inv_one]
      exact one_mem R
    · intro x hx
      simp at hx
  · intro a t _ ih hs
    obtain ⟨w, hwA, hw0, hwR, hw⟩ :=
      ih (fun x hx => hs x (Finset.mem_insert_of_mem hx))
    obtain ⟨u, huA, v, hvA, hv0, hvR, hav⟩ := hfrac a (hs a (Finset.mem_insert_self a t))
    refine ⟨w * v, mul_mem hwA hvA, mul_ne_zero hw0 hv0, ?_, ?_⟩
    · rw [mul_inv]
      exact mul_mem hwR hvR
    · intro x hx
      rcases Finset.mem_insert.mp hx with hxa | hxt
      · have key : w * v * x = w * u := by
          rw [hxa, hav, div_eq_mul_inv]
          calc w * v * (u * v⁻¹) = w * u * (v * v⁻¹) := by ring
            _ = w * u := by rw [mul_inv_cancel₀ hv0, mul_one]
        rw [key]
        exact mul_mem hwA huA
      · have key : w * v * x = v * (w * x) := by ring
        rw [key]
        exact mul_mem hvA (hw x hxt)

theorem exists_mul_isIntegral :
    ∀ {o K : Type} [CommRing o] [Field K] [Algebra o K] (A : Subalgebra o K) (R : Subring K),
      (∀ a ∈ A, a ∈ R) → (∀ r ∈ R, ∃ u ∈ A, ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ r = u / v) →
      ∀ (t : K), IsIntegral R t → ∃ v ∈ A, v ≠ 0 ∧ v⁻¹ ∈ R ∧ IsIntegral A (v * t) := by
  intro o K _ _ _ A R _ hfrac t ht
  classical
  obtain ⟨p, hpm, hp⟩ := ht
  have hPm : (p.map (algebraMap R K)).Monic := hpm.map (algebraMap R K)
  have hP : (p.map (algebraMap R K)).eval₂ (RingHom.id K) t = 0 := by
    rw [Polynomial.eval₂_map, RingHom.id_comp]
    exact hp
  have hPR : ∀ i, (p.map (algebraMap R K)).coeff i ∈ R := by
    intro i
    rw [Polynomial.coeff_map]
    exact (p.coeff i).2
  generalize p.map (algebraMap R K) = P at hPm hP hPR
  obtain ⟨w, hwA, hw0, hwR, hw⟩ := exists_common_denominator A R hfrac
    ((Finset.range (P.natDegree + 1)).image P.coeff) (by
      intro x hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
      exact hPR i)
  refine ⟨w, hwA, hw0, hwR, ?_⟩
  have hcoef : ∀ i, P.coeff i * w ^ (P.natDegree - i) ∈ A := by
    intro i
    rcases lt_trichotomy i P.natDegree with hi | hi | hi
    · obtain ⟨k, hk⟩ : ∃ k, P.natDegree - i = k + 1 := ⟨P.natDegree - i - 1, by omega⟩
      have h1 : P.coeff i * w ^ (P.natDegree - i) = w ^ k * (w * P.coeff i) := by
        rw [hk]
        ring
      rw [h1]
      exact mul_mem (pow_mem hwA k)
        (hw _ (Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by omega))))
    · rw [hi, Nat.sub_self, pow_zero, mul_one, hPm.coeff_natDegree]
      exact one_mem A
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hi, zero_mul]
      exact zero_mem A
  have hQm : (P.scaleRoots w).Monic := by
    rw [Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_scaleRoots,
      Polynomial.coeff_scaleRoots_natDegree]
    exact hPm
  have hlift : P.scaleRoots w ∈ Polynomial.lifts (algebraMap A K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro i
    rw [Polynomial.coeff_scaleRoots]
    exact ⟨⟨_, hcoef i⟩, rfl⟩
  obtain ⟨q, hqmap, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hQm
  refine ⟨q, hqm, ?_⟩
  rw [Polynomial.eval₂_eq_eval_map, hqmap]
  exact Polynomial.scaleRoots_eval₂_eq_zero (RingHom.id K) hP

end GlobalTheory.CompanionTheory.Ggeo.ClearDenominators
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IotaMultiNeZeroOfLinIndep
section
namespace GlobalTheory.CompanionTheory.Exterior

theorem ιMulti_ne_zero_of_linearIndependent :
    ∀ (Ω V : Type) [Field Ω] [AddCommGroup V] [Module Ω V] (n : ℕ) (e : Fin n → V),
      LinearIndependent Ω e → exteriorPower.ιMulti Ω n e ≠ 0 := by
  intro Ω V _ _ _ n e he h
  let f : (Fin n → Ω) →ₗ[Ω] V := Fintype.linearCombination Ω e
  have hf : LinearMap.ker f = ⊥ :=
    LinearMap.ker_eq_bot.2 he.fintypeLinearCombination_injective
  obtain ⟨π, hπ⟩ := f.exists_leftInverse_of_injective hf
  have hπe : ∀ j, π (e j) = Pi.single j 1 := by
    intro j
    have h2 := LinearMap.congr_fun hπ (Pi.single j 1)
    simpa [f, Fintype.linearCombination_apply_single] using h2
  let D : V [⋀^Fin n]→ₗ[Ω] Ω :=
    (Matrix.detRowAlternating (n := Fin n) (R := Ω)).compLinearMap π
  have h1 := exteriorPower.alternatingMapLinearEquiv_apply_ιMulti D e
  rw [h, map_zero] at h1
  have h3 : D e = 1 := by
    have h4 : (fun i => π (e i)) = (1 : Matrix (Fin n) (Fin n) Ω) := by
      ext i j
      simp [hπe, Matrix.one_apply, Pi.single_apply, eq_comm]
    change Matrix.det (fun i => π (e i)) = 1
    rw [h4, Matrix.det_one]
  rw [h3] at h1
  exact zero_ne_one h1

end GlobalTheory.CompanionTheory.Exterior
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsUnitOfBasicOpenNonemptyOfUniversallyClosed
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem exists_pow_mul_unit_add_eq_zero_of_integral {K A : Type*} [Field K] [CommRing A]
    (φ : K →+* A) (a : A) (ha : φ.IsIntegralElem a) :
    ∃ (m : ℕ) (u b : A), IsUnit u ∧ a ^ m * (u + a * b) = 0 := by
  obtain ⟨p, hp, hpa⟩ := ha
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hp.ne_zero 0
  rw [map_zero, sub_zero] at hpq hq
  have hq0 : q.coeff 0 ≠ 0 := fun h => hq (Polynomial.X_dvd_iff.2 h)
  refine ⟨p.rootMultiplicity 0, φ (q.coeff 0), q.divX.eval₂ φ a, (Ne.isUnit hq0).map φ, ?_⟩
  have hsplit : p.eval₂ φ a = a ^ p.rootMultiplicity 0 * q.eval₂ φ a := by
    conv_lhs => rw [hpq]
    rw [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X]
  have hq' : q.eval₂ φ a = φ (q.coeff 0) + a * q.divX.eval₂ φ a := by
    conv_lhs => rw [← Polynomial.X_mul_divX_add q]
    rw [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C,
      add_comm]
  rw [← hq', ← hsplit, hpa]

theorem isUnit_of_pow_mul_unit_add_eq_zero (X : Scheme.{0}) [ConnectedSpace X]
    (a u b : Γ(X, ⊤)) (m : ℕ) (hu : IsUnit u) (h : a ^ m * (u + a * b) = 0)
    (hne : ((X.basicOpen a : X.Opens) : Set X).Nonempty) : IsUnit a := by
  have hcover : ∀ x : X, x ∈ X.basicOpen a ∨ x ∈ X.basicOpen (u + a * b) := by
    intro x
    rw [Scheme.mem_basicOpen_top, Scheme.mem_basicOpen_top]
    by_cases hxa : IsUnit (X.presheaf.germ ⊤ x trivial a)
    · exact Or.inl hxa
    · right
      have hU : IsUnit (X.presheaf.germ ⊤ x trivial u) := hu.map _
      have hsum : X.presheaf.germ ⊤ x trivial u =
          X.presheaf.germ ⊤ x trivial (u + a * b) +
            -(X.presheaf.germ ⊤ x trivial a * X.presheaf.germ ⊤ x trivial b) := by
        rw [map_add, map_mul]; ring
      rw [hsum] at hU
      rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add hU with h1 | h1
      · exact h1
      · exact absurd (isUnit_of_mul_isUnit_left (IsUnit.neg_iff _ |>.1 h1)) hxa
  have hdisj : ∀ x : X, x ∈ X.basicOpen a → x ∈ X.basicOpen (u + a * b) → False := by
    intro x hxa hxg
    rw [Scheme.mem_basicOpen_top] at hxa hxg
    have hx : x ∈ X.basicOpen (a ^ m * (u + a * b)) := by
      rw [Scheme.mem_basicOpen_top, map_mul, map_pow]
      exact (hxa.pow m).mul hxg
    rw [h, Scheme.basicOpen_zero] at hx
    exact hx
  have hall : ∀ x : X, x ∈ X.basicOpen a := by
    intro x
    by_contra hx
    have hxg := (hcover x).resolve_left hx
    obtain ⟨y, -, hy1, hy2⟩ := isPreconnected_univ
      ((X.basicOpen a : X.Opens) : Set X) ((X.basicOpen (u + a * b) : X.Opens) : Set X)
      (X.basicOpen a).isOpen (X.basicOpen (u + a * b)).isOpen
      (fun z _ => hcover z) (by simpa using hne) ⟨x, Set.mem_univ _, hxg⟩
    exact hdisj y hy1 hy2
  exact X.toRingedSpace.isUnit_of_isUnit_germ ⊤ a
    (fun x _ => (X.mem_basicOpen_top a x).1 (hall x))

theorem isUnit_of_basicOpen_nonempty_of_universallyClosed :
    ∀ (k : Type) [Field k] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of k))
      [UniversallyClosed f] [ConnectedSpace X] (a : Γ(X, ⊤)),
      ((X.basicOpen a : X.Opens) : Set X).Nonempty → IsUnit a := by
  intro k _ X f _ _ a hne
  let F := (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2
      (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  obtain ⟨m, u, b, hu, h⟩ := exists_pow_mul_unit_add_eq_zero_of_integral F.hom a (hF a)
  exact isUnit_of_pow_mul_unit_add_eq_zero X a u b m hu h hne

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KaehlerFinrankFractionField
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.Ggeo

theorem finrank_kaehler_fractionRing_eq_of_basis
    (S T K L : Type) [CommRing S] [CommRing T] [Field K] [Field L] [Algebra S T] [Algebra S K]
    [Algebra S L] [Algebra T L] [Algebra K L] [IsScalarTower S T L] [IsScalarTower S K L]
    [IsFractionRing S K] [IsFractionRing T L] (m : ℕ) (w : Fin m → T)
    (hli : LinearIndependent T (fun i => KaehlerDifferential.D S T (w i)))
    (hspan : Submodule.span T (Set.range fun i => KaehlerDifferential.D S T (w i)) = ⊤) :
    Module.finrank L (KaehlerDifferential K L) = m := by
  haveI : Algebra.FormallyEtale T L := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors T)
  haveI : Algebra.FormallyUnramified S K :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors S)
  haveI : Subsingleton (KaehlerDifferential S K) :=
    Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  have hinj : Function.Injective (KaehlerDifferential.map S K L L) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map S K L x).1 hx
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hy]
  let e : KaehlerDifferential S L ≃ₗ[L] KaehlerDifferential K L :=
    LinearEquiv.ofBijective (KaehlerDifferential.map S K L L)
      ⟨hinj, KaehlerDifferential.map_surjective S K L⟩
  let b : Module.Basis (Fin m) T (KaehlerDifferential S T) := Module.Basis.mk hli hspan.ge
  let b' : Module.Basis (Fin m) L (KaehlerDifferential K L) :=
    ((Algebra.TensorProduct.basis L b).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale S T L)).map e
  simpa using Module.finrank_eq_card_basis b'

end GlobalTheory.CompanionTheory.Ggeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalHomCharZeroUnits
section
open AlgebraicGeometry CategoryTheory

namespace GlobalTheory.CompanionTheory.Ggeo

private theorem map_aeval_int' {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (a : A)
    (q : Polynomial ℤ) : f (Polynomial.aeval a q) = Polynomial.aeval (f a) q := by
  rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂,
    RingHom.ext_int (f.comp (algebraMap ℤ A)) (algebraMap ℤ B)]

theorem unit_of_local_hom_charZero_nf : ∀ (O F L K : Type) [CommRing O] [Field F] [NumberField F] [CommRing L] [Field K] [CharZero K] (β : O →+* F) (θ : O →+* L) (ρ : L →+* K), IsLocalHom ρ → (∀ a, β a = 0 → θ a = 0) → ∀ b, β b ≠ 0 → IsUnit (θ b) := by
  intro O F L K _ _ _ _ _ _ β θ ρ hρ hker b hb
  have halg : IsAlgebraic ℤ (β b) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ F).mpr (Algebra.IsAlgebraic.isAlgebraic (β b))
  obtain ⟨q, hq0, hq⟩ :=
    halg.exists_nonzero_coeff_and_aeval_eq_zero (mem_nonZeroDivisors_of_ne_zero hb)
  have h1 : β (Polynomial.aeval b q) = 0 := by rw [map_aeval_int', hq]
  have h2 : ρ (θ (Polynomial.aeval b q)) = 0 := by rw [hker _ h1, map_zero]
  rw [map_aeval_int', map_aeval_int'] at h2
  have h3 : ρ (θ b) ≠ 0 := by
    intro h0
    rw [h0, ← Polynomial.coeff_zero_eq_aeval_zero'] at h2
    exact hq0 (by simpa using h2)
  exact hρ.map_nonunit _ (isUnit_iff_ne_zero.mpr h3)

end GlobalTheory.CompanionTheory.Ggeo
end

