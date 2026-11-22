import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0040
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Formalism.FormalDegreeBessel.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.SamePartIffOfNeZero
import Development.AbelianVarietyTheory.Definitions.Foundations.CyclotomicDvdExpandOfCoprime
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0037

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdjacentSelfDualLatticesIndexSimpleStatement
section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adjacent_selfDual_lattices_index_simple : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ (A B : Submodule R X), SelfDual γ A → SelfDual γ B → ∀ x ∈ B, ∀ P : Ideal R, P.IsMaximal → Finite (R ⧸ P) → (∀ r : R, r • x ∈ A ↔ r ∈ P) → B ≤ (A ⊓ B) ⊔ Submodule.span R {x} → idx A B = Nat.card (R ⧸ P) ∧ idx B A = Nat.card (R ⧸ P) ∧ (∀ b ∈ B, ∃! q : R ⧸ P, b - (Quotient.out q : R) • x ∈ A) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ B → T ≤ A ∨ T = B) ∧ (∀ T : Submodule R X, A ⊓ B ≤ T → T ≤ A → T ≤ B ∨ T = A) := by
  first | exact @GlobalTheory.FinWeil.adjacent_selfDual_simple | exact GlobalTheory.FinWeil.adjacent_selfDual_simple | (intros; apply GlobalTheory.FinWeil.adjacent_selfDual_simple <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.AdmissibleOfSl2ActionStatement
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_of_sl2_action : ∀ (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)), admitted c x → admitted c (act x γ) := by
  first | exact @GlobalTheory.Sieg.admissible_act_SL2 | exact GlobalTheory.Sieg.admissible_act_SL2 | (intros; apply GlobalTheory.Sieg.admissible_act_SL2 <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BesselJUnitaryEquivariant
section
open Matrix MeasureTheory Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory.BesselUnitary

def partner (k r : ℕ) (i : Fin (2 * r + k + 1)) : Fin (2 * r + k + 1) :=
  if r ≤ i.val ∧ i.val ≤ r + k then i else ⟨2 * r + k - i.val, by omega⟩

lemma gram_apply (k r : ℕ) (i j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j = partner k r i then (if i.val = r + k then -1 else 1) else 0 := by
  have hi := i.isLt
  have hj := j.isLt
  unfold Hpk partner
  split_ifs <;> simp only [Fin.ext_iff] at * <;> first | rfl | omega

lemma gram_sq (k r : ℕ) : Hpk k r * Hpk k r = 1 := by
  ext i j
  have hi := i.isLt
  have hj := j.isLt
  rw [Matrix.mul_apply, Finset.sum_eq_single (partner k r i)]
  · rw [gram_apply, gram_apply, Matrix.one_apply, if_pos rfl]
    unfold partner
    split_ifs <;> simp only [Fin.ext_iff] at * <;> first | omega | (simp; done) | (split_ifs <;> first | omega | simp)
  · intro b _ hb
    rw [gram_apply k r i b, if_neg hb, zero_mul]
  · simp

lemma isUnit_det_of_mem {k r : ℕ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UH (Hpk k r)) : IsUnit g.det := by
  have h : (Hpk k r * (gᴴ * Hpk k r)) * g = 1 := by
    rw [mul_assoc, show gᴴ * Hpk k r * g = Hpk k r from hg, gram_sq]
  exact Matrix.isUnit_det_of_left_inverse h

lemma inv_mulVec_fixed {m : ℕ} {g : Matrix (Fin m) (Fin m) ℂ} (hg : IsUnit g.det) {v : Fin m → ℂ}
    (hv : g *ᵥ v = v) : g⁻¹ *ᵥ v = v := by
  conv_lhs => rw [← hv]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hg, Matrix.one_mulVec]

lemma inv_mem {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ}
    {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : g ∈ UWset k r z) : g⁻¹ ∈ UWset k r z := by
  have hu := isUnit_det_of_mem hg.1
  refine ⟨?_, fun a => ⟨inv_mulVec_fixed hu (hg.2.1 a).1, inv_mulVec_fixed hu (hg.2.1 a).2⟩,
    inv_mulVec_fixed hu hg.2.2⟩
  have h1 : gᴴ * Hpk k r * g = Hpk k r := hg.1
  show (g⁻¹)ᴴ * Hpk k r * g⁻¹ = Hpk k r
  calc (g⁻¹)ᴴ * Hpk k r * g⁻¹ = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) * g⁻¹ := by rw [h1]
    _ = (g * g⁻¹)ᴴ * Hpk k r * (g * g⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [mul_assoc]
    _ = Hpk k r := by rw [Matrix.mul_nonsing_inv _ hu]; simp

def mulEquiv {k r : ℕ} (a b : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)
    (ha : IsUnit a.det) (hb : IsUnit b.det) : Mt k r ≃ᵐ Mt k r where
  toFun x := a * Matrix.of x * b
  invFun x := a⁻¹ * Matrix.of x * b⁻¹
  left_inv x := by
    show a⁻¹ * (a * Matrix.of x * b) * b⁻¹ = Matrix.of x
    rw [← mul_assoc, ← mul_assoc, Matrix.nonsing_inv_mul _ ha, one_mul, mul_assoc,
      Matrix.mul_nonsing_inv _ hb, mul_one]
  right_inv x := by
    show a * (a⁻¹ * Matrix.of x * b⁻¹) * b = Matrix.of x
    rw [← mul_assoc, ← mul_assoc, Matrix.mul_nonsing_inv _ ha, one_mul, mul_assoc,
      Matrix.nonsing_inv_mul _ hb, mul_one]
  measurable_toFun := by
    refine Continuous.measurable ?_
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  measurable_invFun := by
    refine Continuous.measurable ?_
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

def repEquiv {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] {k r : ℕ}
    {z : Fin (2 * r + k + 1) → ℂ}
    {π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (W →L[ℂ] W)}
    (hπ : IsCRepOn (UWset k r z) π) {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : W ≃L[ℂ] W :=
  ContinuousLinearEquiv.equivOfInverse (π h) (π h⁻¹)
    (fun x => by
      have := hπ.2 _ (inv_mem hh) _ hh
      rw [Matrix.nonsing_inv_mul _ (isUnit_det_of_mem hh.1), hπ.1] at this
      exact (congrArg (fun T : W →L[ℂ] W => T x) this).symm)
    (fun x => by
      have := hπ.2 _ hh _ (inv_mem hh)
      rw [Matrix.mul_nonsing_inv _ (isUnit_det_of_mem hh.1), hπ.1] at this
      exact (congrArg (fun T : W →L[ℂ] W => T x) this).symm)

end GlobalTheory.BesselUnitary

namespace GlobalTheory

open BesselUnitary

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.BigCellMemUnitary
section
open Matrix Formalism.QuantumDeterminants

noncomputable section

namespace GlobalTheory

namespace BigCellUnitary

def pos (k r : ℕ) : (Fin r ⊕ Fin r) ⊕ Fin (k + 1) → Fin (2 * r + k + 1) :=
  Sum.elim (Sum.elim (eI k r) (esI k r)) (wI k r)

theorem pos_bijective (k r : ℕ) : Function.Bijective (pos k r) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨?_, by simp; omega⟩
  rintro ((a | a) | a) ((b | b) | b) h <;>
    simp only [pos, eI, esI, wI, Sum.elim_inl, Sum.elim_inr, Fin.mk.injEq] at h <;>
    have ha := a.isLt <;> have hb := b.isLt <;>
    first
      | (exfalso; omega)
      | (have : a = b := Fin.ext (by omega); rw [this])

def posEquiv (k r : ℕ) : (Fin r ⊕ Fin r) ⊕ Fin (k + 1) ≃ Fin (2 * r + k + 1) :=
  Equiv.ofBijective _ (pos_bijective k r)

theorem gram_submatrix (k r : ℕ) :
    (Hpk k r).submatrix (pos k r) (pos k r) =
      fromBlocks (fromBlocks 0 1 1 0) 0 0 (Hb k) := by
  ext ((a | a) | a) ((b | b) | b) <;>
    have ha := a.isLt <;> have hb := b.isLt <;>
    simp only [pos, eI, esI, wI, Hpk, Hb, Sum.elim_inl, Sum.elim_inr, submatrix_apply,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.one_apply, diagonal_apply, Fin.ext_iff, Fin.val_last] <;>
    split_ifs <;> first | rfl | (exfalso; omega) | contradiction | (exfalso; simp_all; done) |
      (rename_i h1 h2
       first
        | exact (if_pos h2).trans (by rw [if_pos (by omega), if_pos (by omega)])
        | exact (if_neg h2).trans (by rw [if_pos (by omega), if_neg (by omega)]))

theorem col_e (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i : Fin (2 * r + k + 1)) (b : Fin r) :
    bigCell k r c μ i (eI k r b) = if i.val = 2 * r + k - b.val then c b else 0 := by
  have hb : (eI k r b).val < r := b.isLt
  unfold bigCell
  rw [dif_pos hb]
  exact if_congr Fin.ext_iff rfl rfl

theorem col_w (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i : Fin (2 * r + k + 1)) (b : Fin (k + 1)) :
    bigCell k r c μ i (wI k r b) =
      if hi : r ≤ i.val ∧ i.val ≤ r + k then μ ⟨i.val - r, by omega⟩ b else 0 := by
  have hb := b.isLt
  have hv : (wI k r b).val = r + b.val := rfl
  unfold bigCell
  rw [dif_neg (by omega), dif_pos (by omega)]
  split_ifs
  · congr 1
    apply Fin.ext
    show (wI k r b).val - r = b.val
    omega
  · rfl

theorem col_es (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ)
    (i : Fin (2 * r + k + 1)) (b : Fin r) :
    bigCell k r c μ i (esI k r b) = if i.val = b.val then (star (c b))⁻¹ else 0 := by
  have hb := b.isLt
  have hv : (esI k r b).val = 2 * r + k - b.val := rfl
  unfold bigCell
  rw [dif_neg (by omega), dif_neg (by omega)]
  refine if_congr (by omega) ?_ rfl
  congr 3
  apply Fin.ext
  show 2 * r + k - (esI k r b).val = b.val
  omega

theorem bigCell_submatrix (k r : ℕ) (c : Fin r → ℂ) (μ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) :
    (bigCell k r c μ).submatrix (pos k r) (pos k r) =
      fromBlocks (fromBlocks 0 (diagonal fun a => (star (c a))⁻¹) (diagonal c) 0) 0 0 μ := by
  ext ((a | a) | a) ((b | b) | b) <;>
    have ha := a.isLt <;> have hb := b.isLt <;>
    simp only [pos, Sum.elim_inl, Sum.elim_inr, submatrix_apply, col_e, col_w, col_es,
      fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂,
      Matrix.zero_apply, diagonal_apply]
  · exact if_neg (by show ¬ a.val = _; omega)
  · have : ((eI k r a).val = b.val) ↔ a = b := (Fin.ext_iff (a := a) (b := b)).symm
    exact (if_congr this rfl rfl).trans (by split_ifs with h <;> simp [h])
  · exact dif_neg (by show ¬ (r ≤ a.val ∧ _); omega)
  · have : ((esI k r a).val = 2 * r + k - b.val) ↔ a = b := by
      rw [Fin.ext_iff]; show 2 * r + k - a.val = _ ↔ _; omega
    exact (if_congr this rfl rfl).trans (by split_ifs with h <;> simp [h])
  · exact if_neg (by show ¬ 2 * r + k - a.val = _; omega)
  · exact dif_neg (by show ¬ (_ ∧ 2 * r + k - a.val ≤ _); omega)
  · exact if_neg (by show ¬ r + a.val = _; omega)
  · exact if_neg (by show ¬ r + a.val = _; omega)
  · rw [dif_pos (by show r ≤ r + a.val ∧ r + a.val ≤ _; omega)]
    congr 1
    apply Fin.ext
    show r + a.val - r = a.val
    omega

end BigCellUnitary

open BigCellUnitary in

theorem bigCell_mem_unitary : Formalism.QuantumDeterminants.BigCellMem := by
  intro k r c μ hc hμ
  have key : ((bigCell k r c μ)ᴴ * Hpk k r * bigCell k r c μ).submatrix (posEquiv k r) (posEquiv k r) =
      (Hpk k r).submatrix (posEquiv k r) (posEquiv k r) := by
    rw [← submatrix_mul_equiv _ _ _ (posEquiv k r), ← submatrix_mul_equiv _ _ _ (posEquiv k r),
      ← conjTranspose_submatrix]
    have hp : ⇑(posEquiv k r) = pos k r := rfl
    rw [hp, gram_submatrix, bigCell_submatrix]
    have h1 : diagonal (fun a => star (c a)) * diagonal (fun a => (star (c a))⁻¹) =
        (1 : Matrix (Fin r) (Fin r) ℂ) := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext a
      exact mul_inv_cancel₀ (star_ne_zero.2 (hc a))
    have h2 : diagonal (fun a => star (star (c a))⁻¹) * diagonal c =
        (1 : Matrix (Fin r) (Fin r) ℂ) := by
      rw [diagonal_mul_diagonal, ← diagonal_one]
      congr 1; funext a
      rw [star_inv₀, star_star]
      exact inv_mul_cancel₀ (hc a)
    simp only [fromBlocks_conjTranspose, fromBlocks_multiply, conjTranspose_zero, diagonal_conjTranspose,
      Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, add_zero, zero_add, hμ]
    rw [show star c = fun a => star (c a) from rfl,
      show star (fun a => (star (c a))⁻¹) = fun a => star (star (c a))⁻¹ from rfl, h1, h2]
  ext i j
  obtain ⟨i, rfl⟩ := (posEquiv k r).surjective i
  obtain ⟨j, rfl⟩ := (posEquiv k r).surjective j
  exact congrFun (congrFun key i) j

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.C1FieldNormSurjective
section
open GlobalTheory.NeedB Polynomial

namespace GlobalTheory

theorem norm_surjective_of_norm_form {K L : Type} [Field K] [Field L] [Algebra K L] (hC : IsFirstChernClassOfLineBundle K) (m : ℕ) (hm0 : 0 < m)
    (B : Module.Basis (Fin m) K L) (f : MvPolynomial (Fin m) K) (hf : f.IsHomogeneous m)
    (hnorm : ∀ x : L, Algebra.norm K x = MvPolynomial.eval (fun i => B.repr x i) f)
    (hpow : ∀ a : K, Algebra.norm K (algebraMap K L a) = a ^ m)
    (b : K) : ∃ x : L, Algebra.norm K x = b := by
  let g : MvPolynomial (Fin (m + 1)) K :=
    MvPolynomial.rename Fin.succ f - MvPolynomial.C b * MvPolynomial.X 0 ^ m
  have hg : g.IsHomogeneous m := by
    refine (hf.rename_isHomogeneous).sub ?_
    have := (MvPolynomial.isHomogeneous_C (Fin (m + 1)) b).mul (MvPolynomial.isHomogeneous_X_pow (0 : Fin (m + 1)) m)
    rwa [zero_add] at this
  obtain ⟨y, hy0, hy⟩ := hC (m + 1) m g hg hm0 (Nat.lt_succ_self m)
  let x : L := B.equivFun.symm (fun i => y i.succ)
  have hrepr : ∀ i, B.repr x i = y i.succ := by
    intro i
    have h := congrFun (B.equivFun.apply_symm_apply (fun i => y i.succ)) i
    rw [Module.Basis.equivFun_apply] at h
    exact h
  have hev : Algebra.norm K x = b * y 0 ^ m := by
    have h1 := hy
    simp only [g, map_sub, map_mul, map_pow, MvPolynomial.eval_rename, MvPolynomial.eval_C,
      MvPolynomial.eval_X] at h1
    rw [hnorm]
    have e : (fun i => B.repr x i) = y ∘ Fin.succ := funext hrepr
    rw [e]; exact sub_eq_zero.mp h1
  have hnz : ∀ z : L, Algebra.norm K z = 0 → z = 0 := by
    intro z hz
    by_contra hz'
    have hu : IsUnit z := (isUnit_iff_ne_zero).mpr hz'
    exact (hu.map (Algebra.norm K)).ne_zero hz
  have hy00 : y 0 ≠ 0 := by
    intro h0
    apply hy0
    have hx : x = 0 := hnz x (by rw [hev, h0, zero_pow hm0.ne', mul_zero])
    funext i
    refine Fin.cases h0 (fun j => ?_) i
    have := hrepr j
    rw [hx, map_zero] at this
    simpa using this.symm
  refine ⟨x * algebraMap K L (y 0)⁻¹, ?_⟩
  rw [map_mul, hpow, hev, mul_assoc, ← mul_pow, mul_inv_cancel₀ hy00, one_pow, mul_one]

theorem norm_surjective_of_is_c1 : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L], IsFirstChernClassOfLineBundle K →
    ∀ b : K, b ≠ 0 → ∃ x : L, Algebra.norm K x = b := by
  intro K L _ _ _ _ hC b _
  obtain ⟨f, hf, hnorm⟩ := GlobalTheory.T.algebraNorm_eq_homogeneous_polynomial_in_coordinates K L
  exact norm_surjective_of_norm_form hC _ Module.finrank_pos (Module.finBasis K L) f hf hnorm
    (fun a => Algebra.norm_algebraMap a) b

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardCycleTypeConsMul
section
open Polynomial Classical GlobalTheory.BadShare

namespace GlobalTheory.BadShare

open Equiv Finset

theorem card_cycleType_cons_mul (N p : ℕ) (hp : 2 ≤ p) (hpN : p ≤ N) (m : Multiset ℕ)
    (hpm : p ∉ m) (hs : m.sum ≤ N - p) (h2 : ∀ a ∈ m, 2 ≤ a) :
    (univ.filter fun σ : Perm (Fin N) => σ.cycleType = p ::ₘ m).card * p * (N - p).factorial
      = N.factorial * (univ.filter fun σ : Perm (Fin (N - p)) => σ.cycleType = m).card := by
  have hA := Equiv.Perm.card_of_cycleType_mul_eq (α := Fin N) (p ::ₘ m)
  have hB := Equiv.Perm.card_of_cycleType_mul_eq (α := Fin (N - p)) m
  rw [Fintype.card_fin] at hA hB
  have hcA : (p ::ₘ m).sum ≤ N ∧ ∀ a ∈ p ::ₘ m, 2 ≤ a := by
    refine ⟨by rw [Multiset.sum_cons]; omega, fun a ha => ?_⟩
    rcases Multiset.mem_cons.1 ha with rfl | ha
    · exact hp
    · exact h2 a ha
  rw [if_pos hcA] at hA
  rw [if_pos ⟨hs, h2⟩] at hB
  have hsum : N - (p ::ₘ m).sum = N - p - m.sum := by
    rw [Multiset.sum_cons, Nat.sub_sub]
  have hfac : ∏ n ∈ (p ::ₘ m).toFinset, ((p ::ₘ m).count n).factorial =
      ∏ n ∈ m.toFinset, (m.count n).factorial := by
    rw [Multiset.toFinset_cons, Finset.prod_insert (by simpa using hpm), Multiset.count_cons_self,
      Multiset.count_eq_zero.2 hpm, zero_add, Nat.factorial_one, one_mul]
    refine Finset.prod_congr rfl fun n hn => ?_
    have hne : n ≠ p := fun h => hpm (h ▸ Multiset.mem_toFinset.1 hn)
    rw [Multiset.count_cons_of_ne hne]
  rw [hsum, Multiset.prod_cons, hfac] at hA
  rw [← hB, ← hA]
  ring

theorem card_mem_cycleType_mul (N p : ℕ) (hp : 2 ≤ p) (hN : N < 2 * p) (hpN : p ≤ N) :
    (univ.filter fun σ : Perm (Fin N) => p ∈ σ.cycleType).card * p = N.factorial := by
  have hTm : ∀ m ∈ (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType,
      m.sum ≤ N - p ∧ ∀ a ∈ m, 2 ≤ a := by
    intro m hm
    obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 hm
    refine ⟨?_, fun a ha => Perm.two_le_of_mem_cycleType ha⟩
    simpa using τ.sum_cycleType_le
  have hpT : ∀ m ∈ (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType, p ∉ m := by
    intro m hm hpm
    have h1 := Multiset.le_sum_of_mem hpm
    have h2 := (hTm m hm).1
    omega
  have hfib : (univ.filter fun σ : Perm (Fin N) => p ∈ σ.cycleType).card =
      ∑ m ∈ (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType,
        (univ.filter fun σ : Perm (Fin N) => σ.cycleType = p ::ₘ m).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun σ : Perm (Fin N) => σ.cycleType.erase p)
      (t := (univ : Finset (Perm (Fin (N - p)))).image Perm.cycleType)]
    · refine Finset.sum_congr rfl fun m _ => ?_
      congr 1
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2⟩
        rw [← h2, Multiset.cons_erase h1]
      · intro h
        rw [h]
        exact ⟨Multiset.mem_cons_self _ _, Multiset.erase_cons_head _ _⟩
    · intro σ hσ
      have hσ' : p ∈ σ.cycleType := by simpa using hσ
      have hsum := Multiset.sum_erase hσ'
      have hle := σ.sum_cycleType_le
      rw [Fintype.card_fin] at hle
      have hc : (σ.cycleType.erase p).sum ≤ Fintype.card (Fin (N - p)) ∧
          ∀ a ∈ σ.cycleType.erase p, 2 ≤ a := by
        refine ⟨by rw [Fintype.card_fin]; omega, fun a ha => ?_⟩
        exact Perm.two_le_of_mem_cycleType (Multiset.mem_of_mem_erase ha)
      obtain ⟨τ, hτ⟩ := (Perm.exists_with_cycleType_iff (Fin (N - p))).2 hc
      exact Finset.mem_image.2 ⟨τ, Finset.mem_univ _, hτ⟩
  have hmain : (univ.filter fun σ : Perm (Fin N) => p ∈ σ.cycleType).card * p * (N - p).factorial
      = N.factorial * (N - p).factorial := by
    rw [hfib, Finset.sum_mul, Finset.sum_mul,
      Finset.sum_congr rfl fun m hm =>
        card_cycleType_cons_mul N p hp hpN m (hpT m hm) (hTm m hm).1 (hTm m hm).2,
      ← Finset.mul_sum]
    congr 1
    have hc := Finset.card_eq_sum_card_image Perm.cycleType (univ : Finset (Perm (Fin (N - p))))
    rw [Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at hc
    exact hc.symm
  exact Nat.eq_of_mul_eq_mul_right (Nat.factorial_pos _) hmain

theorem card_perm_long_cycle : ∀ N p : ℕ, N < 2 * p → p ≤ N →
    (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts).card * p
      = N.factorial := by
  intro N p hN hpN
  rcases Nat.lt_or_ge p 2 with hp | hp
  · obtain rfl : p = 1 := by omega
    obtain rfl : N = 1 := by omega
    have hall : ∀ σ : Equiv.Perm (Fin 1), 1 ∈ σ.partition.parts := by
      intro σ
      have hs : σ.partition.parts.sum = 1 := σ.partition.parts_sum.trans (Fintype.card_fin 1)
      obtain ⟨a, ha⟩ := Multiset.exists_mem_of_ne_zero (s := σ.partition.parts)
        (fun h => by rw [h, Multiset.sum_zero] at hs; exact absurd hs (by norm_num))
      have h1 := σ.partition.parts_pos ha
      have h2 := Multiset.le_sum_of_mem ha
      obtain rfl : a = 1 := by omega
      exact ha
    rw [Finset.filter_true_of_mem (fun σ _ => hall σ), Finset.card_univ, Fintype.card_perm]
    simp
  · have hiff : ∀ σ : Equiv.Perm (Fin N), p ∈ σ.partition.parts ↔ p ∈ σ.cycleType := by
      intro σ
      rw [Equiv.Perm.parts_partition, Multiset.mem_add]
      constructor
      · rintro (h | h)
        · exact h
        · have := Multiset.eq_of_mem_replicate h
          omega
      · exact Or.inl
    simp_rw [hiff]
    exact card_mem_cycleType_mul N p hp hN hpN

end GlobalTheory.BadShare
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ClassGroupNthPowerOfCongruentPointsModStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classGroup_nthPower_of_congruent_points_mod : ∀ (k A : Type) [Field k] [IsAlgClosed k] [CharZero k] [CommRing A] [IsDedekindDomain A] [Algebra k A] [Algebra.FiniteType k A] (N : ℕ), 1 ≤ N → (∀ P₀ : Ideal A, P₀.IsMaximal → ∀ h₀ : P₀ ∈ nonZeroDivisors (Ideal A), ∃ a : A, a ≠ 0 ∧ ∀ P : Ideal A, P.IsMaximal → a ∉ P → ∀ h : P ∈ nonZeroDivisors (Ideal A), ∃ d : ClassGroup A, ClassGroup.mk0 ⟨P, h⟩ = ClassGroup.mk0 ⟨P₀, h₀⟩ * d ^ N) → (∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N) → ∀ c : ClassGroup A, ∃ d, c = d ^ N := by
  first | exact @GlobalTheory.classGroup_nthPower_of_codim_one_mod | exact GlobalTheory.classGroup_nthPower_of_codim_one_mod | (intros; apply GlobalTheory.classGroup_nthPower_of_codim_one_mod <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ColemanNormOperatorPowerSeriesCoeffAutMapComm
section
open GlobalTheory.Col PowerSeries

noncomputable section

namespace GlobalTheory.Col.NormCoeff

variable {R : Type} [CommRing R]

def smapEquiv (σ : R ≃+* R) : PowerSeries R ≃+* PowerSeries R :=
  RingEquiv.ofRingHom (smap σ) (smap σ.symm)
    (by ext h n; simp [PowerSeries.coeff_map])
    (by ext h n; simp [PowerSeries.coeff_map])

theorem smapEquiv_apply (σ : R ≃+* R) (h : PowerSeries R) : smapEquiv σ h = smap σ h := rfl

theorem map_phi (p : ℕ) (hp : 0 < p) (f : R →+* R) (h : PowerSeries R) :
    PowerSeries.map f (phi (R := R) p hp h) = phi (R := R) p hp (PowerSeries.map f h) := by
  unfold phi
  rw [PowerSeries.coe_substAlgHom]
  have key := PowerSeries.map_subst (hasSubst_om (R := R) p hp) (h := f) h
  have e : (MvPowerSeries.map f) (((1 + PowerSeries.X : PowerSeries R) ^ p) - 1)
      = ((1 + PowerSeries.X : PowerSeries R) ^ p) - 1 := by
    change PowerSeries.map f _ = _
    simp
  rw [e] at key
  exact key

theorem normOp_smap (R : Type) [CommRing R] (p : ℕ) [hp : Fact p.Prime] (σ : R ≃+* R) (h : PowerSeries R) :
    normOp p (smap σ h) = smap σ (normOp p h) := by
  have key := @Algebra.norm_eq_of_equiv_equiv (PowerSeries R) (PowerSeries R) (PowerSeries R) (PowerSeries R)
    _ _ _ _ (phi (R := R) p hp.out.pos).toRingHom.toAlgebra (phi (R := R) p hp.out.pos).toRingHom.toAlgebra
    (smapEquiv σ) (smapEquiv σ) (by
      ext1 x
      exact (map_phi p hp.out.pos (σ : R →+* R) x).symm) h
  have key2 : normOp p h = (smapEquiv σ).symm (normOp p (smap σ h)) := key
  rw [key2, ← smapEquiv_apply, ← smapEquiv_apply, RingEquiv.apply_symm_apply]

end GlobalTheory.Col.NormCoeff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormIsCuspidalAtAllCuspsSL2Statement
section
open GlobalTheory.HeckeFamilyMatrices UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_isCuspidalAtAllCuspsSL2 : ∀ (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] (k : ℤ) (f : CuspForm Γ k), CuspAll k f := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll | exact GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll | (intros; apply GlobalTheory.HeckeFamilyMatrices.cuspForm_cuspAll <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.DeformMultipleZerosLinearFamilyStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.deform_multiple_zeros_linear_family : ∀ (k J I : Type) [Field k] [CharZero k] [Fintype J] [Fintype I] (N : ℕ) (ξ : J → PowerSeries k) (s : I → J → PowerSeries k) (y₀ : J → k), 1 ≤ N →
 ∑ j, y₀ j * PowerSeries.constantCoeff (ξ j) = 0 →
 (∀ i, ∀ l < N, ∑ j, y₀ j * PowerSeries.coeff l (s i j) = 0) → (∀ i, ∑ j, y₀ j * PowerSeries.coeff N (s i j) ≠ 0) →
 (∀ (e₀ : k) (e : I → ℕ → k), ∃ h : J → k, ∑ j, h j * PowerSeries.constantCoeff (ξ j) = e₀ ∧ ∀ i, ∀ l, l + 1 < N → ∑ j, h j * PowerSeries.coeff l (s i j) = e i l) →
 ∃ (y : J → PowerSeries k) (a : I → PowerSeries k), (∀ j, PowerSeries.constantCoeff (y j) = y₀ j) ∧ (∀ i, PowerSeries.constantCoeff (a i) = 0) ∧
   ∑ j, y j * ξ j = 0 ∧ ∀ i, ∀ l < N, ∑ j, y j * (((PowerSeries.derivativeFun)^[l] (s i j)).subst (a i) : PowerSeries k) = 0 := by
  first | exact @GlobalTheory.DeformZeros.deform | exact GlobalTheory.DeformZeros.deform | (intros; apply GlobalTheory.DeformZeros.deform <;> assumption)
end

