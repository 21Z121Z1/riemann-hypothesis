import Formalism.SubspaceCounting.Bundle0001

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.CramerCofactor
section
namespace Formalism.G0

open Matrix in
theorem cramer_cofactor : CramerCofactor := by
  intro R _ r T σ a
  have h : T.adjugate *ᵥ (T *ᵥ σ) = T.det • σ := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 := congrFun h a
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at h2
  rw [mul_comm, ← h2]
  exact Finset.sum_congr rfl fun l _ => mul_comm _ _

end Formalism.G0
end

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.DetVal
section
noncomputable section
open scoped BigOperators

namespace Formalism.G0.DetValP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι]

lemma substS_det {L : Type} [Field L] [Algebra K L] {r : ℕ} (vec : ι → Bool) (S : Finset ι)
    (g : GL (Fin r) L) (A : Fin r → ι) {R : Type} [CommRing R]
    (φ : MvPolynomial (ι × Fin r) (Polynomial L) →+* R) :
    φ (substS (K := K) vec S g (detLetters A)) =
      Matrix.det (Matrix.of fun l a => φ (substS (K := K) vec S g (MvPolynomial.X (A l, a)))) := by
  unfold detLetters
  rw [AlgHom.map_det, RingHom.map_det]
  congr 1

lemma substS_X {L : Type} [Field L] [Algebra K L] {r : ℕ} (vec : ι → Bool) (S : Finset ι)
    (g : GL (Fin r) L) (p : ι × Fin r) :
    substS (K := K) vec S g (MvPolynomial.X p) =
      (if p.1 ∈ S then
      (if vec p.1 then ∑ b, MvPolynomial.C ((msMat g) p.2 b) * MvPolynomial.X (p.1, b)
       else ∑ b, MvPolynomial.C ((msDualMat g) p.2 b) * MvPolynomial.X (p.1, b))
    else MvPolynomial.X p) := by
  simp [substS]

lemma sum_cov_zero {r : ℕ} (vec : ι → Bool) (S : Finset ι) (A : Fin r → ι)
    (hv : ∀ l, vec (A l) = true) :
    ∑ i ∈ S.filter (fun i => vec i = false), (if i ∈ Set.range A then 1 else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_filter] at hi
  have : i ∉ Set.range A := by rintro ⟨l, rfl⟩; simp [hv l] at hi
  simp [this]

lemma msMat_one {L : Type} [Field L] {r : ℕ} :
    msMat (1 : GL (Fin r) L) =
      Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then Polynomial.X else 1) := by
  simp [msMat]

end Formalism.G0.DetValP

namespace Formalism.G0.DetValP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι]

lemma prod_last {L : Type} [Field L] {r : ℕ} (hr : 1 ≤ r) :
    ∏ a : Fin r, (if a.val + 1 = r then (Polynomial.X : Polynomial L) else 1) = Polynomial.X := by
  rw [Finset.prod_eq_single (⟨r - 1, by omega⟩ : Fin r)]
  · simp; omega
  · intro b _ hb
    have : b.val + 1 ≠ r := by
      intro h; apply hb; ext; simp; omega
    simp [this]
  · simp

lemma part1a {L : Type} [Field L] [Algebra K L] {r : ℕ} (hr : 1 ≤ r) (vec : ι → Bool)
    (S : Finset ι) (A : Fin r → ι) (hv : ∀ l, vec (A l) = true) (hS : ∀ l, A l ∈ S)
    (g : GL (Fin r) L) :
    MvPolynomial.C Polynomial.X ∣ substS (K := K) vec S g (detLetters A) := by
  have h1 : substS (K := K) vec S g (detLetters A) =
      Matrix.det ((Matrix.of fun (l b : Fin r) =>
          (MvPolynomial.X (A l, b) : MvPolynomial (ι × Fin r) (Polynomial L))) *
        ((msMat g).map MvPolynomial.C).transpose) := by
    have := substS_det (K := K) vec S g A (RingHom.id _)
    simp only [RingHom.id_apply] at this
    rw [this]
    congr 1
    refine Matrix.ext fun l a => ?_
    rw [Matrix.of_apply, substS_X]
    simp only [hS l, hv l, if_true, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply]
    refine Finset.sum_congr rfl fun b _ => mul_comm _ _
  have hC := RingHom.map_det (MvPolynomial.C : Polynomial L →+* MvPolynomial (ι × Fin r) (Polynomial L)) (msMat g)
  rw [RingHom.mapMatrix_apply] at hC
  rw [h1, Matrix.det_mul, Matrix.det_transpose, ← hC]
  apply dvd_mul_of_dvd_right
  apply map_dvd
  unfold msMat
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, prod_last hr]
  exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _

end Formalism.G0.DetValP

namespace Formalism.G0.DetValP
open Formalism.G0

variable {K ι : Type} [Field K] [DecidableEq ι]

lemma entry_one_mem {R : Type} [CommRing R] {r : ℕ} (vec : ι → Bool) (S : Finset ι)
    (φ : Polynomial K →+* R) (v : ι × Fin r → R) (i : ι) (hi : i ∈ S) (hvi : vec i = true)
    (a : Fin r) :
    MvPolynomial.eval₂Hom φ v (substS (K := K) vec S (1 : GL (Fin r) K) (MvPolynomial.X (i, a))) =
      φ (if a.val + 1 = r then Polynomial.X else 1) * v (i, a) := by
  rw [substS_X]
  simp only [hi, hvi, if_true, msMat_one, map_sum, map_mul, MvPolynomial.eval₂Hom_C,
    MvPolynomial.eval₂Hom_X', Matrix.diagonal_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [Ne.symm hb]
  · simp

lemma entry_one_nmem {R : Type} [CommRing R] {r : ℕ} (vec : ι → Bool) (S : Finset ι)
    (φ : Polynomial K →+* R) (v : ι × Fin r → R) (i : ι) (hi : i ∉ S) (a : Fin r) :
    MvPolynomial.eval₂Hom φ v (substS (K := K) vec S (1 : GL (Fin r) K) (MvPolynomial.X (i, a))) =
      v (i, a) := by
  rw [substS_X]
  simp [hi]

lemma part1b {r : ℕ} (hr : 1 ≤ r) (vec : ι → Bool)
    (S : Finset ι) (A : Fin r → ι) (hA : Function.Injective A) (hv : ∀ l, vec (A l) = true)
    (hS : ∀ l, A l ∈ S) :
    ¬ MvPolynomial.C (Polynomial.X ^ 2) ∣
      substS (K := K) vec S (1 : GL (Fin r) K) (detLetters A) := by
  intro h
  let v : ι × Fin r → Polynomial K := fun p => if p.1 = A p.2 then 1 else 0
  have h2 := map_dvd (MvPolynomial.eval₂Hom (RingHom.id (Polynomial K)) v) h
  rw [MvPolynomial.eval₂Hom_C, RingHom.id_apply, substS_det] at h2
  have hM : (Matrix.of fun l a => MvPolynomial.eval₂Hom (RingHom.id (Polynomial K)) v
      (substS (K := K) vec S (1 : GL (Fin r) K) (MvPolynomial.X (A l, a)))) =
      Matrix.diagonal (fun a : Fin r => if a.val + 1 = r then Polynomial.X else 1) := by
    refine Matrix.ext fun l a => ?_
    rw [Matrix.of_apply, entry_one_mem vec S _ v (A l) (hS l) (hv l) a, Matrix.diagonal_apply]
    by_cases hla : l = a
    · subst hla; simp [v]
    · have : A l ≠ A a := fun e => hla (hA e)
      simp [v, this, hla]
  rw [hM, Matrix.det_diagonal, prod_last hr] at h2
  have := Polynomial.natDegree_le_of_dvd h2 Polynomial.X_ne_zero
  simp at this

lemma part2 {r : ℕ} (hr : 1 ≤ r) (vec : ι → Bool)
    (S : Finset ι) (A : Fin r → ι) (hA : Function.Injective A) (hv : ∀ l, vec (A l) = true)
    (hS : ¬ ∀ l, A l ∈ S) :
    ¬ MvPolynomial.C (Polynomial.X ^ 1) ∣
      substS (K := K) vec S (1 : GL (Fin r) K) (detLetters A) := by
  intro h
  obtain ⟨l₀, hl₀⟩ := not_forall.mp hS
  let last : Fin r := ⟨r - 1, by omega⟩
  let τ : Equiv.Perm (Fin r) := Equiv.swap l₀ last
  let v : ι × Fin r → K := fun p => if p.1 = A (τ p.2) then 1 else 0
  have h2 := map_dvd (MvPolynomial.eval₂Hom (Polynomial.evalRingHom (0 : K)) v) h
  rw [MvPolynomial.eval₂Hom_C, substS_det] at h2
  simp only [Polynomial.coe_evalRingHom, pow_one, Polynomial.eval_X, zero_dvd_iff] at h2
  have hM : (Matrix.of fun l a => MvPolynomial.eval₂Hom (Polynomial.evalRingHom (0 : K)) v
      (substS (K := K) vec S (1 : GL (Fin r) K) (MvPolynomial.X (A l, a)))) =
      (1 : Matrix (Fin r) (Fin r) K).submatrix id τ := by
    refine Matrix.ext fun l a => ?_
    rw [Matrix.of_apply, Matrix.submatrix_apply, id, Matrix.one_apply]
    have hvv : v (A l, a) = if l = τ a then 1 else 0 := by
      simp only [v]
      by_cases e : l = τ a
      · simp [e]
      · have : A l ≠ A (τ a) := fun x => e (hA x)
        simp [e, this]
    by_cases hl : A l ∈ S
    · rw [entry_one_mem vec S _ v (A l) hl (hv l) a, hvv]
      by_cases e : l = τ a
      · have ha : a.val + 1 ≠ r := by
          intro ha
          have : a = last := by ext; simp [last]; omega
          apply hl₀
          have hll : l = l₀ := by rw [e, this]; exact Equiv.swap_apply_right l₀ last
          rw [← hll]; exact hl
        simp [e, ha]
      · simp [e]
    · rw [entry_one_nmem vec S _ v (A l) hl a, hvv]
  rw [hM, Matrix.det_permute', Matrix.det_one, mul_one] at h2
  rcases Int.units_eq_one_or (Equiv.Perm.sign τ) with e | e <;> simp [e] at h2

end Formalism.G0.DetValP

open Formalism.G0.DetValP in
theorem Formalism.G0.det_valuation : Formalism.G0.DetVal := by
  intro K ι _ _ _ r vec S' A hr hA hv
  simp only
  have hsum := sum_cov_zero vec S' A hv
  refine ⟨fun hS => ⟨?_, ?_⟩, fun hS => ?_⟩
  · intro L _ _ g
    rw [hsum]
    simpa using part1a (K := K) hr vec S' A hv hS g
  · intro hval
    have := hval K (1 : GL (Fin r) K)
    rw [hsum] at this
    exact part1b hr vec S' A hA hv hS this
  · intro hval
    have := hval K (1 : GL (Fin r) K)
    rw [hsum] at this
    exact part2 hr vec S' A hA hv hS this
end
end

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.QVandermonde
section
namespace Formalism.G0

namespace QVandermondeP

theorem gb_zero_right (q n : ℕ) : gaussBinom q n 0 = 1 := by
  cases n <;> rfl

theorem gb_zero_succ (q k : ℕ) : gaussBinom q 0 (k + 1) = 0 := rfl

theorem gb_succ_succ (q n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) = gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1) :=
  rfl

theorem gb_eq_zero (q : ℕ) : ∀ n k : ℕ, n < k → gaussBinom q n k = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    rw [gb_succ_succ, gb_eq_zero q n k (by omega), gb_eq_zero q n (k + 1) (by omega)]
    simp

theorem form2 (q m : ℕ) : ∀ g n : ℕ, gaussBinom q (m + g) n =
    ∑ l ∈ Finset.range (n + 1),
      q ^ ((n - l) * (g - l)) * gaussBinom q m (n - l) * gaussBinom q g l := by
  intro g
  induction g with
  | zero =>
    intro n
    rw [Finset.sum_range_succ']
    simp [gb_zero_succ, gb_zero_right]
  | succ g ih =>
    intro n
    cases n with
    | zero => simp [gb_zero_right]
    | succ k =>
      show gaussBinom q ((m + g) + 1) (k + 1) = _
      rw [gb_succ_succ, ih k, ih (k + 1)]
      rw [Finset.sum_range_succ' _ (k + 1), Finset.sum_range_succ' _ (k + 1)]
      have h1 : ∀ l ∈ Finset.range (k + 1),
          q ^ ((k + 1 - (l + 1)) * (g + 1 - (l + 1))) * gaussBinom q m (k + 1 - (l + 1)) *
              gaussBinom q (g + 1) (l + 1) =
            q ^ ((k - l) * (g - l)) * gaussBinom q m (k - l) * gaussBinom q g l +
              q ^ (k + 1) * (q ^ ((k + 1 - (l + 1)) * (g - (l + 1))) *
                gaussBinom q m (k + 1 - (l + 1)) * gaussBinom q g (l + 1)) := by
        intro l hl
        have hl' : l ≤ k := by
          have := Finset.mem_range.mp hl
          omega
        rw [gb_succ_succ]
        simp only [Nat.add_sub_add_right]
        rcases Nat.lt_or_ge g (l + 1) with h | h
        · rw [gb_eq_zero q g (l + 1) h]
          ring
        · obtain ⟨a, rfl⟩ : ∃ a, k = l + a := ⟨k - l, by omega⟩
          obtain ⟨b, rfl⟩ : ∃ b, g = l + 1 + b := ⟨g - (l + 1), by omega⟩
          have e1 : l + a - l = a := by omega
          have e2 : l + 1 + b - l = b + 1 := by omega
          have e3 : l + 1 + b - (l + 1) = b := by omega
          rw [e1, e2, e3]
          ring
      rw [Finset.sum_congr rfl h1, Finset.sum_add_distrib, mul_add, Finset.mul_sum]
      simp only [Nat.sub_zero, gb_zero_right]
      ring

theorem form1 (q m g n : ℕ) : gaussBinom q (m + g) n =
    ∑ l ∈ Finset.range (n + 1),
      q ^ (l * (m + l - n)) * gaussBinom q m (n - l) * gaussBinom q g l := by
  rw [Nat.add_comm m g, form2 q g m n]
  refine (Finset.sum_range_reflect _ _).symm.trans ?_
  apply Finset.sum_congr rfl
  intro l hl
  have hl' : l ≤ n := by
    have := Finset.mem_range.mp hl
    omega
  have e1 : n + 1 - 1 - l = n - l := by omega
  have e2 : n - (n - l) = l := by omega
  have e3 : m - (n - l) = m + l - n := by omega
  simp only [e1, e2, e3]
  ring

end QVandermondeP

theorem qVandermondeIdentity : QVandermonde := fun q m g n =>
  ⟨QVandermondeP.form1 q m g n, QVandermondeP.form2 q m g n⟩

end Formalism.G0
end

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.SaturatedMember
section
namespace Formalism.G0

theorem saturated_member : SaturatedMember := by
  intro O M _ _ _ _ π hπ M' P τ hsat
  have hπτ : π ^ τ ≠ 0 := pow_ne_zero _ hπ
  refine ⟨?_, ?_⟩
  · intro x hx
    obtain ⟨⟨_, hxT⟩, hxM'⟩ := hx
    rw [Submodule.ideal_span_singleton_smul] at hxT ⊢
    obtain ⟨y, -, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hxT
    have hy : y ∈ M' := hsat _ _ hπτ hxM'
    exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨y, hy, rfl⟩
  · set N := P ⊓ (Ideal.span {π ^ τ}) • (⊤ : Submodule O M)
    let f : (M' ⧸ Submodule.comap M'.subtype N) →ₗ[O] (M ⧸ N) :=
      Submodule.mapQ _ _ M'.subtype le_rfl
    have hf : Function.Injective f := by
      rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
      simp
    exact Module.length_le_of_injective f hf

end Formalism.G0
end

-- bundled from Formalism.SubspaceCounting.SubspaceCountingProofs.SubspaceCount
section
noncomputable section

open scoped BigOperators
open Module

namespace Formalism.G0

namespace SubspaceCountP

theorem gb_zero_right (q n : ℕ) : gaussBinom q n 0 = 1 := by
  cases n <;> rfl

theorem gb_succ_succ (q n k : ℕ) :
    gaussBinom q (n + 1) (k + 1) = gaussBinom q n k + q ^ (k + 1) * gaussBinom q n (k + 1) :=
  rfl

theorem gb_eq_zero (q : ℕ) : ∀ n k : ℕ, n < k → gaussBinom q n k = 0
  | 0, 0, h => absurd h (lt_irrefl 0)
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, h => absurd h (Nat.not_lt_zero _)
  | n + 1, k + 1, h => by
    rw [gb_succ_succ, gb_eq_zero q n k (by omega), gb_eq_zero q n (k + 1) (by omega)]
    simp

def P (q : ℤ) (m k : ℕ) : ℤ := ∏ i ∈ Finset.range k, (q ^ m - q ^ i)

theorem P_succ_right (q : ℤ) (m k : ℕ) : P q m (k + 1) = P q m k * (q ^ m - q ^ k) := by
  unfold P; rw [Finset.prod_range_succ]

theorem P_succ_succ (q : ℤ) (m k : ℕ) :
    P q (m + 1) (k + 1) = (q ^ (m + 1) - 1) * (q ^ k * P q m k) := by
  unfold P
  rw [Finset.prod_range_succ', pow_zero, mul_comm]
  congr 1
  rw [← Finset.card_range k, ← Finset.prod_const, Finset.card_range, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

theorem gb_mul_P (q : ℤ) (qn : ℕ) (hq : (qn : ℤ) = q) :
    ∀ n k : ℕ, (gaussBinom qn n k : ℤ) * P q k k = P q n k := by
  intro n
  induction n with
  | zero =>
    intro k
    cases k with
    | zero => simp [P, gb_zero_right]
    | succ k =>
      have : P q 0 (k + 1) = 0 := by
        unfold P
        exact Finset.prod_eq_zero (Finset.mem_range.mpr (Nat.succ_pos k)) (by simp)
      rw [this]; simp [gaussBinom]
  | succ n ih =>
    intro k
    cases k with
    | zero => simp [P, gb_zero_right]
    | succ k =>
      rw [gb_succ_succ]
      push_cast
      rw [hq]
      have h1 := ih k
      have h2 := ih (k + 1)
      rw [P_succ_succ q k k, P_succ_succ q n k]
      rw [P_succ_succ q k k, P_succ_right] at h2
      linear_combination (q ^ (k + 1) - 1) * q ^ k * h1 + q ^ (k + 1) * h2

end SubspaceCountP

namespace SubspaceCountP

abbrev LI (F V : Type) [Field F] [AddCommGroup V] [Module F V] (k : ℕ) :=
  {s : Fin k → V // LinearIndependent F s}

abbrev Gr (F W : Type) [Field F] [AddCommGroup W] [Module F W] (k : ℕ) :=
  {U : Submodule F W // finrank F U = k}

variable {F W : Type} [Field F] [AddCommGroup W] [Module F W]

def spanMap (k : ℕ) (s : LI F W k) : Gr F W k :=
  ⟨Submodule.span F (Set.range s.1), (finrank_span_eq_card s.2).trans (Fintype.card_fin k)⟩

variable [Finite W]

def fiberEquiv (k : ℕ) (U : Gr F W k) : {s : LI F W k // spanMap k s = U} ≃ LI F U.1 k where
  toFun s := ⟨fun i => ⟨s.1.1 i, by
      have h := congrArg Subtype.val s.2
      simp only [spanMap] at h
      rw [← h]
      exact Submodule.subset_span ⟨i, rfl⟩⟩, by
      apply LinearIndependent.of_comp U.1.subtype
      exact s.1.2⟩
  invFun t := ⟨⟨U.1.subtype ∘ t.1, t.2.map' _ (Submodule.ker_subtype _)⟩, by
      apply Subtype.ext
      apply Submodule.eq_of_le_of_finrank_eq
      · show Submodule.span F (Set.range (U.1.subtype ∘ t.1)) ≤ U.1
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact (t.1 i).2
      · rw [(spanMap k _).2, U.2]⟩
  left_inv s := rfl
  right_inv t := rfl

end SubspaceCountP

namespace SubspaceCountP

variable {F W : Type} [Field F] [Fintype F] [AddCommGroup W] [Module F W] [Finite W]

theorem card_LI_eq (k : ℕ) :
    Nat.card (LI F W k) =
      Nat.card (Gr F W k) * ∏ i : Fin k, (Fintype.card F ^ k - Fintype.card F ^ i.val) := by
  classical
  let _ := Fintype.ofFinite (Gr F W k)
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv (spanMap (F := F) (W := W) k)), Nat.card_sigma]
  have h : ∀ U : Gr F W k, Nat.card {s // spanMap k s = U} =
      ∏ i : Fin k, (Fintype.card F ^ k - Fintype.card F ^ i.val) := by
    intro U
    rw [Nat.card_congr (fiberEquiv k U), card_linearIndependent (by rw [U.2]), U.2]
  simp only [h, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.card_eq_fintype_card]

theorem cast_prod_eq_P (q m k : ℕ) (hq : 1 ≤ q) (hm : k ≤ m) :
    ((∏ i : Fin k, (q ^ m - q ^ i.val) : ℕ) : ℤ) = P (q : ℤ) m k := by
  rw [Nat.cast_prod, P, ← Fin.prod_univ_eq_prod_range]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Nat.cast_sub (Nat.pow_le_pow_right hq (by omega))]
  push_cast
  rfl

end SubspaceCountP

open SubspaceCountP in
theorem countSubspacesEq : SubspaceCount := by
  intro F W _ _ _ _ _ k
  classical
  have hcount : countBelow (⊤ : Submodule F W) k = Nat.card (Gr F W k) :=
    Nat.card_congr (Equiv.subtypeEquivRight (fun U => by simp))
  rw [hcount]
  rcases lt_or_ge (finrank F W) k with hnk | hkn
  · rw [gb_eq_zero _ _ _ hnk, Nat.card_eq_zero]
    left
    constructor
    rintro ⟨U, hU⟩
    have := Submodule.finrank_le U
    omega
  · have hq : 1 < Fintype.card F := Fintype.one_lt_card
    have h1 := card_LI_eq (F := F) (W := W) k
    rw [card_linearIndependent hkn] at h1
    have h2 := congrArg (Nat.cast : ℕ → ℤ) h1
    rw [Nat.cast_mul, cast_prod_eq_P _ _ _ hq.le hkn, cast_prod_eq_P _ _ _ hq.le le_rfl] at h2
    have h3 := gb_mul_P (Fintype.card F : ℤ) (Fintype.card F) rfl (finrank F W) k
    have hP : P (Fintype.card F : ℤ) k k ≠ 0 := by
      unfold P
      rw [Finset.prod_ne_zero_iff]
      intro i hi
      have : (Fintype.card F : ℤ) ^ i < (Fintype.card F : ℤ) ^ k :=
        pow_lt_pow_right₀ (by exact_mod_cast hq) (Finset.mem_range.mp hi)
      omega
    have : (Nat.card (Gr F W k) : ℤ) = gaussBinom (Fintype.card F) (finrank F W) k :=
      mul_right_cancel₀ hP (h2.symm.trans h3.symm)
    exact_mod_cast this

end Formalism.G0
end
end

