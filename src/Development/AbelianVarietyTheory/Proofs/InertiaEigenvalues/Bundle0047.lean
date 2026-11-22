import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0001
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0002
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0008

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdEApply
section
noncomputable section

namespace GlobalTheory.StableLatCount

def adE (E : Type) [Field E] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂]
    (g₁ : A₁) (g₂ : A₂) : (A₂ →ₗ[E] A₁) →ₗ[E] (A₂ →ₗ[E] A₁) :=
  LinearMap.llcomp E A₂ A₁ A₁ (LinearMap.mulLeft E g₁) - LinearMap.lcomp E A₁ (LinearMap.mulLeft E g₂)

def homLat (E : Type) [Field E] {O A₁ A₂ : Type} [CommRing O] [Algebra O E] [CommRing A₁] [CommRing A₂]
    [Algebra E A₁] [Algebra E A₂] [Algebra O A₁] [Algebra O A₂] [IsScalarTower O E A₁]
    (M₁ : Submodule O A₁) (M₂ : Submodule O A₂) : Submodule O (A₂ →ₗ[E] A₁) where
  carrier := {ψ | ∀ x ∈ M₂, ψ x ∈ M₁}
  add_mem' := fun ha hb x hx => by simpa using M₁.add_mem (ha x hx) (hb x hx)
  zero_mem' := fun x _ => by simp
  smul_mem' := fun c ψ hψ x hx => by simpa using M₁.smul_mem c (hψ x hx)

theorem adE_apply (E : Type) [Field E] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂] [Algebra E A₁] [Algebra E A₂]
    (g₁ : A₁) (g₂ : A₂) (ψ : A₂ →ₗ[E] A₁) (x : A₂) : adE E g₁ g₂ ψ x = g₁ * ψ x - ψ (g₂ * x) := rfl

end GlobalTheory.StableLatCount
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddValuationNonnegRingOfIntegersNumberFieldStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.addValuation_nonneg_ringOfIntegers_numberField : ∀ (L : Type) [Field L] [NumberField L] (v : AddValuation L (WithTop ℤ)) (a : 𝓞 L), 0 ≤ v (a : L) := by
  first | exact @GlobalTheory.addValuation_nonneg_of_ringOfIntegers | exact GlobalTheory.addValuation_nonneg_of_ringOfIntegers | (intros; apply GlobalTheory.addValuation_nonneg_of_ringOfIntegers <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditivePolyTaylorCoeffSubNormLeStatement
section
open Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_taylor_coeff_sub_coeff_le_norm_l : ∀ (l : ℕ) [Fact l.Prime] (E : ℕ) (a : ℕ → ℂ_[l]) (W : ℂ_[l]), (∀ k, k ≤ E → ‖a k‖ ≤ 1) → ‖W‖ ≤ 1 → ∀ j : ℕ, 1 ≤ j → ‖(Polynomial.taylor W (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l])).coeff j - (∑ k ∈ Finset.range (E + 1), Polynomial.monomial (l ^ k) (a k) : Polynomial ℂ_[l]).coeff j‖ ≤ ‖(l : ℂ_[l])‖ := by
  first | exact @GlobalTheory.additive_poly_taylor_coeff_sub_norm_le | exact GlobalTheory.additive_poly_taylor_coeff_sub_norm_le | (intros; apply GlobalTheory.additive_poly_taylor_coeff_sub_norm_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemIntegralSolutionCountOfOrderOne
section
noncomputable section

namespace GlobalTheory.PMonE.LinCount

open Finset GlobalTheory.PMonE

variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]

def lin (K : ℕ) (M : ℕ → Matrix m m F) (k : ℕ) : Matrix (Fin (K + 1) × m) (Fin (K + 1) × m) F :=
  fun r c =>
    if r.1 = Fin.last K then
      (if k = 0 then M c.1 r.2 c.2 else if c.1 = Fin.last K then M (k + K) r.2 c.2 else 0)
    else
      (if k = 0 then (if (c.1 : ℕ) = r.1 + 1 ∧ r.2 = c.2 then -1 else 0)
        else if k = 1 then (if r = c then 1 else 0) else 0)

theorem lin_normal (K : ℕ) (M : ℕ → Matrix m m F) (h : Normal (K + 1) M) : Normal 1 (lin K M) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n r c
    unfold lin
    split_ifs <;> first | exact h.int _ _ _ | simp
  · ext ⟨i, a⟩ ⟨j, b⟩
    have h1 : M (1 + K) = 1 := by rw [add_comm]; exact h.top
    by_cases hi : i = Fin.last K
    · subst hi
      by_cases hj : j = Fin.last K
      · subst hj
        simp [lin, h1, Matrix.one_apply]
      · simp [lin, hj, Matrix.one_apply, Ne.symm hj]
    · simp [lin, hi, Matrix.one_apply]
  · intro n hn r c
    have h0 : n ≠ 0 := by omega
    have h1 : n ≠ 1 := by omega
    simp only [lin, h0, h1, if_false]
    split_ifs
    · exact h.small _ (by omega) _ _
    · simp
    · simp

theorem lin_zero_cast (K : ℕ) (M : ℕ → Matrix m m F) (Y : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    (lin K M 0).mulVec Y (i.castSucc, a) = - Y (i.succ, a) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (i.succ, a)]
  · simp [lin, (Fin.castSucc_lt_last i).ne]
  · rintro ⟨j, b⟩ _ hne
    have : ¬ ((j : ℕ) = i + 1 ∧ a = b) := by
      rintro ⟨h1, rfl⟩
      exact hne (by congr 1; exact Fin.ext (by simpa using h1))
    simp [lin, (Fin.castSucc_lt_last i).ne, this]
  · simp

theorem lin_one_cast (K : ℕ) (M : ℕ → Matrix m m F) (Y : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    (lin K M 1).mulVec Y (i.castSucc, a) = Y (i.castSucc, a) := by
  simp [Matrix.mulVec, dotProduct, lin, (Fin.castSucc_lt_last i).ne]

theorem lin_two_cast (K : ℕ) (M : ℕ → Matrix m m F) (k : ℕ) (Y : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    (lin K M (k + 1 + 1)).mulVec Y (i.castSucc, a) = 0 := by
  simp [Matrix.mulVec, dotProduct, lin, (Fin.castSucc_lt_last i).ne]

theorem lin_zero_last (K : ℕ) (M : ℕ → Matrix m m F) (Y : Fin (K + 1) × m → F) (a : m) :
    (lin K M 0).mulVec Y (Fin.last K, a) = ∑ j : Fin (K + 1), (M j).mulVec (fun b => Y (j, b)) a := by
  simp [Matrix.mulVec, dotProduct, lin, Fintype.sum_prod_type]

theorem lin_succ_last (K : ℕ) (M : ℕ → Matrix m m F) (k : ℕ) (Y : Fin (K + 1) × m → F) (a : m) :
    (lin K M (k + 1)).mulVec Y (Fin.last K, a) = (M (k + 1 + K)).mulVec (fun b => Y (Fin.last K, b)) a := by
  simp only [Matrix.mulVec, dotProduct, lin, Fintype.sum_prod_type]
  rw [Finset.sum_eq_single (Fin.last K)]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

theorem lin_det (K : ℕ) (M : ℕ → Matrix m m F) (h : (M 0).det ≠ 0) : (lin K M 0).det ≠ 0 := by
  intro h0
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
  have hs : ∀ (i : Fin K) (a : m), v (i.succ, a) = 0 := by
    intro i a
    have := congrFun hv0 (i.castSucc, a)
    rw [lin_zero_cast] at this
    simpa using this
  have hz : (M 0).mulVec (fun b => v (0, b)) = 0 := by
    funext a
    have := congrFun hv0 (Fin.last K, a)
    rw [lin_zero_last, Fin.sum_univ_succ] at this
    simpa [hs, Matrix.mulVec, dotProduct] using this
  have h00 : (fun b => v (0, b)) = 0 := by
    by_contra hne
    exact h (Matrix.exists_mulVec_eq_zero_iff.mp ⟨_, hne, hz⟩)
  apply hv
  funext ⟨j, b⟩
  refine Fin.cases ?_ (fun i => ?_) j
  · exact congrFun h00 b
  · exact hs i b

theorem gsum_lin_cast (q K E : ℕ) (M : ℕ → Matrix m m F) (X : Fin (K + 1) × m → F) (i : Fin K) (a : m) :
    gsum q (E + 1) (lin K M) X (i.castSucc, a) = X (i.castSucc, a) ^ q - X (i.succ, a) := by
  simp only [gsum, Finset.sum_apply]
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  simp only [lin_two_cast, zero_add, lin_one_cast, lin_zero_cast]
  simp [sub_eq_add_neg]

theorem gsum_lin_last (q K E : ℕ) (M : ℕ → Matrix m m F) (x : m → F) (a : m) :
    gsum q E (lin K M) (fun r => x r.2 ^ q ^ (r.1 : ℕ)) (Fin.last K, a) = gsum q (K + E) M x a := by
  simp only [gsum, Finset.sum_apply]
  rw [Finset.sum_range_succ', show K + E + 1 = (K + 1) + E by ring, Finset.sum_range_add, add_comm]
  congr 1
  · rw [lin_zero_last, Finset.sum_range]
    simp
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [lin_succ_last, show k + 1 + K = K + 1 + k by ring]
    congr 1
    funext b
    simp only [Fin.val_last]
    rw [← pow_mul, ← pow_add, show K + (k + 1) = K + 1 + k by ring]

theorem card_lin (q K E : ℕ) (M : ℕ → Matrix m m F) :
    Nat.card {x : m → F // Integral x ∧ gsum q (K + (E + 1)) M x = 0} =
      Nat.card {X : Fin (K + 1) × m → F // Integral X ∧ gsum q (E + 1) (lin K M) X = 0} := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => ⟨fun r => x.1 r.2 ^ q ^ (r.1 : ℕ), ?_, ?_⟩) ⟨?_, ?_⟩)
  · intro r
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (x.2.1 _)
  · funext ⟨j, a⟩
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [gsum_lin_last, x.2.2]; rfl
    · rw [gsum_lin_cast]
      simp [pow_succ, pow_mul]
  · intro x y hxy
    ext a
    have := congrFun (congrArg Subtype.val hxy) (0, a)
    simpa using this
  · rintro ⟨X, hX, hX0⟩
    have key : X = fun r => X (0, r.2) ^ q ^ (r.1 : ℕ) := by
      funext ⟨j, a⟩
      induction j using Fin.induction with
      | zero => simp
      | succ i ih =>
        have := congrFun hX0 (i.castSucc, a)
        rw [gsum_lin_cast, Pi.zero_apply, sub_eq_zero] at this
        rw [← this, ih]
        simp [pow_succ, pow_mul]
    refine ⟨⟨fun a => X (0, a), fun a => hX _, ?_⟩, Subtype.ext key.symm⟩
    funext a
    rw [← gsum_lin_last, ← key, hX0]; rfl

theorem glCount_of_one : ∀ N : ℕ, 1 ≤ N → GLCount 1 → GLCount N := by
  intro N hN h1 F _ _ _ _ p _ _ m _ _ e D he hD M hM hdet
  obtain ⟨K, rfl⟩ : ∃ K, N = K + 1 := ⟨N - 1, by omega⟩
  obtain ⟨E, rfl⟩ : ∃ E, D = K + (E + 1) := ⟨D - K - 1, by omega⟩
  rw [card_lin, h1 F p (Fin (K + 1) × m) e (E + 1) he (by omega) (lin K M) (lin_normal K M hM) (lin_det K M hdet)]
  simp [mul_comm]

end GlobalTheory.PMonE.LinCount

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdditiveSystemIntegralSurjectivityOfOne
section
noncomputable section

namespace GlobalTheory.PMonE

open Finset Matrix

section Lower

variable {F : Type*} [NormedField F] {m : Type*} [Fintype m] [DecidableEq m]

def lowerOrder (N : ℕ) (M : ℕ → Matrix m m F) (n : ℕ) : Matrix (m ⊕ m) (m ⊕ m) F :=
  fromBlocks (if n = N then 1 else 0) (if n + 1 = N then -1 else 0) (if n = 0 then M 0 else 0) (M (n + 1))

omit [Fintype m] in
theorem norm_one_apply_le (i j : m) : ‖(1 : Matrix m m F) i j‖ ≤ 1 := by
  rw [Matrix.one_apply]
  split_ifs <;> simp

omit [Fintype m] in
theorem lowerOrder_normal {N : ℕ} (hN : 1 ≤ N) {M : ℕ → Matrix m m F} (hM : Normal (N + 1) M) :
    Normal N (lowerOrder N M) where
  int n i j := by
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [lowerOrder, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]
    · split_ifs
      · exact norm_one_apply_le i j
      · simp
    · split_ifs
      · rw [Matrix.neg_apply, norm_neg]
        exact norm_one_apply_le i j
      · simp
    · split_ifs
      · exact hM.int 0 i j
      · simp
    · exact hM.int (n + 1) i j
  top := by
    have h1 : N + 1 ≠ N := by omega
    have h2 : N ≠ 0 := by omega
    simp [lowerOrder, h1, h2, hM.top]
  small n hn i j := by
    have h1 : n ≠ N := by omega
    have h2 : n + 1 ≠ N := by omega
    have h3 : n ≠ 0 := by omega
    rcases i with i | i <;> rcases j with j | j <;>
      simp only [lowerOrder, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, if_neg h1, if_neg h2, if_neg h3,
        Matrix.zero_apply, norm_zero, zero_lt_one]
    exact hM.small (n + 1) (by omega) i j

theorem gsum_lowerOrder_inl (q : ℕ) {K D : ℕ} (hD : K + 1 ≤ D) (M : ℕ → Matrix m m F) (z : m ⊕ m → F) (i : m) :
    gsum q D (lowerOrder (K + 1) M) z (Sum.inl i) = z (Sum.inl i) ^ q ^ (K + 1) - z (Sum.inr i) ^ q ^ K := by

  have h : ∀ n, (lowerOrder (K + 1) M n).mulVec (fun k => z k ^ q ^ n) (Sum.inl i) =
      (if n = K + 1 then z (Sum.inl i) ^ q ^ (K + 1) else 0) +
        (if n = K then -z (Sum.inr i) ^ q ^ K else 0) := by
    intro n
    simp only [lowerOrder, Matrix.fromBlocks_mulVec, Sum.elim_inl, Pi.add_apply, Function.comp_def]
    by_cases h1 : n = K + 1
    · subst h1
      simp
    · by_cases h2 : n = K
      · subst h2
        simp [Matrix.neg_mulVec]
      · have h3 : n ≠ K := h2
        simp [h1, h3]
  simp only [gsum, Finset.sum_apply, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
  rw [if_pos (by omega), if_pos (by omega), sub_eq_add_neg]

theorem gsum_lowerOrder_inr (q : ℕ) (N D : ℕ) (M : ℕ → Matrix m m F) (z : m ⊕ m → F)
    (hz : ∀ i, z (Sum.inr i) = z (Sum.inl i) ^ q) (i : m) :
    gsum q D (lowerOrder N M) z (Sum.inr i) = gsum q (D + 1) M (fun j => z (Sum.inl j)) i := by

  have h : ∀ n, (lowerOrder N M n).mulVec (fun k => z k ^ q ^ n) (Sum.inr i) =
      (if n = 0 then (M 0).mulVec (fun j => z (Sum.inl j) ^ q ^ 0) i else 0) +
        (M (n + 1)).mulVec (fun j => z (Sum.inl j) ^ q ^ (n + 1)) i := by
    intro n
    simp only [lowerOrder, Matrix.fromBlocks_mulVec, Sum.elim_inr, Pi.add_apply, Function.comp_def, hz]
    congr 1
    · split_ifs with h0
      · subst h0
        rfl
      · simp
    · congr 2
      funext j
      rw [← pow_mul, ← pow_succ']
  simp only [gsum, Finset.sum_apply, h, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_range]
  rw [Finset.sum_range_succ' _ (D + 1), if_pos (by omega), add_comm]

end Lower

theorem glOnto_succ (K : ℕ) (H : GLOnto (K + 1)) : GLOnto (K + 2) := by
  intro F _ _ _ _ p _ _ m _ _ e D he hD M hM b hb
  obtain ⟨D, rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩

  obtain ⟨z, hzI, hzs⟩ := H F p (m ⊕ m) e D he (by omega) (lowerOrder (K + 1) M)
    (lowerOrder_normal (by omega) hM) (Sum.elim 0 b) (by
      intro k
      rcases k with k | k
      · simp
      · exact hb k)

  have hz : ∀ i, z (Sum.inr i) = z (Sum.inl i) ^ p ^ e := by
    intro i
    have h0 := congrFun hzs (Sum.inl i)
    rw [gsum_lowerOrder_inl (p ^ e) (by omega)] at h0
    simp only [Sum.elim_inl, Pi.zero_apply] at h0
    have hqK : (p ^ e) ^ K = p ^ (e * K) := (pow_mul p e K).symm
    have h1 : (z (Sum.inl i) ^ p ^ e - z (Sum.inr i)) ^ p ^ (e * K) = 0 := by
      rw [sub_pow_char_pow, ← hqK, ← pow_mul, ← pow_succ']
      exact h0
    exact (sub_eq_zero.mp (pow_eq_zero_iff (pow_ne_zero _ (Fact.out : p.Prime).ne_zero) |>.mp h1)).symm
  refine ⟨fun j => z (Sum.inl j), fun j => hzI (Sum.inl j), ?_⟩
  funext i
  rw [← gsum_lowerOrder_inr (p ^ e) (K + 1) D M z hz i, hzs]
  rfl

theorem glOnto_of_one : ∀ N : ℕ, 1 ≤ N → GLOnto 1 → GLOnto N := by
  intro N hN H
  induction N, hN using Nat.le_induction with
  | base => exact H
  | succ n hn ih =>
    obtain ⟨K, rfl⟩ : ∃ K, n = K + 1 := ⟨n - 1, by omega⟩
    exact glOnto_succ K ih

end GlobalTheory.PMonE

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionPrincipalPerfectStatement
section
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_principal_perfect : ∀ (l : ℕ) [Fact l.Prime] (V : Type) [CommRing V] [CharP V l] [PerfectRing V l] (x : V), ((l : ℕ) : AdicCompletion (Ideal.span {x}) V) = 0 ∧ Function.Bijective fun y : AdicCompletion (Ideal.span {x}) V => y ^ l := by
  first | exact @GlobalTheory.PerfectCompletion.perfect | exact GlobalTheory.PerfectCompletion.perfect | (intros; apply GlobalTheory.PerfectCompletion.perfect <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicCompletionValuationRingCompleteValuationDomaStatement
section
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adicCompletion_valuationRing_complete_valuationDomain : ∀ (V : Type) [CommRing V] [IsDomain V] [ValuationRing V] (x : V), x ≠ 0 → ¬ IsUnit x → IsDomain (AdicCompletion (Ideal.span {x}) V) ∧ PreValuationRing (AdicCompletion (Ideal.span {x}) V) ∧ algebraMap V (AdicCompletion (Ideal.span {x}) V) x ≠ 0 ∧ ¬ IsUnit (algebraMap V (AdicCompletion (Ideal.span {x}) V) x) ∧ IsAdicComplete (Ideal.span {algebraMap V (AdicCompletion (Ideal.span {x}) V) x}) (AdicCompletion (Ideal.span {x}) V) := by
  first | exact @GlobalTheory.adicCompletion_valuationRing_props | exact GlobalTheory.adicCompletion_valuationRing_props | (intros; apply GlobalTheory.adicCompletion_valuationRing_props <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseChangePolynomialAnnihilatesDescentStatement
section
open Polynomial
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_polynomial_annihilates_descent : ∀ (Ks L0 KB WK ι : Type) [Field Ks] [Field L0] [Field KB] [Algebra Ks L0] [Algebra Ks KB] [AddCommGroup WK]
    [Module Ks WK] (rd : L0 →+* KB), (∀ a : Ks, rd (algebraMap Ks L0 a) = algebraMap Ks KB a) →
    ∀ (T0 : Module.End Ks WK) (s : Finset ι) (ρ : ι → Module.End Ks WK) (a : ι → L0) (q : L0[X]),
    (∀ z ∈ LinearMap.range (∑ g ∈ s, a g • LinearMap.baseChange L0 (ρ g)),
      Polynomial.aeval (LinearMap.baseChange L0 T0) q z = 0) →
    ∀ y ∈ LinearMap.range (∑ g ∈ s, rd (a g) • LinearMap.baseChange KB (ρ g)),
      Polynomial.aeval (LinearMap.baseChange KB T0) (q.map rd) y = 0 := by
  first | exact @GlobalTheory.baseChange_polynomial_kills_descent | exact GlobalTheory.baseChange_polynomial_kills_descent | (intros; apply GlobalTheory.baseChange_polynomial_kills_descent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockDecompositionFractionFieldStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_decomposition_fraction_field : ∀ {O Γ : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [TopologicalSpace O] [IsTopologicalRing O], IsAdic (IsLocalRing.maximalIdeal O) → ∀ [TopologicalSpace Γ] {n r t : ℕ} (M : Γ → Matrix (Fin n) (Fin n) O) (P : Γ → Matrix (Fin r) (Fin r) O) (e : (Fin n → FractionRing O) ≃ₗ[FractionRing O] ((Fin r → FractionRing O) × (Fin t → FractionRing O))), Continuous M → (∀ g v, (e (((M g).map (algebraMap O (FractionRing O))).mulVec v)).1 = ((P g).map (algebraMap O (FractionRing O))).mulVec (e v).1) → Continuous P := by
  first | exact @GlobalTheory.continuous_block_of_continuous_matrix | exact GlobalTheory.continuous_block_of_continuous_matrix | (intros; apply GlobalTheory.continuous_block_of_continuous_matrix <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CDvdOfDvdXPowMul
section
noncomputable section

open PowerSeries GlobalTheory.NB.LT

namespace GlobalTheory.NB.LT.EEBasic

section General
variable {B : Type} [CommRing B] (b : B)

theorem pow_dvd_iff_eval (k : ℕ) (x : AdicCompletion (Ideal.span {b}) B) :
    (algebraMap B (AdicCompletion (Ideal.span {b}) B) b) ^ k ∣ x ↔
      AdicCompletion.eval (Ideal.span {b}) B k x = 0 := by
  rw [← LinearMap.mem_ker, ← AdicCompletion.pow_smul_top_eq_ker_eval
    (Submodule.fg_span_singleton b), Ideal.smul_top_eq_map, Submodule.restrictScalars_mem,
    Ideal.span_singleton_pow, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton,
    map_pow]

theorem eval_algebraMap (k : ℕ) (c : B) :
    AdicCompletion.eval (Ideal.span {b}) B k (algebraMap B (AdicCompletion (Ideal.span {b}) B) c)
      = Submodule.Quotient.mk c := by
  rw [AdicCompletion.algebraMap_apply]
  rfl

theorem pow_dvd_of_pow_dvd (k : ℕ) (c : B)
    (h : (algebraMap B (AdicCompletion (Ideal.span {b}) B) b) ^ k ∣
      algebraMap B (AdicCompletion (Ideal.span {b}) B) c) : b ^ k ∣ c := by
  rw [pow_dvd_iff_eval, eval_algebraMap, Submodule.Quotient.mk_eq_zero, smul_eq_mul,
    Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h
  exact h

theorem exists_pow_dvd_sub (k : ℕ) (x : AdicCompletion (Ideal.span {b}) B) :
    ∃ c : B, (algebraMap B (AdicCompletion (Ideal.span {b}) B) b) ^ k ∣
      x - algebraMap B (AdicCompletion (Ideal.span {b}) B) c := by
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _
    (AdicCompletion.eval (Ideal.span {b}) B k x)
  exact ⟨c, by rw [pow_dvd_iff_eval, map_sub, eval_algebraMap, hc, sub_self]⟩

theorem complete : IsAdicComplete
    (Ideal.span {algebraMap B (AdicCompletion (Ideal.span {b}) B) b})
    (AdicCompletion (Ideal.span {b}) B) := by
  have h : Ideal.span {algebraMap B (AdicCompletion (Ideal.span {b}) B) b} =
      (Ideal.span {b}).map (algebraMap B (AdicCompletion (Ideal.span {b}) B)) := by
    rw [Ideal.map_span, Set.image_singleton]
  rw [h, IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete (Submodule.fg_span_singleton b)

end General

variable {O : Type} [CommRing O]

theorem C_dvd_iff (c : O) (a : O⟦X⟧) : C c ∣ a ↔ ∀ n, c ∣ coeff n a := by
  constructor
  · rintro ⟨q, rfl⟩ n
    rw [coeff_C_mul]
    exact dvd_mul_right _ _
  · intro h
    choose q hq using h
    exact ⟨PowerSeries.mk q, PowerSeries.ext fun n => by rw [coeff_C_mul, coeff_mk, hq]⟩

theorem C_dvd_of_dvd_X_pow_mul (c : O) (m : ℕ) (a : O⟦X⟧) (h : C c ∣ X ^ m * a) : C c ∣ a := by
  rw [C_dvd_iff] at h ⊢
  intro n
  have := h (n + m)
  rwa [coeff_X_pow_mul] at this

theorem C_dvd_of_dvd_away (c : O) (a : O⟦X⟧)
    (h : algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (C c) ∣
      algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) a) : C c ∣ a := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨m, q, hq⟩ := IsLocalization.Away.surj (X : O⟦X⟧) z
  have h1 : algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (X ^ m * a) =
      algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) (C c * q) := by
    rw [map_mul, map_mul, map_pow, hz, ← hq]; ring
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq (X : O⟦X⟧) h1
  refine C_dvd_of_dvd_X_pow_mul c (n + m) a ⟨X ^ n * q, ?_⟩
  rw [pow_add, mul_assoc, hn]; ring

theorem algebraMap_EE (l : ℕ) (a : O⟦X⟧) : algebraMap O⟦X⟧ (EE O l) a =
    algebraMap (Localization.Away (X : O⟦X⟧)) (EE O l)
      (algebraMap O⟦X⟧ (Localization.Away (X : O⟦X⟧)) a) := by
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.algebraMap_apply]; rfl

theorem saturated (l : ℕ) (a : O⟦X⟧) (k : ℕ)
    (h : (l : EE O l) ^ k ∣ algebraMap O⟦X⟧ (EE O l) a) : (l : O⟦X⟧) ^ k ∣ a := by
  rw [algebraMap_EE, ← map_natCast (algebraMap (Localization.Away (X : O⟦X⟧)) (EE O l)) l] at h
  have h2 := pow_dvd_of_pow_dvd _ k _ h
  have e : (l : O⟦X⟧) ^ k = C ((l : O) ^ k) := by rw [map_pow, map_natCast]
  rw [e]
  apply C_dvd_of_dvd_away
  rwa [← e, map_pow, map_natCast]

end GlobalTheory.NB.LT.EEBasic

namespace GlobalTheory.NB.LT

open EEBasic

theorem EE_basic : ∀ {l : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] [CharZero O], l.Prime → ¬ IsUnit (l : O) → Function.Injective (algebraMap O⟦X⟧ (EE O l)) ∧ IsUnit (algebraMap O⟦X⟧ (EE O l) X) ∧ IsAdicComplete (Ideal.span {(l : EE O l)}) (EE O l) ∧ (∀ (x : EE O l) (k : ℕ), ∃ (a : O⟦X⟧) (m : ℕ), (l : EE O l) ^ k ∣ x * algebraMap O⟦X⟧ (EE O l) (X ^ m) - algebraMap O⟦X⟧ (EE O l) a) ∧ (∀ (a : O⟦X⟧) (k : ℕ), (l : EE O l) ^ k ∣ algebraMap O⟦X⟧ (EE O l) a → (l : O⟦X⟧) ^ k ∣ a) := by
  intro l O _ _ _ _ _ _ hl
  refine ⟨?_, ?_, ?_, ?_, saturated l⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    refine PowerSeries.ext fun n => ?_
    rw [map_zero]
    refine IsHausdorff.haus (I := IsLocalRing.maximalIdeal O) inferInstance _ fun k => ?_
    have h1 := saturated l a k (by rw [ha]; exact dvd_zero _)
    have e : (l : O⟦X⟧) ^ k = C ((l : O) ^ k) := by rw [map_pow, map_natCast]
    rw [e, C_dvd_iff] at h1
    obtain ⟨q, hq⟩ := h1 n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hq]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ((IsLocalRing.mem_maximalIdeal _).2 hl) k)
  · rw [algebraMap_EE]
    exact (IsLocalization.Away.algebraMap_isUnit (X : O⟦X⟧)).map _
  · have := complete (l : Localization.Away (X : O⟦X⟧))
    rwa [map_natCast] at this
  · intro x k
    obtain ⟨c, hc⟩ := exists_pow_dvd_sub (l : Localization.Away (X : O⟦X⟧)) k x
    rw [map_natCast] at hc
    obtain ⟨m, q, hq⟩ := IsLocalization.Away.surj (X : O⟦X⟧) c
    refine ⟨q, m, ?_⟩
    rw [algebraMap_EE l q, ← hq, map_mul, algebraMap_EE, map_pow (algebraMap O⟦X⟧ _), ← sub_mul]
    exact hc.mul_right _

end GlobalTheory.NB.LT
end
end

