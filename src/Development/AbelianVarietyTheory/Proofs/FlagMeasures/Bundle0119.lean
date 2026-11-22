import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0112
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0111
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0002
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCoveringSetExpLieLatticeRootGroup
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExponentialUnipotentStabilizer
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.BlockParabolicUnitriangularSubgroupsGLnPrimeFiel
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm.ParBasic

variable {g : ℕ} [Fact g.Prime] {a b : ℕ}

theorem tl_apply (M : Mt g (a + b)) (i j : Fin a) : tl a M i j = M (Fin.castAdd b i) (Fin.castAdd b j) := by
  have hi : (i : ℕ) < a + b := by omega
  have hj : (j : ℕ) < a + b := by omega
  simp only [tl, entN, hi, hj, and_self, dif_pos]
  rfl

theorem br_apply (M : Mt g (a + b)) (i j : Fin b) : br a b M i j = M (Fin.natAdd a i) (Fin.natAdd a j) := by
  have hi : a + (i : ℕ) < a + b := by omega
  have hj : a + (j : ℕ) < a + b := by omega
  simp only [br, entN, hi, hj, and_self, dif_pos]
  rfl

def blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : Mt g (a + b) :=
  (Matrix.fromBlocks A B 0 D).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

def ur (a b : ℕ) (M : Mt g (a + b)) : Matrix (Fin a) (Fin b) (ZMod g) :=
  fun i j => M (Fin.castAdd b i) (Fin.natAdd a j)

theorem tl_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : tl a (blkM A B D) = A := by
  ext i j; simp [tl_apply, blkM]

theorem br_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : br a b (blkM A B D) = D := by
  ext i j; simp [br_apply, blkM]

theorem ur_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : ur a b (blkM A B D) = B := by
  ext i j; simp [ur, blkM]

theorem inPar_iff (M : Mt g (a + b)) :
    InPar a M ↔ ∀ (i : Fin b) (j : Fin a), M (Fin.natAdd a i) (Fin.castAdd b j) = 0 := by
  constructor
  · intro h i j
    exact h _ _ (by simp) (by simp)
  · intro h i j hj hi
    have := h ⟨i - a, by omega⟩ ⟨j, hj⟩
    convert this using 2 <;> ext <;> simp
    omega

theorem inPar_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) : InPar a (blkM A B D) := by
  rw [inPar_iff]
  intro i j; simp [blkM]

theorem blkM_eq {M : Mt g (a + b)} (h : InPar a M) : blkM (tl a M) (ur a b M) (br a b M) = M := by
  rw [inPar_iff] at h
  ext i j
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
    simp [blkM, tl_apply, br_apply, ur, h]

theorem det_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) :
    (blkM A B D).det = A.det * D.det := by
  rw [blkM, Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]

theorem isUnit_blkM (A : Mt g a) (B : Matrix (Fin a) (Fin b) (ZMod g)) (D : Mt g b) :
    IsUnit (blkM A B D) ↔ IsUnit A ∧ IsUnit D := by
  simp only [Matrix.isUnit_iff_isUnit_det, det_blkM, IsUnit.mul_iff]

theorem blkM_mul (A A' : Mt g a) (B B' : Matrix (Fin a) (Fin b) (ZMod g)) (D D' : Mt g b) :
    blkM A B D * blkM A' B' D' = blkM (A * A') (A * B' + B * D') (D * D') := by
  rw [blkM, blkM, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp [blkM]

theorem isUnit_blocks (x : Gn g (a + b)) (h : InPar a (x : Mt g (a + b))) :
    IsUnit (tl a (x : Mt g (a + b))) ∧ IsUnit (br a b (x : Mt g (a + b))) := by
  rw [← isUnit_blkM _ (ur a b x.val), blkM_eq h]
  exact x.isUnit

theorem blocks_mul (x y : Mt g (a + b)) (hx : InPar a x) (hy : InPar a y) :
    InPar a (x * y) ∧ tl a (x * y) = tl a x * tl a y ∧ br a b (x * y) = br a b x * br a b y := by
  have e := blkM_mul (tl a x) (tl a y) (ur a b x) (ur a b y) (br a b x) (br a b y)
  rw [blkM_eq hx, blkM_eq hy] at e
  rw [e]
  exact ⟨inPar_blkM _ _ _, tl_blkM _ _ _, br_blkM _ _ _⟩

theorem exists_subgroup {G : Type} [Group G] [Finite G] (p : G → Prop) (h1 : p 1)
    (hm : ∀ x y, p x → p y → p (x * y)) : ∃ P : Subgroup G, ∀ x, x ∈ P ↔ p x := by
  have hp : ∀ x, p x → ∀ k : ℕ, p (x ^ k) := fun x hx k => by
    induction k with
    | zero => simpa using h1
    | succ k ih => rw [pow_succ]; exact hm _ _ ih hx
  refine ⟨{ carrier := {x | p x}, mul_mem' := fun {x y} => hm x y, one_mem' := h1, inv_mem' := fun {x} hx => ?_ },
    fun x => Iff.rfl⟩
  have : x⁻¹ = x ^ (orderOf x - 1) := by
    have h0 := orderOf_pos x
    rw [inv_eq_iff_mul_eq_one, ← pow_succ', Nat.sub_add_cancel h0, pow_orderOf_eq_one]
  change p x⁻¹
  rw [this]
  exact hp x hx _

theorem inPar_one (a n : ℕ) : InPar a (1 : Mt g n) := fun i j hj hi =>
  Matrix.one_apply_ne (by rintro rfl; omega)

theorem card_fibre (h₁ : Gn g a) (h₂ : Gn g b) :
    (Finset.univ.filter fun x : Gn g (a + b) => InPar a (x : Mt g (a + b)) ∧
      tl a (x : Mt g (a + b)) = (h₁ : Mt g a) ∧ br a b (x : Mt g (a + b)) = (h₂ : Mt g b)).card = g ^ (a * b) := by
  have hc : (Finset.univ : Finset (Matrix (Fin a) (Fin b) (ZMod g))).card = g ^ (a * b) := by
    rw [Finset.card_univ]
    change Fintype.card (Fin a → Fin b → ZMod g) = _
    simp [pow_mul']
  rw [← hc]
  refine Finset.card_bij (fun x _ => ur a b x.val) (fun _ _ => Finset.mem_univ _) ?_ ?_
  · intro x hx y hy h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
    apply Units.ext
    rw [← blkM_eq hx.1, ← blkM_eq hy.1, hx.2.1, hx.2.2, hy.2.1, hy.2.2, h]
  · intro B _
    have hu := (isUnit_blkM h₁.val B h₂.val).2 ⟨h₁.isUnit, h₂.isUnit⟩
    refine ⟨hu.unit, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, IsUnit.unit_spec]
      exact ⟨inPar_blkM _ _ _, tl_blkM _ _ _, br_blkM _ _ _⟩
    · simp only [IsUnit.unit_spec, ur_blkM]

theorem toG_val {n : ℕ} {M : Mt g n} (h : IsUnit M) : (toG M).val = M := by
  rw [toG, dif_pos h, IsUnit.unit_spec]

theorem card_par :
    (Finset.univ.filter fun x : Gn g (a + b) => InPar a (x : Mt g (a + b))).card =
      Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) := by
  rw [Finset.card_eq_sum_card_fiberwise (t := (Finset.univ : Finset (Gn g a × Gn g b)))
    (f := fun x : Gn g (a + b) => (toG (tl a x.val), toG (br a b x.val))) (fun _ _ => Finset.mem_univ _)]
  rw [Finset.sum_congr rfl (g := fun _ => g ^ (a * b))]
  · simp
  · rintro ⟨h₁, h₂⟩ _
    rw [← card_fibre h₁ h₂, Finset.filter_filter]
    congr 1
    refine Finset.filter_congr fun x _ => and_congr_right fun hx => ?_
    have hu := isUnit_blocks x hx
    rw [Prod.mk.injEq, Units.ext_iff, Units.ext_iff, toG_val hu.1, toG_val hu.2]

theorem isUniUp_one (n : ℕ) : IsUniUp (1 : Mt g n) := fun _ _ =>
  ⟨fun h => Matrix.one_apply_ne h.ne', fun h => h ▸ Matrix.one_apply_eq _⟩

theorem isUniUp_mul {n : ℕ} (x y : Mt g n) (hx : IsUniUp x) (hy : IsUniUp y) : IsUniUp (x * y) := by
  intro i j
  refine ⟨fun h => ?_, ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k < i
    · rw [(hx i k).1 hk, zero_mul]
    · rw [(hy k j).1 (h.trans_le (not_lt.1 hk)), mul_zero]
  · rintro rfl
    rw [Matrix.mul_apply, Finset.sum_eq_single i, (hx i i).2 rfl, (hy i i).2 rfl, mul_one]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [(hx i k).1 h, zero_mul]
      · rw [(hy k i).1 h, mul_zero]
    · simp

theorem par_basic : ∀ (g : ℕ) [Fact g.Prime] (a b n : ℕ), n = a + b → (∃ P : Subgroup (Gn g n), ∀ x, x ∈ P ↔ InPar a (x : Mt g n)) ∧ (∃ U : Subgroup (Gn g n), ∀ x, x ∈ U ↔ IsUniUp (x : Mt g n)) ∧ (∀ x : Gn g n, InPar a (x : Mt g n) → IsUnit (tl a (x : Mt g n)) ∧ IsUnit (br a b (x : Mt g n))) ∧ (∀ x y : Mt g n, InPar a x → InPar a y → tl a (x * y) = tl a x * tl a y ∧ br a b (x * y) = br a b x * br a b y) ∧ (∀ (h₁ : Gn g a) (h₂ : Gn g b), (Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n) ∧ tl a (x : Mt g n) = (h₁ : Mt g a) ∧ br a b (x : Mt g n) = (h₂ : Mt g b)).card = g ^ (a * b)) ∧ (Finset.univ.filter fun x : Gn g n => InPar a (x : Mt g n)).card = Fintype.card (Gn g a) * Fintype.card (Gn g b) * g ^ (a * b) := by
  intro g _ a b n hn
  subst hn
  exact ⟨exists_subgroup _ (inPar_one _ _) fun x y hx hy => (blocks_mul _ _ hx hy).1,
    exists_subgroup _ (isUniUp_one _) fun x y hx hy => isUniUp_mul _ _ hx hy,
    isUnit_blocks, fun x y hx hy => (blocks_mul x y hx hy).2, card_fibre, card_par⟩

end GlobalTheory.GLm.ParBasic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardDoubleCosetMulCardInter
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem card_doubleCoset_mul_card_inter {G : Type} [Group G] [Fintype G] (H K : Subgroup G) (w : G) :
    (Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w * k).card *
      (Finset.univ.filter fun x : G => x ∈ H ∧ w⁻¹ * x * w ∈ K).card = Nat.card H * Nat.card K := by
  have hmaps : ∀ p ∈ (Finset.univ : Finset (H × K)),
      (p.1 : G) * w * p.2 ∈ Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w * k := by
    intro p _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨p.1, p.1.2, p.2, p.2.2, rfl⟩
  have hcard := Finset.card_eq_sum_card_fiberwise
    (f := fun p : H × K => (p.1 : G) * w * p.2) (s := Finset.univ) hmaps
  have hfib : ∀ y ∈ (Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w * k),
      ((Finset.univ : Finset (H × K)).filter fun p => (p.1 : G) * w * p.2 = y).card =
        (Finset.univ.filter fun x : G => x ∈ H ∧ w⁻¹ * x * w ∈ K).card := by
    intro y hy
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
    obtain ⟨h0, hh0, k0, hk0, rfl⟩ := hy
    symm
    refine Finset.card_bij'
      (fun t ht => ((⟨h0 * t, H.mul_mem hh0 (Finset.mem_filter.1 ht).2.1⟩ : H),
        (⟨w⁻¹ * t⁻¹ * w * k0, by
          have hinv := K.inv_mem (Finset.mem_filter.1 ht).2.2
          rw [show (w⁻¹ * t * w)⁻¹ = w⁻¹ * t⁻¹ * w by group] at hinv
          exact K.mul_mem hinv hk0⟩ : K)))
      (fun p _ => h0⁻¹ * (p.1 : G)) ?_ ?_ ?_ ?_
    · intro t _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      group
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      have e : (p.1 : G) = h0 * w * k0 * (p.2 : G)⁻¹ * w⁻¹ := by
        rw [← hp]; group
      refine ⟨H.mul_mem (H.inv_mem hh0) p.1.2, ?_⟩
      rw [e, show w⁻¹ * (h0⁻¹ * (h0 * w * k0 * (p.2 : G)⁻¹ * w⁻¹)) * w = k0 * (p.2 : G)⁻¹ by group]
      exact K.mul_mem hk0 (K.inv_mem p.2.2)
    · intro t _
      group
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      have e : (p.2 : G) = w⁻¹ * (p.1 : G)⁻¹ * (h0 * w * k0) := by
        rw [← hp]; group
      ext
      · simp
      · simp only
        rw [e]
        group
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul] at hcard
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, ← Fintype.card_prod, ← Finset.card_univ,
    hcard]

private theorem sum_conj_double_coset_eq_of_invariant {G : Type} [Group G] [Fintype G] (H K : Subgroup G) (w h k : G)
    (hh : h ∈ H) (hk : k ∈ K) (lam φ : G → ℂ)
    (hlam : ∀ h ∈ H, ∀ x ∈ H, lam (h * x * h⁻¹) = lam x)
    (hφ : ∀ k ∈ K, ∀ x ∈ K, φ (k * x * k⁻¹) = φ x) :
    (∑ x : G, if x ∈ H ∧ (h * w * k)⁻¹ * x * (h * w * k) ∈ K then
        lam x * φ ((h * w * k)⁻¹ * x * (h * w * k)) else 0) =
      ∑ x : G, if x ∈ H ∧ w⁻¹ * x * w ∈ K then lam x * φ (w⁻¹ * x * w) else 0 := by
  refine (Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ fun x => ?_).symm
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply]
  have e1 : (h * w * k)⁻¹ * (h * x * h⁻¹) * (h * w * k) = k⁻¹ * (w⁻¹ * x * w) * k := by group
  simp only [e1]
  have eH : h * x * h⁻¹ ∈ H ↔ x ∈ H := by
    rw [H.mul_mem_cancel_right (H.inv_mem hh), H.mul_mem_cancel_left hh]
  have eK : k⁻¹ * (w⁻¹ * x * w) * k ∈ K ↔ w⁻¹ * x * w ∈ K := by
    rw [K.mul_mem_cancel_right hk, K.mul_mem_cancel_left (K.inv_mem hk)]
  by_cases hx : x ∈ H ∧ w⁻¹ * x * w ∈ K
  · have hc := hφ k⁻¹ (K.inv_mem hk) _ hx.2
    rw [inv_inv] at hc
    rw [if_pos hx, if_pos ⟨eH.2 hx.1, eK.2 hx.2⟩, hlam h hh x hx.1, hc]
  · rw [if_neg hx, if_neg]
    rintro ⟨h1, h2⟩
    exact hx ⟨eH.1 h1, eK.1 h2⟩

theorem mackey_doubleCoset_pairing : ∀ (G : Type) [Group G] [Fintype G] (H K : Subgroup G) (ι : Type) (R : Finset ι) (w : ι → G), (∀ x : G, ∃! i, i ∈ R ∧ ∃ h ∈ H, ∃ k ∈ K, x = h * w i * k) → ∀ (lam φ : G → ℂ), (∀ h ∈ H, ∀ x ∈ H, lam (h * x * h⁻¹) = lam x) → (∀ k ∈ K, ∀ x ∈ K, φ (k * x * k⁻¹) = φ x) → (Nat.card H : ℂ)⁻¹ * ∑ x : G, (if x ∈ H then lam x * ((Nat.card K : ℂ)⁻¹ * ∑ y : G, if y⁻¹ * x * y ∈ K then φ (y⁻¹ * x * y) else 0) else 0) = ∑ i ∈ R, ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ * ∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0 := by
  intro G _ _ H K ι R w hR lam φ hlam hφ
  have hHpos : (Nat.card H : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have hKpos : (Nat.card K : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  have h1 : ∀ x : G, (if x ∈ H then lam x * ((Nat.card K : ℂ)⁻¹ *
        ∑ y : G, if y⁻¹ * x * y ∈ K then φ (y⁻¹ * x * y) else 0) else 0) =
      (Nat.card K : ℂ)⁻¹ * ∑ y : G,
        (if x ∈ H ∧ y⁻¹ * x * y ∈ K then lam x * φ (y⁻¹ * x * y) else 0) := by
    intro x
    by_cases hx : x ∈ H
    · rw [if_pos hx]
      simp only [Finset.mul_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      by_cases hy : y⁻¹ * x * y ∈ K
      · rw [if_pos hy, if_pos ⟨hx, hy⟩]; ring
      · rw [if_neg hy, if_neg (fun hc => hy hc.2)]; ring
    · simp [hx]
  rw [Finset.sum_congr rfl (fun x _ => h1 x), ← Finset.mul_sum, Finset.sum_comm]
  have h2 : ∀ y : G, (∑ x : G,
        (if x ∈ H ∧ y⁻¹ * x * y ∈ K then lam x * φ (y⁻¹ * x * y) else 0)) =
      ∑ i ∈ R, if (∃ h ∈ H, ∃ k ∈ K, y = h * w i * k) then
        (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0)
        else 0 := by
    intro y
    obtain ⟨i, ⟨hi, h, hhH, k, hkK, rfl⟩, huniq⟩ := hR y
    rw [Finset.sum_eq_single_of_mem i hi]
    · rw [if_pos ⟨h, hhH, k, hkK, rfl⟩]
      exact sum_conj_double_coset_eq_of_invariant H K (w i) h k hhH hkK lam φ hlam hφ
    · intro j hj hji
      rw [if_neg]
      intro hP
      exact hji (huniq j ⟨hj, hP⟩)
  rw [Finset.sum_congr rfl (fun y _ => h2 y), Finset.sum_comm]
  have h3 : ∀ i ∈ R, (∑ y : G, if (∃ h ∈ H, ∃ k ∈ K, y = h * w i * k) then
        (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0)
        else 0) =
      ((Nat.card H : ℂ) * Nat.card K) *
        ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ *
        (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0) := by
    intro i _
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc : ((Finset.univ.filter fun y : G => ∃ h ∈ H, ∃ k ∈ K, y = h * w i * k).card : ℂ) *
        ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ) =
          (Nat.card H : ℂ) * Nat.card K := by
      exact_mod_cast card_doubleCoset_mul_card_inter H K (w i)
    have hI : ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ) ≠ 0 := by
      have hmem : (1 : G) ∈ Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K := by
        simp [H.one_mem, K.one_mem]
      exact_mod_cast (Finset.card_pos.2 ⟨1, hmem⟩).ne'
    rw [← hc, mul_inv_cancel_right₀ hI]
  rw [Finset.sum_congr rfl h3, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e1 : (Nat.card H : ℂ)⁻¹ * Nat.card H = 1 := inv_mul_cancel₀ hHpos
  have e2 : (Nat.card K : ℂ)⁻¹ * Nat.card K = 1 := inv_mul_cancel₀ hKpos
  linear_combination
    ((Nat.card K : ℂ)⁻¹ * Nat.card K *
      ((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ *
      (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0)) * e1 +
    (((Finset.univ.filter fun x : G => x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K).card : ℂ)⁻¹ *
      (∑ x : G, if x ∈ H ∧ (w i)⁻¹ * x * w i ∈ K then lam x * φ ((w i)⁻¹ * x * w i) else 0)) * e2

end GlobalTheory.GLm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardInnerLatticesWithDefiniteTraceLeNormStatement
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_innerLattices_with_definite_trace_le_norm : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ((({L' : Submodule (𝓞 K) V | ∃ Λ', N.IsTerm g Λ' ∧ L' = latL N.F' N.F Λ' ∧ flagPairDefinitePartLattice N.F' N.F Λ' = flagPairDefinitePartLattice N.F' N.F Λ}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (N.NT ^ 2) := by
  first | exact @GlobalTheory.DegCnt.GlueZ.main | exact GlobalTheory.DegCnt.GlueZ.main | (intros; apply GlobalTheory.DegCnt.GlueZ.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CardLeCardMulCardSupport
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLm

theorem norm_unitsChar_apply {C : Type} [CommGroup C] [Fintype C] (θ : C →* ℂˣ) (z : C) :
    ‖(θ z : ℂ)‖ = 1 := by
  have h : (θ z : ℂ) ^ Fintype.card C = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_card_eq_one, map_one, Units.val_one]
  exact Complex.norm_eq_one_of_pow_eq_one h Fintype.card_ne_zero

theorem sum_unitsChar_mul_inv {C : Type} [CommGroup C] [Fintype C] (θ η : C →* ℂˣ) :
    ∑ z : C, (θ z : ℂ) * (η z⁻¹ : ℂ) = if θ = η then (Fintype.card C : ℂ) else 0 := by
  split_ifs with h
  · subst h
    have : ∀ z : C, (θ z : ℂ) * (θ z⁻¹ : ℂ) = 1 := by
      intro z
      rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one]
    simp only [this]
    simp
  · have hne : (Units.coeHom ℂ).comp (θ * η⁻¹) ≠ 1 := by
      intro h1
      apply h
      ext z
      have h2 := DFunLike.congr_fun h1 z
      have h3 : θ z * (η z)⁻¹ = 1 := by
        apply Units.ext
        simpa using h2
      rw [mul_inv_eq_one] at h3
      rw [h3]
    have := sum_hom_units_eq_zero _ hne
    rw [← this]
    refine Finset.sum_congr rfl fun z _ => ?_
    simp

theorem card_le_card_mul_card_support :
    ∀ (C : Type) [CommGroup C] [Fintype C] (S : Finset (C →* ℂˣ)) (c : (C →* ℂˣ) → ℂ), (∃ z : C, ∑ θ ∈ S, c θ * (θ z : ℂ) ≠ 0) → Fintype.card C ≤ S.card * (Finset.univ.filter fun z : C => ∑ θ ∈ S, c θ * (θ z : ℂ) ≠ 0).card := by
  intro C _ _ S c hz
  obtain ⟨z₁, hz₁⟩ := hz
  set f : C → ℂ := fun z => ∑ θ ∈ S, c θ * (θ z : ℂ) with hf
  set T : Finset C := Finset.univ.filter fun z : C => f z ≠ 0 with hT
  obtain ⟨z₀, -, hz₀⟩ := Finset.exists_max_image Finset.univ (fun z => ‖f z‖) ⟨z₁, Finset.mem_univ _⟩
  have hM : 0 < ‖f z₀‖ := lt_of_lt_of_le (norm_pos_iff.mpr hz₁) (hz₀ z₁ (Finset.mem_univ _))
  have hinv : ∀ η ∈ S, (Fintype.card C : ℂ) * c η = ∑ z ∈ T, f z * (η z⁻¹ : ℂ) := by
    intro η hη
    have h1 : ∑ z ∈ T, f z * (η z⁻¹ : ℂ) = ∑ z : C, f z * (η z⁻¹ : ℂ) := by
      rw [hT]
      refine Finset.sum_subset (Finset.filter_subset _ _) fun z _ hz => ?_
      have : f z = 0 := by simpa using hz
      rw [this, zero_mul]
    rw [h1]
    simp only [hf, Finset.sum_mul, mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, sum_unitsChar_mul_inv, mul_ite, mul_zero]
    rw [Finset.sum_ite_eq' S η, if_pos hη, mul_comm]
  have hc : ∀ η ∈ S, (Fintype.card C : ℝ) * ‖c η‖ ≤ T.card * ‖f z₀‖ := by
    intro η hη
    have h1 : ‖(Fintype.card C : ℂ) * c η‖ = (Fintype.card C : ℝ) * ‖c η‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [← h1, hinv η hη]
    refine (norm_sum_le _ _).trans ?_
    rw [← nsmul_eq_mul]
    refine Finset.sum_le_card_nsmul _ _ _ fun z _ => ?_
    rw [norm_mul, norm_unitsChar_apply, mul_one]
    exact hz₀ z (Finset.mem_univ _)
  have hf0 : ‖f z₀‖ ≤ ∑ η ∈ S, ‖c η‖ := by
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun η _ => ?_
    rw [norm_mul, norm_unitsChar_apply, mul_one]
  have hfin : (Fintype.card C : ℝ) * ‖f z₀‖ ≤ ((S.card : ℝ) * T.card) * ‖f z₀‖ := by
    calc (Fintype.card C : ℝ) * ‖f z₀‖ ≤ (Fintype.card C : ℝ) * ∑ η ∈ S, ‖c η‖ :=
          mul_le_mul_of_nonneg_left hf0 (Nat.cast_nonneg _)
      _ = ∑ η ∈ S, (Fintype.card C : ℝ) * ‖c η‖ := Finset.mul_sum _ _ _
      _ ≤ S.card • ((T.card : ℝ) * ‖f z₀‖) := Finset.sum_le_card_nsmul _ _ _ hc
      _ = _ := by rw [nsmul_eq_mul, mul_assoc]
  have := le_of_mul_le_mul_right hfin hM
  exact_mod_cast this

end GlobalTheory.GLm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CentredCapelliOperatorFormsAgreeStatement
section
open Formalism.FourierDecayAlt GlobalTheory.ThA MeasureTheory Formalism.QuantumDeterminants Matrix
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centredCapelliOperator_forms_agree : ∀ (k r : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (Y : ℂ) (F : B.Mat k r → V), Q.CV k r Y F = PI.CapelliEig.capC (k := k) (r := r) Y F ∧ Q.CV k r Y F = Formalism.MainNotions.S.capC (k := k) (r := r) Y F := by
  first | exact @GlobalTheory.ThA.centredCapelli_forms_agree | exact GlobalTheory.ThA.centredCapelli_forms_agree | (intros; apply GlobalTheory.ThA.centredCapelli_forms_agree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoveringRadiiIff
section
open NumberField Matrix Finset

noncomputable section

namespace GlobalTheory.CoverRadiiEq

open Formalism.MainNotions.S GlobalTheory.Count

section Lie

variable {A : Type} [CommRing A] {n : ℕ}

theorem hform_eq_dot (s : A →+* A) (M : Matrix (Fin n) (Fin n) A) (u u' : Fin n → A) :
    Formalism.UG.hform s M u u' = (fun i => s (u i)) ⬝ᵥ (M *ᵥ u') := by
  unfold Formalism.UG.hform
  simp only [dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem hform_skew (s : A →+* A) (J Y : Matrix (Fin n) (Fin n) A) (u u' : Fin n → A) :
    Formalism.UG.hform s J (Y *ᵥ u) u' + Formalism.UG.hform s J u (Y *ᵥ u') =
      Formalism.UG.hform s (Formalism.UG.cT s Y * J + J * Y) u u' := by
  rw [hform_eq_dot, hform_eq_dot, hform_eq_dot]
  have h1 : (fun i => s ((Y *ᵥ u) i)) = (Y.map s) *ᵥ (fun i => s (u i)) := by
    funext i
    simp [mulVec, dotProduct, map_sum, map_mul]
  have h2 : ((Y.map s) *ᵥ (fun i => s (u i))) ⬝ᵥ (J *ᵥ u') =
      (fun i => s (u i)) ⬝ᵥ (((Y.map s)ᵀ * J) *ᵥ u') := by
    rw [← mulVec_mulVec, dotProduct_mulVec (fun i => s (u i)) (Y.map s)ᵀ, vecMul_transpose]
  rw [h1, h2, mulVec_mulVec, ← dotProduct_add, ← add_mulVec]
  rfl

private lemma hform_single_single' (s : A →+* A) (M : Matrix (Fin n) (Fin n) A) (i j : Fin n) :
    Formalism.UG.hform s M (Pi.single i 1) (Pi.single j 1) = M i j := by
  rw [hform_eq_dot]
  have e : (fun a => s ((Pi.single i (1 : A) : Fin n → A) a)) = (Pi.single i 1 : Fin n → A) := by
    funext a
    by_cases h : a = i
    · subst h; simp
    · simp [Pi.single_apply, h]
  rw [e]
  simp

theorem skew_iff (s : A →+* A) (J Y : Matrix (Fin n) (Fin n) A) :
    Formalism.UG.cT s Y * J + J * Y = 0 ↔ GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets.IsSkew s J Y := by
  constructor
  · intro h u u'
    rw [hform_skew, h, hform_eq_dot, zero_mulVec, dotProduct_zero]
  · intro h
    ext i j
    rw [Matrix.zero_apply, ← hform_single_single' s (Formalism.UG.cT s Y * J + J * Y) i j, ← hform_skew]
    exact h _ _

end Lie

variable (I : AutInst)

end GlobalTheory.CoverRadiiEq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCoveringSetExpLieLatticeRootGroupStatement
section
open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_covering_set_exp_lie_lattice_rootGroup : ∀ (ι : Type) [Fintype ι] (N : ℕ) (R : Finset (Fin N × Fin N)) (Λ : Submodule ℤ (ι → R → ℂ)) (Ω₀ : Set (ι → R → ℂ)), (∀ q ∈ R, q.1 < q.2) → (∀ a b c : Fin N, (a, b) ∈ R → (b, c) ∈ R → (a, c) ∈ R) → MeasurableSet Ω₀ → MeasureTheory.IsAddFundamentalDomain Λ Ω₀ MeasureTheory.volume → MeasureTheory.volume Ω₀ ≠ ⊤ → DiscreteTopology Λ → (∀ x ∈ Λ, ∀ y ∈ Λ, ∃ z ∈ Λ, ∀ v, expT (ofRoots R (x v) - 1) * expT (ofRoots R (y v) - 1) = expT (ofRoots R (z v) - 1)) → ∃ Ω : Set (ι → R → ℂ), MeasurableSet Ω ∧ MeasureTheory.volume Ω = MeasureTheory.volume Ω₀ ∧ ∀ c : ι → R → ℂ, ∃ x ∈ Λ, (fun v (q : R) => (expT (ofRoots R (x v) - 1) * ofRoots R (c v) : Matrix (Fin N) (Fin N) ℂ) q.1.1 q.1.2) ∈ Ω := by
  first | exact @GlobalTheory.LoopV.Cover.cover | exact GlobalTheory.LoopV.Cover.cover | (intros; apply GlobalTheory.LoopV.Cover.cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExponentialUnipotentStabilizerStatement
section
open NumberField Module Matrix Formalism.MainNotions.S GlobalTheory.LoopV
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exponential_unipotent_stabilizer : ∀ (K : Type) [Field K] [NumberField K] (N : ℕ) (Z : Matrix (Fin N) (Fin N) K) (I : Ideal (𝓞 K)), Z.det ≠ 0 → (∀ x ∈ lieU Z, EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) x → expT x ∈ stabU Z ∧ EntIn I (expT x - 1) ∧ expT x * expT (-x) = 1) ∧ ∀ x ∈ lieU Z, ∀ y ∈ lieU Z, EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) x → EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) y → ∃ z ∈ lieU Z, EntIn (Ideal.span {(N.factorial : 𝓞 K)} * I) z ∧ expT x * expT y = expT z := by
  first | exact @GlobalTheory.LoopV.ExpGroup.exp_group | exact GlobalTheory.LoopV.ExpGroup.exp_group | (intros; apply GlobalTheory.LoopV.ExpGroup.exp_group <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagCoefIntegralOfLocalIntegralStatement
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_coef_integral_of_local_integral : ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [inst_2 : StarRing E] {S : HSpace E} {r : ℕ} (Λ : Submodule (𝓞 E) S.V) (g : ℕ) {T : E} (F : LFlag S r T), IsFixedConv Λ g F → ∀ (j : ℕ) (x : S.V), x ∈ Xflag F j → (∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → x ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal Λ)) → ∃ w : Fin r → E, x = ∑ c, w c • F.fl.e c ∧ (∀ c : Fin r, j ≤ c.val → w c = 0) ∧ ∀ P : HeightOneSpectrum (𝓞 E), (g : 𝓞 E) ∈ P.asIdeal → ∀ c, ∃ s : 𝓞 E, s ∉ P.asIdeal ∧ ∃ o : 𝓞 E, (s : E) * w c = o := by
  first | exact @GlobalTheory.FlagCoef.coef_integral_of_flag | exact GlobalTheory.FlagCoef.coef_integral_of_flag | (intros; apply GlobalTheory.FlagCoef.coef_integral_of_flag <;> assumption)
end

