import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0532

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviRadicalProductLengthOfLatticeSteps
section
open GlobalTheory.InertZeta

noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem exists_eq_exp_of_ne {x : WithZero (Multiplicative ℤ)} (h : x ≠ 0) : ∃ m : ℤ, x = WithZero.exp m :=
  ⟨x.log, (WithZero.exp_log h).symm⟩

theorem exp_mul_le_exp_iff {x : WithZero (Multiplicative ℤ)} {s k : ℤ} :
    WithZero.exp s * x ≤ WithZero.exp k ↔ x ≤ WithZero.exp (k - s) := by
  by_cases h : x = 0
  · subst h; simp
  · obtain ⟨m, rfl⟩ := exists_eq_exp_of_ne h
    rw [← WithZero.exp_add, WithZero.exp_le_exp, WithZero.exp_le_exp]
    omega

theorem exp_succ_le_of_not_le {x : WithZero (Multiplicative ℤ)} {k : ℤ} (h : ¬ x ≤ WithZero.exp k) :
    WithZero.exp (k + 1) ≤ x := by
  by_cases h0 : x = 0
  · subst h0; exact absurd zero_le h
  · obtain ⟨m, rfl⟩ := exists_eq_exp_of_ne h0
    rw [WithZero.exp_le_exp] at h ⊢
    omega

theorem exists_le_exp_add (x : WithZero (Multiplicative ℤ)) (k₀ : ℤ) : ∃ e : ℕ, x ≤ WithZero.exp (k₀ + e) := by
  by_cases h0 : x = 0
  · exact ⟨0, by simp [h0]⟩
  · obtain ⟨m, rfl⟩ := exists_eq_exp_of_ne h0
    exact ⟨(m - k₀).toNat, WithZero.exp_le_exp.2 (by omega)⟩

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem v_pow_unif {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℕ) :
    Valued.v (ϖ ^ k) = WithZero.exp (-(k : ℤ)) := by
  rw [map_pow, hϖ, ← WithZero.exp_nsmul]; congr 1; simp

theorem v_zpow_unif {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℤ) :
    Valued.v (ϖ ^ k) = WithZero.exp (-k) := by
  rw [map_zpow₀, hϖ, ← WithZero.exp_zsmul]; congr 1; simp

theorem pow_mul_mem_intL_iff {ϖ : L} (hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (k : ℕ) (x : L) :
    ϖ ^ k * x ∈ intL L ↔ Valued.v x ≤ WithZero.exp (k : ℤ) := by
  show Valued.v (ϖ ^ k * x) ≤ 1 ↔ _
  rw [map_mul, v_pow_unif hϖ, ← WithZero.exp_zero, exp_mul_le_exp_iff]
  simp

section Entries

variable {σ : L →+* L} {N : ℕ}

omit [Valued L (WithZero (Multiplicative ℤ))] in

theorem leviElt_mul_rad_entries {ϖ : L} {a : ℤ} {g₀ : GU σ N} {m u : GU σ (N + 2)} (hm : IsLeviElt ϖ a g₀ m)
    (hu : u ∈ radQ σ N) :
    mat (m * u) 0 0 = ϖ ^ a ∧ (∀ j, mat (m * u) 0 (mid j) = ϖ ^ a * rowOf u j) ∧
    mat (m * u) 0 (Fin.last (N + 1)) = ϖ ^ a * cornerOf u ∧
    (∀ i, mat (m * u) (mid i) 0 = 0) ∧ (∀ i j, mat (m * u) (mid i) (mid j) = mat g₀ i j) ∧
    (∀ i, mat (m * u) (mid i) (Fin.last (N + 1)) = (mat g₀ *ᵥ colOf u) i) ∧
    mat (m * u) (Fin.last (N + 1)) 0 = 0 ∧ (∀ j, mat (m * u) (Fin.last (N + 1)) (mid j) = 0) ∧
    mat (m * u) (Fin.last (N + 1)) (Fin.last (N + 1)) = ϖ ^ (-a) := by
  obtain ⟨hmz, h00, hll, hmm⟩ := hm
  have hmz' : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := hmz
  have hu' : ∀ i j, blk N j ≤ blk N i → mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j := hu
  have m0m : ∀ j, mat m 0 (mid j) = 0 := fun j => hmz' _ _ (by simp)
  have m0l : mat m 0 (Fin.last (N + 1)) = 0 := hmz' _ _ (by simp)
  have mm0 : ∀ i, mat m (mid i) 0 = 0 := fun i => hmz' _ _ (by simp)
  have mml : ∀ i, mat m (mid i) (Fin.last (N + 1)) = 0 := fun i => hmz' _ _ (by simp)
  have ml0 : mat m (Fin.last (N + 1)) 0 = 0 := hmz' _ _ (by simp)
  have mlm : ∀ j, mat m (Fin.last (N + 1)) (mid j) = 0 := fun j => hmz' _ _ (by simp)
  have u00 : mat u 0 0 = 1 := by rw [hu' _ _ le_rfl, Matrix.one_apply_eq]
  have um0 : ∀ i, mat u (mid i) 0 = 0 := fun i => by
    rw [hu' _ _ (by simp), Matrix.one_apply_ne (mid_ne_zero i)]
  have ul0 : mat u (Fin.last (N + 1)) 0 = 0 := by
    rw [hu' _ _ (by simp), Matrix.one_apply_ne last_ne_zero]
  have hu_mm : ∀ i j, mat u (mid i) (mid j) = if i = j then 1 else 0 := fun i j => by
    rw [hu' _ _ (by simp), Matrix.one_apply]; simp [mid_injective.eq_iff]
  have ulm : ∀ j, mat u (Fin.last (N + 1)) (mid j) = 0 := fun j => by
    rw [hu' _ _ (by simp), Matrix.one_apply_ne (fun h => mid_ne_last j h.symm)]
  have ull : mat u (Fin.last (N + 1)) (Fin.last (N + 1)) = 1 := by rw [hu' _ _ le_rfl, Matrix.one_apply_eq]
  simp only [mat_mul, Matrix.mul_apply, sum_idx]
  refine ⟨?_, fun j => ?_, ?_, fun i => ?_, fun i j => ?_, fun i => ?_, ?_, fun j => ?_, ?_⟩ <;>
    simp [m0m, m0l, mm0, mml, ml0, mlm, u00, um0, ul0, hu_mm, ulm, ull, h00, hll, hmm, rowOf, colOf, cornerOf,
      Matrix.mulVec, dotProduct]

end Entries

theorem pointwise_of_steps (hA : AddVec) (hD : Dual) (hS : SpanEq) (hH : Heis) : Pointwise := by
  intro L _ _ ϖ σ q N hU a g₀ m hm U V C l hf hl u hu
  classical
  have hϖ : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hU.2.2.2.1
  obtain ⟨e00, e0m, e0l, em0, emm, eml, el0, elm, ell⟩ := leviElt_mul_rad_entries hm hu
  have hrb : ∀ j, rowOf u j = -σ (colOf u j.rev) := ((hH L ϖ σ q N hU).1 u hu).1

  let Q : ℕ → Prop := fun e => ∀ j, Valued.v ((rowOf u ᵥ* C) j) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ)
  have hQD : ∀ e, Q e ↔
      (∀ i, Valued.v (((C * V * mat g₀) *ᵥ colOf u) i) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ)) ∧
      ∀ i, Valued.v (((mat g₀ * C * U) *ᵥ colOf u) i) ≤ WithZero.exp ((a.toNat + e : ℕ) : ℤ) := fun e => by
    have := hD L ϖ σ q N hU g₀ U V C hf (rowOf u) (colOf u) (ϖ ^ (a.toNat + e)) hrb
    simp only [pow_mul_mem_intL_iff hϖ] at this
    exact this
  have hQex : ∃ e, Q e := by
    choose f hf' using fun j => exists_le_exp_add (Valued.v ((rowOf u ᵥ* C) j)) (a.toNat : ℤ)
    obtain ⟨M, hM⟩ := Finite.exists_le f
    exact ⟨M, fun j => (hf' j).trans (WithZero.exp_le_exp.2 (by have := hM j; push_cast; omega))⟩
  let e := Nat.find hQex
  have hQe : Q e := Nat.find_spec hQex
  have hQmono : ∀ e', Q e' ↔ e ≤ e' := fun e' =>
    ⟨fun h => Nat.find_min' hQex h, fun h j => (hQe j).trans (WithZero.exp_le_exp.2 (by push_cast; omega))⟩
  have hnQ : 0 < e → ¬ Q (e - 1) := fun he h => by have := (hQmono _).1 h; omega
  have hsucc : 0 < e → ((a.toNat + (e - 1) : ℕ) : ℤ) + 1 = ((a.toNat + e : ℕ) : ℤ) := fun he => by omega
  have hQsharp : 0 < e → ∃ j, Valued.v ((rowOf u ᵥ* C) j) = WithZero.exp ((a.toNat + e : ℕ) : ℤ) := fun he => by
    obtain ⟨j, hj⟩ := not_forall.1 (hnQ he)
    refine ⟨j, le_antisymm (hQe j) ?_⟩
    have := exp_succ_le_of_not_le hj
    rwa [hsucc he] at this

  let y : L := ϖ ^ (-((a.toNat + e : ℕ) : ℤ))
  have hy : Valued.v y = WithZero.exp ((a.toNat + e : ℕ) : ℤ) := by rw [v_zpow_unif hϖ, neg_neg]
  obtain ⟨h2, h3⟩ := (hQD e).1 hQe
  have h4 : Valued.v y = WithZero.exp (a.toNat : ℤ) ∨
      (∃ i, Valued.v y = Valued.v (((C * V * mat g₀) *ᵥ colOf u) i)) ∨
      ∃ i, Valued.v y = Valued.v (((mat g₀ * C * U) *ᵥ colOf u) i) := by
    rcases Nat.eq_zero_or_pos e with he | he
    · left; rw [hy, he]; rfl
    · right
      have hn := hnQ he
      rw [hQD] at hn
      rcases not_and_or.1 hn with hn | hn
      · obtain ⟨i, hi⟩ := not_forall.1 hn
        have := exp_succ_le_of_not_le hi
        rw [hsucc he] at this
        exact Or.inl ⟨i, by rw [hy]; exact le_antisymm this (h2 i)⟩
      · obtain ⟨i, hi⟩ := not_forall.1 hn
        have := exp_succ_le_of_not_le hi
        rw [hsucc he] at this
        exact Or.inr ⟨i, by rw [hy]; exact le_antisymm this (h3 i)⟩
  obtain ⟨P, ρ, hPdet, hρ0, hρm, hρl, hlat⟩ :=
    hS L ϖ N a (mat (m * u)) (mat g₀) U V C (rowOf u) (colOf u) (cornerOf u) y hϖ hf e00 e0m e0l em0 emm eml el0 elm
      ell (by rw [hy, WithZero.exp_le_exp]; push_cast; omega) (fun i => by rw [hy]; exact h2 i)
      (fun i => by rw [hy]; exact h3 i) h4
  obtain ⟨c', hc'⟩ : ∃ c', c' = cornerOf u - rowOf u ⬝ᵥ ((C * V * mat g₀) *ᵥ colOf u) := ⟨_, rfl⟩
  rw [← hc'] at hρl
  have hPdet' : Valued.v P.det = WithZero.exp ((a.natAbs + l + e : ℕ) : ℤ) := by
    rw [hPdet, hl, hy, ← WithZero.exp_neg, neg_neg, ← WithZero.exp_add, ← WithZero.exp_add]
    congr 1; simp only [Nat.cast_add]; omega
  have hvm : ∀ j (k : ℤ), Valued.v (ρ (mid j)) ≤ WithZero.exp k ↔
      Valued.v ((rowOf u ᵥ* C) j) ≤ WithZero.exp (k + a.toNat) := fun j k => by
    rw [hρm, map_mul, v_pow_unif hϖ, exp_mul_le_exp_iff, sub_neg_eq_add]
  have hvl : Valued.v (ρ (Fin.last (N + 1))) = WithZero.exp (-((2 * a.toNat + e : ℕ) : ℤ)) * Valued.v c' := by
    rw [hρl, map_div₀, map_mul, v_pow_unif hϖ, hy, div_eq_mul_inv, ← WithZero.exp_neg, mul_comm, ← mul_assoc,
      ← WithZero.exp_add]
    congr 2; push_cast; ring
  have hvl' : ∀ k : ℤ, Valued.v (ρ (Fin.last (N + 1))) ≤ WithZero.exp k ↔
      Valued.v c' ≤ WithZero.exp (k + ((2 * a.toNat + e : ℕ) : ℤ)) := fun k => by
    rw [hvl, exp_mul_le_exp_iff, sub_neg_eq_add]

  let R : ℕ → Prop := fun e₂ => e ≤ e₂ ∧ Valued.v (ρ (Fin.last (N + 1))) ≤ WithZero.exp (e₂ : ℤ)
  have hRex : ∃ e₂, R e₂ := by
    obtain ⟨k, hk⟩ := exists_le_exp_add (Valued.v (ρ (Fin.last (N + 1)))) (e : ℤ)
    exact ⟨e + k, by omega, by rwa [Nat.cast_add]⟩
  let e₂ := Nat.find hRex
  have hRe₂ : R e₂ := Nat.find_spec hRex
  have hbound : ∀ i, Valued.v (ρ i) ≤ WithZero.exp (e₂ : ℤ) := fun i => by
    rcases idx_cases i with rfl | ⟨j, rfl⟩ | rfl
    · rw [hρ0, map_zero]; exact zero_le
    · rw [hvm]
      exact (hQe j).trans (WithZero.exp_le_exp.2 (by have := hRe₂.1; push_cast; omega))
    · exact hRe₂.2
  have hsharp : e₂ = 0 ∨ ∃ i, Valued.v (ρ i) = WithZero.exp (e₂ : ℤ) := by
    by_cases h : e₂ = e
    · rcases Nat.eq_zero_or_pos e with he | he
      · left; omega
      · right
        obtain ⟨j, hj⟩ := hQsharp he
        refine ⟨mid j, ?_⟩
        rw [hρm, map_mul, v_pow_unif hϖ, hj, ← WithZero.exp_add, h]
        congr 1; push_cast; ring
    · right
      have hlt : e < e₂ := lt_of_le_of_ne hRe₂.1 (Ne.symm h)
      have hn : ¬ R (e₂ - 1) := Nat.find_min hRex (by omega)
      have hn' : ¬ Valued.v (ρ (Fin.last (N + 1))) ≤ WithZero.exp ((e₂ - 1 : ℕ) : ℤ) := fun h' =>
        hn ⟨by omega, h'⟩
      refine ⟨Fin.last (N + 1), le_antisymm hRe₂.2 ?_⟩
      have := exp_succ_le_of_not_le hn'
      rwa [show ((e₂ - 1 : ℕ) : ℤ) + 1 = (e₂ : ℤ) by omega] at this
  have hLat := hA L (N + 2) P ((a.natAbs + l + e : ℕ) : ℤ) ρ e₂ hPdet' hbound hsharp
  rw [← hlat] at hLat
  have hlen : len (mat (m * u)) = a.natAbs + l + e + e₂ :=
    (hasLen_of_latLen (k := a.natAbs + l + e + e₂) (by convert hLat using 1; push_cast; ring)).len_eq
  rw [hlen]
  refine ⟨by omega, fun j => ?_⟩
  have hsm : Small ϖ (a.toNat + j / 2) (2 * a.toNat + j) C (C * V * mat g₀) u ↔
      e ≤ j / 2 ∧ Valued.v c' ≤ WithZero.exp ((2 * a.toNat + j : ℕ) : ℤ) := by
    unfold Small
    rw [← hc']
    simp only [pow_mul_mem_intL_iff hϖ]
    exact and_congr (hQmono (j / 2)) Iff.rfl
  rw [hsm]
  constructor
  · intro h
    have h1 := hRe₂.1
    refine ⟨by omega, ?_⟩
    refine ((hvl' _).1 hRe₂.2).trans (WithZero.exp_le_exp.2 ?_)
    push_cast; omega
  · rintro ⟨h1, h2⟩
    have hR : R (j - e) := ⟨by omega, (hvl' _).2 (h2.trans_eq (by congr 1; push_cast; omega))⟩
    have := Nat.find_min' hRex hR
    omega

example : AddVec → Dual → SpanEq → Heis → Pointwise := pointwise_of_steps

end GlobalTheory.InertZeta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallCornerOfHeisenbergDuality
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section Herm

variable {L : Type} [Field L] {N : ℕ}

def hermJ (σ : L →+* L) (x y : Fin N → L) : L := ∑ i, σ (x i) * y i.rev

theorem hermJ_add_left (σ : L →+* L) (x x' y : Fin N → L) :
    hermJ σ (x + x') y = hermJ σ x y + hermJ σ x' y := by
  simp only [hermJ, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hermJ_add_right (σ : L →+* L) (x y y' : Fin N → L) :
    hermJ σ x (y + y') = hermJ σ x y + hermJ σ x y' := by
  simp only [hermJ, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem map_hermJ {σ : L →+* L} (hσσ : ∀ x, σ (σ x) = x) (x y : Fin N → L) :
    σ (hermJ σ x y) = hermJ σ y x := by
  simp only [hermJ, map_sum, map_mul, hσσ]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun i => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, mul_comm]

theorem dotProduct_eq_neg_hermJ {σ : L →+* L} (r b w : Fin N → L) (h : ∀ j, r j = -σ (b j.rev)) :
    r ⬝ᵥ w = -hermJ σ b w := by
  rw [hermJ, ← Finset.sum_neg_distrib]
  refine Fintype.sum_equiv Fin.revPerm _ _ fun j => ?_
  simp only [Fin.revPerm_apply, Fin.rev_rev, h, neg_mul]

end Herm

section Unitary

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem hermJ_mulVec (g : GU σ N) (x y : Fin N → L) :
    hermJ σ (mat g *ᵥ x) (mat g *ᵥ y) = hermJ σ x y := by
  have hconj : ∀ i k : Fin N, σ (mat g i k) = mat g⁻¹ k.rev i.rev := fun i k => by
    rw [mat_inv_apply, Fin.rev_rev, Fin.rev_rev]
  have hinner : ∀ k l : Fin N, ∑ i : Fin N, mat g⁻¹ k.rev i.rev * mat g i.rev l = (1 : Matrix (Fin N) (Fin N) L) k.rev l := by
    intro k l
    rw [← mat_inv_mul g, Matrix.mul_apply]
    exact Fintype.sum_equiv Fin.revPerm _ _ fun i => rfl
  calc hermJ σ (mat g *ᵥ x) (mat g *ᵥ y)
      = ∑ k : Fin N, ∑ l : Fin N, σ (x k) * y l * ∑ i : Fin N, mat g⁻¹ k.rev i.rev * mat g i.rev l := by
        simp only [hermJ, Matrix.mulVec, dotProduct, map_sum, map_mul, hconj, Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        conv_rhs => rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = ∑ k : Fin N, σ (x k) * y k.rev := by
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [hinner, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
          if_true]

theorem sigma_mem_intL {x : L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (h : x ∈ intL L) : σ x ∈ intL L := by
  change Valued.v (σ x) ≤ 1
  rw [hσ]
  exact h

theorem hermJ_int {ϖ : L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (hϖ : σ ϖ = ϖ) (e : ℕ) (x : Fin N → L)
    (h : ∀ i, ϖ ^ e * x i ∈ intL L) : ϖ ^ (2 * e) * hermJ σ x x ∈ intL L := by
  have hsum : ϖ ^ (2 * e) * hermJ σ x x = ∑ i, σ (ϖ ^ e * x i) * (ϖ ^ e * x i.rev) := by
    simp only [hermJ, Finset.mul_sum, map_mul, map_pow, hϖ]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum]
  exact Subring.sum_mem _ fun i _ => Subring.mul_mem _ (sigma_mem_intL hσ (h i)) (h i.rev)

end Unitary

theorem smallCorner_of_heis_dual : Heis → Dual → SmallCorner := by
  intro hH hD
  unfold SmallCorner
  intro L _ _ ϖ σ q N hU g₀ U V C hF e f r hef hr
  have hU' := hU
  unfold IsUnramInv at hU'
  obtain ⟨hσσ, hσv, hϖσ, hϖv, -⟩ := hU'

  obtain ⟨b, hb⟩ : ∃ b : Fin N → L, b = fun i => -σ (r i.rev) := ⟨_, rfl⟩
  have hrb : ∀ j, r j = -σ (b j.rev) := fun j => by
    rw [hb]
    simp only [Fin.rev_rev, map_neg, hσσ, neg_neg]
  obtain ⟨b₁, hb₁⟩ : ∃ x : Fin N → L, x = (C * V * mat g₀) *ᵥ b := ⟨_, rfl⟩
  obtain ⟨b₂, hb₂⟩ : ∃ x : Fin N → L, x = (C * U) *ᵥ b := ⟨_, rfl⟩
  have hsplit : b₁ + b₂ = b := by
    have hCinv : C * (U + V * mat g₀) = 1 := mul_eq_one_comm.mp hF.2.2.2.2
    rw [hb₁, hb₂, ← Matrix.add_mulVec, add_comm, Matrix.mul_assoc, ← Matrix.mul_add, hCinv,
      Matrix.one_mulVec]
  obtain ⟨τ, hτint, hτ⟩ := exists_trace_one hU
  obtain ⟨s, hs⟩ : ∃ s : L, s = hermJ σ b₁ b₁ - hermJ σ b₂ b₂ := ⟨_, rfl⟩
  have hσs : σ s = s := by rw [hs, map_sub, map_hermJ hσσ, map_hermJ hσσ]
  have hrb₁ : r ⬝ᵥ b₁ = -hermJ σ b b₁ := dotProduct_eq_neg_hermJ r b b₁ hrb
  have hnorm : -∑ j, r j * σ (r j.rev) = -hermJ σ b b := by
    rw [← dotProduct_eq_neg_hermJ r b b hrb, hb]
    simp only [dotProduct, mul_neg, Finset.sum_neg_distrib]
  have hc : r ⬝ᵥ b₁ + τ * s + σ (r ⬝ᵥ b₁ + τ * s) = -∑ j, r j * σ (r j.rev) := by
    rw [hnorm, hrb₁, map_add, map_mul, map_neg, map_hermJ hσσ, hσs, ← hsplit]
    simp only [hermJ_add_left, hermJ_add_right]
    linear_combination s * hτ + hs
  obtain ⟨hHrad, -, hHex⟩ := hH L ϖ σ q N hU
  obtain ⟨u, hu, hur, huc⟩ := hHex r (r ⬝ᵥ b₁ + τ * s) hc
  have hcol : colOf u = b := by
    funext i
    have hi := (hHrad u hu).1 i.rev
    rw [hur, Fin.rev_rev] at hi
    rw [hb]
    simp only [hi, map_neg, hσσ, neg_neg]
  obtain ⟨h₁, h₂⟩ := (hD L ϖ σ q N hU g₀ U V C hF r b (ϖ ^ e) hrb).1 hr
  refine ⟨u, hu, hur, ?_, ?_⟩
  · rw [hur]
    exact hr
  · rw [hur, hcol, huc, ← hb₁, add_sub_cancel_left]
    have hϖint : ϖ ∈ intL L := by
      change Valued.v ϖ ≤ 1
      rw [hϖv]
      exact WithZero.coe_le_one.mpr (by decide)
    have i₁ : ϖ ^ (2 * e) * hermJ σ b₁ b₁ ∈ intL L :=
      hermJ_int hσv hϖσ e b₁ (by rw [hb₁]; exact h₁)
    have hg : mat g₀ *ᵥ b₂ = (mat g₀ * C * U) *ᵥ b := by
      rw [hb₂, Matrix.mulVec_mulVec, Matrix.mul_assoc]
    have i₂ : ϖ ^ (2 * e) * hermJ σ b₂ b₂ ∈ intL L := by
      rw [← hermJ_mulVec g₀ b₂ b₂, hg]
      exact hermJ_int hσv hϖσ e _ h₂
    have hf : ϖ ^ f = ϖ ^ (f - 2 * e) * ϖ ^ (2 * e) := by rw [← pow_add, Nat.sub_add_cancel hef]
    have hsplit' : ϖ ^ f * (τ * s) =
        τ * ϖ ^ (f - 2 * e) * (ϖ ^ (2 * e) * hermJ σ b₁ b₁ - ϖ ^ (2 * e) * hermJ σ b₂ b₂) := by
      rw [hf, hs]
      ring
    rw [hsplit']
    exact Subring.mul_mem _ (Subring.mul_mem _ hτint (Subring.pow_mem _ hϖint _)) (Subring.sub_mem _ i₁ i₂)

end GlobalTheory.InertZeta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SphericalInductionTransitivityOfLeviExists
section
noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem blk_mono {i j : Fin (N + 2)} (h : j ≤ i) : blk N j ≤ blk N i := by
  rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;> simp
  all_goals first
    | (rw [Fin.le_iff_val_le_val] at h; have := i'.2; simp at h; omega)
    | (rw [Fin.le_iff_val_le_val] at h; simp at h; done)
    | (rw [Fin.le_iff_val_le_val] at h; simp at h; omega)

theorem levi_ext {ϖ : L} {a : ℤ} {g₀ : GU σ N} {m m' : GU σ (N + 2)} (h : IsLeviElt ϖ a g₀ m)
    (h' : IsLeviElt ϖ a g₀ m') : m = m' := by
  apply mat_injective
  funext i j
  by_cases hij : blk N i = blk N j
  · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;>
      simp at hij
    · rw [h.2.1, h'.2.1]
    · rw [h.2.2.2 i' j', h'.2.2.2 i' j']
    · rw [h.2.2.1, h'.2.2.1]
  · rw [h.1 i j hij, h'.1 i j hij]

theorem levi_mul {ϖ : L} (hϖ : ϖ ≠ 0) {a a' : ℤ} {g g' : GU σ N} {m m' : GU σ (N + 2)} (h : IsLeviElt ϖ a g m)
    (h' : IsLeviElt ϖ a' g' m') : IsLeviElt ϖ (a + a') (g * g') (m * m') := by
  have e : ∀ i j, mat (m * m') i j = mat m i 0 * mat m' 0 j + ∑ l, mat m i (mid l) * mat m' (mid l) j +
      mat m i (Fin.last (N + 1)) * mat m' (Fin.last (N + 1)) j := fun i j => by
    rw [mat_mul, Matrix.mul_apply, sum_idx (fun l => mat m i l * mat m' l j)]
  have z : ∀ i j, blk N i ≠ blk N j → mat m i j = 0 := h.1
  have z' : ∀ i j, blk N i ≠ blk N j → mat m' i j = 0 := h'.1
  refine ⟨mul_mem h.1 h'.1, ?_, ?_, fun i j => ?_⟩
  · rw [e, h.2.1, h'.2.1, z 0 (Fin.last (N + 1)) (by simp), zero_mul, add_zero,
      Finset.sum_eq_zero (fun l _ => by rw [z 0 (mid l) (by simp), zero_mul]), add_zero, zpow_add₀ hϖ]
  · rw [e, h.2.2.1, h'.2.2.1, z (Fin.last (N + 1)) 0 (by simp), zero_mul, zero_add,
      Finset.sum_eq_zero (fun l _ => by rw [z (Fin.last (N + 1)) (mid l) (by simp), zero_mul]), zero_add,
      neg_add, zpow_add₀ hϖ]
  · rw [e, z (mid i) 0 (by simp), z (mid i) (Fin.last (N + 1)) (by simp), zero_mul, zero_mul, zero_add, add_zero,
      mat_mul, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [h.2.2.2, h'.2.2.2]

end

theorem sphTrans (hL : LeviExists) : SphTrans := by
  intro L _ _ ϖ σ q N r hU hr α φ φ₀ hα hsph h1 hsph₀ h10 a g₀ m hm u hu
  have hϖ : ϖ ≠ 0 := by
    intro h; have := hU.2.2.2.1; rw [h, Valuation.map_zero] at this; exact WithZero.zero_ne_coe this
  obtain ⟨b₀, k₀, hb₀, hk₀, rfl⟩ := P.fIwasawa_iwasawa σ hU.1 hU.2.1 g₀
  obtain ⟨mb, hmb⟩ := hL L ϖ σ q N hU a b₀
  obtain ⟨mk, hmk⟩ := hL L ϖ σ q N hU 0 k₀
  have hm' : m = mb * mk := by
    have := levi_mul hϖ hmb hmk
    rw [add_zero] at this
    exact levi_ext hm this
  subst hm'

  have hmkK : mk ∈ KU σ (N + 2) := by
    rw [mem_KU_iff hU.2.1]
    intro i j
    by_cases hij : blk N i = blk N j
    · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;>
        simp at hij
      · rw [hmk.2.1, zpow_zero]; exact one_mem _
      · rw [hmk.2.2.2 i' j']; exact P.fSatake_K_int hk₀ i' j'
      · rw [hmk.2.2.1, neg_zero, zpow_zero]; exact one_mem _
    · rw [hmk.1 i j hij]; exact zero_mem _
  set v := mk * u * mk⁻¹ with hv
  have hvR : v ∈ radQ σ N := (leviRad L σ (N + 2) (blk N) hU.2.1 mk hmk.1 u hu).1
  have hdiag : ∀ i j, blk N j ≤ blk N i → mat (mb * v) i j = mat mb i j :=
    fun i j h => levi_mul_rad_apply hmb.1 hvR h
  have hB : IsBorelU (mb * v) := by
    intro i j hji
    show mat (mb * v) i j = 0
    rw [hdiag i j (blk_mono hji.le)]
    by_cases hij : blk N i = blk N j
    · rcases idx_cases i with rfl | ⟨i', rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j', rfl⟩ | rfl <;>
        simp at hij
      · exact absurd hji (lt_irrefl _)
      · rw [hmb.2.2.2 i' j']
        exact hb₀ i' j' (by rw [Fin.lt_iff_val_lt_val] at hji ⊢; simpa using hji)
      · exact absurd hji (lt_irrefl _)
    · exact hmb.1 i j hij
  have e1 : mb * mk * u = (mb * v) * 1 * mk := by rw [hv]; group
  have hφ : φ (mb * mk * u) = chiDeltaU q α (mb * v) := by
    rw [e1, hsph _ _ _ hB hmkK, h1, mul_one]
  have hφ₀ : φ₀ (b₀ * k₀) = chiDeltaU q (Fin.tail α) b₀ := by
    have := hsph₀ b₀ 1 k₀ hb₀ hk₀
    rwa [mul_one, h10, mul_one] at this
  rw [hφ, hφ₀]
  unfold chiDeltaU
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [dif_pos (by simp)]
    have e0 : (⟨(0 : Fin (r + 1)).val, by simp⟩ : Fin (N + 2)) = 0 := rfl
    rw [e0]
    show α 0 ^ ordL (mat (mb * v) 0 0) * (q : ℂ) ^ (-ordL (mat (mb * v) 0 0) * (((N + 2 : ℕ) : ℤ) - 1 - 2 * ((0 : ℕ) : ℤ))) = _
    rw [hdiag 0 0 le_rfl, hmb.2.1, P.fSatake_ord_zpow hU.2.2.2.1]
    congr 2
    push_cast
    ring
  · refine Finset.prod_congr rfl fun i _ => ?_
    have hiN : i.val < N := by have := i.2; omega
    rw [dif_pos (by simp; omega), dif_pos hiN]
    have ei : (⟨(Fin.succ i).val, by simp; omega⟩ : Fin (N + 2)) = mid ⟨i.val, hiN⟩ := by
      ext; simp
    rw [ei]
    show α i.succ ^ ordL (mat (mb * v) (mid ⟨i.val, hiN⟩) (mid ⟨i.val, hiN⟩)) *
      (q : ℂ) ^ (-ordL (mat (mb * v) (mid ⟨i.val, hiN⟩) (mid ⟨i.val, hiN⟩)) *
        (((N + 2 : ℕ) : ℤ) - 1 - 2 * ((i.succ.val : ℕ) : ℤ))) = _
    rw [hdiag _ _ le_rfl, hmb.2.2.2]
    show _ = Fin.tail α i ^ ordL (mat b₀ ⟨i.val, hiN⟩ ⟨i.val, hiN⟩) *
      (q : ℂ) ^ (-ordL (mat b₀ ⟨i.val, hiN⟩ ⟨i.val, hiN⟩) * ((N : ℤ) - 1 - 2 * ((i.val : ℕ) : ℤ)))
    congr 2
    simp only [Fin.val_succ]
    push_cast
    ring

end GlobalTheory.InertZeta

end
end

