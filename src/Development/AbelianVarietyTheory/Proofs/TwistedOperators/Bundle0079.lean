import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasLenOfLatLen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0516

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmallRadicalCosetCountOfHeisenberg
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

section HeisCalc

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem rowOf_one : rowOf (1 : GU σ (N + 2)) = 0 := funext fun j =>
  Matrix.one_apply_ne (mid_ne_zero j).symm

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem colOf_one : colOf (1 : GU σ (N + 2)) = 0 := funext fun i =>
  Matrix.one_apply_ne (mid_ne_last i)

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem cornerOf_one : cornerOf (1 : GU σ (N + 2)) = 0 :=
  Matrix.one_apply_ne (last_ne_zero (N := N)).symm

variable
  (h1 : ∀ u ∈ radQ σ N, (∀ j, rowOf u j = -σ (colOf u j.rev)) ∧ cornerOf u + σ (cornerOf u) = rowOf u ⬝ᵥ colOf u ∧
      (u ∈ KU σ (N + 2) ↔ (∀ j, rowOf u j ∈ intL L) ∧ cornerOf u ∈ intL L))
  (h2 : ∀ u ∈ radQ σ N, ∀ u' ∈ radQ σ N, rowOf (u * u') = rowOf u + rowOf u' ∧ colOf (u * u') = colOf u + colOf u' ∧
      cornerOf (u * u') = cornerOf u + cornerOf u' + rowOf u ⬝ᵥ colOf u')
include h1

theorem colOf_eq_of_rowOf_eq {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N)
    (h : rowOf u = rowOf u') : colOf u = colOf u' := funext fun i => by
  have a := (h1 u hu).1 i.rev
  have b := (h1 u' hu').1 i.rev
  rw [Fin.rev_rev, h] at a
  rw [Fin.rev_rev] at b
  exact σ.injective (neg_injective (a.symm.trans b))

theorem colOf_eq_zero {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) (h : rowOf u = 0) : colOf u = 0 := by
  rw [colOf_eq_of_rowOf_eq h1 hu (one_mem _) (h.trans rowOf_one.symm), colOf_one]

include h2

theorem rowOf_inv {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) :
    rowOf u⁻¹ = -rowOf u ∧ cornerOf u⁻¹ = -cornerOf u + rowOf u ⬝ᵥ colOf u := by
  obtain ⟨r, -, c⟩ := h2 u⁻¹ (inv_mem hu) u hu
  rw [inv_mul_cancel, rowOf_one] at r
  rw [inv_mul_cancel, cornerOf_one] at c
  have r' : rowOf u⁻¹ = -rowOf u := eq_neg_of_add_eq_zero_left r.symm
  refine ⟨r', ?_⟩
  rw [r', neg_dotProduct] at c
  linear_combination -c

theorem inv_mul_of_rowOf_eq {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N)
    (h : rowOf u = rowOf u') : rowOf (u⁻¹ * u') = 0 ∧ cornerOf (u⁻¹ * u') = cornerOf u' - cornerOf u := by
  obtain ⟨ri, ci⟩ := rowOf_inv h1 h2 hu
  obtain ⟨r, -, c⟩ := h2 u⁻¹ (inv_mem hu) u' hu'
  have hc := colOf_eq_of_rowOf_eq h1 hu hu' h
  refine ⟨by rw [r, ri, h, neg_add_cancel], ?_⟩
  rw [c, ci, ri, ← hc, neg_dotProduct]
  ring

theorem rowOf_inv_mul {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N) :
    rowOf (u⁻¹ * u') = -rowOf u + rowOf u' := by
  rw [(h2 u⁻¹ (inv_mem hu) u' hu').1, (rowOf_inv h1 h2 hu).1]

theorem mul_of_rowOf_eq_zero {u z : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hz : z ∈ radQ σ N) (h : rowOf z = 0) :
    rowOf (u * z) = rowOf u ∧ colOf (u * z) = colOf u ∧ cornerOf (u * z) = cornerOf u + cornerOf z := by
  obtain ⟨r, b, c⟩ := h2 u hu z hz
  have hb := colOf_eq_zero h1 hz h
  refine ⟨by rw [r, h, add_zero], by rw [b, hb, add_zero], by rw [c, hb, dotProduct_zero, add_zero]⟩

end HeisCalc

end GlobalTheory.InertZeta

namespace GlobalTheory.InertZeta

theorem count_of_heis : Heis → LatIndex → TraceIndex → Count := by
  intro hH hL hT L _ _ ϖ σ q N hU C D l e f hC hdet hex hinv
  obtain ⟨h1, h2, h3⟩ := hH L ϖ σ q N hU
  have hσσ := hU.1
  have hσv := hU.2.1
  have hϖ : Valued.v ϖ = WithZero.exp (-1) := hU.2.2.2.1
  have hϖ1 : ϖ ∈ intL L := by show Valued.v ϖ ≤ 1; rw [hϖ]; exact oneLePart_eq_one.mp rfl
  have hσint : ∀ x ∈ intL L, σ x ∈ intL L := fun x hx => by
    show Valued.v (σ x) ≤ 1; rw [hσv]; exact hx

  set A : Matrix (Fin N) (Fin N) L := ϖ ^ e • C with hA
  have hAint : IsInt A := fun i j => by
    rw [hA, Matrix.smul_apply, smul_eq_mul]; exact mul_mem (pow_mem hϖ1 _) (hC i j)
  have hAdet : Valued.v A.det = WithZero.exp (-((l + N * e : ℕ) : ℤ)) := by
    rw [hA, Matrix.det_smul, map_mul, map_pow, map_pow, hϖ, hdet, Fintype.card_fin, ← WithZero.exp_nsmul,
      ← WithZero.exp_nsmul, ← WithZero.exp_add]
    congr 1; push_cast; ring
  have iL := hL L ϖ σ q N hU A (l + N * e) hAint hAdet
  have iT := hT L ϖ σ q f hU
  set Λ := preLat A
  set I := intV L N
  set T := traceZero σ (ϖ ^ f)
  set T₀ := traceZero σ 1
  have memΛ : ∀ r : Fin N → L, r ∈ Λ ↔ ∀ j, ϖ ^ e * (r ᵥ* C) j ∈ intL L := fun r => by
    rw [mem_preLat, hA, Matrix.vecMul_smul]; rfl
  rw [pow_add, ← iL, ← iT]

  have ex0 : ∀ r : Λ, ∃ u : radQ σ N, rowOf (u : GU σ (N + 2)) = r ∧ Small ϖ e f C D (u : GU σ (N + 2)) := fun r => by
    obtain ⟨u, hu, h, hs⟩ := hex r ((memΛ r).1 r.2)
    exact ⟨⟨u, hu⟩, h, hs⟩
  choose u₀ hu₀r hu₀s using ex0
  have exz : ∀ t : T, ∃ z : radQ σ N, rowOf (z : GU σ (N + 2)) = 0 ∧ cornerOf (z : GU σ (N + 2)) = t := fun t => by
    have ht := (mem_traceZero.1 t.2).2
    obtain ⟨z, hz, h, hc⟩ := h3 0 t (by
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, neg_zero]; linear_combination ht)
    exact ⟨⟨z, hz⟩, h, hc⟩
  choose z hzr hzc using exz
  have smallOut : ∀ w : radQ σ N, Small ϖ e f C D (w : GU σ (N + 2)) →
      Small ϖ e f C D (((QuotientGroup.mk w : RadQuot σ N).out : radQ σ N) : GU σ (N + 2)) := fun w hw => by
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul ((KU σ (N + 2)).subgroupOf (radQ σ N)) w
    rw [hk]
    exact hinv w.1 w.2 k.1.1 k.1.2 (Subgroup.mem_subgroupOf.1 k.2) hw
  have smallW : ∀ (r : Λ) (t : T), Small ϖ e f C D ((u₀ r * z t : radQ σ N) : GU σ (N + 2)) := fun r t => by
    obtain ⟨hr, hb, hc⟩ := mul_of_rowOf_eq_zero h1 h2 (u₀ r).2 (z t).2 (hzr t)
    have hs := hu₀s r
    show Small ϖ e f C D ((u₀ r : GU σ (N + 2)) * (z t : GU σ (N + 2)))
    refine ⟨fun j => ?_, ?_⟩
    · rw [hr]; exact hs.1 j
    · rw [hr, hb, hc, hzc]
      convert add_mem hs.2 (mem_traceZero.1 t.2).1 using 1
      ring
  have rowW : ∀ (r : Λ) (t : T), rowOf ((u₀ r * z t : radQ σ N) : GU σ (N + 2)) = r := fun r t =>
    ((mul_of_rowOf_eq_zero h1 h2 (u₀ r).2 (z t).2 (hzr t)).1).trans (hu₀r r)
  have cornerW : ∀ (r : Λ) (t : T), cornerOf ((u₀ r * z t : radQ σ N) : GU σ (N + 2)) =
      cornerOf (u₀ r : GU σ (N + 2)) + t := fun r t => by
    rw [← hzc t]; exact (mul_of_rowOf_eq_zero h1 h2 (u₀ r).2 (z t).2 (hzr t)).2.2
  let Φ : (Λ ⧸ I.addSubgroupOf Λ) × (T ⧸ T₀.addSubgroupOf T) →
      {x : RadQuot σ N // Small ϖ e f C D (x.out : radQ σ N).1} := fun p =>
    ⟨QuotientGroup.mk (u₀ p.1.out * z p.2.out), smallOut _ (smallW _ _)⟩
  have hΦ : Function.Bijective Φ := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ h
      have hk := QuotientGroup.eq.1 (congrArg Subtype.val h)
      rw [Subgroup.mem_subgroupOf] at hk
      have hK := (h1 _ ((u₀ a.out * z b.out)⁻¹ * (u₀ a'.out * z b'.out)).2).2.2.1 hk
      have ha : a = a' := by
        rw [← QuotientAddGroup.out_eq' a, ← QuotientAddGroup.out_eq' a', QuotientAddGroup.eq,
          AddSubgroup.mem_addSubgroupOf, mem_intV]
        intro j
        have := hK.1 j
        rwa [Subgroup.coe_mul, Subgroup.coe_inv, rowOf_inv_mul h1 h2 (u₀ a.out * z b.out).2 (u₀ a'.out * z b'.out).2,
          rowW, rowW] at this
      subst ha
      have hb : b = b' := by
        rw [← QuotientAddGroup.out_eq' b, ← QuotientAddGroup.out_eq' b', QuotientAddGroup.eq,
          AddSubgroup.mem_addSubgroupOf, mem_traceZero]
        have hd := inv_mul_of_rowOf_eq h1 h2 (u₀ a.out * z b.out).2 (u₀ a.out * z b'.out).2
          ((rowW _ _).trans (rowW _ _).symm)
        have hc := hK.2
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hd.2, cornerW, cornerW] at hc
        have t1 := (mem_traceZero.1 b.out.2).2
        have t2 := (mem_traceZero.1 b'.out.2).2
        refine ⟨?_, ?_⟩
        · convert hc using 1; push_cast; ring
        · push_cast; rw [map_add, map_neg]; linear_combination t2 - t1
      rw [hb]
    · rintro ⟨x, hx⟩

      have hrΛ : rowOf ((x.out : radQ σ N) : GU σ (N + 2)) ∈ Λ := (memΛ _).2 hx.1
      have hρ : (-(⟨_, hrΛ⟩ : Λ) + (QuotientAddGroup.mk (⟨_, hrΛ⟩ : Λ) : Λ ⧸ I.addSubgroupOf Λ).out) ∈
          I.addSubgroupOf Λ := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _).symm
      rw [AddSubgroup.mem_addSubgroupOf, mem_intV] at hρ
      set a : Λ ⧸ I.addSubgroupOf Λ := QuotientAddGroup.mk (⟨_, hrΛ⟩ : Λ) with ha
      set u : radQ σ N := x.out with hu
      set ρ : Fin N → L := -rowOf (u : GU σ (N + 2)) + (a.out : Fin N → L) with hρdef
      have hρ' : ∀ i, ρ i ∈ intL L := hρ
      obtain ⟨τ, hτ, hτ1⟩ := exists_trace_one hU
      set s : L := -∑ j, ρ j * σ (ρ j.rev) with hsdef
      have hs : σ s = s := by
        simp only [hsdef, map_neg, map_sum, map_mul, hσσ]
        congr 1
        exact Fintype.sum_equiv Fin.revPerm _ _ (fun j => by simp [mul_comm])
      have hsint : s ∈ intL L := neg_mem (Subring.sum_mem _ fun j _ => mul_mem (hρ' j) (hσint _ (hρ' _)))
      obtain ⟨k, hk, hkr, hkc⟩ := h3 ρ (τ * s) (by rw [map_mul, hs]; linear_combination s * hτ1)
      have hkK : k ∈ KU σ (N + 2) := (h1 k hk).2.2.2 ⟨fun j => hkr ▸ hρ' j, hkc ▸ mul_mem hτ hsint⟩
      set uk : radQ σ N := u * ⟨k, hk⟩ with hukdef
      have hukS : Small ϖ e f C D (uk : GU σ (N + 2)) := hinv u.1 u.2 k hk hkK hx
      have hukr : rowOf (uk : GU σ (N + 2)) = a.out := by
        rw [hukdef, Subgroup.coe_mul, (h2 _ u.2 _ hk).1, hkr, hρdef, add_neg_cancel_left]
      have hv := inv_mul_of_rowOf_eq h1 h2 (u₀ a.out).2 uk.2 ((hu₀r _).trans hukr.symm)
      set v : radQ σ N := (u₀ a.out)⁻¹ * uk with hvdef
      have hvr : rowOf (v : GU σ (N + 2)) = 0 := hv.1
      have hvc : cornerOf (v : GU σ (N + 2)) = cornerOf (uk : GU σ (N + 2)) - cornerOf (u₀ a.out : GU σ (N + 2)) := hv.2
      have htT : cornerOf (v : GU σ (N + 2)) ∈ T := by
        rw [mem_traceZero]
        refine ⟨?_, ?_⟩
        · have hcol := colOf_eq_of_rowOf_eq h1 (u₀ a.out).2 uk.2 ((hu₀r _).trans hukr.symm)
          have := sub_mem hukS.2 (hu₀s a.out).2
          rw [hukr, ← hcol, hu₀r] at this
          rw [hvc]
          convert this using 1
          ring
        · have := (h1 _ v.2).2.1
          rw [hvr, zero_dotProduct] at this
          linear_combination this
      set bq : T ⧸ T₀.addSubgroupOf T := QuotientAddGroup.mk (⟨_, htT⟩ : T) with hbq
      have hδ : (-(⟨_, htT⟩ : T) + bq.out) ∈ T₀.addSubgroupOf T := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' _).symm
      rw [AddSubgroup.mem_addSubgroupOf, mem_traceZero] at hδ
      refine ⟨(a, bq), Subtype.ext ?_⟩
      show (QuotientGroup.mk (u₀ a.out * z bq.out) : RadQuot σ N) = x
      have e1 : (QuotientGroup.mk u : RadQuot σ N) = QuotientGroup.mk uk :=
        QuotientGroup.eq.2 (by rw [hukdef, inv_mul_cancel_left]; exact Subgroup.mem_subgroupOf.2 hkK)
      rw [← QuotientGroup.out_eq' x, ← hu, e1, QuotientGroup.eq,
        show (u₀ a.out * z bq.out)⁻¹ * uk = (z bq.out)⁻¹ * v by rw [hvdef, _root_.mul_inv_rev, mul_assoc],
        Subgroup.mem_subgroupOf]
      have hzv := inv_mul_of_rowOf_eq h1 h2 (z bq.out).2 v.2 ((hzr _).trans hvr.symm)
      refine (h1 _ ((z bq.out)⁻¹ * v).2).2.2.2 ⟨fun j => ?_, ?_⟩
      · rw [Subgroup.coe_mul, Subgroup.coe_inv, hzv.1]; exact zero_mem _
      · rw [Subgroup.coe_mul, Subgroup.coe_inv, hzv.2, hzc]
        have := neg_mem hδ.1
        convert this using 1
        push_cast
        ring
  rw [show I.relIndex Λ * T₀.relIndex T = Nat.card ((Λ ⧸ I.addSubgroupOf Λ) × (T ⧸ T₀.addSubgroupOf T)) from
    (Nat.card_prod _ _).symm]
  exact (Nat.card_eq_of_bijective Φ hΦ).symm

end GlobalTheory.InertZeta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TraceZeroIntegersIndexInUniformizerMultiples
section
noncomputable section

open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta

theorem traceIndex : TraceIndex := by
  intro L _ _ ϖ σ q f hU
  have hq := traceZeroIndex_of_intIndex intIndex L ϖ σ q hU
  obtain ⟨-, -, hϖ, h4, -, -, -⟩ := hU
  have h0 : ϖ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h4
    exact WithZero.zero_ne_coe h4
  have hϖO : ϖ ∈ intL L := by
    show Valued.v ϖ ≤ 1
    rw [h4, ← WithZero.coe_one, WithZero.coe_le_coe]
    show (-1 : ℤ) ≤ 0
    omega
  set T := (intL L).toAddSubgroup ⊓ (σ.toAddMonoidHom + AddMonoidHom.id L).ker with hT
  have memT : ∀ y, y ∈ T ↔ y ∈ intL L ∧ σ y + y = 0 := fun y => Iff.rfl
  have hinj : ∀ e : ℕ, Function.Injective (AddMonoidHom.mulLeft (ϖ ^ e)) := fun e =>
    mul_right_injective₀ (pow_ne_zero e h0)
  have hmap : ∀ e : ℕ, (traceZero σ (ϖ ^ e)).map (AddMonoidHom.mulLeft (ϖ ^ e)) = T := fun e => by
    ext x
    rw [AddSubgroup.mem_map, memT]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_traceZero] at hy
      refine ⟨hy.1, ?_⟩
      rw [AddMonoidHom.coe_mulLeft, map_mul, map_pow, hϖ]
      linear_combination ϖ ^ e * hy.2
    · rintro ⟨hx, hx0⟩
      refine ⟨(ϖ ^ e)⁻¹ * x, ?_, ?_⟩
      · rw [mem_traceZero, mul_inv_cancel_left₀ (pow_ne_zero e h0)]
        refine ⟨hx, ?_⟩
        rw [map_mul, map_inv₀, map_pow, hϖ]
        linear_combination (ϖ ^ e)⁻¹ * hx0
      · rw [AddMonoidHom.coe_mulLeft, mul_inv_cancel_left₀ (pow_ne_zero e h0)]
  have h1 : traceZero σ 1 = T := by
    ext x
    rw [mem_traceZero, memT, one_mul]
  have hmulle : ∀ e : ℕ, T.map (AddMonoidHom.mulLeft (ϖ ^ e)) ≤ T := by
    rintro e _ ⟨y, hy, rfl⟩
    have hy : y ∈ T := hy
    rw [memT] at hy ⊢
    refine ⟨(intL L).mul_mem (pow_mem hϖO e) hy.1, ?_⟩
    rw [AddMonoidHom.coe_mulLeft, map_mul, map_pow, hϖ]
    linear_combination ϖ ^ e * hy.2
  rw [← AddSubgroup.relIndex_map_map_of_injective (traceZero σ 1) (traceZero σ (ϖ ^ f)) (hinj f), hmap f, h1]
  induction f with
  | zero =>
    have : T.map (AddMonoidHom.mulLeft (ϖ ^ 0)) = T := by
      ext x
      simp [AddSubgroup.mem_map]
    rw [this]
    simp
  | succ e ih =>
    have hcomp : T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) =
        (T.map (AddMonoidHom.mulLeft ϖ)).map (AddMonoidHom.mulLeft (ϖ ^ e)) := by
      ext x
      simp only [AddSubgroup.mem_map, AddMonoidHom.coe_mulLeft]
      constructor
      · rintro ⟨o, ho, rfl⟩
        exact ⟨ϖ * o, ⟨o, ho, rfl⟩, by rw [pow_succ, mul_assoc]⟩
      · rintro ⟨_, ⟨o, ho, rfl⟩, rfl⟩
        exact ⟨o, ho, by rw [pow_succ, mul_assoc]⟩
    have hstep : (T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1)))).relIndex
        (T.map (AddMonoidHom.mulLeft (ϖ ^ e))) = q := by
      rw [hcomp, AddSubgroup.relIndex_map_map_of_injective _ _ (hinj e)]
      exact hq
    have hle1 : T.map (AddMonoidHom.mulLeft (ϖ ^ (e + 1))) ≤ T.map (AddMonoidHom.mulLeft (ϖ ^ e)) := by
      rw [hcomp]
      exact AddSubgroup.map_mono (by simpa using hmulle 1)
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hle1 (hmulle e), hstep, ih]
    exact (pow_succ' _ _).symm

end GlobalTheory.InertZeta

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryHeisenbergRadicalCoordinates
section
noncomputable section

open Formalism.UG Matrix GlobalTheory.SatakeWeyl

namespace GlobalTheory.InertZeta.HeisCoord

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

def Shape (M : Matrix (Fin (N + 2)) (Fin (N + 2)) L) (r b : Fin N → L) (c : L) : Prop :=
  M 0 0 = 1 ∧ (∀ j, M 0 (mid j) = r j) ∧ M 0 (Fin.last (N + 1)) = c ∧ (∀ i, M (mid i) 0 = 0) ∧
  (∀ i j, M (mid i) (mid j) = if i = j then 1 else 0) ∧ (∀ i, M (mid i) (Fin.last (N + 1)) = b i) ∧
  M (Fin.last (N + 1)) 0 = 0 ∧ (∀ j, M (Fin.last (N + 1)) (mid j) = 0) ∧
  M (Fin.last (N + 1)) (Fin.last (N + 1)) = 1

theorem form_apply {n : ℕ} (M : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (cT σ M * antiJ L n * M) i j = ∑ l, σ (M l.rev i) * M l j := by
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun l _ => by rw [P.fSatake_cTJ]

omit [Valued L (WithZero (Multiplicative ℤ))] in
theorem antiJ_eq {n : ℕ} (a b : Fin n) : antiJ L n a b = if a = b.rev then 1 else 0 := by
  simp only [antiJ, P.fSatake_rev_iff]

theorem shape_of_mem {u : GU σ (N + 2)} (hu : u ∈ radQ σ N) : Shape (mat u) (rowOf u) (colOf u) (cornerOf u) := by
  have h : ∀ i j, blk N j ≤ blk N i → mat u i j = (1 : Matrix (Fin (N + 2)) (Fin (N + 2)) L) i j := hu
  refine ⟨?_, fun j => rfl, rfl, fun i => ?_, fun i j => ?_, fun i => rfl, ?_, fun j => ?_, ?_⟩
  · rw [h 0 0 le_rfl, Matrix.one_apply_eq]
  · rw [h _ _ (by simp), Matrix.one_apply_ne (mid_ne_zero i)]
  · rw [h _ _ (by simp)]; simp [Matrix.one_apply, mid_injective.eq_iff]
  · rw [h _ _ (by simp), Matrix.one_apply_ne last_ne_zero]
  · rw [h _ _ (by simp), Matrix.one_apply_ne (mid_ne_last j).symm]
  · rw [h _ _ le_rfl, Matrix.one_apply_eq]

theorem sum_rev_ite {M : Type} [AddCommMonoid M] (f : Fin N → M) (j : Fin N) :
    (∑ x, if x.rev = j then f x else 0) = f j.rev := by
  rw [Finset.sum_eq_single j.rev]
  · simp
  · intro x _ hx
    rw [if_neg fun e => hx (by rw [← e, Fin.rev_rev])]
  · simp

theorem form_mid_last {M : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {r b : Fin N → L} {c : L} (h : Shape M r b c)
    (j : Fin N) : (cT σ M * antiJ L (N + 2) * M) (mid j) (Fin.last (N + 1)) = b j.rev + σ (r j) := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := h
  rw [form_apply, sum_idx]
  simp [Fin.rev_zero, Fin.rev_last, ← mid_rev, h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll, sum_rev_ite]

theorem form_last_last {M : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {r b : Fin N → L} {c : L} (h : Shape M r b c) :
    (cT σ M * antiJ L (N + 2) * M) (Fin.last (N + 1)) (Fin.last (N + 1)) = c + ∑ k, σ (b k.rev) * b k + σ c := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := h
  rw [form_apply, sum_idx]
  simp [Fin.rev_zero, Fin.rev_last, ← mid_rev, h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll, sum_rev_ite]

theorem zero_ne_mid (i : Fin N) : (0 : Fin (N + 2)) ≠ mid i := (mid_ne_zero i).symm
theorem last_ne_mid (i : Fin N) : Fin.last (N + 1) ≠ mid i := (mid_ne_last i).symm

theorem form_eq_of (hσσ : ∀ x, σ (σ x) = x) {M : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {r b : Fin N → L} {c : L}
    (h : Shape M r b c) (h1 : ∀ j, b j.rev + σ (r j) = 0) (h2 : c + ∑ k, σ (b k.rev) * b k + σ c = 0) :
    cT σ M * antiJ L (N + 2) * M = antiJ L (N + 2) := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := h
  ext i j
  rw [form_apply, sum_idx, antiJ_eq]
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [Fin.rev_zero, Fin.rev_last, ← mid_rev, h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll, sum_rev_ite,
      mid_ne_zero, mid_ne_last, zero_ne_mid, last_ne_mid, mid_injective.eq_iff]
  · by_cases e : i = j.rev
    · subst e; simp
    · rw [if_neg e, if_neg fun e' => e e'.symm]
  · exact h1 i
  · have := congrArg σ (h1 j)
    simp only [map_add, hσσ, map_zero] at this
    linear_combination this
  · exact h2

def heisMat (r b : Fin N → L) (c : L) : Matrix (Fin (N + 2)) (Fin (N + 2)) L := fun i j =>
  if i = j then 1
  else if i = 0 ∧ j = Fin.last (N + 1) then c
  else if h : i = 0 ∧ 0 < j.val ∧ j.val < N + 1 then r ⟨j.val - 1, by omega⟩
  else if h : j = Fin.last (N + 1) ∧ 0 < i.val ∧ i.val < N + 1 then b ⟨i.val - 1, by omega⟩
  else 0

theorem shape_heisMat (r b : Fin N → L) (c : L) : Shape (heisMat r b c) r b c := by
  refine ⟨by simp [heisMat], fun j => ?_, by simp [heisMat, last_ne_zero.symm], fun i => ?_, fun i j => ?_,
    fun i => ?_, by simp [heisMat, last_ne_zero], fun j => ?_, by simp [heisMat]⟩
  · have := j.2
    simp [heisMat, zero_ne_mid, mid_ne_last]
  · simp [heisMat, mid_ne_zero, last_ne_zero.symm]
  · simp [heisMat, mid_injective.eq_iff, mid_ne_zero, mid_ne_last]
  · have := i.2
    simp [heisMat, mid_ne_zero, mid_ne_last]
  · simp [heisMat, last_ne_mid, last_ne_zero]

theorem mem_radQ_of_shape {u : GU σ (N + 2)} {r b : Fin N → L} {c : L} (h : Shape (mat u) r b c) :
    u ∈ radQ σ N := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := h
  intro i j hij
  rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
    simp [Matrix.one_apply, h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll, mid_ne_zero, mid_ne_last, zero_ne_mid,
      last_ne_mid, mid_injective.eq_iff] at hij ⊢

theorem mul_coords {u u' : GU σ (N + 2)} (hu : u ∈ radQ σ N) (hu' : u' ∈ radQ σ N) :
    rowOf (u * u') = rowOf u + rowOf u' ∧ colOf (u * u') = colOf u + colOf u' ∧
      cornerOf (u * u') = cornerOf u + cornerOf u' + rowOf u ⬝ᵥ colOf u' := by
  obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := shape_of_mem hu
  obtain ⟨h00', h0m', h0l', hm0', hmm', hml', hl0', hlm', hll'⟩ := shape_of_mem hu'
  refine ⟨funext fun j => ?_, funext fun i => ?_, ?_⟩
  · simp only [rowOf, mat_mul, Matrix.mul_apply, sum_idx, Pi.add_apply]
    simp [h00, h0m, h0l, hmm', hl0', hlm', h0m']
    ring
  · simp only [colOf, mat_mul, Matrix.mul_apply, sum_idx, Pi.add_apply]
    simp [hm0, hmm, hml, hml', hll', h0l']
    ring
  · simp only [cornerOf, mat_mul, Matrix.mul_apply, sum_idx, dotProduct]
    simp [h00, h0m, h0l, hml', hll', h0l']
    ring

theorem Heisenberg₂ : Heis := by
  intro L _ _ ϖ σ q N hU
  obtain ⟨hσσ, hv, -⟩ := hU
  have hσint : ∀ x, x ∈ intL L → σ x ∈ intL L := fun x hx => by
    show Valued.v (σ x) ≤ 1
    rw [hv]; exact hx
  refine ⟨fun u hu => ?_, fun u hu u' hu' => mul_coords hu hu', fun r c hc => ?_⟩
  · have hs := shape_of_mem hu
    have hf : cT σ (mat u) * antiJ L (N + 2) * mat u = antiJ L (N + 2) := u.2
    have h1 : ∀ j, colOf u j.rev + σ (rowOf u j) = 0 := fun j => by
      have := congrFun (congrFun hf (mid j)) (Fin.last (N + 1))
      rwa [form_mid_last hs, antiJ_eq, if_neg (by rw [Fin.rev_last]; exact mid_ne_zero j)] at this
    have h2 : cornerOf u + ∑ k, σ (colOf u k.rev) * colOf u k + σ (cornerOf u) = 0 := by
      have := congrFun (congrFun hf (Fin.last (N + 1))) (Fin.last (N + 1))
      rwa [form_last_last hs, antiJ_eq, if_neg (by rw [Fin.rev_last]; exact last_ne_zero)] at this
    have hr : ∀ j, rowOf u j = -σ (colOf u j.rev) := fun j => by
      have := congrArg σ (h1 j)
      simp only [map_add, hσσ, map_zero] at this
      linear_combination this
    refine ⟨hr, ?_, ?_⟩
    · simp only [dotProduct, hr, neg_mul, Finset.sum_neg_distrib]
      linear_combination h2
    · rw [mem_KU_iff hv]
      constructor
      · intro h
        exact ⟨fun j => h _ _, h _ _⟩
      · rintro ⟨hr', hc'⟩ i j
        obtain ⟨h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll⟩ := hs
        have hb : ∀ i, colOf u i ∈ intL L := fun i => by
          have e := hr i.rev
          rw [Fin.rev_rev] at e
          have h' : colOf u i = -σ (rowOf u i.rev) := by rw [e, map_neg, hσσ, neg_neg]
          rw [h']
          exact neg_mem (hσint _ (hr' _))
        rcases idx_cases i with rfl | ⟨i, rfl⟩ | rfl <;> rcases idx_cases j with rfl | ⟨j, rfl⟩ | rfl <;>
          simp only [h00, h0m, h0l, hm0, hmm, hml, hl0, hlm, hll] <;>
          first | exact one_mem _ | exact zero_mem _ | exact hr' _ | exact hc' | exact hb _ |
            (split_ifs <;> first | exact one_mem _ | exact zero_mem _)
  · let b : Fin N → L := fun i => -σ (r i.rev)
    have h1 : ∀ j, b j.rev + σ (r j) = 0 := fun j => by simp [b]
    have h2 : c + ∑ k, σ (b k.rev) * b k + σ c = 0 := by
      simp only [b, Fin.rev_rev, map_neg, hσσ, neg_mul_neg]
      linear_combination hc
    obtain ⟨g, hg⟩ := exists_mat (σ := σ) (heisMat r b c) (form_eq_of hσσ (shape_heisMat r b c) h1 h2)
    have hs : Shape (mat g) r b c := hg ▸ shape_heisMat r b c
    exact ⟨g, mem_radQ_of_shape hs, funext hs.2.1, hs.2.2.1⟩

end GlobalTheory.InertZeta.HeisCoord
end
end

