import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.FramesTor
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0097
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0096
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0105
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0144

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUniqueShuffle
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm Formalism.L2.DIV GlobalTheory.FinGL.Bruhat
open scoped Classical

namespace GlobalTheory.GLm.Shuffle

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

theorem pm_eq_mono (σ : Equiv.Perm (Fin n)) : (pm g σ : Mt g n) = mono (σ, fun _ => 1) := by
  have hm : (fun r j : Fin n => if r = σ j then (1 : ZMod g) else 0) = mono (σ, fun _ => (1 : (ZMod g)ˣ)) := by
    ext r j; simp [mono]
  have hu : IsUnit (mono (F := ZMod g) (σ, fun _ => (1 : (ZMod g)ˣ))) := by
    refine IsUnit.of_mul_eq_one (mono (σ.symm, fun _ => (1 : (ZMod g)ˣ))) ?_
    ext r j
    rw [mul_mono]
    simp [mono, Matrix.one_apply]
  unfold pm toG
  rw [hm, dif_pos hu]
  rfl

theorem isUniUp_iff (u : Gn g n) : IsUniUp (u : Mt g n) ↔ u ∈ unip (ZMod g) n :=
  ⟨fun h => ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2 rfl⟩,
    fun h a b => ⟨fun hab => unip_lower h hab, fun e => e ▸ unip_diag h a⟩⟩

theorem inPar_iff (a : ℕ) (p : Gn g n) :
    InPar a (p : Mt g n) ↔ p ∈ blockTri (κ := ZMod g) (fun i : Fin n => if (i : ℕ) < a then 0 else 1 : Fin n → ℕ) := by
  rw [mem_blockTri]
  constructor
  · intro h i j hij
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj] at hij
    exact h i j hj (not_lt.1 hi)
  · intro h i j hj hi
    exact h i j (by simp [hj, not_lt.2 hi])

theorem block_of_eq {a : ℕ} {σ σ' : Equiv.Perm (Fin n)} {u u' p p' : Gn g n} (hu : IsUniUp (u : Mt g n))
    (hu' : IsUniUp (u' : Mt g n)) (hp : InPar a (p : Mt g n)) (hp' : InPar a (p' : Mt g n))
    (h : u * pm g σ * p = u' * pm g σ' * p') (r : Fin n) (hr : (σ.symm r : ℕ) < a) : (σ'.symm r : ℕ) < a := by
  have hv : u'⁻¹ * u ∈ unip (ZMod g) n :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ ((isUniUp_iff _).1 hu')) ((isUniUp_iff _).1 hu)
  have hq : InPar a ((p' * p⁻¹ : Gn g n) : Mt g n) :=
    (inPar_iff _ _).2 (Subgroup.mul_mem _ ((inPar_iff _ _).1 hp') (Subgroup.inv_mem _ ((inPar_iff _ _).1 hp)))
  have h1 : (u'⁻¹ * u) * pm g σ = pm g σ' * (p' * p⁻¹) := by
    calc (u'⁻¹ * u) * pm g σ = u'⁻¹ * (u * pm g σ * p) * p⁻¹ := by group
      _ = _ := by rw [h]; group
  have h2 := congrFun (congrFun (congrArg (fun z : Gn g n => (z : Mt g n)) h1) r) (σ.symm r)
  rw [Units.val_mul _ (pm g σ), Units.val_mul (pm g σ'), pm_eq_mono, pm_eq_mono, mul_mono, mono_mul] at h2
  simp only [Equiv.apply_symm_apply, Units.val_one, mul_one, one_mul] at h2
  rw [unip_diag hv] at h2
  by_contra hc
  rw [hq _ _ hr (not_lt.1 hc)] at h2
  exact one_ne_zero h2

noncomputable def key (S : Fin n → Prop) (r : Fin n) : ℕ := if S r then (r : ℕ) else n + r

theorem key_injective (S : Fin n → Prop) : Function.Injective (key S) := by
  intro r s h
  have := r.2; have := s.2
  unfold key at h
  apply Fin.ext
  split_ifs at h <;> omega

theorem key_mono {a : ℕ} {σ : Equiv.Perm (Fin n)} {S : Fin n → Prop} (hS : ∀ r, S r ↔ (σ.symm r : ℕ) < a)
    (hσ : ∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) : Monotone (key S ∘ σ) := by
  refine StrictMono.monotone fun i j hij => ?_
  have h1 := hσ i j hij
  have h2 : (i : ℕ) < j := hij
  have := (σ i).2
  simp only [Function.comp, key, hS, Equiv.symm_apply_apply, Fin.lt_def] at h1 ⊢
  split_ifs <;> omega

theorem exists_shuffle {a : ℕ} (ha : a ≤ n) (s : Equiv.Perm (Fin n)) : ∃ σ : Equiv.Perm (Fin n),
    (∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) ∧
      ∀ j : Fin n, (s.symm (σ j) : ℕ) < a ↔ (j : ℕ) < a := by
  set S : Fin n → Prop := fun r => (s.symm r : ℕ) < a with hS
  set σ := Tuple.sort (key S) with hσ
  have hm : Monotone (key S ∘ σ) := Tuple.monotone_sort _
  have hlt : ∀ r, key S r < n ↔ S r := by
    intro r
    have := r.2
    unfold key
    split_ifs with h <;> simp [h]
  have hcard : (Finset.univ.filter fun i => (key S ∘ σ) i < n).card = a := by
    have : (Finset.univ.filter fun i : Fin n => (i : ℕ) < a).card = a := by
      rw [Fin.card_filter_val_lt]; omega
    rw [← this]
    refine Finset.card_equiv (σ.trans s.symm) fun i => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
    exact hlt _
  have hiff : ∀ j : Fin n, S (σ j) ↔ (j : ℕ) < a := by
    intro j
    rw [← hlt, ← hcard]
    exact (Tuple.lt_card_lt_iff_apply_lt_of_monotone hm).symm
  refine ⟨σ, fun i j hij hb => ?_, hiff⟩
  have h1 : (key S ∘ σ) i < (key S ∘ σ) j :=
    (hm.strictMono_of_injective ((key_injective S).comp σ.injective)) hij
  have h2 : (i : ℕ) < j := hij
  simp only [Function.comp, key, hiff] at h1
  rw [Fin.lt_def]
  split_ifs at h1 <;> omega

theorem existsUnique_shuffle : ∀ (g : ℕ) [Fact g.Prime] (a n : ℕ), a ≤ n → ∀ x : Gn g n, ∃! σ : Equiv.Perm (Fin n), (∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) ∧ ∃ u p : Gn g n, IsUniUp (u : Mt g n) ∧ InPar a (p : Mt g n) ∧ x = u * pm g σ * p := by
  intro g _ a n ha x
  obtain ⟨m, u, hu, u', hu', hx⟩ := exists_decomp x
  obtain ⟨σ, hσ, hb⟩ := exists_shuffle ha m.1
  have hp : InPar a (((pm g σ)⁻¹ * u⁻¹ * x : Gn g n) : Mt g n) := by
    intro i j hj hi
    have h1 : (pm g σ : Mt g n) * (((pm g σ)⁻¹ * u⁻¹ * x : Gn g n) : Mt g n) = mono m * (u' : Mt g n) := by
      rw [← Units.val_mul, ← mul_assoc, mul_inv_cancel_left, Units.val_mul, hx, Matrix.mul_assoc,
        Units.inv_mul_cancel_left]
    have h2 := congrFun (congrFun h1 (σ i)) j
    rw [pm_eq_mono, mono_mul, mono_mul] at h2
    simp only [Equiv.symm_apply_apply, Units.val_one, one_mul] at h2
    have h3 : j < m.1.symm (σ i) := by
      have := (hb i).not.2 (not_lt.2 hi)
      rw [Fin.lt_def]; omega
    rw [h2, unip_lower hu' h3, mul_zero]
  have hu1 := (isUniUp_iff u).2 hu
  have hx1 : x = u * pm g σ * ((pm g σ)⁻¹ * u⁻¹ * x) := by group
  refine ⟨σ, ⟨hσ, u, _, hu1, hp, hx1⟩, ?_⟩
  rintro τ ⟨hτ, v, q, hv, hq, hx2⟩
  have h1 : Monotone (key (fun r => (σ.symm r : ℕ) < a) ∘ σ) := key_mono (fun _ => Iff.rfl) hσ
  have h2 : Monotone (key (fun r => (σ.symm r : ℕ) < a) ∘ τ) := key_mono (fun r =>
    ⟨block_of_eq hu1 hv hp hq (hx1.symm.trans hx2) r, block_of_eq hv hu1 hq hp (hx2.symm.trans hx1) r⟩) hτ
  exact Equiv.ext fun i => key_injective _ (congrFun (Tuple.unique_monotone h2 h1) i)

end GlobalTheory.GLm.Shuffle
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryTorusScaleBesselCharacter
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.TorusScale

variable {k r : ℕ}

def dS (k r : ℕ) (l : ℂ) (i : Fin (2 * r + k + 1)) : ℂ :=
  if i.val < r then l ^ (r - i.val)
  else if r + k < i.val then (star (l ^ (r - (2 * r + k - i.val))))⁻¹ else 1

theorem dS_ne {l : ℂ} (hl : l ≠ 0) (i : Fin (2 * r + k + 1)) : dS k r l i ≠ 0 := by
  unfold dS
  split_ifs
  · exact pow_ne_zero _ hl
  · exact inv_ne_zero (star_ne_zero.2 (pow_ne_zero _ hl))
  · exact one_ne_zero

theorem dS_eI (l : ℂ) (a : Fin r) : dS k r l (eI k r a) = l ^ (r - a.val) := by
  unfold dS eI; simp [a.isLt]

theorem dS_mid (l : ℂ) (i : Fin (2 * r + k + 1)) (h : ¬ (i.val < r ∨ r + k < i.val)) : dS k r l i = 1 := by
  unfold dS
  rw [if_neg (by omega), if_neg (by omega)]

theorem dS_pair {l : ℂ} (hl : l ≠ 0) (i j : Fin (2 * r + k + 1)) (hi : i.val < r) (hij : i.val + j.val = 2 * r + k) :
    star (dS k r l i) * dS k r l j = 1 := by
  unfold dS
  rw [if_pos hi, if_neg (by omega), if_pos (by omega)]
  have : 2 * r + k - j.val = i.val := by omega
  rw [this]
  exact mul_inv_cancel₀ (star_ne_zero.2 (pow_ne_zero _ hl))

theorem diag_inv {n : Type} [Fintype n] [DecidableEq n] (d : n → ℂ) (hd : ∀ i, d i ≠ 0) :
    (diagonal d)⁻¹ = diagonal fun i => (d i)⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext i
  exact mul_inv_cancel₀ (hd i)

theorem conj_diag {n : Type} [Fintype n] [DecidableEq n] (d : n → ℂ) (hd : ∀ i, d i ≠ 0) (M : Matrix n n ℂ) (i j : n) :
    (diagonal d * M * (diagonal d)⁻¹) i j = d i * M i j * (d j)⁻¹ := by
  rw [diag_inv d hd]
  simp [Matrix.diagonal_mul, Matrix.mul_diagonal]

theorem diag_mem_UH (d : Fin (2 * r + k + 1) → ℂ) (h : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1) :
    diagonal d ∈ UH (Hpk k r) := by
  show (diagonal d)ᴴ * Hpk k r * diagonal d = Hpk k r
  ext i j
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hM : Hpk k r i j = 0
  · rw [hM]; ring
  · have := h i j hM
    rw [Pi.star_apply, mul_right_comm, this, one_mul]

theorem dS_Hpk {l : ℂ} (hl : l ≠ 0) (i j : Fin (2 * r + k + 1)) (h : Hpk k r i j ≠ 0) :
    star (dS k r l i) * dS k r l j = 1 := by
  by_cases h1 : i.val < r ∧ i.val + j.val = 2 * r + k
  · exact dS_pair hl i j h1.1 h1.2
  by_cases h2 : j.val < r ∧ i.val + j.val = 2 * r + k
  · have := congrArg star (dS_pair hl j i h2.1 (by omega))
    rw [star_mul, star_star, star_one] at this
    exact this
  by_cases h3 : r ≤ i.val ∧ i.val ≤ r + k ∧ i = j
  · rw [← h3.2.2, dS_mid l i (by omega)]; simp
  exfalso
  unfold Hpk at h
  rw [if_neg h1, if_neg h2, if_neg h3] at h
  exact h rfl

theorem conj_mem_N (d : Fin (2 * r + k + 1) → ℂ) (hd : ∀ i, d i ≠ 0)
    (h : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1) {n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hn : n ∈ Nset k r) : diagonal d * n * (diagonal d)⁻¹ ∈ Nset k r := by
  obtain ⟨h1, h2, h3⟩ := hn
  refine ⟨?_, fun a i hi => ?_, fun i j a b c => ?_⟩
  · refine Pv.Frames.UH_mul (Pv.Frames.UH_mul (diag_mem_UH d h) h1) ?_
    rw [diag_inv d hd]
    refine diag_mem_UH _ fun i j hij => ?_
    rw [star_inv₀, ← mul_inv, h i j hij, inv_one]
  · rw [conj_diag d hd, h2 a i hi]
    split_ifs with e
    · rw [e, mul_one, mul_inv_cancel₀ (hd _)]
    · ring
  · rw [conj_diag d hd, h3 i j a b c]
    split_ifs with e
    · rw [e, mul_one, mul_inv_cancel₀ (hd _)]
    · ring

theorem conj_mem_N_iff (d : Fin (2 * r + k + 1) → ℂ) (hd : ∀ i, d i ≠ 0)
    (h : ∀ i j, Hpk k r i j ≠ 0 → star (d i) * d j = 1) (n : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    n ∈ Nset k r ↔ diagonal d * n * (diagonal d)⁻¹ ∈ Nset k r := by
  refine ⟨conj_mem_N d hd h, fun hn => ?_⟩
  have hd' : ∀ i, (d i)⁻¹ ≠ 0 := fun i => inv_ne_zero (hd i)
  have := conj_mem_N (fun i => (d i)⁻¹) hd'
    (fun i j hij => by rw [star_inv₀, ← mul_inv, h i j hij, inv_one]) hn
  convert this using 1
  ext i j
  rw [conj_diag _ hd', conj_diag _ hd]
  have := hd i
  have := hd j
  field_simp

theorem UW_col {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (i j : Fin (2 * r + k + 1)) (hj : j.val < r ∨ r + k < j.val) :
    h i j = if i = j then 1 else 0 := by
  have key : h *ᵥ bvec j = bvec j := by
    rcases hj with hj | hj
    · exact (hh.2.1 ⟨j.val, hj⟩).1
    · have := (hh.2.1 ⟨2 * r + k - j.val, by omega⟩).2
      have e : esI k r ⟨2 * r + k - j.val, by omega⟩ = j := by
        apply Fin.ext
        have := j.isLt
        show 2 * r + k - (2 * r + k - j.val) = j.val
        omega
      rwa [e] at this
  have := congrFun key i
  simpa [bvec, Pi.single_apply] using this

theorem Hpk_outer (i j p : Fin (2 * r + k + 1)) (hj : j.val < r ∨ r + k < j.val) (hij : i.val + j.val = 2 * r + k) :
    Hpk k r j p = if p = i then 1 else 0 := by
  unfold Hpk
  by_cases e : p = i
  · subst e
    rw [if_pos rfl]
    by_cases h1 : j.val < r
    · rw [if_pos ⟨h1, by omega⟩]
    · rw [if_neg (by omega), if_pos (by omega)]
  · have e' : p.val ≠ i.val := fun x => e (Fin.ext x)
    rw [if_neg e, if_neg (by omega), if_neg (by omega), if_neg (by omega)]

theorem UW_row {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) (i j : Fin (2 * r + k + 1)) (hi : i.val < r ∨ r + k < i.val) :
    h i j = if j = i then 1 else 0 := by
  have hi0 := i.isLt
  let q : Fin (2 * r + k + 1) := ⟨2 * r + k - i.val, by omega⟩
  have hq : q.val < r ∨ r + k < q.val := by show 2 * r + k - i.val < r ∨ r + k < 2 * r + k - i.val; omega
  have hiq : i.val + q.val = 2 * r + k := by show i.val + (2 * r + k - i.val) = _; omega
  have hU : hᴴ * Hpk k r * h = Hpk k r := hh.1
  have := congrFun (congrFun hU q) j
  rw [Hpk_outer i q j hq hiq, Matrix.mul_assoc, Matrix.mul_apply] at this
  simp only [Matrix.conjTranspose_apply, UW_col hh _ q hq] at this
  rw [Finset.sum_eq_single q (fun b _ hb => by simp [hb]) (by simp), Matrix.mul_apply] at this
  simp only [Hpk_outer i q _ hq hiq] at this
  simpa using this

theorem dS_comm (l : ℂ) {z : Fin (2 * r + k + 1) → ℂ} {h : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hh : h ∈ UWset k r z) : diagonal (dS k r l) * h = h * diagonal (dS k r l) := by
  ext i j
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hj : j.val < r ∨ r + k < j.val
  · rw [UW_col hh i j hj]
    split_ifs with e
    · rw [e]; ring
    · ring
  by_cases hi : i.val < r ∨ r + k < i.val
  · rw [UW_row hh i j hi]
    split_ifs with e
    · rw [e]; ring
    · ring
  rw [dS_mid l i hi, dS_mid l j hj]; ring

theorem diag_fix (d : Fin (2 * r + k + 1) → ℂ) (hd : ∀ i : Fin (2 * r + k + 1), ¬ (i.val < r ∨ r + k < i.val) → d i = 1)
    {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) : diagonal d *ᵥ z = z := by
  funext i
  rw [Matrix.mulVec_diagonal]
  by_cases h : i.val < r ∨ r + k < i.val
  · rw [hz i h]; ring
  · rw [hd i h, one_mul]

theorem inv_fix {l : ℂ} (hl : l ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) :
    (diagonal (dS k r l))⁻¹ *ᵥ z = z := by
  rw [diag_inv _ (dS_ne hl)]
  exact diag_fix _ (fun i hi => by rw [dS_mid l i hi, inv_one]) hz

theorem ell_conj {l : ℂ} (hl : l ≠ 0) {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z)
    (M : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    ell k r z (diagonal (dS k r l) * M * (diagonal (dS k r l))⁻¹) = l * ell k r z M := by
  unfold ell
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  split_ifs with h
  · rw [conj_diag _ (dS_ne hl), dS_eI, dS_eI]
    have e : r - a.val = (r - (a.val + 1)) + 1 := by omega
    rw [e, pow_succ]
    have := pow_ne_zero (r - (a.val + 1)) hl
    field_simp
  · have hra : r - a.val = 1 := by have := a.isLt; omega
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_fix hl hz, Matrix.mulVec_diagonal, dS_eI, hra, pow_one]

theorem pow_bound {x : ℝ} (hx : 0 < x) {m : ℕ} (hm : m ≤ r) :
    (x / 2) ^ m ≤ max (x / 2) (2 / x) ^ r ∧ (2 / x) ^ m ≤ max (x / 2) (2 / x) ^ r := by
  have h1 : 1 ≤ max (x / 2) (2 / x) := by
    rcases le_total x 2 with h | h
    · exact le_max_of_le_right ((one_le_div hx).2 h)
    · exact le_max_of_le_left ((one_le_div two_pos).2 h)
  exact ⟨(pow_le_pow_left₀ (by positivity) (le_max_left _ _) m).trans (pow_le_pow_right₀ h1 hm),
    (pow_le_pow_left₀ (by positivity) (le_max_right _ _) m).trans (pow_le_pow_right₀ h1 hm)⟩

theorem exists_torus_scale : ∀ (k r : ℕ) (c : ℂ), c ≠ 0 → ∃ t ∈ GG k r, (∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r) ∧ (∀ z, inWb k r z → t *ᵥ z = z ∧ (∀ h ∈ UWset k r z, t * h = h * t) ∧ ∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) ∧ ∀ a : Fin (r + 1), ∃ s : ℂ, s ≠ 0 ∧ ‖s‖ ≤ max (‖c‖ / 2) (2 / ‖c‖) ^ r ∧ ‖s‖⁻¹ ≤ max (‖c‖ / 2) (2 / ‖c‖) ^ r ∧ ∀ z, inWb k r z → t⁻¹ *ᵥ fvec k r z a = s • fvec k r z a := by
  intro k r c hc
  have hS : cStd ≠ 0 := by unfold cStd; simp
  have hl : cStd / c ≠ 0 := div_ne_zero hS hc
  have hn : ‖cStd / c‖ = 2 / ‖c‖ := by unfold cStd; simp
  have hx : 0 < ‖c‖ := norm_pos_iff.2 hc
  refine ⟨diagonal (dS k r (cStd / c)), diag_mem_UH _ (dS_Hpk hl), conj_mem_N_iff _ (dS_ne hl) (dS_Hpk hl),
    fun z hz => ⟨diag_fix _ (dS_mid _) hz, fun h hh => dS_comm _ hh, fun n _ => ?_⟩, fun a => ?_⟩
  · unfold psi
    rw [ell_conj hl hz, ← mul_assoc, mul_div_cancel₀ _ hc]
  · have hb := pow_bound (r := r) hx (Nat.sub_le r a.val)
    refine ⟨((cStd / c) ^ (r - a.val))⁻¹, inv_ne_zero (pow_ne_zero _ hl), ?_, ?_, fun z hz => ?_⟩
    · rw [norm_inv, norm_pow, hn, ← inv_pow, inv_div]; exact hb.1
    · rw [norm_inv, inv_inv, norm_pow, hn]; exact hb.2
    · unfold fvec
      split_ifs with h
      · rw [diag_inv _ (dS_ne hl)]
        funext i
        rw [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
        by_cases e : i = eI k r ⟨a.val, h⟩
        · rw [e, dS_eI]
        · simp [bvec, e]
      · have : r - a.val = 0 := by omega
        rw [inv_fix hl hz, this]; simp

end GlobalTheory.TorusScale

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormInvVolSkewLayerLe
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.WtSkew

theorem invVol_le_relIndex {G : Type} [Group G] (A B : Subgroup G) :
    GlobalTheory.HL.invVol A B ≤ (B.relIndex A : ℝ) := by
  unfold GlobalTheory.HL.invVol
  rcases Nat.eq_zero_or_pos (A.relIndex B) with h | h
  · simp [h]
  · exact div_le_self (Nat.cast_nonneg _) (by exact_mod_cast h)

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}

omit [NumberField K] [StarRing K] in
theorem line_le {A : Submodule (𝓞 K) K} {v : V} {S : Submodule K V} (h : v ∈ S) :
    line A v ≤ rs (𝓞 K) S := by
  rintro _ ⟨t, -, rfl⟩
  exact S.smul_mem t h

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem e_mem_X (F : FlagD H r) (a : Fin r) : F.e a.castSucc ∈ F.X :=
  Submodule.subset_span ⟨a, a.2, rfl⟩

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
theorem lastVector_mem_jointSpan_left (F F' : FlagD H r) : F.z ∈ V0 F F' :=
  Submodule.mem_sup_right (Submodule.subset_span (by simp))

theorem normalForm_baseLattice_le_dualSpan_sup_line (N : NF H r) : N.P0 ≤ rs (𝓞 K) (V0 N.F N.F' ⊔ N.Ist) := by
  unfold NF.P0
  refine sup_le (sup_le (sup_le (iSup_le fun a => line_le ?_) (iSup_le fun a => iSup_le fun _ => line_le ?_))
    (line_le ?_)) (iSup_le fun a => iSup_le fun ha => line_le ?_)
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_left (e_mem_X _ a)))
  · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (e_mem_X _ a)))
  · exact Submodule.mem_sup_left (lastVector_mem_jointSpan_left _ _)
  · exact Submodule.mem_sup_right (Submodule.subset_span ⟨a, ha, rfl⟩)

theorem ref_inf_Pi (N : NF H r) (L : Submodule (𝓞 K) V) (hc : IsCompl N.Wt N.Pi)
    (hn : N.Wn = N.Wt ⊔ Submodule.span K {N.F.z}) (hp : N.Pi = V0 N.F N.F' ⊔ N.Ist)
    (hz : ∀ t : K, t • N.F.z ∈ L → t ∈ (1 : Submodule (𝓞 K) K)) :
    N.Ref L ⊓ rs (𝓞 K) N.Pi = N.P0 := by
  have h0 : N.P0 ≤ rs (𝓞 K) N.Pi := hp ▸ normalForm_baseLattice_le_dualSpan_sup_line N
  have hzP : N.F.z ∈ N.Pi := hp ▸ Submodule.mem_sup_left (lastVector_mem_jointSpan_left _ _)
  refine le_antisymm ?_ (le_inf le_sup_left h0)
  rintro x ⟨hx, hxP⟩
  obtain ⟨p, hpP, l, ⟨hlL, hlW⟩, rfl⟩ := Submodule.mem_sup.1 hx
  have hlW' : l ∈ N.Wt ⊔ Submodule.span K {N.F.z} := hn ▸ hlW
  obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.1 hlW'
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hy
  have hxP' : p + (w + t • N.F.z) ∈ N.Pi := hxP
  have hpP' : p ∈ N.Pi := h0 hpP
  have hwP : w ∈ N.Pi := by
    have := N.Pi.sub_mem (N.Pi.sub_mem hxP' hpP') (N.Pi.smul_mem t hzP)
    simpa using this
  have hw0 : w = 0 := (Submodule.disjoint_def.1 hc.disjoint) w hw hwP
  subst hw0
  rw [zero_add] at hlL ⊢
  refine N.P0.add_mem hpP ?_
  unfold NF.P0
  exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨t, hz t hlL, rfl⟩)

theorem invVol_skew_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → ∀ 𝔠 : Ideal (𝓞 K), 𝔠 ≠ ⊥ → (∀ x ∈ 𝔠, ∃ y ∈ 𝔠, (y : K) = star (x : K)) → (∀ x ∈ 𝔠, (N.T : 𝓞 K) ∣ x) → (∀ (l : ℕ) (hl : l ≤ r + 1), l ≤ N.j → Dl N.F N.F' l hl ≠ 0 → ∀ x ∈ 𝔠, ∀ y ∈ ipow N.𝔡 (2 * ∑ a ∈ Finset.range l, ((r : ℤ) - a)), (x : K) * y / Dl N.F N.F' l hl ∈ (1 : Submodule (𝓞 K) K) ∧ (x : K) * y / star (Dl N.F N.F' l hl) ∈ (1 : Submodule (𝓞 K) K)) → ∀ e : ℕ, N.Split Λ → N.Near (𝔠 ^ e) Λ → GlobalTheory.HL.invVol (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) (N.Gam Λ ⊓ N.ZI) ≤ (Ideal.absNorm 𝔠 : ℝ) ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hT 𝔠 h0 hst hdT hD e hS hN
  obtain ⟨-, -, hc, hdim, hn, -, -, -, -, -, -, hp⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨hR, -⟩ := GlobalTheory.T.hermFramePairCommonUnipotentStabiliser_summary K V H hK r N
  obtain ⟨-, -, hz, -, hlat, -⟩ := GlobalTheory.T.hermFramePair_innerLattices_unimodular_primitive K V H hK r N g Λ hg hT
  have hstab := GlobalTheory.T.stabilizer_hermitianLattice_of_deep_star_congruence K V H hK r N g Λ hg hT 𝔠 h0 hst hdT hD e hS hN
  have hP := ref_inf_Pi N (latL N.F N.F' Λ) hc hn hp (fun t ht => (hz t).1 ht)
  have hfg : N.P0.FG := by
    refine Submodule.FG.of_le hlat.fg ?_
    rw [← hP]; exact inf_le_left
  have hmap : ∀ s ∈ N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI, ∀ x ∈ N.P0, s x ∈ N.P0 := by
    rintro s ⟨⟨hsR, hsS⟩, -, hsW⟩ x hx
    rw [← hP] at hx ⊢
    have hsS' : s • N.Ref (latL N.F N.F' Λ) = N.Ref (latL N.F N.F' Λ) := hsS
    refine ⟨?_, ?_⟩
    · rw [← hsS']
      exact Submodule.smul_mem_pointwise_smul _ _ _ hx.1
    · have hx2 : x ∈ perp H N.Wt := hx.2
      change s x ∈ perp H N.Wt
      rw [mem_perp_iff] at hx2 ⊢
      intro w hw
      have hw' : s w = w := (mem_fixingSubgroup_iff _).1 hsW w hw
      have := ((hR s).1 hsR).1.1 x w
      simp only [LinearEquiv.coe_coe, hw'] at this
      rw [this]; exact hx2 w hw
  have hfix : ∀ s ∈ N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI, s • N.P0 = N.P0 := by
    intro s hs
    refine le_antisymm ?_ ?_
    · intro y hy
      obtain ⟨x, hx, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
      exact hmap s hs x hx
    · intro y hy
      refine (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨s⁻¹ y, hmap _ (inv_mem hs) y hy, ?_⟩
      exact s.apply_symm_apply y
  have hm : 𝔠 ^ (3 * e + 10) ≠ ⊥ := pow_ne_zero _ h0
  obtain ⟨-, hle⟩ := GlobalTheory.T.relIndex_congruence_subgroup_le_absNorm_pow K V (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) N.P0 (𝔠 ^ (3 * e + 10))
    (N.Gam Λ ⊓ N.ZI) hfg hm hfix (fun s hs hx =>
      ⟨⟨hs.1.1, hstab s ⟨hs.1.1, hs.2.2⟩ hx⟩, hs.2⟩)
  have hrk : Module.finrank K (Submodule.span K (N.P0 : Set V)) ≤ 2 * r + 1 := by
    have h1 : Submodule.span K (N.P0 : Set V) ≤ N.Pi := by
      rw [Submodule.span_le, ← hP]
      exact fun x hx => hx.2
    have h2 := Submodule.finrank_mono h1
    have h3 := Submodule.finrank_add_eq_of_isCompl hc
    omega
  have hpos : 1 ≤ Ideal.absNorm 𝔠 := Nat.one_le_iff_ne_zero.2 (fun h => h0 (Ideal.absNorm_eq_zero_iff.1 h))
  refine (invVol_le_relIndex _ _).trans ?_
  have : (N.Gam Λ ⊓ N.ZI).relIndex (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.ZI) ≤
      Ideal.absNorm 𝔠 ^ ((3 * e + 11) * (2 * r + 1) ^ 2) := by
    refine hle.trans ?_
    rw [map_pow, ← pow_mul]
    exact Nat.pow_le_pow_right hpos (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hrk 2))
  exact_mod_cast this

end GlobalTheory.DegCnt.WtSkew
end

