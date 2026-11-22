import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0291
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0207
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0205
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0138
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0119
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0156
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WhittakerTermEqZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsUnitOfUniUp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0127

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPhiGammaModelSenWeightCount
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.ModelCount

theorem telescope (S S₀ m : ℤ → ℕ) (h : ∀ y, S y + m (y + 1) = S₀ y + m y) (a : ℤ) (L : ℕ) :
    ∑ j ∈ Finset.range L, S (a + j) + m (a + L) = ∑ j ∈ Finset.range L, S₀ (a + j) + m a := by
  induction L with
  | zero => simp
  | succ L ih =>
    have step := h (a + L)
    have e : a + ((L + 1 : ℕ) : ℤ) = a + L + 1 := by push_cast; ring
    rw [Finset.sum_range_succ, Finset.sum_range_succ, e]
    omega

theorem eq_of_cast_eq {k : Type} [Field k] (l : ℕ) [CharP k l] {u y : ℤ} (h : (u : k) = (y : k))
    (h1 : u - y < l) (h2 : y - u < l) : u = y := by
  have hd : (l : ℤ) ∣ y - u := ((CharP.intCast_eq_intCast k l).mp h).dvd
  have hz : y - u = 0 := Int.eq_zero_of_abs_lt_dvd hd (abs_lt.mpr ⟨by omega, by omega⟩)
  omega

theorem sum_resCount {k : Type} [Field k] (U : Multiset ℤ) (w a : ℤ) (L : ℕ) (p : ℤ → Prop) [DecidablePred p]
    (h : ∀ u ∈ U, (p u → a ≤ u ∧ u < a + L) ∧
      ∀ y : ℤ, a ≤ y → y < a + L → (u : k) = (y : k) → u = y ∧ p u) :
    ∑ j ∈ Finset.range L, resCount U w ((a + j - w : ℤ) : k) = Multiset.card (U.filter p) := by
  classical
  induction U using Multiset.induction_on with
  | empty => simp [resCount]
  | cons u U ih =>
    have hU := ih (fun v hv => h v (Multiset.mem_cons_of_mem hv))
    have hu := h u (Multiset.mem_cons_self u U)
    have split : ∀ x : k, resCount (u ::ₘ U) w x =
        (if ((u - w : ℤ) : k) = x then 1 else 0) + resCount U w x := by
      intro x
      unfold resCount
      rw [Multiset.filter_cons, Multiset.card_add]
      split_ifs <;> simp
    simp only [split]
    rw [Finset.sum_add_distrib, hU, Multiset.filter_cons, Multiset.card_add]
    congr 1
    have tr : ∀ j : ℕ, (((u - w : ℤ) : k) = ((a + j - w : ℤ) : k)) ↔ ((u : k) = ((a + j : ℤ) : k)) := by
      intro j
      push_cast
      exact sub_left_inj
    by_cases hp : p u
    · rw [if_pos hp, Multiset.card_singleton]
      obtain ⟨ha, hb⟩ := hu.1 hp
      rw [Finset.sum_eq_single (u - a).toNat]
      · rw [if_pos]
        rw [tr]
        congr 1
        omega
      · intro j _ hj
        rw [if_neg]
        intro hc
        have := (hu.2 (a + j) (by omega) (by have := Finset.mem_range.mp ‹j ∈ Finset.range L›; omega) ((tr j).mp hc)).1
        omega
      · intro hn
        exfalso
        exact hn (Finset.mem_range.mpr (by omega))
    · rw [if_neg hp, Multiset.card_zero]
      apply Finset.sum_eq_zero
      intro j hj
      rw [if_neg]
      intro hc
      have hj' := Finset.mem_range.mp hj
      exact hp (hu.2 (a + j) (by omega) (by omega) ((tr j).mp hc)).2

theorem exists_of_resCount_ne {k : Type} [Field k] {U : Multiset ℤ} {w : ℤ} {x : k} (h : resCount U w x ≠ 0) :
    ∃ u ∈ U, ((u - w : ℤ) : k) = x := by
  classical
  unfold resCount at h
  obtain ⟨u, hu⟩ := Multiset.card_pos_iff_exists_mem.mp (Nat.pos_of_ne_zero h)
  rw [Multiset.mem_filter] at hu
  exact ⟨u, hu.1, hu.2⟩

theorem count : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt), Dt.T1 l → Dt.T2 l → Dt.T3 l → ∀ N : Lats k n M.T.m, M.Model M.T N → (∀ i, M.Nstd i ≤ N i) → ∀ i, (∀ a : ℕ, a ≤ Dt.sg l i + 1 → sen ((F.D M.T).γ i) (N i) (a : k) = 0) ∧ (Dt.ty i = LType.G → ∑ j ∈ Finset.range (Dt.w i).toNat, sen ((F.D M.T).γ i) (N i) ((-Dt.w i + j : ℤ) : k) = Dt.d i) ∧ (Dt.ty i = LType.Bd → Dt.d i + ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen ((F.D M.T).γ i) (N i) (a : k) = r) := by
  intro k G _ _ l n _ _ _ R F r Dt M h1 h2 h3 N hN hle i
  have hNabc := (GlobalTheory.T.obj_and_abc_of_model F M M.T N hN).2
  have hSabc := (GlobalTheory.T.obj_and_abc_of_model F M M.T M.Nstd M.std_model).2
  have hs : Dt.sg l i = GlobalTheory.PhiGam.sg l Dt.h i := rfl
  have hsh := GlobalTheory.T.phiGamma_lattice_families_shift_inclusion (F.D M.T) Dt.h Dt.w N M.Nstd hNabc.1 hSabc.1 hNabc.2.1 hSabc.2.1 i
  rw [← hs] at hsh
  have hP : N i ≤ sh (-(Dt.sg l i : ℤ)) (M.Nstd i) := by
    have h' := sh_le_sh (-(Dt.sg l i : ℤ)) hsh
    rwa [sh_sh_eq, neg_add_cancel, sh_zero_eq] at h'
  have tel := fun y : ℤ => GlobalTheory.T.senMultiplicity_lattice_count_relation R ((F.D M.T).γ i) ((F.D M.T).γ_semi i) (N i) (M.Nstd i)
    (hNabc.1 i) (hSabc.1 i) (hle i) (hNabc.2.2 i) (hSabc.2.2 i) (Dt.sg l i) hP (y : k)
  have rel : ∀ y : ℤ, sen ((F.D M.T).γ i) (N i) (y : k) + qmult ((F.D M.T).γ i) (N i) (M.Nstd i) ((y + 1 : ℤ) : k) =
      sen ((F.D M.T).γ i) (M.Nstd i) (y : k) + qmult ((F.D M.T).γ i) (N i) (M.Nstd i) (y : k) := by
    intro y
    rw [Int.cast_add, Int.cast_one]
    exact (tel y).1
  have mz : ∀ y : ℤ, qmult ((F.D M.T).γ i) (N i) (M.Nstd i) (y : k) ≠ 0 →
      ∃ j : ℕ, 1 ≤ j ∧ j ≤ Dt.sg l i ∧ ∃ u ∈ Dt.U i, (u : k) = ((y - j + Dt.w i : ℤ) : k) := by
    intro y hy
    obtain ⟨j, hj1, hj2, hj⟩ := (tel y).2 hy
    rw [M.std_sen] at hj
    obtain ⟨u, hu, hux⟩ := exists_of_resCount_ne hj
    refine ⟨j, hj1, hj2, u, hu, ?_⟩
    push_cast at hux ⊢
    linear_combination hux
  have sz : ∀ y : ℤ, sen ((F.D M.T).γ i) (N i) (y : k) ≠ 0 → ∃ u ∈ Dt.U i, (u : k) = ((y + Dt.w i : ℤ) : k) := by
    intro y hy
    obtain ⟨u, hu, hux⟩ := GlobalTheory.T.senWeight_subquotient_model_mem_residues F M h1 h2 h3 M.T M.T LinearMap.id LinearMap.id N (fun _ _ => rfl)
      (fun _ _ hab => hab) (fun _ _ => rfl) (fun b => ⟨b, rfl⟩) hN i (y : k) hy
    refine ⟨u, hu, ?_⟩
    push_cast at hux ⊢
    linear_combination hux
  obtain ⟨-, hwin, hG, hB⟩ := GlobalTheory.T.admissibleLetterData_window_arithmetic (k := k) Dt h1 h2 h3 i
  have hT1 := h1 i
  have ht := Dt.one_le_letterBlockLength
  have e1 : qmult ((F.D M.T).γ i) (N i) (M.Nstd i) ((0 : ℤ) : k) = 0 := by
    by_contra hne
    obtain ⟨j, hj1, hj2, u, hu, hux⟩ := mz 0 hne
    exact hwin u hu _ (by omega) (by omega) hux
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    by_contra hne
    obtain ⟨u, hu, hux⟩ := sz a (by simpa using hne)
    exact hwin u hu _ (by omega) (by omega) hux
  · intro hG'
    obtain ⟨hGU, hGc, hw1, hwt⟩ := hG hG'
    have hL : ((Dt.w i).toNat : ℤ) = Dt.w i := Int.toNat_of_nonneg (by omega)
    have tl := telescope (fun y => sen ((F.D M.T).γ i) (N i) (y : k)) (fun y => sen ((F.D M.T).γ i) (M.Nstd i) (y : k))
      (fun y => qmult ((F.D M.T).γ i) (N i) (M.Nstd i) (y : k)) rel (-Dt.w i) (Dt.w i).toNat
    have e0 : qmult ((F.D M.T).γ i) (N i) (M.Nstd i) ((-Dt.w i + ((Dt.w i).toNat : ℤ) : ℤ) : k) = 0 := by
      rw [hL, neg_add_cancel]
      exact e1
    have e2 : qmult ((F.D M.T).γ i) (N i) (M.Nstd i) ((-Dt.w i : ℤ) : k) = 0 := by
      by_contra hne
      obtain ⟨j, hj1, hj2, u, hu, hux⟩ := mz (-Dt.w i) hne
      exact hGU u hu _ (by omega) (by omega) hux
    have hsum := sum_resCount (k := k) (Dt.U i) (Dt.w i) 0 (Dt.w i).toNat (· < Dt.w i) (by
      intro u hu
      have hr := Dt.range i u (Multiset.mem_add.mpr (Or.inl hu))
      refine ⟨fun _ => ⟨by omega, by omega⟩, fun y hy0 hyL hc => ?_⟩
      rcases Multiset.mem_add.mp hu with hlow | hcl
      · have hb := Dt.lowG i hG' u (Multiset.mem_add.mpr (Or.inl hlow))
        have hy := eq_of_cast_eq l hc (by omega) (by omega)
        exact ⟨hy, by omega⟩
      · exact absurd hc (hGc u hcl y hy0 (by omega)))
    have e3 : ∀ j : ℕ, ((0 : ℤ) + (j : ℤ) - Dt.w i) = -Dt.w i + j := fun j => by ring
    simp only [e3] at hsum
    have hsum' : ∑ j ∈ Finset.range (Dt.w i).toNat, sen ((F.D M.T).γ i) (M.Nstd i) ((-Dt.w i + j : ℤ) : k) = Dt.d i := by
      change _ = Multiset.card ((Dt.U i).filter (· < Dt.w i))
      rw [← hsum]
      exact Finset.sum_congr rfl (fun j _ => M.std_sen i _)
    rw [e0, e2, hsum'] at tl
    omega
  · intro hB'
    obtain ⟨hBU, hBc, htw, hwη⟩ := hB hB'
    have hwst : Dt.wst i = (Dt.h i : ℤ) - Dt.w i := rfl
    have hL : ((Dt.wst i).toNat : ℤ) = Dt.wst i := Int.toNat_of_nonneg (by omega)
    have tl := telescope (fun y => sen ((F.D M.T).γ i) (N i) (y : k)) (fun y => sen ((F.D M.T).γ i) (M.Nstd i) (y : k))
      (fun y => qmult ((F.D M.T).γ i) (N i) (M.Nstd i) (y : k)) rel 0 ((Dt.wst i).toNat + 1 + (Dt.sg l i + 1))
    have e0 : qmult ((F.D M.T).γ i) (N i) (M.Nstd i)
        (((0 : ℤ) + (((Dt.wst i).toNat + 1 + (Dt.sg l i + 1) : ℕ) : ℤ) : ℤ) : k) = 0 := by
      by_contra hne
      obtain ⟨j, hj1, hj2, u, hu, hux⟩ := mz _ hne
      exact hBU u hu _ (by push_cast; omega) (by push_cast; omega) hux
    rw [e0, e1, Finset.sum_range_add] at tl
    have hz : ∑ j ∈ Finset.range (Dt.sg l i + 1),
        sen ((F.D M.T).γ i) (N i) (((0 : ℤ) + (((Dt.wst i).toNat + 1 + j : ℕ) : ℤ) : ℤ) : k) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      have hj' := Finset.mem_range.mp hj
      by_contra hne
      obtain ⟨u, hu, hux⟩ := sz _ hne
      exact hBU u hu _ (by push_cast; omega) (by push_cast; omega) hux
    rw [hz] at tl
    have hsum := sum_resCount (k := k) (Dt.U i) (Dt.w i) (Dt.w i) ((Dt.wst i).toNat + 1 + (Dt.sg l i + 1))
      (fun u => ¬ u < Dt.w i) (by
      intro u hu
      have hr := Dt.range i u (Multiset.mem_add.mpr (Or.inl hu))
      refine ⟨fun _ => ⟨by omega, by push_cast; omega⟩, fun y hy0 hyL hc => ?_⟩
      push_cast at hyL
      rcases Multiset.mem_add.mp hu with hlow | hcl
      · have hb := Dt.lowBd i hB' u (Multiset.mem_add.mpr (Or.inl hlow))
        have hy := eq_of_cast_eq l hc (by omega) (by omega)
        exact ⟨hy, by omega⟩
      · by_cases hyh : y ≤ (Dt.h i : ℤ)
        · exact absurd hc (hBc u hcl y (by omega) hyh)
        · exact absurd hc (hBU u (Multiset.mem_add.mpr (Or.inr hcl)) y (by omega) (by omega)))
    have e3 : ∀ j : ℕ, (Dt.w i + (j : ℤ) - Dt.w i) = 0 + j := fun j => by ring
    simp only [e3] at hsum
    have hsum' : ∑ j ∈ Finset.range ((Dt.wst i).toNat + 1 + (Dt.sg l i + 1)),
        sen ((F.D M.T).γ i) (M.Nstd i) (((0 : ℤ) + j : ℤ) : k) = Multiset.card ((Dt.U i).filter (fun u => ¬ u < Dt.w i)) := by
      rw [← hsum]
      exact Finset.sum_congr rfl (fun j _ => M.std_sen i _)
    rw [hsum'] at tl
    have hfirst : ∑ j ∈ Finset.range ((Dt.wst i).toNat + 1), sen ((F.D M.T).γ i) (N i) (((0 : ℤ) + j : ℤ) : k) =
        ∑ a ∈ Finset.range ((Dt.wst i).toNat + 1), sen ((F.D M.T).γ i) (N i) (a : k) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      simp
    have hsplit := congrArg Multiset.card (Multiset.filter_add_not (· < Dt.w i) (Dt.U i))
    rw [Multiset.card_add] at hsplit
    have hU : Multiset.card (Dt.U i) = r := Dt.card_eq i
    have hd : Dt.d i = Multiset.card ((Dt.U i).filter (· < Dt.w i)) := rfl
    rw [hfirst] at tl
    omega

end GlobalTheory.ModelCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwoBlockEqZeroIff
section
open Formalism.IrreducibleCountingLemmas.TYPES

noncomputable section

namespace GlobalTheory.SerOSys

theorem twoBlock_eq_zero_iff {n a : ℕ} (i : Fin n) : twoBlock n a i = 0 ↔ (i : ℕ) < a := by
  unfold twoBlock
  by_cases h : (i : ℕ) < a
  · simp [h]
  · simp only [h, if_false, iff_false]
    decide

theorem twoBlock_eq_one_iff {n a : ℕ} (i : Fin n) : twoBlock n a i = 1 ↔ a ≤ (i : ℕ) := by
  unfold twoBlock
  by_cases h : (i : ℕ) < a
  · simp only [h, if_true]
    exact ⟨fun h' => absurd h' (by decide), fun h' => absurd h' (by omega)⟩
  · simp only [h, if_false]
    exact ⟨fun _ => by omega, fun _ => trivial⟩

def firstBlock (a b : ℕ) : {i : Fin (a + b) // twoBlock (a + b) a i = 0} ≃ Fin a where
  toFun i := ⟨i.1, (twoBlock_eq_zero_iff i.1).1 i.2⟩
  invFun j := ⟨⟨j, by omega⟩, (twoBlock_eq_zero_iff _).2 j.2⟩
  left_inv i := by rcases i with ⟨⟨i, hi⟩, h⟩; rfl
  right_inv j := by rcases j with ⟨j, hj⟩; rfl

def secondBlock (a b : ℕ) : {i : Fin (a + b) // twoBlock (a + b) a i = 1} ≃ Fin b where
  toFun i := ⟨i.1 - a, by have := (twoBlock_eq_one_iff i.1).1 i.2; have := i.1.2; omega⟩
  invFun j := ⟨⟨a + j, by omega⟩, (twoBlock_eq_one_iff _).2 (by simp)⟩
  left_inv i := by
    rcases i with ⟨⟨i, hi⟩, h⟩
    have hai : a ≤ i := (twoBlock_eq_one_iff _).1 h
    apply Subtype.ext
    apply Fin.ext
    show a + (i - a) = i
    omega
  right_inv j := by
    rcases j with ⟨j, hj⟩
    apply Fin.ext
    simp

def twoRep {K : Type} [Field K] [Fintype K] [DecidableEq K] {a b : ℕ} (ρ : FDRep ℂ (GL (Fin a) K))
    (ρ' : FDRep ℂ (GL (Fin b) K)) : ∀ c : Fin 2, FDRep ℂ (GL {i : Fin (a + b) // twoBlock (a + b) a i = c} K)
  | 0 => transp (firstBlock a b).symm ρ
  | 1 => transp (secondBlock a b).symm ρ'

def UFix {g : ℕ} [Fact g.Prime] (a b : ℕ) {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GlobalTheory.GLq.Gn g (a + b)) V) (w : V) : Prop :=
  ∀ u : GlobalTheory.GLq.Gn g (a + b), GlobalTheory.GLq.InPar a (u : GlobalTheory.GLq.Mt g (a + b)) →
    GlobalTheory.GLq.tl a (u : GlobalTheory.GLq.Mt g (a + b)) = 1 → GlobalTheory.GLq.br a b (u : GlobalTheory.GLq.Mt g (a + b)) = 1 → ρ u w = w

end GlobalTheory.SerOSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDimensionHarishChandraInductionMul
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical

namespace GlobalTheory.GLq.WhMul

variable {g : ℕ} [Fact g.Prime]

theorem entN_mul_succ {n : ℕ} (M N : Mt g n) (hM : IsUniUp M) (hN : IsUniUp N) (k : ℕ) :
    entN (M * N) k (k + 1) = entN M k (k + 1) + entN N k (k + 1) := by
  unfold entN
  split_ifs with h
  · set i : Fin n := ⟨k, h.1⟩
    set j : Fin n := ⟨k + 1, h.2⟩
    have hij : i ≠ j := by simp [i, j, Fin.ext_iff]
    rw [Matrix.mul_apply, Fintype.sum_eq_add i j hij]
    · rw [(hM i i).2 rfl, (hN j j).2 rfl, one_mul, mul_one, add_comm]
    · rintro c ⟨hci, hcj⟩
      by_cases hc : c < i
      · rw [(hM i c).1 hc, zero_mul]
      · have : j < c := by
          rw [Fin.lt_def] at hc ⊢
          have h1 : (c : ℕ) ≠ k := fun e => hci (Fin.ext e)
          have h2 : (c : ℕ) ≠ k + 1 := fun e => hcj (Fin.ext e)
          simp only [i, j] at hc ⊢
          omega
        rw [(hN c j).1 this, mul_zero]
  · simp only [add_zero]

theorem supFrom_mul {n : ℕ} (M N : Mt g n) (hM : IsUniUp M) (hN : IsUniUp N) :
    supFrom 0 (M * N) = supFrom 0 M + supFrom 0 N := by
  unfold supFrom
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => entN_mul_succ M N hM hN k

theorem supFrom_one (n : ℕ) : supFrom 0 (1 : Mt g n) = 0 := by
  unfold supFrom
  refine Finset.sum_eq_zero fun k _ => ?_
  unfold entN
  split_ifs with h
  · rw [Matrix.one_apply_ne]
    simp [Fin.ext_iff]
  · rfl

theorem tl_one (a b : ℕ) : tl a (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [ParBasic.tl_apply, Matrix.one_apply, Matrix.one_apply]
  simp [Fin.ext_iff]

theorem br_one (a b : ℕ) : br a b (1 : Mt g (a + b)) = 1 := by
  ext i j
  rw [ParBasic.br_apply, Matrix.one_apply, Matrix.one_apply]
  simp [Fin.ext_iff]

theorem wh_hcT : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (a b n : ℕ), n = a + b →
    ∀ Φ : Gn g a → Gn g b → ℂ, (∀ y, IsClass fun x => Φ x y) → (∀ x, IsClass (Φ x)) →
      wh ψ (hcT a b Φ n) = wh ψ (fun x => wh ψ (Φ x)) := by
  intro g _ ψ hψ a b n hn Φ hΦ1 hΦ2
  obtain ⟨⟨P, hP⟩, ⟨U, hU⟩, -, -, -, -⟩ := ParBasic.par_basic g a b n hn
  subst hn

  have hl : ∀ h ∈ U, ∀ x ∈ U, (fun x : Gn g (a + b) => (ψ (supFrom 0 (x : Mt g (a + b))))⁻¹) (h * x * h⁻¹) =
      (fun x : Gn g (a + b) => (ψ (supFrom 0 (x : Mt g (a + b))))⁻¹) x := by
    intro h hh x hx
    have hh' := (hU h).1 hh
    have hx' := (hU x).1 hx
    have hi' := (hU h⁻¹).1 (U.inv_mem hh)
    have e1 : supFrom 0 ((h : Mt g (a + b)) * ((h⁻¹ : Gn g (a + b)) : Mt g (a + b))) = 0 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one, supFrom_one]
    rw [supFrom_mul _ _ hh' hi'] at e1
    have hxh := ParBasic.isUniUp_mul _ _ hh' hx'
    simp only [Units.val_mul]
    rw [supFrom_mul _ _ hxh hi', supFrom_mul _ _ hh' hx']
    congr 2
    linear_combination e1

  have hφ : ∀ k ∈ P, ∀ x ∈ P,
      (fun z : Gn g (a + b) => Φ (toG (tl a (z : Mt g (a + b)))) (toG (br a b (z : Mt g (a + b))))) (k * x * k⁻¹) =
      (fun z : Gn g (a + b) => Φ (toG (tl a (z : Mt g (a + b)))) (toG (br a b (z : Mt g (a + b))))) x := by
    intro k hk x hx
    have hk' := (hP k).1 hk
    have hx' := (hP x).1 hx
    have hi' := (hP k⁻¹).1 (P.inv_mem hk)
    have hkx := (hP (k * x)).1 (P.mul_mem hk hx)
    obtain ⟨uk, vk⟩ := ParBasic.isUnit_blocks k hk'
    obtain ⟨ux, vx⟩ := ParBasic.isUnit_blocks x hx'
    have m1 := ParBasic.blocks_mul _ _ hk' hi'
    have m2 := ParBasic.blocks_mul _ _ hk' hx'
    have m3 := ParBasic.blocks_mul _ _ hkx hi'
    have hkxk := (hP (k * x * k⁻¹)).1 (P.mul_mem (P.mul_mem hk hx) (P.inv_mem hk))
    obtain ⟨uc, vc⟩ := ParBasic.isUnit_blocks _ hkxk
    have e1 : ((k * x * k⁻¹ : Gn g (a + b)) : Mt g (a + b)) = (k : Mt g (a + b)) * (x : Mt g (a + b)) * ((k⁻¹ : Gn g (a + b)) : Mt g (a + b)) := by
      simp only [Units.val_mul]
    have e0 : (k : Mt g (a + b)) * ((k⁻¹ : Gn g (a + b)) : Mt g (a + b)) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have iA : (((toG (tl a (k : Mt g (a + b))))⁻¹ : Gn g a) : Mt g a) = tl a ((k⁻¹ : Gn g (a + b)) : Mt g (a + b)) := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [OpenCell.coe_toG uk, ← m1.2.1, e0, tl_one]
    have iB : (((toG (br a b (k : Mt g (a + b))))⁻¹ : Gn g b) : Mt g b) = br a b ((k⁻¹ : Gn g (a + b)) : Mt g (a + b)) := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [OpenCell.coe_toG vk, ← m1.2.2, e0, br_one]
    have cA : toG (tl a ((k * x * k⁻¹ : Gn g (a + b)) : Mt g (a + b))) =
        toG (tl a (k : Mt g (a + b))) * toG (tl a (x : Mt g (a + b))) * (toG (tl a (k : Mt g (a + b))))⁻¹ := by
      apply Units.ext
      rw [OpenCell.coe_toG uc]
      simp only [Units.val_mul] at m3 ⊢
      rw [iA, OpenCell.coe_toG uk, OpenCell.coe_toG ux, m3.2.1, m2.2.1]
    have cB : toG (br a b ((k * x * k⁻¹ : Gn g (a + b)) : Mt g (a + b))) =
        toG (br a b (k : Mt g (a + b))) * toG (br a b (x : Mt g (a + b))) * (toG (br a b (k : Mt g (a + b))))⁻¹ := by
      apply Units.ext
      rw [OpenCell.coe_toG vc]
      simp only [Units.val_mul] at m3 ⊢
      rw [iB, OpenCell.coe_toG vk, OpenCell.coe_toG vx, m3.2.2, m2.2.2]
    show Φ _ _ = Φ _ _
    rw [cA, cB]
    have h1 := hΦ1 (toG (br a b (k : Mt g (a + b))) * toG (br a b (x : Mt g (a + b))) * (toG (br a b (k : Mt g (a + b))))⁻¹)
      (toG (tl a (x : Mt g (a + b)))) (toG (tl a (k : Mt g (a + b))))
    have h2 := hΦ2 (toG (tl a (x : Mt g (a + b)))) (toG (br a b (x : Mt g (a + b)))) (toG (br a b (k : Mt g (a + b))))
    simp only at h1 h2
    rw [h1, h2]
  set R : Finset (Equiv.Perm (Fin (a + b))) := Finset.univ.filter fun σ =>
    ∀ i j : Fin (a + b), i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j with hR
  have hRu : ∀ x : Gn g (a + b), ∃! σ, σ ∈ R ∧ ∃ h ∈ U, ∃ k ∈ P, x = h * pm g σ * k := by
    intro x
    obtain ⟨σ, ⟨hσ, u, p, hu, hp, hx⟩, huniq⟩ :=
      Shuffle.existsUnique_shuffle g a (a + b) (Nat.le_add_right a b) x
    refine ⟨σ, ⟨by simpa [hR] using hσ, u, (hU u).2 hu, p, (hP p).2 hp, hx⟩, ?_⟩
    rintro τ ⟨hτ, u', hu', p', hp', hx'⟩
    exact huniq τ ⟨by simpa [hR] using hτ, u', p', (hU u').1 hu', (hP p').1 hp', hx'⟩
  have M := mackey_doubleCoset_pairing (Gn g (a + b)) U P _ R (pm g) hRu
    (fun x : Gn g (a + b) => (ψ (supFrom 0 (x : Mt g (a + b))))⁻¹)
    (fun z : Gn g (a + b) => Φ (toG (tl a (z : Mt g (a + b)))) (toG (br a b (z : Mt g (a + b))))) hl hφ
  have cU : (Nat.card U : ℂ) = ((Finset.univ.filter fun u : Gn g (a + b) => IsUniUp (u : Mt g (a + b))).card : ℂ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [hU]
  have cP : (Nat.card P : ℂ) = ((Finset.univ.filter fun p : Gn g (a + b) => InPar a (p : Mt g (a + b))).card : ℂ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    simp only [hP]
  refine Eq.trans ?_ (M.trans ?_)
  · rw [OpenCell.wh_eq, cU, cP, ← Finset.sum_filter]
    simp only [hU, hP]
    rfl
  obtain ⟨σ₀, h0⟩ : ∃ σ₀ : Equiv.Perm (Fin (a + b)),
      ∀ j : Fin (a + b), (σ₀ j : ℕ) = if (j : ℕ) < a then b + j else j - a := by
    let f : Fin (a + b) → Fin (a + b) := fun j =>
      ⟨if (j : ℕ) < a then b + j else j - a, by have := j.2; split_ifs <;> omega⟩
    have hf : Function.Injective f := by
      intro i j h
      have := i.2
      have := j.2
      simp only [f, Fin.mk.injEq] at h
      ext
      split_ifs at h <;> omega
    exact ⟨Equiv.ofBijective f hf.bijective_of_finite, fun j => rfl⟩
  have h0R : σ₀ ∈ R := by
    simp only [hR, Finset.mem_filter, Finset.mem_univ, true_and]
    intro i j hij hb
    rw [Fin.lt_def] at hij ⊢
    rw [h0, h0]
    split_ifs <;> omega
  rw [Finset.sum_eq_single_of_mem σ₀ h0R]
  · simp only [hU, hP]
    exact OpenCell.openCell g ψ a b (a + b) σ₀ Φ rfl h0
  · intro σ hσ hne
    have hσ' : ∀ i j : Fin (a + b), i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j := by
      simpa [hR] using hσ
    have hnd : ¬ ∀ i j : Fin (a + b), (i : ℕ) < a → a ≤ (j : ℕ) → (σ j : ℕ) ≠ σ i + 1 := by
      intro h
      apply hne
      exact Equiv.ext fun j => Fin.ext (by rw [(shuffle_noDescent_iff_open a b (a + b) σ rfl hσ').1 h j, h0 j])
    push Not at hnd
    obtain ⟨i, j, hi, hj, hij⟩ := hnd
    simp only [hU, hP]
    rw [NonOpenCell.whittaker_term_eq_zero g ψ hψ a b (a + b) σ Φ i j rfl hi hj hij, mul_zero]

end GlobalTheory.GLq.WhMul
end

