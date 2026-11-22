import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0001
import Formalism.LocalToGlobal.Columns.HeckeSp
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0039
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.FormalDegreeBessel.StatementDS
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0065
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0031
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0040

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BlockDetLowUEmb
section
noncomputable section

open ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition

namespace GlobalTheory.LowerHecke

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D]

def lowU (ν : Matrix D A k) : GL (A ⊕ D) k where
  val := fromBlocks 1 0 ν 1
  inv := fromBlocks 1 0 (-ν) 1
  val_inv := by rw [fromBlocks_multiply]; simp
  inv_val := by rw [fromBlocks_multiply]; simp

theorem val_lowU (ν : Matrix D A k) : (lowU ν).1 = fromBlocks 1 0 ν 1 := rfl

open Classical in

def blockDet (j : GL (A ⊕ D) k) : kˣ :=
  if h : j.1.toBlocks₂₂.det ≠ 0 then Units.mk0 _ h else 1

theorem val_emb_one (m : GL D k) :
    (emb₂ k (Equiv.refl (A ⊕ D)) (1, m)).1 = fromBlocks 1 0 0 m.1 := by
  rw [val_emb₂]; simp

theorem blockDet_lowU_emb (ν : Matrix D A k) (m : GL D k) :
    blockDet (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, m)) = GeneralLinearGroup.det m := by
  have h : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, m)).1.toBlocks₂₂ = m.1 := by
    rw [Units.val_mul, val_emb_one, val_lowU, fromBlocks_multiply]; simp
  have h0 : (lowU ν * emb₂ k (Equiv.refl (A ⊕ D)) (1, m)).1.toBlocks₂₂.det ≠ 0 := by
    rw [h]; exact (GeneralLinearGroup.det m).ne_zero
  rw [blockDet, dif_pos h0]; ext; rw [Units.val_mk0, h, GeneralLinearGroup.val_det_apply]

theorem emb_mul_lowU (m : GL D k) (ν : Matrix D A k) :
    emb₂ k (Equiv.refl (A ⊕ D)) (1, m) * lowU ν = lowU (m.1 * ν) * emb₂ k (Equiv.refl (A ⊕ D)) (1, m) := by
  ext1
  rw [Units.val_mul, Units.val_mul, val_emb_one, val_lowU, val_lowU, fromBlocks_multiply, fromBlocks_multiply]
  simp

theorem emb_mul_emb (m m' : GL D k) :
    emb₂ k (Equiv.refl (A ⊕ D)) (1, m) * emb₂ k (Equiv.refl (A ⊕ D)) (1, m') =
      emb₂ k (Equiv.refl (A ⊕ D)) (1, m * m') := by
  rw [← map_mul]; simp

theorem mtor_eq (ϖ : kˣ) (e : D → ℤ) :
    (mtor ϖ e : GL (A ⊕ D) k) = emb₂ k (Equiv.refl (A ⊕ D)) (1, torusElt k D ϖ e) := by
  ext1
  rw [val_emb_one, mtor, val_torusElt, val_torusElt]
  ext (i | i) (j | j) <;> simp [diagonal_apply, Matrix.one_apply]

theorem inv_lowU (ν : Matrix D A k) : (lowU ν)⁻¹ = lowU (-ν) := Units.ext rfl

theorem lowU_mem {ν : Matrix D A k} (h : ∀ i a, valuation k (ν i a) < 1) : lowU ν ∈ parahoric k A D := by
  rw [mem_parahoric, GlobalTheory.StepData.mem_KO]
  refine ⟨⟨?_, ?_⟩, fun i j => by simpa [val_lowU] using h i j⟩
  · rintro (i | i) (j | j) <;> simp only [val_lowU, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply]
    · split_ifs <;> simp
    · exact zero_mem _
    · exact (h i j).le
    · split_ifs <;> simp
  · rw [inv_lowU]
    rintro (i | i) (j | j) <;> simp only [val_lowU, fromBlocks_apply₁₁, fromBlocks_apply₁₂,
      fromBlocks_apply₂₁, fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply, Matrix.neg_apply]
    · split_ifs <;> simp
    · exact zero_mem _
    · exact neg_mem (h i j).le
    · split_ifs <;> simp

theorem emb_mem {κ : GL D k} (h : κ ∈ KO k D) : emb₂ k (Equiv.refl (A ⊕ D)) (1, κ) ∈ parahoric k A D := by
  rw [mem_parahoric, GlobalTheory.StepData.mem_KO]
  obtain ⟨h1, h2⟩ := GlobalTheory.StepData.mem_KO.1 h
  have hinv : (emb₂ k (Equiv.refl (A ⊕ D)) (1, κ))⁻¹ = emb₂ k (Equiv.refl (A ⊕ D)) (1, κ⁻¹) := by
    rw [← map_inv]; simp
  refine ⟨⟨?_, ?_⟩, fun i j => by simp [val_emb_one]⟩
  · rintro (i | i) (j | j) <;> simp only [val_emb_one, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply]
    · split_ifs <;> simp
    · exact zero_mem _
    · exact zero_mem _
    · exact h1 i j
  · rw [hinv]
    rintro (i | i) (j | j) <;> simp only [val_emb_one, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
      fromBlocks_apply₂₂, Matrix.one_apply, Matrix.zero_apply]
    · split_ifs <;> simp
    · exact zero_mem _
    · exact zero_mem _
    · exact h2 i j

variable (k D) in

def mLat : AddSubgroup (D → k) where
  carrier := {v | ∀ i, valuation k (v i) < 1}
  add_mem' ha hb i := by simpa using Valuation.map_add_lt _ (ha i) (hb i)
  zero_mem' i := by simp
  neg_mem' ha i := by simpa using ha i

def preLat (m : Matrix D D k) : AddSubgroup (D → k) := (mLat k D).comap (Matrix.mulVecLin m).toAddMonoidHom

theorem mem_mLat {v : D → k} : v ∈ mLat k D ↔ ∀ i, valuation k (v i) < 1 := Iff.rfl

theorem mem_preLat {m : Matrix D D k} {v : D → k} : v ∈ preLat m ↔ m.mulVec v ∈ mLat k D := Iff.rfl

end GlobalTheory.LowerHecke

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsParahoricAndIntegralGLDoubleCosetReps
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection
  GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

namespace GlobalTheory.ParHeckeReps

theorem exists_reps_both : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (A D : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D],
    (∀ g : GL (A ⊕ D) k, ∃ R d, IsReps g R d) ∧ ∀ g : GL D k, ∃ R, IsRepsK g R :=
  fun _ _ _ _ _ _ _ _ _ _ _ => ⟨fun g => Model.exists_isReps g, fun g => Model.exists_isRepsK g⟩

end GlobalTheory.ParHeckeReps
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsUnitSolutionTwistedFrobeniusSquareStatement
section
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_solution_twisted_frobenius_square : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] [CompleteSpace K] (l : ℕ) (σ : K →+* K), Unr K l σ → ResAlg K → ∀ c : K, ‖c‖ = 1 → ∃ ε : K, ‖ε‖ = 1 ∧ ε = c * (σ ^ 2) ε := by
  first | exact @GlobalTheory.Honda.unit_solution_twisted_frobenius | exact GlobalTheory.Honda.unit_solution_twisted_frobenius | (intros; apply GlobalTheory.Honda.unit_solution_twisted_frobenius <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FdegHCRowsMulSuperfactorialLeVandermonde
section
open Formalism.BasicNotions

namespace GlobalTheory.FdegRowsBound

open Finset

theorem pairs_append {p q : ℕ} (g : Fin (p + q) → Fin (p + q) → ℝ) :
    ∏ a : Fin (p + q), ∏ b ∈ univ.filter (fun b => a < b), g a b =
      (∏ i : Fin p, ∏ j ∈ univ.filter (fun j => i < j), g (Fin.castAdd q i) (Fin.castAdd q j)) *
      (∏ i : Fin p, ∏ j : Fin q, g (Fin.castAdd q i) (Fin.natAdd p j)) *
      (∏ i : Fin q, ∏ j ∈ univ.filter (fun j => i < j), g (Fin.natAdd p i) (Fin.natAdd p j)) := by
  simp only [Finset.prod_filter, Fin.prod_univ_add, Fin.lt_def, Fin.coe_castAdd, Fin.coe_natAdd]
  have h1 : ∀ (i : Fin p) (j : Fin q), (i : ℕ) < p + (j : ℕ) := fun i j => by omega
  have h2 : ∀ (i : Fin q) (j : Fin p), ¬ p + (i : ℕ) < (j : ℕ) := fun i j => by omega
  have h3 : ∀ (i j : Fin q), (p + (i : ℕ) < p + (j : ℕ)) ↔ ((i : ℕ) < (j : ℕ)) := fun i j => by omega
  simp only [h1, h2, h3, if_true, if_false, Finset.prod_const_one, mul_one, one_mul, Finset.prod_mul_distrib]

theorem pairs_cast {n n' : ℕ} (h : n = n') (f : Fin n' → Fin n' → ℝ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b => a < b), f (Fin.cast h a) (Fin.cast h b) =
      ∏ a : Fin n', ∏ b ∈ univ.filter (fun b => a < b), f a b := by
  subst h; rfl

theorem den_eq (n : ℕ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), (((b : ℕ) : ℝ) - ((a : ℕ) : ℝ)) =
      Formalism.MainNotions.StandardLattice.facProd n := by
  unfold Formalism.MainNotions.StandardLattice.facProd
  rcases n with _ | m
  · simp
  have h := Matrix.det_vandermonde_id_eq_superFactorial (R := ℝ) m
  rw [Matrix.det_vandermonde, ← Nat.prod_range_succ_factorial, Nat.cast_prod] at h
  simp only [Finset.filter_lt_eq_Ioi]
  rw [← h]

theorem facProd_pos (n : ℕ) : 0 < Formalism.MainNotions.StandardLattice.facProd n := by
  unfold Formalism.MainNotions.StandardLattice.facProd
  exact Finset.prod_pos fun i _ => by exact_mod_cast Nat.factorial_pos i

theorem anti_of {K n : ℕ} (hn : K + 1 = n) (u : Fin n → ℚ) (v : Fin K → ℚ)
    (h1 : ∀ i : Fin K, v i < u ⟨i.1, by omega⟩) (h2 : ∀ i : Fin K, u ⟨i.1 + 1, by omega⟩ < v i) :
    StrictAnti u := by
  subst hn
  exact Fin.strictAnti_iff_succ_lt.2 fun i => (h2 i).trans (h1 i)

theorem mono_of {m : ℕ} (f : Fin m → ℚ) (h : ∀ j : Fin m, ∀ hj : j.1 + 1 < m, f j < f ⟨j.1 + 1, hj⟩) :
    StrictMono f := by
  rcases m with _ | m
  · exact fun a => a.elim0
  · exact Fin.strictMono_iff_lt_succ.2 fun i => h (Fin.castSucc i) (by simp)

theorem vand_cast {K : ℕ} (u : Fin (K + 1) → ℝ) :
    Formalism.MainNotions.StandardLattice.vand u = ∏ i : Fin K, ∏ j : Fin K,
      (if i ≤ j then u (Fin.castSucc i) - u (Fin.succ j) else 1) := by
  unfold Formalism.MainNotions.StandardLattice.vand
  rw [Fin.prod_univ_castSucc]
  have hlast : ∏ b ∈ univ.filter (fun b => Fin.last K < b), (u (Fin.last K) - u b) = 1 := by
    apply Finset.prod_eq_one
    intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    exact absurd hb (not_lt.2 (Fin.le_last b))
  rw [hlast, mul_one]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Finset.prod_filter, Fin.prod_univ_succ]
  simp [Fin.castSucc_lt_succ_iff]

theorem interlace_bound {K n : ℕ} (hn : K + 1 = n) (u : Fin n → ℝ) (v : Fin K → ℝ)
    (h1 : ∀ i : Fin K, v i < u ⟨i.1, by omega⟩) (h2 : ∀ i : Fin K, u ⟨i.1 + 1, by omega⟩ < v i)
    (h3 : ∀ i : Fin K, 1 ≤ u ⟨i.1, by omega⟩ - u ⟨i.1 + 1, by omega⟩) :
    ∏ a : Fin K, ∏ b ∈ univ.filter (fun b => a < b), |v a - v b| ≤ Formalism.MainNotions.StandardLattice.vand u := by
  subst hn
  have hu : StrictAnti u := Fin.strictAnti_iff_succ_lt.2 fun i => (h2 i).trans (h1 i)
  rw [vand_cast]
  simp only [Finset.prod_filter]
  apply Finset.prod_le_prod
  · intro i _
    exact Finset.prod_nonneg fun j _ => by split_ifs <;> positivity
  intro i _
  apply Finset.prod_le_prod
  · intro j _; split_ifs <;> positivity
  intro j _
  by_cases hij : i < j
  · have hle : i ≤ j := hij.le
    simp only [hij, hle, if_true]
    have hsj : Fin.succ i ≤ Fin.castSucc j := by
      rw [Fin.le_def]; simp only [Fin.val_succ, Fin.coe_castSucc]; exact hij
    have a1 := h1 i
    have a2 := h2 j
    have a3 := h1 j
    have a4 := h2 i
    have a5 := hu.antitone hsj
    have e1 : u ⟨i.1, by omega⟩ = u (Fin.castSucc i) := rfl
    have e2 : u ⟨j.1 + 1, by omega⟩ = u (Fin.succ j) := rfl
    have e3 : u ⟨j.1, by omega⟩ = u (Fin.castSucc j) := rfl
    have e4 : u ⟨i.1 + 1, by omega⟩ = u (Fin.succ i) := rfl
    rw [abs_of_pos (by linarith)]
    linarith
  · simp only [hij, if_false]
    by_cases hle : i ≤ j
    · have : i = j := le_antisymm hle (not_lt.1 hij)
      subst this
      simp only [hle, if_true]
      exact h3 i
    · simp [hle]

theorem lamSH_congr (R : Ranks) (P Q : HCParam R) (hv : Q.v = P.v) (hb : Q.b = P.b) :
    Formalism.MainNotions.S.lamSH R P = Formalism.MainNotions.S.lamSH R Q := by
  unfold Formalism.MainNotions.S.lamSH Formalism.MainNotions.S.lamS; rw [hv, hb]

theorem lamS_left (R : Ranks) (P : HCParam R) (h : (R.k - 1) + R.m = R.r) (i : Fin (R.k - 1)) :
    Formalism.MainNotions.S.lamS R P (Fin.cast h (Fin.castAdd R.m i)) = (P.v i : ℝ) := by
  simp [Formalism.MainNotions.S.lamS]

theorem lamS_right (R : Ranks) (P : HCParam R) (h : (R.k - 1) + R.m = R.r) (j : Fin R.m) :
    Formalism.MainNotions.S.lamS R P (Fin.cast h (Fin.natAdd (R.k - 1) j)) = -(P.b j : ℝ) := by
  simp [Formalism.MainNotions.S.lamS]

theorem count_pairs (m : ℕ) :
    ∑ j : Fin m, (univ.filter (fun j' : Fin m => j < j')).card = m * (m - 1) / 2 := by
  simp only [Finset.filter_lt_eq_Ioi, Fin.card_Ioi]
  rw [Fin.sum_univ_eq_sum_range (fun i => m - 1 - i) m, Finset.sum_range_reflect (fun i => i) m]
  exact Finset.sum_range_id m

theorem fdeg_rows_le : ∀ (R : Ranks) (P Q : HCParam R), Q.v = P.v → Q.b = P.b → ∀ B : ℝ, 1 ≤ B →
    (∀ i j, ((P.v i : ℚ) : ℝ) + ((P.b j : ℚ) : ℝ) ≤ B) →
    (∀ j j', ((P.b j' : ℚ) : ℝ) - ((P.b j : ℚ) : ℝ) ≤ B) →
    Formalism.QuantumDeterminants.fdegHC (Formalism.MainNotions.S.lamSH R P) * Formalism.MainNotions.StandardLattice.facProd R.r ≤
      B ^ ((R.k - 1) * R.m + R.m * (R.m - 1) / 2) * Formalism.MainNotions.StandardLattice.vand (fun i => ((Q.u i : ℚ) : ℝ)) := by
  intro R P Q hv hb B hB1 hvb hbb
  rw [lamSH_congr R P Q hv hb]
  rw [← hv, ← hb] at hvb
  rw [← hb] at hbb
  have hk := R.m_add_three_le_k
  have hm2 := R.two_le_m
  have hr : (R.k - 1) + R.m = R.r := by simp only [Ranks.r]; omega
  have huanti : StrictAnti Q.u := anti_of (by omega : R.k - 1 + 1 = R.k) Q.u Q.v Q.u_gt_v Q.v_gt_u
  have hbmono : StrictMono Q.b := mono_of Q.b fun j hj => by
    have a1 := Q.gap_be j
    have a2 := Q.gap_eb j hj
    have : (0:ℚ) ≤ R.t := by positivity
    linarith
  have hpos : ∀ i j, 0 < ((Q.v i : ℚ) : ℝ) + ((Q.b j : ℚ) : ℝ) := by
    intro i j
    have a1 := Q.v_gt_u i
    have a2 : Q.u ⟨R.k - 1, by omega⟩ ≤ Q.u ⟨i.1 + 1, by omega⟩ :=
      huanti.antitone (by rw [Fin.le_def]; simp only; omega)
    have a3 := Q.u_last_gt (by omega) (by omega)
    have a4 : Q.b ⟨0, by omega⟩ ≤ Q.b j := hbmono.monotone (by rw [Fin.le_def]; simp)
    have : (0:ℚ) < Q.v i + Q.b j := by linarith
    exact_mod_cast this
  have h3 : ∀ i : Fin (R.k - 1), (1:ℝ) ≤ ((Q.u ⟨i.1, by omega⟩ : ℚ) : ℝ) - ((Q.u ⟨i.1 + 1, by omega⟩ : ℚ) : ℝ) := by
    intro i
    obtain ⟨z, hz⟩ := Q.u_half ⟨i.1, by omega⟩
    obtain ⟨z', hz'⟩ := Q.u_half ⟨i.1 + 1, by omega⟩
    have a := (Q.v_gt_u i).trans (Q.u_gt_v i)
    rw [hz, hz'] at a
    have b1 : z' < z := by exact_mod_cast (by linarith : (z':ℚ) < z)
    have b2 : (z':ℚ) + 1 ≤ z := by exact_mod_cast b1
    have : (1:ℚ) ≤ Q.u ⟨i.1, by omega⟩ - Q.u ⟨i.1 + 1, by omega⟩ := by rw [hz, hz']; linarith
    exact_mod_cast this
  have hden := den_eq (2 * R.rS + R.k + 1)
  have hfp : Formalism.MainNotions.StandardLattice.facProd (2 * R.rS + R.k + 1) = Formalism.MainNotions.StandardLattice.facProd R.r := by rw [Formalism.MainNotions.S.dimS_eq]
  unfold Formalism.QuantumDeterminants.fdegHC
  rw [hden, hfp, div_mul_cancel₀ _ (facProd_pos _).ne']
  unfold Formalism.MainNotions.S.lamSH
  have e1 := pairs_cast (Formalism.MainNotions.S.dimS_eq R) (fun a b => |Formalism.MainNotions.S.lamS R Q a - Formalism.MainNotions.S.lamS R Q b|)
  have e2 := pairs_cast hr (fun a b => |Formalism.MainNotions.S.lamS R Q a - Formalism.MainNotions.S.lamS R Q b|)
  beta_reduce at e1 e2
  rw [e1, ← e2, pairs_append]
  simp only [lamS_left, lamS_right]
  have hA : ∏ i : Fin (R.k - 1), ∏ j ∈ univ.filter (fun j => i < j),
      |((Q.v i : ℚ) : ℝ) - ((Q.v j : ℚ) : ℝ)| ≤ Formalism.MainNotions.StandardLattice.vand (fun i => ((Q.u i : ℚ) : ℝ)) :=
    interlace_bound (by omega : R.k - 1 + 1 = R.k) (fun i => ((Q.u i : ℚ) : ℝ)) (fun i => ((Q.v i : ℚ) : ℝ))
      (fun i => by exact_mod_cast Q.u_gt_v i) (fun i => by exact_mod_cast Q.v_gt_u i) h3
  have hC : ∏ i : Fin (R.k - 1), ∏ j : Fin R.m, |((Q.v i : ℚ) : ℝ) - -((Q.b j : ℚ) : ℝ)| ≤
      B ^ ((R.k - 1) * R.m) := by
    calc _ ≤ ∏ i : Fin (R.k - 1), ∏ j : Fin R.m, B :=
          Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _)
            (fun i _ => Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j _ => by
              rw [sub_neg_eq_add, abs_of_pos (hpos i j)]; exact hvb i j))
      _ = B ^ ((R.k - 1) * R.m) := by
          simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul, mul_comm]
  have hD : ∏ i : Fin R.m, ∏ j ∈ univ.filter (fun j => i < j),
      |-((Q.b i : ℚ) : ℝ) - -((Q.b j : ℚ) : ℝ)| ≤ B ^ (R.m * (R.m - 1) / 2) := by
    calc _ ≤ ∏ i : Fin R.m, ∏ j ∈ univ.filter (fun j => i < j), B :=
          Finset.prod_le_prod (fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _)
            (fun i _ => Finset.prod_le_prod (fun j _ => abs_nonneg _) (fun j hj => by
              simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
              have c1 : ((Q.b i : ℚ) : ℝ) < ((Q.b j : ℚ) : ℝ) := by exact_mod_cast hbmono hj
              have c2 := hbb i j
              rw [abs_le]; constructor <;> linarith))
      _ = ∏ i : Fin R.m, B ^ (univ.filter (fun j => i < j)).card := by
          simp only [Finset.prod_const]
      _ = B ^ (∑ i : Fin R.m, (univ.filter (fun j => i < j)).card) := Finset.prod_pow_eq_pow_sum _ _ _
      _ = B ^ (R.m * (R.m - 1) / 2) := by rw [count_pairs]
  have nA : 0 ≤ ∏ i : Fin (R.k - 1), ∏ j ∈ univ.filter (fun j => i < j),
      |((Q.v i : ℚ) : ℝ) - ((Q.v j : ℚ) : ℝ)| :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _
  have nC : 0 ≤ ∏ i : Fin (R.k - 1), ∏ j : Fin R.m, |((Q.v i : ℚ) : ℝ) - -((Q.b j : ℚ) : ℝ)| :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _
  have nD : 0 ≤ ∏ i : Fin R.m, ∏ j ∈ univ.filter (fun j => i < j),
      |-((Q.b i : ℚ) : ℝ) - -((Q.b j : ℚ) : ℝ)| :=
    Finset.prod_nonneg fun i _ => Finset.prod_nonneg fun j _ => abs_nonneg _
  have hB0 : (0:ℝ) ≤ B := by linarith
  calc _ ≤ Formalism.MainNotions.StandardLattice.vand (fun i => ((Q.u i : ℚ) : ℝ)) * B ^ ((R.k - 1) * R.m) * B ^ (R.m * (R.m - 1) / 2) :=
        mul_le_mul (mul_le_mul hA hC nC (nA.trans hA)) hD nD
          (mul_nonneg (nA.trans hA) (pow_nonneg hB0 _))
    _ = _ := by rw [pow_add]; ring

end GlobalTheory.FdegRowsBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatMapFourierJacobiFactorsLocalFlat
section
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData

noncomputable section

namespace GlobalTheory.FlatFactor

theorem ch_add_mat {k : Type} [Field k] {n n' : Type} {c : ℕ} (a b : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :
    ch (a + b) = ch a + ch b := by
  simp [ch, Finset.sum_add_distrib]

theorem continuous_ch {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] {n n' : Type} {c : ℕ} :
    Continuous (ch : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → k) :=
  continuous_finset_sum _ fun i _ => continuous_id.matrix_elem _ _

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k] {m m' : Type} [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']

theorem kerRed_empty {M : Type} [AddCommGroup M] [Module ℂ M] (ν : Measure k) (β : Matrix m m' k)
    (l : SB (Matrix m m' k) →ₗ[ℂ] M) : KerRed ν ∅ ∅ β l := by
  intro Θ h
  have hΘ : Θ = 0 := by
    ext t
    have ht := h t
    simp only [red] at ht
    haveI : IsEmpty {e : m × m' // e ∈ (∅ : Finset (m × m'))} := ⟨fun e => Finset.notMem_empty _ e.2⟩
    rw [Measure.pi_of_empty (x := isEmptyElim), integral_dirac] at ht
    have hf : fill ∅ ∅ β t isEmptyElim = t := by ext r q; simp [fill]
    rw [hf] at ht
    simpa using ht
  rw [hΘ, map_zero]

theorem mem_SB_addChar_mul (ψ : AddChar k Circle) (hψ : Continuous ψ) {X : Type} [TopologicalSpace X]
    (f : X → k) (hf : Continuous f) (Θ : X → ℂ) (hΘ : Θ ∈ SB X) :
    (fun t => (ψ (f t) : ℂ) * Θ t) ∈ SB X :=
  ⟨((GlobalTheory.RootEx.OpenKernel.isLocallyConstant_coe_addChar ψ hψ).comp_continuous hf).mul hΘ.1,
    hΘ.2.mul_left⟩

end

end GlobalTheory.FlatFactor

open GlobalTheory.FlatFactor in
theorem GlobalTheory.FlatFactor.flCol_factor : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k), Continuous ψ → ψ ≠ 1 → ν.IsAddHaarMeasure → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c ρ : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (L : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) →ₗ[ℂ] M), c = 2 * ρ → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ i, q = Sum.inr i ∧ i.val < ρ ∧ ¬ Free (ρ + 1) (r, q)) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), (∃ l, r = Sum.inr l ∧ ρ ≤ l.val ∧ ∀ i, q = Sum.inr i → i.val = ρ) → ∀ (b : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = (ψ (b * (t r q - basePt c (0 : Matrix n n' k) r q)) : ℂ) * Φ.1 t) → L Φ' = L Φ) → (∀ (r : n ⊕ Fin c) (q : n' ⊕ Fin (c + 1)), Free (ρ + 1) (r, q) → (∀ i, q = Sum.inr i → ρ ≤ i.val) → ∀ (a : k) (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (t + Matrix.single r q a)) → L Φ' = (ψ (ch (Matrix.single r q a)) : ℂ) • L Φ) → (∀ u : GL (Fin c) k, embA n u ∈ N k n c (ρ + 1) → (∀ l l' : Fin c, l.val < ρ → ρ ≤ l'.val → u.val l l' = 0) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → L Φ' = (ψ (-simpleSum (embA n u)) : ℂ) • L Φ) → ∃ L₀ : SB (Matrix n (n' ⊕ Unit) k) →ₗ[ℂ] M, ∀ Φ Ψ, Ψ.1 = GlobalTheory.LocFlat.flCol ψ ν (ρ + 1) Φ.1 → L Φ = L₀ Ψ := by
  intro k _ _ _ _ _ _ ψ ν hψc hψ1 hν n n' _ _ _ _ c ρ M _ _ L hc H1 H2 H3 H4
  set Mt := Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k
  set β : Mt := basePt c (0 : Matrix n n' k)
  have tw : ∀ (f : Mt → k), Continuous f → ∀ Θ : SB Mt, (fun t => (ψ (f t) : ℂ) * Θ.1 t) ∈ SB Mt :=
    fun f hf Θ => mem_SB_addChar_mul ψ hψc f hf Θ.1 Θ.2
  let T : SB Mt → SB Mt := fun Θ => ⟨fun t => (ψ (ch t) : ℂ) * Θ.1 t, tw _ continuous_ch Θ⟩
  let L' : SB Mt →ₗ[ℂ] M :=
    { toFun := fun Θ => L (T Θ)
      map_add' := fun Θ₁ Θ₂ => by
        show L (T (Θ₁ + Θ₂)) = L (T Θ₁) + L (T Θ₂)
        rw [← map_add]; congr 1; apply Subtype.ext; funext t
        show (ψ (ch t) : ℂ) * (Θ₁.1 t + Θ₂.1 t) = (ψ (ch t) : ℂ) * Θ₁.1 t + (ψ (ch t) : ℂ) * Θ₂.1 t
        ring
      map_smul' := fun a Θ => by
        show L (T (a • Θ)) = a • L (T Θ)
        rw [← map_smul]; congr 1; apply Subtype.ext; funext t
        show (ψ (ch t) : ℂ) * (a * Θ.1 t) = a * ((ψ (ch t) : ℂ) * Θ.1 t)
        ring }
  have hL' : ∀ Θ, L' Θ = L (T Θ) := fun _ => rfl

  have hTw : TwLaw ρ ψ L' := by
    intro u hN hblk Θ Θ' Θ'' h' h''
    rw [hL', hL']
    have := H4 u hN hblk (T Θ'') (T Θ') (fun t => by
      simp only [T, h', h'']
      rw [← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]
      rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul]
      congr 3; ring)
    exact this

  have hS1 : KerRed ν (evC n n' c ρ) (itB n n' c ρ) β L' := by
    refine GlobalTheory.T.kernelReduction_extend_evaluated_integrated k ψ ν hψc hψ1 hν _ _ M L' β ∅ ∅ _ _ (Finset.empty_subset _) (Finset.empty_subset _) ?_
      (kerRed_empty ν β L') ?_ ?_
    · rw [Finset.disjoint_left]
      rintro ⟨r, q⟩ h1 h2
      simp only [evC, itB, Finset.mem_filter, Finset.mem_univ, true_and] at h1 h2
      rcases h1 with ⟨i, hq, -, hfr⟩ | ⟨l, hr, hl, hq⟩
      · exact hfr h2.1
      · subst hr
        rcases q with q | q
        · simp [Free] at h2; omega
        · have := hq q rfl; simp [Free] at h2; omega
    · rintro ⟨r, q⟩ he - b Θ Θ' hΘ
      simp only [evC, Finset.mem_filter, Finset.mem_univ, true_and] at he
      rw [hL', hL']
      rcases he with he | he
      · exact H1 r q he b (T Θ) (T Θ') (fun t => by simp only [T, hΘ]; ring)
      · exact H2 r q he b (T Θ) (T Θ') (fun t => by simp only [T, hΘ]; ring)
    · rintro ⟨r, q⟩ he - a Θ Θ' hΘ
      simp only [itB, Finset.mem_filter, Finset.mem_univ, true_and] at he
      rw [hL', hL']
      set E : Mt := Matrix.single r q a
      let Φ' : SB Mt := ⟨fun t => (ψ (ch (t + E)) : ℂ) * Θ'.1 t, tw _ (continuous_ch.comp (continuous_add_right E)) Θ'⟩
      have h3 := H3 r q he.1 he.2 a (T Θ) Φ' (fun t => by
        show (ψ (ch (t + E)) : ℂ) * Θ'.1 t = (ψ (ch (t + E)) : ℂ) * Θ.1 (t + E)
        rw [hΘ])
      have hT : T Θ' = (ψ (-ch E) : ℂ) • Φ' := by
        ext t
        show (ψ (ch t) : ℂ) * Θ'.1 t = (ψ (-ch E) : ℂ) * ((ψ (ch (t + E)) : ℂ) * Θ'.1 t)
        have hm : ∀ x y : k, (ψ x : ℂ) * ψ y = ψ (x + y) := by
          intro x y; rw [AddChar.map_add_eq_mul, Circle.coe_mul]
        rw [← mul_assoc, hm, ch_add_mat, show -ch E + (ch t + ch E) = ch t by ring]
      rw [hT, map_smul, h3, smul_smul, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, neg_add_cancel,
        AddChar.map_zero_eq_one, Circle.coe_one, one_smul]
  have hS2 := GlobalTheory.T.flatFactorReduction_kernel_all_nonFreeUnread_entries k ψ ν hψc hψ1 hν n n' c ρ M L' hc hTw hS1
  have hS3 := GlobalTheory.T.flatFactorReduction_kernel_integrates_free_entries k ψ ν hψc hψ1 hν n n' c ρ M L' hc hTw hS2
  refine GlobalTheory.T.exists_factor_through_flatMapFourierJacobiColumn k ψ ν hψc hν n n' c (ρ + 1) (by omega) (by omega) M L ?_
  intro Φ hΦ
  let Θ : SB Mt := ⟨fun t => (ψ (-ch t) : ℂ) * Φ.1 t, tw _ continuous_ch.neg Φ⟩
  have hΘ : T Θ = Φ := by
    ext t
    simp only [T, Θ]
    rw [← mul_assoc, ← Circle.coe_mul, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one,
      Circle.coe_one, one_mul]
  have := hS3 Θ (GlobalTheory.T.partialReduction_eq_zero_of_flatMapColumn_zero k ψ ν n n' c ρ hc Φ.1 hΦ)
  rw [hL', hΘ] at this
  exact this
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeightTwoHondaTypeFirstCoeffNormEqOneStatement
section
open PowerSeries GlobalTheory.Honda
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_two_hondaType_first_coeff_norm_eq_one : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), IntLog f e → ∀ c : ℕ → K, (∀ j, ‖c j‖ ≤ 1) → CoefLe ‖(l : K)‖ (C (l : K) * f - hondaSum (σ ^ 2) (l ^ 2) c f) → (∃ n, n ≤ l ^ 2 ∧ ‖coeff n (Formalism.L2.Th1.C.mulBy f e (l : K))‖ = 1) → ‖c 0‖ = 1 := by
  first | exact @GlobalTheory.Honda.HeightTwo.norm_first_coeff_eq_one | exact GlobalTheory.Honda.HeightTwo.norm_first_coeff_eq_one | (intros; apply GlobalTheory.Honda.HeightTwo.norm_first_coeff_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HondaFunctionalEquationOneTermTypeStatement
section
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.honda_functional_equation_one_term_type : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CharZero K] (l : ℕ) (σ : K →+* K), Unr K l σ → ∀ (f e : K⟦X⟧), Formalism.L2.Th1.C.IsLogPair f e → ∀ c ε : K, ‖ε‖ = 1 → ε = c * (σ ^ 2) ε → CoefLe ‖(l : K)‖ (C (l : K) * f - C c * frobOp (σ ^ 2) (l ^ 2) 1 f) → CoefLe 1 (e.subst (C ε * ltLog K l)) := by
  first | exact @GlobalTheory.HondaFunEq.honda_funEq | exact GlobalTheory.HondaFunEq.honda_funEq | (intros; apply GlobalTheory.HondaFunEq.honda_funEq <;> assumption)
end

