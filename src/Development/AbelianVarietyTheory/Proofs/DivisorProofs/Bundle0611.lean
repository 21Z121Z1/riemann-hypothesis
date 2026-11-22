import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0601
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0597
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0605
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0018
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0602
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0585
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeStrictHenselisationRetractMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0599
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0586

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerateWhittakerDimParabolicInductionCuspidal
section
noncomputable section

namespace GlobalTheory.FinGL.WhCutInd

open GlobalTheory.FinGL Formalism.L2.DIV Module

variable {F : Type} [Field F] {r : ℕ}

def pm (F : Type) [Field F] (w : Equiv.Perm (Fin r)) : GL (Fin r) F where
  val := Matrix.of fun a c => if a = w c then 1 else 0
  inv := Matrix.of fun a c => if c = w a then 1 else 0
  val_inv := by
    ext a c
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (w.symm a)]
    · simp [eq_comm]
    · intro l _ hl
      rw [if_neg, zero_mul]
      rintro rfl
      exact hl (by simp)
    · simp
  inv_val := by
    ext a c
    simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single (w a)]
    · simp
    · intro l _ hl
      rw [if_neg hl, zero_mul]
    · simp

theorem pm_val (w : Equiv.Perm (Fin r)) (a c : Fin r) :
    (pm F w : Matrix (Fin r) (Fin r) F) a c = if a = w c then 1 else 0 := rfl

theorem pm_inv_val (w : Equiv.Perm (Fin r)) (a c : Fin r) :
    (((pm F w)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a c = if c = w a then 1 else 0 := rfl

theorem pm_conj (w' w : Equiv.Perm (Fin r)) (g : GL (Fin r) F) (a c : Fin r) :
    (((pm F w')⁻¹ * g * pm F w : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) a c =
      (g : Matrix (Fin r) (Fin r) F) (w' a) (w c) := by
  simp only [Units.val_mul, Matrix.mul_apply, pm_val, pm_inv_val]
  simp

theorem pm_mul_inv_mem {b : Fin r → ℕ} {w w' : Equiv.Perm (Fin r)} (h : ∀ c, b (w c) = b (w' c)) :
    pm F w * (pm F w')⁻¹ ∈ blockTri (κ := F) b := by
  rw [mem_blockTri]
  intro i k hik
  simp only [Units.val_mul, Matrix.mul_apply, pm_val, pm_inv_val]
  refine Finset.sum_eq_zero fun c _ => ?_
  split_ifs with h1 h2
  · subst h1 h2
    exact absurd (h c) hik.ne'
  all_goals simp

theorem unip_le {b : Fin r → ℕ} (hb : Monotone b) : unip F r ≤ blockTri (κ := F) b := by
  intro u hu
  rw [mem_blockTri]
  intro i k hik
  exact unip_lower hu (hb.reflect_lt hik)

theorem exists_pm {b : Fin r → ℕ} (hb : Monotone b) (g : GL (Fin r) F) :
    ∃ w : Equiv.Perm (Fin r), ∃ p ∈ blockTri (κ := F) b, ∃ u ∈ unip F r, g = p * pm F w * u := by
  obtain ⟨⟨w, t⟩, ⟨u, hu, u', hu', e⟩, -⟩ := GlobalTheory.FinGL.Bruhat.bruhat F r g
  refine ⟨w, u * (u⁻¹ * g * u'⁻¹ * (pm F w)⁻¹), Subgroup.mul_mem _ (unip_le hb hu) ?_, u', hu', by group⟩
  have e1 : ((u⁻¹ * g * u'⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      Matrix.of fun a c => if a = w c then (t c : F) else 0 := by
    rw [Units.val_mul, Units.val_mul, e]
    simp only [← Matrix.mul_assoc]
    rw [Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [mem_blockTri]
  intro i k hik
  rw [Units.val_mul, e1]
  simp only [Matrix.mul_apply, pm_inv_val, Matrix.of_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  split_ifs with h1 h2
  · subst h1 h2
    exact absurd hik (lt_irrefl _)
  all_goals simp

theorem blk_eq_of_rel {b : Fin r → ℕ} {w w' : Equiv.Perm (Fin r)} {p u : GL (Fin r) F} (hp : p ∈ blockTri (κ := F) b)
    (hu : u ∈ unip F r) (e : p * pm F w = pm F w' * u) (c : Fin r) : b (w' c) = b (w c) := by
  have h1 : ∀ c, b (w' c) ≤ b (w c) := fun c => by
    by_contra hlt
    have h2 := pm_conj w' w p c c
    rw [mul_assoc, e, inv_mul_cancel_left, unip_diag hu, mem_blockTri.1 hp _ _ (not_le.1 hlt)] at h2
    exact one_ne_zero h2
  have h2 : ∑ c, b (w' c) = ∑ c, b (w c) := by
    rw [Equiv.sum_comp w' b, Equiv.sum_comp w b]
  exact (Finset.sum_eq_sum_iff_of_le fun c _ => h1 c).1 h2 c (Finset.mem_univ c)

def key (b : Fin r → ℕ) (J : Finset ℕ) (i : Fin r) : ℕ ×ₗ ℕᵒᵈ :=
  toLex (if b i ∈ J then 0 else 1, OrderDual.toDual (b i))

theorem key_le_iff (b : Fin r → ℕ) (J : Finset ℕ) (i k : Fin r) :
    key b J i ≤ key b J k ↔ (b i ∈ J ∧ b k ∉ J) ∨ ((b i ∈ J ↔ b k ∈ J) ∧ b k ≤ b i) := by
  unfold key
  rw [Prod.Lex.toLex_le_toLex]
  by_cases h1 : b i ∈ J <;> by_cases h2 : b k ∈ J <;> simp [h1, h2]

theorem key_eq_iff (b : Fin r → ℕ) (J : Finset ℕ) (i k : Fin r) : key b J i = key b J k ↔ b i = b k := by
  constructor
  · intro h
    exact congrArg (fun z => OrderDual.ofDual (ofLex z).2) h
  · intro h
    unfold key
    rw [h]

theorem sort_mem_iff (b : Fin r → ℕ) (J : Finset ℕ) (a : Fin r) :
    b (Tuple.sort (key b J) a) ∈ J ↔ a.val < (Finset.univ.filter fun i => b i ∈ J).card := by
  set w := Tuple.sort (key b J)
  have hm : Monotone fun a => if b (w a) ∈ J then 0 else 1 := fun a c hac => by
    have := (key_le_iff b J _ _).1 (Tuple.monotone_sort (key b J) hac)
    dsimp only
    split_ifs with h1 h2 h2 <;> first | omega | tauto
  have h := Tuple.lt_card_le_iff_apply_le_of_monotone (a := 0) (j := a) hm
  have hc : (Finset.univ.filter fun i => (if b (w i) ∈ J then 0 else 1) ≤ 0).card =
      (Finset.univ.filter fun i => b i ∈ J).card := by
    refine Finset.card_equiv w fun i => ?_
    by_cases h1 : b (w i) ∈ J <;> simp [h1]
  rw [hc] at h
  rw [h]
  by_cases h1 : b (w a) ∈ J <;> simp [h1]

theorem monotone_of_succ {α : Type} [Preorder α] (f : Fin r → α) (h : ∀ a c : Fin r, c.val = a.val + 1 → f a ≤ f c) :
    Monotone f := by
  cases r with
  | zero => intro a; exact a.elim0
  | succ n => exact Fin.monotone_iff_le_succ.2 fun i => h _ _ (by simp)

theorem exists_set (b : Fin r → ℕ) {j : ℕ} (hj : j ≤ r) (w : Equiv.Perm (Fin r))
    (h1 : ∀ a c : Fin r, cutEdge j a c → b (w c) ≤ b (w a))
    (h2 : ∀ a c : Fin r, a.val < j → j ≤ c.val → b (w a) ≠ b (w c)) :
    ∃ J ∈ (Finset.univ.image b).powerset.filter fun J => (Finset.univ.filter fun i => b i ∈ J).card = j,
      ∀ c, b (w c) = b (Tuple.sort (key b J) c) := by
  set J : Finset ℕ := (Finset.univ.filter fun a : Fin r => a.val < j).image fun a => b (w a) with hJ
  have hmem : ∀ c, b (w c) ∈ J ↔ c.val < j := fun c => by
    simp only [hJ, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨a, ha, e⟩
      by_contra hc
      exact h2 a c ha (not_lt.1 hc) e
    · exact fun hc => ⟨c, hc, rfl⟩
  refine ⟨J, ?_, fun c => ?_⟩
  · rw [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · intro z hz
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hz
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    · have : (Finset.univ.filter fun a : Fin r => a.val < j).card = (Finset.univ.filter fun i => b i ∈ J).card :=
        Finset.card_equiv w fun i => by simp [hmem]
      rw [← this, Fin.card_filter_val_lt]
      omega
  · have hm : Monotone (key b J ∘ w) := monotone_of_succ _ fun a c hac => by
      show key b J (w a) ≤ key b J (w c)
      rw [key_le_iff, hmem, hmem]
      by_cases h : a.val + 1 = j
      · left; omega
      · right; exact ⟨by omega, h1 a c ⟨hac, h⟩⟩
    exact (key_eq_iff b J _ _).1 (congrFun (Tuple.unique_monotone hm (Tuple.monotone_sort (key b J))) c)

theorem edgeSum_cut_mul (j : ℕ) {u u' : GL (Fin r) F} (hu : u ∈ unip F r) (hu' : u' ∈ unip F r) :
    edgeSum (cutEdge j) (u * u') = edgeSum (cutEdge j) u + edgeSum (cutEdge j) u' := by
  unfold edgeSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  split_ifs with h
  · have h' := h.1
    refine unip_mul_entry hu hu' (show a.val < c.val by omega) fun l h1 h2 => ?_
    have h1' : a.val < l.val := h1
    have h2' : l.val < c.val := h2
    omega
  · rw [add_zero]

theorem edgeSum_cut_one (j : ℕ) : edgeSum (cutEdge j) (1 : GL (Fin r) F) = 0 := by
  have := edgeSum_cut_mul (F := F) (r := r) j (Subgroup.one_mem _) (Subgroup.one_mem _)
  rw [mul_one] at this
  exact left_eq_add.1 this

theorem degenerateWhittakerDim_parabolicInduction (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (r : ℕ) (V : Type) [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ) (σ : Representation ℂ (blockTri (κ := F) b) V)
    (hσ : IsCuspDatum b σ) (j : ℕ) (hj : j < r ∨ j = 0) : whCut ψ (parInd b σ) j = splitDoublingNBlock b j * leviWh ψ b σ := by
  have hj' : j ≤ r := by omega
  set T := (Finset.univ.image b).powerset.filter fun J => (Finset.univ.filter fun i => b i ∈ J).card = j with hT
  have hmem : ∀ J : T, ∀ a, b (Tuple.sort (key b J.1) a) ∈ J.1 ↔ a.val < j := fun J a => by
    rw [sort_mem_iff, (Finset.mem_filter.1 J.2).2]
  have hsub : ∀ J J' : T, (∀ c, b (Tuple.sort (key b J.1) c) = b (Tuple.sort (key b J'.1) c)) → J.1 ⊆ J'.1 := by
    intro J J' h z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_powerset.1 (Finset.mem_filter.1 J.2).1 hz)
    obtain ⟨a, rfl⟩ := (Tuple.sort (key b J.1)).surjective i
    rw [h, hmem, ← hmem J]
    exact hz
  unfold whCut
  rw [GlobalTheory.T.finrank_eigen_coind_mackey_double_cosets (GL (Fin r) F) (blockTri b) (unip F r) V σ (fun g => ψ (edgeSum (cutEdge j) g))
    (by simp only [edgeSum_cut_one, AddChar.map_zero_eq_one])
    (fun u hu u' hu' => by simp only [edgeSum_cut_mul j hu hu', AddChar.map_add_eq_mul])
    T (fun J => pm F (Tuple.sort (key b J.1)))
    (fun J J' p hp u hu e => Subtype.ext (Finset.Subset.antisymm
      (hsub J J' fun c => (blk_eq_of_rel hp hu e c).symm) (hsub J' J (blk_eq_of_rel hp hu e)))) ?_]
  · rw [Finset.sum_congr rfl (g := fun _ => leviWh ψ b σ) fun J _ => ?_]
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_coe, smul_eq_mul]
      rfl
    · have hs := (Tuple.eq_sort_iff (f := key b J.1)).1 rfl
      unfold leviWh
      rw [GlobalTheory.T.coindEigen_sorting_perm_eq_levi_whittaker F ψ r V b σ hσ j (Tuple.sort (key b J.1)) _ (pm_conj _ _)]
      · exact fun a c hac e => hs.2 a c hac ((key_eq_iff b J.1 _ _).2 e)
      · intro a e c h1 h2 h3
        have h4 : key b J.1 _ ≤ key b J.1 _ := hs.1 h1
        have h5 : key b J.1 _ ≤ key b J.1 _ := hs.1 h2
        rw [← (key_eq_iff b J.1 _ _).2 h3] at h5
        exact (key_eq_iff b J.1 _ _).1 (le_antisymm h5 h4)
      · intro a c hac
        have h1 := hac.1
        have h2 := hac.2
        have h4 : key b J.1 _ ≤ key b J.1 _ := hs.1 (show a ≤ c from show a.val ≤ c.val by omega)
        rw [key_le_iff, hmem, hmem] at h4
        rcases h4 with h4 | h4
        · omega
        · exact h4.2
      · intro a c ha hc e
        have := (hmem J a).2 ha
        rw [e, hmem] at this
        omega
  · intro g
    obtain ⟨w, p, hp, u, hu, e⟩ := exists_pm hσ.mono g
    by_cases h1 : ∀ a c : Fin r, cutEdge j a c → b (w c) ≤ b (w a)
    · by_cases h2 : ∀ a c : Fin r, a.val < j → j ≤ c.val → b (w a) ≠ b (w c)
      · obtain ⟨J, hJ, h⟩ := exists_set b hj' w h1 h2
        refine Or.inl ⟨⟨J, hJ⟩, p * (pm F w * (pm F (Tuple.sort (key b J)))⁻¹),
          Subgroup.mul_mem _ hp (pm_mul_inv_mem h), u, hu, ?_⟩
        rw [e]
        group
      · push Not at h2
        obtain ⟨a, c, ha, hc, h⟩ := h2
        exact Or.inr ⟨pm F w, ⟨p, hp, u, hu, e⟩, GlobalTheory.T.coindEigen_eq_bot_of_block_cut_cuspidal F ψ r V b σ hσ j w _ (pm_conj _ _) a c ha hc h⟩
    · push Not at h1
      obtain ⟨a, c, hac, h⟩ := h1
      exact Or.inr ⟨pm F w, ⟨p, hp, u, hu, e⟩, GlobalTheory.T.coindEigen_eq_bot_of_root_in_unipotent_radical F ψ r V b σ hσ j w _ (pm_conj _ _) hψ a c hac h⟩

end GlobalTheory.FinGL.WhCutInd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualWeylHighestWeightRestrictionBlockDiagonal
section
open MvPolynomial Formalism.GradedWeylDivisibility TensorProduct

noncomputable section

namespace GlobalTheory.LeviCut

theorem resT_lpMinor_le (p q s : ℕ) (h1 : s ≤ p + q) (h2 : s ≤ p + q) (hs : s ≤ p) :
    resT ℚ p q (lpMinor ℚ s h1 h2) = lpMinor ℚ s hs hs ⊗ₜ[ℚ] (1 : MvPolynomial (Fin q × Fin q) ℚ) := by
  have key : lpMinor ℚ s hs hs ⊗ₜ[ℚ] (1 : MvPolynomial (Fin q × Fin q) ℚ) =
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) (B := MvPolynomial (Fin q × Fin q) ℚ))
        (lpMinor ℚ s hs hs) := rfl
  rw [key, lpMinor, lpMinor, AlgHom.map_det, AlgHom.map_det]
  congr 1
  ext i j
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
  have hi : (Fin.castLE h1 i : Fin (p + q)) = Fin.castAdd q (Fin.castLE hs i) := Fin.ext rfl
  have hj : (Fin.castLE h2 j : Fin (p + q)) = Fin.castAdd q (Fin.castLE hs j) := Fin.ext rfl
  rw [hi, hj, resT, aeval_X]
  simp [resVarT]

theorem resT_lpMinor_ge (p q u : ℕ) (h1 : p + u ≤ p + q) (h2 : p + u ≤ p + q) (hu : u ≤ q) :
    resT ℚ p q (lpMinor ℚ (p + u) h1 h2) = lpMinor ℚ p le_rfl le_rfl ⊗ₜ[ℚ] lpMinor ℚ u hu hu := by
  have key : lpMinor ℚ p le_rfl le_rfl ⊗ₜ[ℚ] lpMinor ℚ u hu hu =
      (Algebra.TensorProduct.includeLeft (R := ℚ) (S := ℚ) (B := MvPolynomial (Fin q × Fin q) ℚ))
        (lpMinor ℚ p le_rfl le_rfl) *
      (Algebra.TensorProduct.includeRight (R := ℚ) (A := MvPolynomial (Fin p × Fin p) ℚ))
        (lpMinor ℚ u hu hu) := by
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  rw [key, lpMinor, lpMinor, lpMinor, AlgHom.map_det, AlgHom.map_det, AlgHom.map_det,
    ← Matrix.det_submatrix_equiv_self finSumFinEquiv, ← Matrix.det_fromBlocks_zero₂₁ (B := 0)]
  congr 1
  ext (a | a) (b | b)
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₁, finSumFinEquiv_apply_left]
    have hi : (Fin.castLE h1 (Fin.castAdd u a) : Fin (p + q)) = Fin.castAdd q (Fin.castLE le_rfl a) := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.castAdd u b) : Fin (p + q)) = Fin.castAdd q (Fin.castLE le_rfl b) := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₁₂, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]
    have hi : (Fin.castLE h1 (Fin.castAdd u a) : Fin (p + q)) = Fin.castAdd q a := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.natAdd p b) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu b) := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₂₁, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.zero_apply]
    have hi : (Fin.castLE h1 (Fin.natAdd p a) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu a) := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.castAdd u b) : Fin (p + q)) = Fin.castAdd q b := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]
  · simp only [Matrix.submatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.fromBlocks_apply₂₂, finSumFinEquiv_apply_right]
    have hi : (Fin.castLE h1 (Fin.natAdd p a) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu a) := Fin.ext rfl
    have hj : (Fin.castLE h2 (Fin.natAdd p b) : Fin (p + q)) = Fin.natAdd p (Fin.castLE hu b) := Fin.ext rfl
    rw [hi, hj, resT, aeval_X]
    simp [resVarT]

theorem nuNext_natAdd (p q : ℕ) (ν : Fin (p + q) → ℕ) (j : Fin q) :
    nuNext ν (Fin.natAdd p j) = nuNext (fun j => ν (Fin.natAdd p j)) j := by
  unfold nuNext
  simp only [Fin.val_natAdd]
  split_ifs with h h' h'
  · congr 1
  · omega
  · omega
  · rfl

theorem nuNext_castAdd (p q : ℕ) (ν : Fin (p + q) → ℕ) (i : Fin p) (hi : (i : ℕ) + 1 < p) :
    nuNext ν (Fin.castAdd q i) = nuNext (fun i => ν (Fin.castAdd q i)) i := by
  unfold nuNext
  simp only [Fin.val_castAdd]
  rw [dif_pos (by omega), dif_pos hi]
  rfl

theorem sum_sub_nuNext (q : ℕ) (μ : Fin (q + 1) → ℕ) (hμ : Antitone μ) :
    ∑ j, (μ j - nuNext μ j) = μ 0 := by
  induction q with
  | zero => simp [nuNext]
  | succ q ih =>
    rw [Fin.sum_univ_succ]
    have h1 : ∀ j : Fin (q + 1), nuNext μ j.succ = nuNext (fun j => μ j.succ) j := by
      intro j
      unfold nuNext
      simp only [Fin.val_succ]
      split_ifs with h h' h' <;> first | omega | rfl
    simp_rw [h1]
    rw [ih (fun j => μ j.succ) (fun a b hab => hμ (Fin.succ_le_succ_iff.mpr hab))]
    have h0 : nuNext μ 0 = μ (Fin.succ 0) := by
      unfold nuNext; rw [dif_pos (by simp)]; rfl
    rw [h0]
    have := hμ (Fin.zero_le (Fin.succ 0 : Fin (q + 2)))
    omega

theorem resT_lpMinor_ge' (p q s u : ℕ) (h1 : s ≤ p + q) (h2 : s ≤ p + q) (hu : u ≤ q) (hs : s = p + u) :
    resT ℚ p q (lpMinor ℚ s h1 h2) = lpMinor ℚ p le_rfl le_rfl ⊗ₜ[ℚ] lpMinor ℚ u hu hu := by
  subst hs
  exact resT_lpMinor_ge p q u h1 h2 hu

theorem prod_tmul_prod {ι A B : Type} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]
    (s : Finset ι) (a : ι → A) (b : ι → B) :
    ∏ i ∈ s, (a i ⊗ₜ[ℚ] b i) = (∏ i ∈ s, a i) ⊗ₜ[ℚ] (∏ i ∈ s, b i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Algebra.TensorProduct.one_def]
  | insert x s hx ih => rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.prod_insert hx, ih,
      Algebra.TensorProduct.tmul_mul_tmul]

theorem hw_first (p q : ℕ) (ν : Fin (p + q) → ℕ) (hν : Antitone ν) :
    (∏ i : Fin p, lpMinor ℚ ((i : ℕ) + 1) (by omega) (by omega) ^
        (ν (Fin.castAdd q i) - nuNext ν (Fin.castAdd q i))) *
      lpMinor ℚ p le_rfl le_rfl ^ (∑ j : Fin q, (ν (Fin.natAdd p j) - nuNext ν (Fin.natAdd p j))) =
      hw ℚ le_rfl (fun i => ν (Fin.castAdd q i)) := by
  rcases p with _ | p
  · simp [hw, lpMinor, Matrix.det_isEmpty]
  · rw [hw, Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, mul_assoc]
    simp only [Fin.val_last]
    rw [← pow_add]
    congr 1
    · refine Finset.prod_congr rfl fun k _ => ?_
      rw [nuNext_castAdd (p + 1) q ν k.castSucc (by simp)]
    · have hl : nuNext (fun i => ν (Fin.castAdd q i)) (Fin.last p) = 0 := by
        unfold nuNext; rw [dif_neg (by simp)]
      rw [hl, Nat.sub_zero]
      congr 1
      simp_rw [nuNext_natAdd]
      rcases q with _ | q
      · simp [nuNext]
      · rw [sum_sub_nuNext q (fun j => ν (Fin.natAdd (p + 1) j))
          (fun a b hab => hν (by rw [Fin.le_def] at hab ⊢; simp only [Fin.val_natAdd]; omega))]
        have h0 : nuNext ν (Fin.castAdd (q + 1) (Fin.last p)) = ν (Fin.natAdd (p + 1) 0) := by
          unfold nuNext; rw [dif_pos (by simp <;> omega)]; congr 1
        have := hν (show Fin.castAdd (q + 1) (Fin.last p) ≤ Fin.natAdd (p + 1) 0 by
          simp [Fin.le_def])
        rw [h0]
        omega

theorem resHw_holds : ResHw := by
  intro p q ν hν
  rw [hw, map_prod, Fin.prod_univ_add]
  have e1 : ∀ i : Fin p, resT ℚ p q (lpMinor ℚ ((Fin.castAdd q i : ℕ) + 1) (by omega) (by omega) ^
      (ν (Fin.castAdd q i) - nuNext ν (Fin.castAdd q i))) =
      (lpMinor ℚ ((i : ℕ) + 1) (by omega) (by omega) ^ (ν (Fin.castAdd q i) - nuNext ν (Fin.castAdd q i))) ⊗ₜ[ℚ]
        (1 : MvPolynomial (Fin q × Fin q) ℚ) := by
    intro i
    rw [map_pow, resT_lpMinor_le p q _ _ _ (by simp <;> omega), Algebra.TensorProduct.tmul_pow, one_pow]
    rfl
  have e2 : ∀ j : Fin q, resT ℚ p q (lpMinor ℚ ((Fin.natAdd p j : ℕ) + 1) (by omega) (by omega) ^
      (ν (Fin.natAdd p j) - nuNext ν (Fin.natAdd p j))) =
      (lpMinor ℚ p le_rfl le_rfl ^ (ν (Fin.natAdd p j) - nuNext ν (Fin.natAdd p j))) ⊗ₜ[ℚ]
        (lpMinor ℚ ((j : ℕ) + 1) (by omega) (by omega) ^
          ((fun j => ν (Fin.natAdd p j)) j - nuNext (fun j => ν (Fin.natAdd p j)) j)) := by
    intro j
    rw [map_pow, resT_lpMinor_ge' p q _ ((j : ℕ) + 1) _ _ (by omega) (by simp <;> omega),
      Algebra.TensorProduct.tmul_pow, nuNext_natAdd]
  rw [Finset.prod_congr rfl fun i _ => e1 i, Finset.prod_congr rfl fun j _ => e2 j, prod_tmul_prod,
    prod_tmul_prod, Algebra.TensorProduct.tmul_mul_tmul, Finset.prod_const_one, one_mul,
    Finset.prod_pow_eq_pow_sum, hw_first p q ν hν]
  rfl

end GlobalTheory.LeviCut
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisensteinWeierstrassValuesLatticeTau
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open NumberField GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F
open GlobalTheory.CMVal GlobalTheory.HeckeGal
open ModularForm (E₄ E₆)

namespace GlobalTheory.WpFam.TauVal

theorem complex_div_pow_div_div_pow (a x k : ℂ) (n : ℕ) (hk : k ≠ 0) :
    a / k ^ n / (x / k) ^ n = a / x ^ n := by
  by_cases hx : x = 0
  · subst hx
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · simp [zero_pow h.ne']
  · rw [div_pow]; field_simp

theorem two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  simp [this, Complex.I_ne_zero]

theorem main : ∀ (Λ : PeriodPair) (c Ω : ℂ) (τ : ℍ), IsTauOf Λ c τ → (G2s τ / (2 * (Real.pi : ℂ) * Complex.I) ^ 2 / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = s2 Λ / Ω ^ 2) ∧ ∀ (N : ℕ) (x : Fin 2 → ZMod N), wp N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 2 = Λ.weierstrassP (c * tors N τ x) / Ω ^ 2 ∧ wpd N x τ / (Ω * c / (2 * Real.pi * Complex.I)) ^ 3 = Λ.derivWeierstrassP (c * tors N τ x) / Ω ^ 3 := by
  intro Λ c Ω τ h
  obtain ⟨_, hP, hD, hs, _⟩ := GlobalTheory.T.weierstrassP_homogeneity_of_isTauOf Λ c τ h
  have hG := (GlobalTheory.WpFam.LatConst.main τ).1
  have hk := two_pi_I_ne_zero
  refine ⟨?_, fun N x => ⟨?_, ?_⟩⟩
  · rw [complex_div_pow_div_div_pow _ _ _ _ hk, hs, hG, mul_pow, inv_mul_eq_div, div_div, mul_comm]
  · rw [wp, complex_div_pow_div_div_pow _ _ _ _ hk, hP, mul_pow, inv_mul_eq_div, div_div, mul_comm]
  · rw [wpd, complex_div_pow_div_div_pow _ _ _ _ hk, hD, mul_pow, inv_mul_eq_div, div_div, mul_comm]

end GlobalTheory.WpFam.TauVal
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EnlargeStrictHenselisationRetractModStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enlarge_strictHenselisation_retract_mod : ∀ (T O : Type) [CommRing T] [IsDomain T] [IsLocalRing T] [CommRing O] [IsLocalRing O] [Algebra T O]
    [Algebra (Polynomial T) O] [IsScalarTower T (Polynomial T) O], GlobalTheory.LocAcyc.AbsIntClosed T →
    ∀ (P : Ideal (Polynomial T)) [P.IsPrime] (φ : Localization.AtPrime P →+* O),
    φ.comp (algebraMap (Polynomial T) _) = algebraMap (Polynomial T) O →
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ → P = GlobalTheory.KeyOriginCut.originIdeal T →
    ∀ (q : ℕ), 0 < q → IsUnit (q : T) →
    ∀ (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
      [Algebra.EssFiniteType ℤ A] (i : A →+* T)
      (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
      [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
      (QA : Ideal EA) [QA.IsPrime] (jA : Localization.AtPrime QA →+* O)
      (ψA : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
      (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginEnlarge.Fits T O q A i EA QA jA ψA DA actA →
    ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : IsLocalRing A') (_ : IsNoetherianRing A')
      (_ : IsIntegrallyClosed A') (_ : Algebra.EssFiniteType ℤ A') (i' : A' →+* T)
      (EA' : Type) (_ : CommRing EA') (_ : Algebra (Polynomial A') EA') (_ : Algebra A' EA')
      (_ : IsScalarTower A' (Polynomial A') EA') (_ : Algebra.Etale (Polynomial A') EA')
      (QA' : Ideal EA') (_ : QA'.IsPrime) (jA' : Localization.AtPrime QA' →+* O)
      (ψA' : GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA') →+* GlobalTheory.LocAcyc.GenFib T O)
      (DA' : Type) (_ : CommRing DA') (_ : Algebra (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA')
      (actA' : Multiplicative (ZMod q) →* (DA' ≃ₐ[GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')] DA')),
      GlobalTheory.KeyOriginEnlarge.Fits T O q A' i' EA' QA' jA' ψA' DA' actA' ∧
      (∃ ρ' : Localization.AtPrime QA' →+* A',
        GlobalTheory.KeyOriginEnlarge.Retracts T O A' i' EA' QA' jA' ρ' ∧ True) ∧
      ∃ (β : GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA) →+* GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) (h : DA →+* DA'),
        ψA'.comp β = ψA ∧
        h.comp (algebraMap (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA) = (algebraMap (GlobalTheory.LocAcyc.GenFib A' (Localization.AtPrime QA')) DA').comp β := by
  first | (exact @GlobalTheory.KeyOriginEnlarge.enlarge_retract) | (exact GlobalTheory.KeyOriginEnlarge.enlarge_retract) | (intros; apply GlobalTheory.KeyOriginEnlarge.enlarge_retract  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBlockTriVecMulEqSinglePredStatement
section
open GlobalTheory.FinGL GlobalTheory.FinGL.LeviWh Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_blockTri_vecMul_eq_single_pred : ∀ (F : Type) [Field F] (r : ℕ) (b : Fin r → ℕ), Monotone b → ∀ (k k' : Fin r), k'.val + 1 = k.val → ∀ l : Fin r → F, l ≠ 0 → (∀ i, l i ≠ 0 → i < k ∧ b i = b k) → ∃ h : blockTri (κ := F) b, (∀ i j, ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) i j ≠ (1 : Matrix (Fin r) (Fin r) F) i j → i < k ∧ j < k) ∧ Matrix.vecMul l ((h : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = Pi.single k' 1 := by
  first | exact @GlobalTheory.FinGL.LeviWh.exists_blockTri_vecMul_eq_single | exact GlobalTheory.FinGL.LeviWh.exists_blockTri_vecMul_eq_single | (intros; apply GlobalTheory.FinGL.LeviWh.exists_blockTri_vecMul_eq_single <;> assumption)
end

