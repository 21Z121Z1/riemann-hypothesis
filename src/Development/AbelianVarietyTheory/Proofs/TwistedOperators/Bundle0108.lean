import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0105
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0106
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0092
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0104
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentity
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerCoeffEqOfIsometricAnalyticModulesStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_coeff_eq_of_isometric_analytic_modules : ∀ (p q : ℕ) (T : GrpData p q), Subgroup.closure (T.expt '' upq p q) = ⊤ → ∀ (π₁ π₂ : URep T) (M : GKMod p q) (j₁ : M.V →ₗ[ℂ] π₁.H) (j₂ : M.V →ₗ[ℂ] π₂.H), (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) (j₁ (M.act Y x)) 0) → (∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) (j₂ (M.act Y x)) 0) → (∀ Y ∈ upq p q, ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) Set.univ) → (∀ Y ∈ upq p q, ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) Set.univ) → (∀ x y, inner ℂ (j₁ x) (j₁ y) = inner ℂ (j₂ x) (j₂ y)) → ∀ g x y, inner ℂ (j₁ x) (π₁.π g (j₁ y)) = inner ℂ (j₂ x) (π₂.π g (j₂ y)) := by
  first | exact @GlobalTheory.AnalyticVec.inner_apply_eq_of_analytic | exact GlobalTheory.AnalyticVec.inner_apply_eq_of_analytic | (intros; apply GlobalTheory.AnalyticVec.inner_apply_eq_of_analytic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerEqOfIrreducibleStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_eq_of_irrGK_of_inner_hw_eq : ∀ (p q : ℕ) (M : GKMod p q) (H₁ : Type) [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (H₂ : Type) [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂] (j₁ : M.V →ₗ[ℂ] H₁) (j₂ : M.V →ₗ[ℂ] H₂), (∀ Z x y, inner ℂ (j₁ (M.act Z x)) (j₁ y) = inner ℂ (j₁ x) (j₁ (M.act (adjZ Z) y))) → (∀ Z x y, inner ℂ (j₂ (M.act Z x)) (j₂ y) = inner ℂ (j₂ x) (j₂ (M.act (adjZ Z) y))) → Function.Injective j₂ → IrrGK M → ∀ (μ : Ix p q → ℚ) (v : M.V), IsHW M.act μ v → Module.finrank ℂ ↥(hwSub M.act μ) = 1 → inner ℂ (j₁ v) (j₁ v) = inner ℂ (j₂ v) (j₂ v) → ∀ x y, inner ℂ (j₁ x) (j₁ y) = inner ℂ (j₂ x) (j₂ y) := by
  first | exact @GlobalTheory.InvFormUnique.inner_eq_of_irreducible | exact GlobalTheory.InvFormUnique.inner_eq_of_irreducible | (intros; apply GlobalTheory.InvFormUnique.inner_eq_of_irreducible <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.InterlacedSignedParameters
section
open Formalism.L2.Theta

namespace GlobalTheory.SignedHC.GridData

def mergedDecreasingWordPiZeroDZero (G : GridData) (p : ℕ) : ℚ :=
  if p ≤ G.m then G.a p
  else if p ≤ G.m + 2 * (G.k - 1) then
    (if (p - G.m) % 2 = 1 then (G.v ((p - G.m + 3) / 2) : ℚ) else G.vHalf ((p - G.m + 2) / 2))
  else -(G.b (p - G.m - 2 * (G.k - 1)) : ℚ)

def mergedDecreasingWordParity (G : GridData) (p : ℕ) : Bool := decide ((G.m + p) % 2 = 1)

theorem merged_word_succ_lt (G : GridData) (hga : 0 < G.ga) (hvb : 1 ≤ G.v G.k + G.b 1) {p : ℕ}
    (hp : p < 2 * G.m + 2 * (G.k - 1)) : G.mergedDecreasingWordPiZeroDZero (p + 1) < G.mergedDecreasingWordPiZeroDZero p := by
  have k2 := G.two_le_k
  have hg : (0 : ℚ) < G.ga := by exact_mod_cast hga
  unfold mergedDecreasingWordPiZeroDZero
  rcases lt_trichotomy p G.m with h | rfl | h
  · rw [if_pos (by omega : p + 1 ≤ G.m), if_pos h.le, G.a_eq_succ_add p]; linarith
  · rw [if_neg (by omega), if_pos (by omega), if_pos (by omega), if_pos le_rfl,
      show (G.m + 1 - G.m + 3) / 2 = 2 by omega, G.a_m]
    linarith
  · rw [if_neg (show ¬ p + 1 ≤ G.m by omega), if_neg (show ¬ p ≤ G.m by omega)]
    rcases lt_trichotomy p (G.m + 2 * (G.k - 1)) with h' | h' | h'
    · rw [if_pos (show p + 1 ≤ G.m + 2 * (G.k - 1) by omega), if_pos h'.le]
      by_cases hj : (p - G.m) % 2 = 1
      · rw [if_neg (show ¬ (p + 1 - G.m) % 2 = 1 by omega), if_pos hj, show (p + 1 - G.m + 2) / 2 = (p - G.m + 3) / 2 by omega, vHalf]
        linarith
      · rw [if_pos (show (p + 1 - G.m) % 2 = 1 by omega), if_neg hj, show (p + 1 - G.m + 3) / 2 = (p - G.m + 2) / 2 + 1 by omega, vHalf]
        have := G.v_anti ((p - G.m + 2) / 2) ((p - G.m + 2) / 2 + 1) (by omega) (by omega) (by omega)
        have : ((G.v ((p - G.m + 2) / 2 + 1) : ℤ) : ℚ) + 1 ≤ (G.v ((p - G.m + 2) / 2) : ℚ) := by
          exact_mod_cast this
        linarith
    · subst h'
      rw [if_neg (show ¬ G.m + 2 * (G.k - 1) + 1 ≤ G.m + 2 * (G.k - 1) by omega), if_pos le_rfl,
        if_neg (show ¬ (G.m + 2 * (G.k - 1) - G.m) % 2 = 1 by omega),
        show G.m + 2 * (G.k - 1) + 1 - G.m - 2 * (G.k - 1) = 1 by omega,
        show (G.m + 2 * (G.k - 1) - G.m + 2) / 2 = G.k by omega, vHalf]
      have : (1 : ℚ) ≤ (G.v G.k : ℚ) + (G.b 1 : ℚ) := by exact_mod_cast hvb
      linarith
    · rw [if_neg (show ¬ p + 1 ≤ G.m + 2 * (G.k - 1) by omega), if_neg (show ¬ p ≤ G.m + 2 * (G.k - 1) by omega),
        show p + 1 - G.m - 2 * (G.k - 1) = (p - G.m - 2 * (G.k - 1)) + 1 by omega]
      have := G.b_mono (p - G.m - 2 * (G.k - 1)) (p - G.m - 2 * (G.k - 1) + 1) (by omega) (by omega) (by omega)
      have : ((G.b (p - G.m - 2 * (G.k - 1)) : ℤ) : ℚ) < (G.b (p - G.m - 2 * (G.k - 1) + 1) : ℚ) := by
        exact_mod_cast this
      linarith

theorem merged_word_strict_anti (G : GridData) (hga : 0 < G.ga) (hvb : 1 ≤ G.v G.k + G.b 1) {p p' : ℕ} (h : p < p')
    (hp' : p' ≤ 2 * G.m + 2 * (G.k - 1)) : G.mergedDecreasingWordPiZeroDZero p' < G.mergedDecreasingWordPiZeroDZero p := by
  induction p' with
  | zero => omega
  | succ p' ih =>
    have h1 := G.merged_word_succ_lt hga hvb (p := p') (by omega)
    rcases Nat.lt_succ_iff_lt_or_eq.1 h with h | rfl
    · exact h1.trans (ih h (by omega))
    · exact h1

end GlobalTheory.SignedHC.GridData

namespace GlobalTheory.SignedHC.GridData

theorem exists_pos_of_mem_lam (G : GridData) {x : ℚ × Bool} (hx : x ∈ G.lam) :
    ∃ p ≤ 2 * G.m + 2 * (G.k - 1), x.1 = G.mergedDecreasingWordPiZeroDZero p ∧ (!x.2) = G.mergedDecreasingWordParity p := by
  have k2 := G.two_le_k
  rcases mem_lam.1 hx with ⟨i, hi, rfl⟩ | ⟨hc, hs⟩
  · refine ⟨i, by omega, by simp [mergedDecreasingWordPiZeroDZero, hi], ?_⟩
    simp only [mergedDecreasingWordParity, Nat.even_iff]
    by_cases h : (G.m - i) % 2 = 0
    · simp [h]; omega
    · simp [h]; omega
  · obtain ⟨i, hi2, hik, hv⟩ := mem_cloudHalf.1 hc
    refine ⟨G.m + 2 * i - 2, by omega, ?_, ?_⟩
    · rw [hv, mergedDecreasingWordPiZeroDZero, if_neg (show ¬ G.m + 2 * i - 2 ≤ G.m by omega),
        if_pos (show G.m + 2 * i - 2 ≤ G.m + 2 * (G.k - 1) by omega),
        if_neg (show ¬ (G.m + 2 * i - 2 - G.m) % 2 = 1 by omega),
        show (G.m + 2 * i - 2 - G.m + 2) / 2 = i by omega]
    · rw [hs, mergedDecreasingWordParity]; simp; omega

theorem exists_position_of_mem_D0 (G : GridData) {x : ℚ × Bool} (hx : x ∈ G.parD0) :
    ∃ p ≤ 2 * G.m + 2 * (G.k - 1), x.1 = G.mergedDecreasingWordPiZeroDZero p ∧ x.2 = G.mergedDecreasingWordParity p := by
  have k2 := G.two_le_k
  rcases mem_discrete_parameter_iff.1 hx with ⟨hc, hs⟩ | ⟨l, hl1, hlm, rfl⟩
  · obtain ⟨i, hi2, hik, hv⟩ := mem_cloud.1 hc
    refine ⟨G.m + 2 * i - 3, by omega, ?_, ?_⟩
    · rw [hv, mergedDecreasingWordPiZeroDZero, if_neg (show ¬ G.m + 2 * i - 3 ≤ G.m by omega),
        if_pos (show G.m + 2 * i - 3 ≤ G.m + 2 * (G.k - 1) by omega),
        if_pos (show (G.m + 2 * i - 3 - G.m) % 2 = 1 by omega),
        show (G.m + 2 * i - 3 - G.m + 3) / 2 = i by omega]
    · rw [hs, mergedDecreasingWordParity]; simp; omega
  · refine ⟨G.m + 2 * (G.k - 1) + l, by omega, ?_, ?_⟩
    · rw [mergedDecreasingWordPiZeroDZero, if_neg (show ¬ G.m + 2 * (G.k - 1) + l ≤ G.m by omega),
        if_neg (show ¬ G.m + 2 * (G.k - 1) + l ≤ G.m + 2 * (G.k - 1) by omega),
        show G.m + 2 * (G.k - 1) + l - G.m - 2 * (G.k - 1) = l by omega]
    · simp only [mergedDecreasingWordParity, Nat.even_iff]
      by_cases h : (l - 1) % 2 = 0
      · simp [h]; omega
      · simp [h]; omega

theorem mem_of_pos (G : GridData) {p : ℕ} (hp : p ≤ 2 * G.m + 2 * (G.k - 1)) :
    (∃ x ∈ G.lam, x.1 = G.mergedDecreasingWordPiZeroDZero p) ∨ ∃ x ∈ G.parD0, x.1 = G.mergedDecreasingWordPiZeroDZero p := by
  have k2 := G.two_le_k
  by_cases h1 : p ≤ G.m
  · exact Or.inl ⟨(G.a p, decide (Even (G.m - p))), mem_lam.2 (Or.inl ⟨p, h1, rfl⟩), by simp [mergedDecreasingWordPiZeroDZero, h1]⟩
  by_cases h2 : p ≤ G.m + 2 * (G.k - 1)
  · by_cases h3 : (p - G.m) % 2 = 1
    · refine Or.inr ⟨((G.v ((p - G.m + 3) / 2) : ℚ), true), mem_discrete_parameter_iff.2 (Or.inl ⟨mem_cloud.2 ⟨_, by omega, by omega, rfl⟩, rfl⟩), ?_⟩
      simp [mergedDecreasingWordPiZeroDZero, h1, h2, h3]
    · refine Or.inl ⟨(G.vHalf ((p - G.m + 2) / 2), true), mem_lam.2 (Or.inr ⟨mem_cloudHalf.2 ⟨_, by omega, by omega, rfl⟩, rfl⟩), ?_⟩
      simp [mergedDecreasingWordPiZeroDZero, h1, h2, h3]
  · refine Or.inr ⟨(-(G.b (p - G.m - 2 * (G.k - 1)) : ℚ), decide (Even (p - G.m - 2 * (G.k - 1) - 1))),
      mem_discrete_parameter_iff.2 (Or.inr ⟨_, by omega, by omega, rfl⟩), ?_⟩
    simp [mergedDecreasingWordPiZeroDZero, h1, h2]

theorem interlaced_pi_zero_and_D0 : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool}
    {mu : Fin n → ℝ} {ε' : Fin n → Bool}, 0 < G.ga → 1 ≤ G.v G.k + G.b 1 → IsEnum (G.parPi 0) lam ε →
    IsEnum G.parD0 mu ε' → GlobalTheory.SepReal.Interlaced ε lam ε' mu := by
  intro G n lam ε mu ε' hga hvb ⟨hA, q, hq, hS⟩ ⟨hB, q', hq', hD⟩ x y hlt hbtw
  rw [parPi_zero] at hS
  set N := 2 * G.m + 2 * (G.k - 1) with hN
  have hV : ∀ z : Fin (n + 1) ⊕ Fin n, Sum.elim lam mu z = ((Sum.elim q q' z : ℚ) : ℝ) := by
    rintro (a | b)
    · exact hq a
    · exact hq' b
  have key : ∀ z : Fin (n + 1) ⊕ Fin n, ∃ p ≤ N, Sum.elim q q' z = G.mergedDecreasingWordPiZeroDZero p ∧
      xor (Sum.elim ε ε' z) z.isLeft = G.mergedDecreasingWordParity p := by
    rintro (a | b)
    · have hm : (q a, ε a) ∈ G.lam := by rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
      obtain ⟨p, hp, h1, h2⟩ := G.exists_pos_of_mem_lam hm
      refine ⟨p, hp, h1, ?_⟩
      simpa using h2
    · have hm : (q' b, ε' b) ∈ G.parD0 := by rw [hD]; exact Finset.mem_image_of_mem _ (Finset.mem_univ b)
      obtain ⟨p, hp, h1, h2⟩ := G.exists_position_of_mem_D0 hm
      refine ⟨p, hp, h1, ?_⟩
      simpa using h2
  have surj : ∀ p ≤ N, ∃ z : Fin (n + 1) ⊕ Fin n, Sum.elim q q' z = G.mergedDecreasingWordPiZeroDZero p := by
    intro p hp
    rcases G.mem_of_pos hp with ⟨x, hx, hx1⟩ | ⟨x, hx, hx1⟩
    · rw [hS] at hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨Sum.inl a, hx1⟩
    · rw [hD] at hx
      obtain ⟨b, -, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨Sum.inr b, hx1⟩
  obtain ⟨px, hpx, hx1, hx2⟩ := key x
  obtain ⟨py, hpy, hy1, hy2⟩ := key y
  rw [hV, hV, hx1, hy1, Rat.cast_lt] at hlt
  have hlt' : px < py := by
    by_contra h
    rcases (not_lt.1 h).eq_or_lt with h | h
    · subst h; exact lt_irrefl _ hlt
    · exact lt_asymm hlt (G.merged_word_strict_anti hga hvb h hpx)
  have hsucc : py = px + 1 := by
    by_contra h
    obtain ⟨z, hz⟩ := surj (px + 1) (by omega)
    refine hbtw z ⟨?_, ?_⟩
    · rw [hV, hV, hy1, hz, Rat.cast_lt]; exact G.merged_word_strict_anti hga hvb (by omega) hpy
    · rw [hV, hV, hx1, hz, Rat.cast_lt]; exact G.merged_word_strict_anti hga hvb (Nat.lt_succ_self px) (by omega)
  have hpar : G.mergedDecreasingWordParity py = !G.mergedDecreasingWordParity px := by
    subst hsucc; simp only [mergedDecreasingWordParity]
    by_cases h : (G.m + px) % 2 = 1
    · simp [h]; omega
    · simp [h]; omega
  rw [← hx2, ← hy2] at hpar
  revert hpar
  cases Sum.elim ε ε' x <;> cases Sum.elim ε ε' y <;> cases x.isLeft <;> cases y.isLeft <;> decide

end GlobalTheory.SignedHC.GridData
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypeFunctionEquivalenceStatement
section
open Matrix MeasureTheory Filter Topology Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.SphJet
open scoped InnerProductSpace ComplexOrder Matrix.Norms.L2Operator
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowest_K_type_function_equivalence : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (W : Type) [NormedAddCommGroup W] [InnerProductSpace ℂ W] (τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)) (w : W), IsHCParam lam → IsTau ε (lowK ε lam) τ w → ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E : Fin n → Fin n → Module.End ℂ V) (u : V) (j : W →ₗᵢ[ℂ] V), LowData ε E (lowK ε lam) u j → TauTie ε E j τ → FunEquiv ε E j (ps ε lam τ w) := by
  first | exact @GlobalTheory.SphJet.PsEquivar.psFunEquiv | exact GlobalTheory.SphJet.PsEquivar.psFunEquiv | (intros; apply GlobalTheory.SphJet.PsEquivar.psFunEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypesJointHarmonicShapeStatement
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowestKTypes_jointHarmonicShape : ∀ (t : ℕ) (al be ga de : List ℚ), HypA t al be ga de → (IsParam (lamA al be ga de) ∧ IsParam (lamA' t al be ga de) ∧ IsParam (lamM' t al be ga de)) ∧ JointShape _ _ _ _ (blattner (lamA al be ga de)) (blattner (lamA' t al be ga de)) ∧ JointShape _ _ _ _ (blattner (lamA al be ga de)) (blattner (lamM' t al be ga de)) := by
  first | exact @GlobalTheory.lowestKTypes_jointShape | exact GlobalTheory.lowestKTypes_jointShape | (intros; apply GlobalTheory.lowestKTypes_jointShape <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParametersSeparatedByOne
section
open Formalism.L2.Theta

namespace GlobalTheory.WordSep

open GlobalTheory.SignedHC

private theorem v_le {G : GridData} {i j : ℕ} (hi : 2 ≤ i) (hij : i ≤ j) (hj : j ≤ G.k) : G.v j ≤ G.v i := by
  rcases hij.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (G.v_anti i j hi h hj).le

private theorem b_ge {G : GridData} {l : ℕ} (hl : 1 ≤ l) (hlm : l ≤ G.m) : G.b 1 ≤ G.b l := by
  rcases hl.eq_or_lt with rfl | h
  · exact le_rfl
  · exact (G.b_mono 1 l le_rfl h hlm).le

theorem sep_rat {G : GridData} (hga : 0 < G.ga)
    (hgap : ∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) (hb : 2 ≤ G.v G.k + G.b 1)
    {x y : ℚ} (hx : (∃ l, l ≤ G.m ∧ x = G.a l) ∨ ∃ j, 2 ≤ j ∧ j ≤ G.k ∧ x = G.vHalf j)
    (hy : (∃ j, 2 ≤ j ∧ j ≤ G.k ∧ y = G.v j) ∨ ∃ l, 1 ≤ l ∧ l ≤ G.m ∧ y = -(G.b l : ℚ)) :
    (y < x → y + 1 < x) ∧ x ≠ y := by
  have hk := G.two_le_k
  rcases hx with ⟨l, hl, rfl⟩ | ⟨j, hj2, hjk, rfl⟩
  · have hal : (G.v 2 : ℚ) + 3 / 2 ≤ G.a l := by
      unfold GridData.a
      have h1 : (1 : ℚ) ≤ (G.m : ℚ) + 1 - l := by
        have : (l : ℚ) ≤ G.m := by exact_mod_cast hl
        linarith
      have h2 : (1 : ℚ) ≤ G.ga := by exact_mod_cast hga
      nlinarith
    obtain ⟨z, hz, hzle⟩ : ∃ z : ℤ, y = z ∧ z ≤ G.v 2 := by
      rcases hy with ⟨j, hj2, hjk, rfl⟩ | ⟨l', hl1, hlm, rfl⟩
      · exact ⟨_, rfl, v_le le_rfl hj2 hjk⟩
      · refine ⟨-G.b l', by push_cast; ring, ?_⟩
        have := b_ge (G := G) hl1 hlm
        have := v_le (G := G) le_rfl hk le_rfl
        linarith
    have : (z : ℚ) ≤ G.v 2 := by exact_mod_cast hzle
    subst hz
    constructor
    · intro _; linarith
    · intro h; linarith
  · obtain ⟨z, hz, hzc⟩ : ∃ z : ℤ, y = z ∧ (G.v j ≤ z ∨ z ≤ G.v j - 2) := by
      rcases hy with ⟨j', hj2', hjk', rfl⟩ | ⟨l', hl1, hlm, rfl⟩
      · refine ⟨_, rfl, ?_⟩
        rcases le_or_gt j' j with h | h
        · exact Or.inl (v_le hj2' h hjk)
        · right
          have h1 := v_le (G := G) (by omega : 2 ≤ j + 1) (by omega : j + 1 ≤ j') hjk'
          have h2 := hgap j hj2 (by omega)
          linarith
      · refine ⟨-G.b l', by push_cast; ring, Or.inr ?_⟩
        have := b_ge (G := G) hl1 hlm
        have := v_le (G := G) hj2 hjk le_rfl
        linarith
    subst hz
    unfold GridData.vHalf
    rcases hzc with h | h
    · have : (G.v j : ℚ) ≤ z := by exact_mod_cast h
      constructor
      · intro h'; linarith
      · intro h'; linarith
    · have : (z : ℚ) ≤ G.v j - 2 := by exact_mod_cast h
      constructor
      · intro _; linarith
      · intro h'; linarith

theorem word_sep : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool}
    {mu : Fin n → ℝ} {ε' : Fin n → Bool}, 0 < G.ga → (∀ i, 2 ≤ i → i < G.k → G.v (i + 1) + 2 ≤ G.v i) →
    2 ≤ G.v G.k + G.b 1 → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' →
    (∀ a i, mu i < lam a → mu i + 1 < lam a) ∧ ∀ a i, lam a ≠ mu i := by
  rintro G n lam ε mu ε' hga hgap hb ⟨-, q, hq, hS⟩ ⟨-, q', hq', hT⟩
  have key : ∀ a i, (q' i < q a → q' i + 1 < q a) ∧ q a ≠ q' i := by
    intro a i
    have ha : (q a, ε a) ∈ G.lam := by
      rw [← G.parPi_zero, hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ a)
    have hi : (q' i, ε' i) ∈ G.parD0 := by
      rw [hT]; exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    refine sep_rat hga hgap hb ?_ ?_
    · rcases GridData.mem_lam.1 ha with ⟨l, hl, e⟩ | ⟨h, -⟩
      · exact Or.inl ⟨l, hl, (Prod.ext_iff.1 e).1⟩
      · exact Or.inr (GridData.mem_cloudHalf.1 h)
    · rcases GridData.mem_discrete_parameter_iff.1 hi with ⟨h, -⟩ | ⟨l, h1, h2, e⟩
      · exact Or.inl (GridData.mem_cloud.1 h)
      · exact Or.inr ⟨l, h1, h2, (Prod.ext_iff.1 e).1⟩
  refine ⟨fun a i h => ?_, fun a i h => ?_⟩
  · rw [hq, hq'] at h ⊢
    have := (key a i).1 (by exact_mod_cast h)
    exact_mod_cast this
  · rw [hq, hq'] at h
    exact (key a i).2 (by exact_mod_cast h)

end GlobalTheory.WordSep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ProdPLinIsHomogeneous
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.InducedPBW

noncomputable section
namespace GlobalTheory.InducedPBW.Onto

private lemma UgF_mono {p q j k : ℕ} (h : j ≤ k) : UgF p q j ≤ UgF p q k :=
  Submodule.span_mono fun _ ⟨l, hl, hu⟩ => ⟨l, hl.trans h, hu⟩

theorem indF_mono {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) {j k : ℕ} (h : j ≤ k) : indF act j ≤ indF act k := by
  refine Submodule.span_mono ?_
  rintro z ⟨u, hu, v, rfl⟩
  exact ⟨u, UgF_mono h hu, v, rfl⟩

theorem indFlt_le {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (k : ℕ) : indFlt act k ≤ indF act k := by
  unfold indFlt
  exact iSup₂_le fun j hj => indF_mono act hj.le

theorem le_indFlt {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) {j k : ℕ} (h : j < k) : indF act j ≤ indFlt act k := by
  unfold indFlt
  exact le_iSup₂ (f := fun i (_ : i < k) => indF act i) j h

theorem pLin_isHomogeneous {p q : ℕ} (Z : Mat p q) : (pLin Z).IsHomogeneous 1 := by
  unfold pLin
  exact MvPolynomial.IsHomogeneous.sum _ _ _ fun ab _ => MvPolynomial.isHomogeneous_C_mul_X _ _

theorem prod_pLin_isHomogeneous {p q : ℕ} (l : List (Mat p q)) :
    (l.map pLin).prod.IsHomogeneous l.length := by
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, List.length_nil]
    exact MvPolynomial.isHomogeneous_one _ _
  | cons Z l ih =>
    rw [List.map_cons, List.prod_cons, List.length_cons, Nat.add_comm]
    exact (pLin_isHomogeneous Z).mul ih

theorem prod_mem_UgF {p q k : ℕ} (l : List (Mat p q)) (h : l.length ≤ k) :
    (l.map (ugι p q)).prod ∈ UgF p q k := Submodule.subset_span ⟨l, h, rfl⟩

theorem symProd_mem_UgF {p q k m : ℕ} (x : Fin m → Mat p q) (h : m ≤ k) :
    symProd (fun i => ugι p q (x i)) ∈ UgF p q k := by
  unfold symProd
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun σ _ => ?_)
  have hmem := prod_mem_UgF (k := k) (List.ofFn fun i => x (σ i)) (by rw [List.length_ofFn]; exact h)
  rw [List.map_ofFn] at hmem
  exact hmem

theorem symU_mem_UgF {p q k : ℕ} (f : MvPolynomial (PIx p q) ℂ) (hf : f.IsHomogeneous k) :
    symU p q f ∈ UgF p q k := by
  rw [f.as_sum, map_sum]
  refine Submodule.sum_mem _ fun d hd => ?_
  have hdeg : d.degree = k := by
    by_contra hne
    exact MvPolynomial.mem_support_iff.mp hd (hf.coeff_eq_zero hne)
  have e : MvPolynomial.monomial d (f.coeff d) =
      f.coeff d • (MvPolynomial.basisMonomials (PIx p q) ℂ) d := by
    rw [MvPolynomial.coe_basisMonomials, MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rw [e, map_smul]
  refine Submodule.smul_mem _ _ ?_
  rw [symU, Module.Basis.constr_basis]
  refine symProd_mem_UgF _ (le_of_eq ?_)
  rw [Multiset.length_toList, Finsupp.card_toMultiset, ← hdeg]
  rfl

private lemma mkQ_tmul_prod_mem_indFlt_sup {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (hc : SymbolCongr act) (k : ℕ)
    (l : List (Mat p q)) (hl : l.length ≤ k) (v : V) :
    (indRel act).mkQ (TensorProduct.tmul ℂ (l.map (ugι p q)).prod v) ∈ indFlt act k ⊔
      (symTens p q V k).map ((indRel act).mkQ ∘ₗ LinearMap.rTensor V (symU p q)) := by
  rcases lt_or_eq_of_le hl with hlt | heq
  · refine Submodule.mem_sup_left (le_indFlt act hlt ?_)
    exact Submodule.subset_span ⟨_, prod_mem_UgF l le_rfl, v, rfl⟩
  · subst heq
    have hP : (l.map pLin).prod ∈ homog (PIx p q) l.length :=
      (MvPolynomial.mem_homogeneousSubmodule _ _).mpr (prod_pLin_isHomogeneous l)
    have hs : (indRel act).mkQ (TensorProduct.tmul ℂ (symU p q (l.map pLin).prod) v) ∈
        (symTens p q V l.length).map ((indRel act).mkQ ∘ₗ LinearMap.rTensor V (symU p q)) := by
      refine ⟨LinearMap.rTensor V (homog (PIx p q) l.length).subtype
        (TensorProduct.tmul ℂ (⟨_, hP⟩ : homog (PIx p q) l.length) v), LinearMap.mem_range_self _ _, ?_⟩
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply]
    have hsum := Submodule.add_mem_sup (hc l v) hs
    rw [sub_add_cancel] at hsum
    exact hsum

theorem indF_eq_sup (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (hc : SymbolCongr act) (k : ℕ) :
    indF act k = indFlt act k ⊔
      (symTens p q V k).map ((indRel act).mkQ ∘ₗ LinearMap.rTensor V (symU p q)) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro z ⟨u, hu, v, rfl⟩
    have key : UgF p q k ≤ (indFlt act k ⊔
        (symTens p q V k).map ((indRel act).mkQ ∘ₗ LinearMap.rTensor V (symU p q))).comap
        ((indRel act).mkQ ∘ₗ (TensorProduct.mk ℂ (Ug p q) V).flip v) := by
      refine Submodule.span_le.mpr ?_
      rintro w ⟨l, hl, rfl⟩
      exact mkQ_tmul_prod_mem_indFlt_sup act hc k l hl v
    exact key hu
  · refine sup_le (indFlt_le act k) ?_
    rintro _ ⟨z, ⟨w, rfl⟩, rfl⟩
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul f v =>
      simp only [LinearMap.comp_apply, LinearMap.rTensor_tmul, Submodule.subtype_apply]
      exact Submodule.subset_span
        ⟨_, symU_mem_UgF f.1 ((MvPolynomial.mem_homogeneousSubmodule _ _).mp f.2), v, rfl⟩
    | add a b ha hb =>
      rw [map_add, map_add]
      exact add_mem ha hb

end GlobalTheory.InducedPBW.Onto
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.SelfDualLatticeResolutionOfIdentityStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.self_dual_lattice_resolution_of_identity : ∀ {D : D7} {N : ℕ} (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)), Formalism.MainNotions.StandardLatticesGL3.SD D L → ∃ (r : ℕ) (s u : Fin r → Fin N → D.host.E), (∀ k, s k ∈ L) ∧ (∀ k, u k ∈ L) ∧ ∑ k, Matrix.vecMulVec (s k) (star (u k)) = 1 := by
  first | exact @GlobalTheory.SelfDualIdDecomp.iddecomp | exact GlobalTheory.SelfDualIdDecomp.iddecomp | (intros; apply GlobalTheory.SelfDualIdDecomp.iddecomp <;> assumption)
end

