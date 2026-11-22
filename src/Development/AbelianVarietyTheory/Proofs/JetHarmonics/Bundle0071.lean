import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0062
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConjugateTransposeLeibniz.YOperatorLeibnizRule
import ReciprocityTheory.GeometryOfNumbers.PluriharmonicAnalysis.Bundle0001
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0064
import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0002
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0065
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0063

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GlRelationRowStepsFunctionalEigen
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.RowChain

theorem quantumMinor_row_removal_chain (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp]
    (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp)
    (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ) (hE : Formalism.REAL.GlRel E)
    (h : ∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) →
      (∀ v, l (E a b v) = p a b • l v) ∧
      ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ)
        else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ
        else 0)) (d : ℕ) :
    ∀ (i t : ℕ) (a b : Fin (t + 1) → Fin (2 * r + k + 1)), i + d + 1 = r → t + 1 + i = 2 * r + k →
      (∀ j, (a j).val = i + j.val) → (∀ j, (b j).val = i + 1 + j.val) →
      ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) =
        c • l (Formalism.REAL.qminor E
          (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1)))
          (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1,
            by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) := by
  induction d with
  | zero =>
    intro i t a b hi ht ha hb
    obtain rfl : t = r + k := by omega
    have hai : Function.Injective a := fun x y hxy => by
      have h1 := ha x; have h2 := ha y; rw [hxy] at h1; exact Fin.ext (by omega)
    have hbi : Function.Injective b := fun x y hxy => by
      have h1 := hb x; have h2 := hb y; rw [hxy] at h1; exact Fin.ext (by omega)
    obtain ⟨e, he, hl⟩ := GlobalTheory.T.quantumMinor_rowExpansion_eigenFunctional M Wp _ _ E l a b
      (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1,
            by split_ifs <;> omega⟩ : Fin (2 * r + k + 1)))
      ⟨i, by omega⟩ ⟨r + k, by omega⟩ (p ⟨i, by omega⟩ ⟨r + k, by omega⟩) hE hai hbi
      (fun x y hxy => by
        simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by omega))
      (fun x y hxy => by
        simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by split_ifs at hxy <;> omega))
      (by
        ext x
        simp only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, ha]
        constructor
        · rintro ⟨j, hj⟩
          by_cases h0 : j.val = 0
          · left; omega
          · right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; omega⟩
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨⟨0, by omega⟩, by simp only; omega⟩
          · exact ⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)
      (by
        simp only [Set.mem_range, Fin.ext_iff]
        rintro ⟨j, hj⟩; omega)
      (by
        ext x
        simp only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, hb]
        constructor
        · rintro ⟨j, hj⟩
          rcases lt_trichotomy j.val k with h0 | h0 | h0
          · right; exact ⟨⟨j.val, by omega⟩, by simp only; split_ifs <;> omega⟩
          · left; omega
          · right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; split_ifs <;> omega⟩
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨⟨k, by omega⟩, by simp only; omega⟩
          · split_ifs at hj
            · exact ⟨⟨j.val, by omega⟩, by simp only; omega⟩
            · exact ⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)
      (by
        simp only [Set.mem_range, Fin.ext_iff]
        rintro ⟨j, hj⟩; split_ifs at hj <;> omega)
      (by
        simp only [Set.mem_range, Fin.ext_iff, hb]
        rintro ⟨j, hj⟩; omega)
      (by
        intro j v
        have hj := hb j
        obtain ⟨h1, h2⟩ := h ⟨i, by omega⟩ (b j) (by rw [Fin.lt_def]; simp only; omega)
          (by simp only; omega)
        rw [h1]
        by_cases hc : b j = ⟨r + k, by omega⟩
        · rw [if_pos hc, hc]
        · rw [if_neg hc]
          have hc' : (b j).val ≠ r + k := fun h' => hc (Fin.ext h')
          rw [if_neg (by simp only; omega), if_neg (by simp only; omega)] at h2
          rw [norm_eq_zero.mp h2])
    refine ⟨_, ?_, hl⟩
    obtain ⟨-, h2⟩ := h ⟨i, by omega⟩ ⟨r + k, by omega⟩ (by rw [Fin.lt_def]; simp only; omega)
          (by simp only; omega)
    rw [if_neg (by simp only; omega), if_pos (Or.inl ⟨by simp only; omega, rfl⟩)] at h2
    rw [norm_mul, he, h2, one_mul]
  | succ d ih =>
    intro i t a b hi ht ha hb
    obtain ⟨t, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    have hai : Function.Injective a := fun x y hxy => by
      have h1 := ha x; have h2 := ha y; rw [hxy] at h1; exact Fin.ext (by omega)
    have hbi : Function.Injective b := fun x y hxy => by
      have h1 := hb x; have h2 := hb y; rw [hxy] at h1; exact Fin.ext (by omega)
    obtain ⟨c, hc, hcl⟩ := ih (i + 1) t
      (fun j : Fin (t + 1) => (⟨i + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      (fun j : Fin (t + 1) => (⟨i + 1 + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      (by omega) (by omega) (fun _ => rfl) (fun _ => rfl)
    obtain ⟨e, he, hl⟩ := GlobalTheory.T.quantumMinor_rowExpansion_eigenFunctional M Wp _ _ E l a b
      (fun j : Fin (t + 1) => (⟨i + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      (fun j : Fin (t + 1) => (⟨i + 1 + 1 + j.val, by omega⟩ : Fin (2 * r + k + 1)))
      ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (p ⟨i, by omega⟩ ⟨i + 1, by omega⟩) hE hai hbi
      (fun x y hxy => by
        simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by omega))
      (fun x y hxy => by
        simp only [Fin.mk.injEq] at hxy; exact Fin.ext (by omega))
      (by
        ext x
        simp only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, ha]
        constructor
        · rintro ⟨j, hj⟩
          by_cases h0 : j.val = 0
          · left; omega
          · right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; omega⟩
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨⟨0, by omega⟩, by simp only; omega⟩
          · exact ⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)
      (by
        simp only [Set.mem_range, Fin.ext_iff]
        rintro ⟨j, hj⟩; omega)
      (by
        ext x
        simp only [Set.mem_range, Set.mem_insert_iff, Fin.ext_iff, hb]
        constructor
        · rintro ⟨j, hj⟩
          by_cases h0 : j.val = 0
          · left; omega
          · right; exact ⟨⟨j.val - 1, by omega⟩, by simp only; omega⟩
        · rintro (hx | ⟨j, hj⟩)
          · exact ⟨⟨0, by omega⟩, by simp only; omega⟩
          · exact ⟨⟨j.val + 1, by omega⟩, by simp only; omega⟩)
      (by
        simp only [Set.mem_range, Fin.ext_iff]
        rintro ⟨j, hj⟩; omega)
      (by
        simp only [Set.mem_range, Fin.ext_iff, hb]
        rintro ⟨j, hj⟩; omega)
      (by
        intro j v
        have hj := hb j
        obtain ⟨h1, h2⟩ := h ⟨i, by omega⟩ (b j) (by rw [Fin.lt_def]; simp only; omega)
          (by simp only; omega)
        rw [h1]
        by_cases hc : b j = ⟨i + 1, by omega⟩
        · rw [if_pos hc, hc]
        · rw [if_neg hc]
          have hc' : (b j).val ≠ i + 1 := fun h' => hc (Fin.ext h')
          rw [if_neg (by simp only; omega), if_neg (by simp only; omega)] at h2
          rw [norm_eq_zero.mp h2])
    obtain ⟨-, h2⟩ := h ⟨i, by omega⟩ ⟨i + 1, by omega⟩ (by rw [Fin.lt_def]; simp only; omega)
          (by simp only; omega)
    rw [if_pos (by simp only; exact ⟨trivial, by omega⟩)] at h2
    refine ⟨e * p ⟨i, by omega⟩ ⟨i + 1, by omega⟩ * c, ?_, fun u v => ?_⟩
    · rw [norm_mul, norm_mul, he, h2, hc, one_mul, one_mul]
    · rw [hl, hcl, smul_smul]

theorem chain_rows : ∀ (M Wp : Type) [AddCommGroup M] [Module ℂ M] [AddCommGroup Wp] [Module ℂ Wp] (k r : ℕ) (E : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ M) (l : M →ₗ[ℂ] Wp) (p : Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → ℂ) (τ : ℝ), 1 ≤ k → Formalism.REAL.GlRel E → (∀ a b : Fin (2 * r + k + 1), a < b → ¬ (r ≤ a.val ∧ b.val ≤ r + k) → (∀ v, l (E a b v) = p a b • l v) ∧ ‖p a b‖ = (if b.val = a.val + 1 ∧ (b.val < r ∨ r + k < a.val) then (1 : ℝ) else if (a.val + 1 = r ∧ b.val = r + k) ∨ (a.val = r + k ∧ b.val = r + k + 1) then τ else 0)) → 1 ≤ r → ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E (Fin.succAbove (Fin.last (2 * r + k))) (Fin.succAbove 0) u v) = c • l (Formalism.REAL.qminor E (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1))) (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1, by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) := by
  intro M Wp _ _ _ _ k r E l p τ _ hE h hr
  have gen : ∀ (n : ℕ) (a b : Fin n → Fin (2 * r + k + 1)), n = 2 * r + k →
      (∀ j, (a j).val = 0 + j.val) → (∀ j, (b j).val = 0 + 1 + j.val) →
      ∃ c : ℂ, ‖c‖ = τ ∧ ∀ u v, l (Formalism.REAL.qminor E a b u v) =
        c • l (Formalism.REAL.qminor E
          (fun j : Fin (r + k) => (⟨r + j.val, by omega⟩ : Fin (2 * r + k + 1)))
          (fun j : Fin (r + k) => (⟨if j.val < k then r + j.val else r + j.val + 1,
            by split_ifs <;> omega⟩ : Fin (2 * r + k + 1))) u v) := by
    intro n a b hn ha hb
    cases n with
    | zero => omega
    | succ t =>
      exact quantumMinor_row_removal_chain M Wp k r E l p τ hE h (r - 1) 0 t a b (by omega) (by omega) ha hb
  exact gen _ _ _ rfl (fun j => by simp) (fun j => by simp; omega)

end GlobalTheory.RowChain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.HcParamSubIntegral
section
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S.ThB

namespace GlobalTheory

theorem hcParam_sub_integral : ∀ (n : ℕ) (lam lam' : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam → Formalism.QuantumDeterminants.IsHCParam lam' → ∃ ν : Fin n → ℤ, lam' = (fun a => lam a + (ν a : ℝ)) ∧ ((BranchingSupport.n1 ν : ℕ) : ℝ) = l1 lam' lam ∧ ∀ s, |lam' s - lam s| ≤ l1 lam' lam := by
  intro n lam lam' h h'
  choose m hm using h.2
  choose m' hm' using h'.2
  have key : ∀ a, lam' a - lam a = ((m' a - m a : ℤ) : ℝ) := by
    intro a
    push_cast
    linarith [hm a, hm' a]
  refine ⟨fun a => m' a - m a, ?_, ?_, ?_⟩
  · funext a
    linarith [key a]
  · unfold BranchingSupport.n1 l1
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [key a, Nat.cast_natAbs, Int.cast_abs]
  · intro s
    unfold l1
    exact Finset.single_le_sum (f := fun a => |lam' a - lam a|) (fun a _ => abs_nonneg _) (Finset.mem_univ s)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InterlaceHalf
section
open BpJoin Formalism.FourierDecayAlt Formalism.MainNotions.S.ThB

namespace GlobalTheory.StdGrid

theorem half_le_of_lt {x y : ℝ} (m : ℤ) (h : y - x = (m : ℝ) + 1 / 2) (hlt : x < y) : x + 1 / 2 ≤ y := by
  have h1 : (-1 : ℝ) < (m : ℝ) := by linarith
  have h2 : (-1 : ℤ) < m := by exact_mod_cast h1
  have h3 : (0 : ℤ) ≤ m := by omega
  have h4 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast h3
  linarith

theorem scale_bounds {Ch b ka T : ℝ} (r : ℕ) (hb : 1 ≤ b) (hka : 0 < ka) (h1 : ka ≤ b ^ Ch) (h2 : ka⁻¹ ≤ b ^ Ch)
    (h3 : 1 ≤ T * (1 / ka) ^ (2 * r)) (h4 : T * (1 / ka) ^ (2 * r) ≤ b ^ (Ch * ((2 * r + 2 : ℕ) : ℝ))) :
    b ^ (-((2 * |Ch|) * ((2 * r + 2 : ℕ) : ℝ))) ≤ T ∧ T ≤ b ^ ((2 * |Ch|) * ((2 * r + 2 : ℕ) : ℝ)) := by
  have hb0 : 0 < b := by linarith
  have hC : Ch ≤ |Ch| := le_abs_self _
  have hC0 : 0 ≤ |Ch| := abs_nonneg _
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hbC : b ^ Ch ≤ b ^ |Ch| := Real.rpow_le_rpow_of_exponent_le hb hC
  have hpow : ∀ x : ℝ, 0 ≤ x → x ≤ b ^ Ch → x ^ (2 * r) ≤ b ^ (|Ch| * ((2 * r + 2 : ℕ) : ℝ)) := by
    intro x hx hxb
    calc x ^ (2 * r) ≤ (b ^ |Ch|) ^ (2 * r) := pow_le_pow_left₀ hx (hxb.trans hbC) _
      _ = b ^ (|Ch| * ((2 * r : ℕ) : ℝ)) := by rw [Real.rpow_mul hb0.le, Real.rpow_natCast]
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hb
        apply mul_le_mul_of_nonneg_left _ hC0
        push_cast; linarith
  have hm : (0 : ℝ) ≤ ((2 * r + 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  set m : ℝ := ((2 * r + 2 : ℕ) : ℝ) with hmdef
  have hk1 := hpow ka hka.le h1
  have hk2 := hpow (1 / ka) (by positivity) (by rwa [one_div])
  have hq : 0 < (1 / ka) ^ (2 * r) := by positivity
  have hT : 0 < T := by
    by_contra hneg
    push_neg at hneg
    have := mul_nonpos_of_nonpos_of_nonneg hneg hq.le
    linarith
  have hTe : T = T * (1 / ka) ^ (2 * r) * ka ^ (2 * r) := by
    rw [mul_assoc, ← mul_pow, one_div_mul_cancel hka.ne', one_pow, mul_one]
  have hE : 0 < b ^ (|Ch| * m) := Real.rpow_pos_of_pos hb0 _
  constructor
  · have h5 : 1 ≤ T * b ^ (|Ch| * m) := h3.trans (mul_le_mul_of_nonneg_left hk2 hT.le)
    have h6 : b ^ (|Ch| * m) ≤ b ^ ((2 * |Ch|) * m) := by
      apply Real.rpow_le_rpow_of_exponent_le hb
      nlinarith [mul_nonneg hC0 hm]
    have h7 : 1 ≤ T * b ^ ((2 * |Ch|) * m) := h5.trans (mul_le_mul_of_nonneg_left h6 hT.le)
    rw [Real.rpow_neg hb0.le, inv_le_iff_one_le_mul₀ (Real.rpow_pos_of_pos hb0 _)]
    exact h7
  · have h5 : b ^ (Ch * m) ≤ b ^ (|Ch| * m) :=
      Real.rpow_le_rpow_of_exponent_le hb (mul_le_mul_of_nonneg_right hC hm)
    calc T = T * (1 / ka) ^ (2 * r) * ka ^ (2 * r) := hTe
      _ ≤ b ^ (|Ch| * m) * b ^ (|Ch| * m) := mul_le_mul (h4.trans h5) hk1 (by positivity) hE.le
      _ = _ := by rw [← Real.rpow_add hb0]; congr 1; ring

theorem cut_gap {k : ℕ} {u u' : Fin k → ℝ} {L : ℝ} (hL : 0 ≤ L) (h : HasCut u u' L) : ∃ l, L ≤ |u l - u' l| := by
  obtain ⟨a, b, ⟨l, a', b', _, hab, hI, h1, h2, _⟩, hLb⟩ := h
  have ha : a ∈ Set.Icc a' b' := hI ▸ (⟨le_rfl, by linarith⟩ : a ∈ Set.Icc a b)
  have hb : b ∈ Set.Icc a' b' := hI ▸ (⟨by linarith, le_rfl⟩ : b ∈ Set.Icc a b)
  refine ⟨l, ?_⟩
  have h3 : max (-u l) (-u' l) - min (-u l) (-u' l) = |u l - u' l| := by
    rw [max_sub_min_eq_abs]
    congr 1; ring
  linarith [ha.1, hb.2]

theorem interlace_half {k r : ℕ} {lam : Fin (2 * r + k + 1) → ℝ} {u : ℕ → ℝ}
    (hl : ∀ a, ∃ m : ℤ, lam a - (((2 * r + k + 1 : ℕ) : ℝ) - 1) / 2 = (m : ℝ))
    (hu : ∀ i ∈ Finset.Icc 1 k, ∃ a : ℤ, u i = (a : ℝ) + ((k : ℝ) - 1) / 2)
    (hI : Formalism.MainNotions.S.InterlaceS (k := k) (by omega) (fun i => u (i.val + 1)) lam)
    (s : Fin (2 * r + k + 1)) (hs : s.val + 2 ≤ k) :
    lam s + 1 / 2 ≤ u (s.val + 1) ∧ u (s.val + 2) + 1 / 2 ≤ lam s := by
  obtain ⟨h1, h2⟩ := hI.1 s.val (by omega)
  obtain ⟨m, hm⟩ := hl s
  obtain ⟨a, ha⟩ := hu (s.val + 1) (by simp; omega)
  obtain ⟨a', ha'⟩ := hu (s.val + 2) (by simp; omega)
  push_cast at hm
  refine ⟨half_le_of_lt (a - m - r - 1) ?_ h1, half_le_of_lt (m + r - a') ?_ h2⟩
  · push_cast; linarith
  · push_cast; linarith

theorem std_grid : ∃ Cg₀ : ℝ, ∀ (Ch Cg : ℝ), Cg₀ ≤ Cg → ∀ (P : M.Par) (lam : Fin (2 * P.r + P.k + 1) → ℝ) (ka b g : ℝ), 2 ≤ P.k → StdHyp Ch Cg P.k P.r (PI.BesselPeriodGGP.eps48 P.k P.r) lam (fun i => P.u (i.val + 1)) (fun i => P.u' (i.val + 1)) (P.T * (1 / ka) ^ (2 * P.r)) (P.T' * (1 / ka) ^ (2 * P.r)) ka b → (∀ i ∈ Finset.Icc 1 P.k, (∃ a : ℤ, P.u i = (a : ℝ) + ((P.k : ℝ) - 1) / 2) ∧ ∃ a : ℤ, P.u' i = (a : ℝ) + ((P.k : ℝ) - 1) / 2) → AllGaps lam g → StdNum (2 * |Ch|) b (max (Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3) g / 2) P lam ∧ P.T ≤ b ^ ((2 * |Ch|) * ((2 * P.r + 2 : ℕ) : ℝ)) ∧ P.T' ≤ b ^ ((2 * |Ch|) * ((2 * P.r + 2 : ℕ) : ℝ)) ∧ ∀ n₀ : ℕ, ((∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i) → n₀ = 30 * (P.r + 1) ^ 2 + 6) → (¬ (∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i) → n₀ = 0) → Cases P n₀ := by
  refine ⟨36, ?_⟩
  intro Ch Cg hCg P lam ka b g hk hS hint hg
  obtain ⟨⟨hanti, hhalf⟩, hI, hI', hka, hka1, hka2, hT1, hT1', hT2, hT2', hlb, hub, hub', hgap, -,
    ⟨bv, hbv, hshape⟩, hcase⟩ := hS
  have hr : (0 : ℝ) ≤ P.r := Nat.cast_nonneg _

  let s1 : Fin (2 * P.r + P.k + 1) := ⟨P.k - 1, by omega⟩
  let s2 : Fin (2 * P.r + P.k + 1) := ⟨P.k, by omega⟩
  have h12 : s1 < s2 := by simp only [s1, s2, Fin.mk_lt_mk]; omega
  have hbelow : ∀ i : Fin P.k, lam s1 < P.u (i.val + 1) := by
    intro i
    by_cases hi : i.val + 1 < P.k
    · have h1 := (hI.1 i.val hi).1
      have h2 : lam s1 ≤ lam ⟨i.val, by omega⟩ := hanti.antitone (by simp only [s1, Fin.mk_le_mk]; omega)
      exact lt_of_le_of_lt h2 h1
    · have h1 := hI.2 (by omega)
      have he : i.val = P.k - 1 := by have := i.isLt; omega
      rw [he]
      exact h1
  have hn1 := (hshape s1).2 (fun h => by
    obtain ⟨i, hi⟩ := h.2
    exact absurd (hbelow i) (not_lt.2 hi.le))
  have hn2 := (hshape s2).2 (fun h => by
    obtain ⟨i, hi⟩ := h.2
    exact absurd ((hanti h12).trans (hbelow i)) (not_lt.2 hi.le))
  have hd : |lam s1 - lam s2| ≤ bv := by
    rw [abs_le]; constructor <;> linarith [hn1.1, hn1.2, hn2.1, hn2.2]
  have hbvb : bv ≤ b := by
    have := hlb s1
    have := neg_abs_le (lam s1)
    linarith [hn1.2]
  have hmaxgap : AllGaps lam (max (Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3) g) :=
    fun s t h => max_le (hgap s t h) (hg s t h)
  have hcb := (hmaxgap s1 s2 h12.ne).trans (hd.trans hbvb)
  have hc4 : 36 ≤ max (Cg * ((2 * P.r + 2 : ℕ) : ℝ) ^ 3) g := by
    refine le_trans ?_ (le_max_left _ _)
    have h1 : (1 : ℝ) ≤ ((2 * P.r + 2 : ℕ) : ℝ) ^ 3 := one_le_pow₀ (by push_cast; linarith)
    nlinarith
  have hb1 : 1 ≤ b := by linarith
  have hkb : (P.k : ℝ) ≤ b := by
    have h0 : (1 : ℝ) ≤ ((2 * P.r + P.k + 1 : ℕ) : ℝ) := by
      have : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
      push_cast; linarith
    have h1 : ((2 * P.r + P.k + 1 : ℕ) : ℝ) ≤ ((2 * P.r + P.k + 1 : ℕ) : ℝ) ^ 7 := le_self_pow₀ h0 (by norm_num)
    have h2 : (P.k : ℝ) ≤ ((2 * P.r + P.k + 1 : ℕ) : ℝ) := by push_cast; linarith
    nlinarith
  obtain ⟨hTl, hTu⟩ := scale_bounds P.r hb1 hka hka1 hka2 hT1 hT2
  obtain ⟨hTl', hTu'⟩ := scale_bounds P.r hb1 hka hka1 hka2 hT1' hT2'
  have hh := interlace_half hhalf (fun i hi => (hint i hi).1) hI
  have hh' := interlace_half hhalf (fun i hi => (hint i hi).2) hI'
  refine ⟨⟨fun l hl => ⟨by linarith, by linarith, hkb, ?_, ?_, hlb, ?_, ?_, ?_, hTl, hTl'⟩,
    fun s hs => ⟨(hh s hs).1, (hh s hs).2, (hh' s hs).1, (hh' s hs).2⟩⟩, hTu, hTu', ?_⟩
  · rw [Finset.mem_Icc] at hl
    have := hub ⟨l - 1, by omega⟩
    simpa [Nat.sub_add_cancel hl.1] using this
  · rw [Finset.mem_Icc] at hl
    have := hub' ⟨l - 1, by omega⟩
    simpa [Nat.sub_add_cancel hl.1] using this
  · intro s t hst
    have h1 := hmaxgap s t hst.ne
    rw [abs_of_pos (sub_pos.2 (hanti hst))] at h1
    linarith
  · exact fun s hs => ⟨fun _ => (hh s hs).1, fun _ => (hh s hs).2⟩
  · exact fun s hs => ⟨fun _ => (hh' s hs).1, fun _ => (hh' s hs).2⟩
  · intro n₀ he hne
    have hL : ((30 * (P.r + 1) ^ 2 + 6 : ℕ) : ℝ) ≤ Cg * ((P.r : ℝ) + 1) ^ 2 := by
      have h1 : (1 : ℝ) ≤ ((P.r : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith)
      push_cast; nlinarith
    rcases hcase with ⟨heq, l, hl, hsl, -⟩ | ⟨hneq, hcut⟩
    · have hall : ∀ i ∈ Finset.Icc 1 P.k, P.u i = P.u' i := by
        intro i hi
        rw [Finset.mem_Icc] at hi
        have := congrFun heq ⟨i - 1, by omega⟩
        simpa [Nat.sub_add_cancel hi.1] using this
      right
      refine ⟨he hall, hall, l + 1, by omega, hl, ?_⟩
      rw [he hall, ← hall (l + 1) (by simp; omega), ← hall (l + 1 + 1) (by simp; omega)]
      simp only at hsl
      linarith
    · left
      refine ⟨hne (fun hall => hneq (funext fun i => hall _ (by simp))), ?_⟩
      obtain ⟨l, hl⟩ := cut_gap (le_trans (Nat.cast_nonneg _) hL) hcut
      exact ⟨l.val + 1, by simp, hL.trans hl⟩

end GlobalTheory.StdGrid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.LeibnizDetFrameMatrixMatrixUnit
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF

namespace GlobalTheory.HatNF.DetLeibniz

open Matrix QnYLeibnizW

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem trace_adjugate_mul_eq_sum_cramer {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    (A.adjugate * B).trace = ∑ j, A.cramer (fun i => B i j) j := by
  simp only [Matrix.trace, Matrix.diag]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [cramer_eq_adjugate_mulVec]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem hasDerivAt_det_Zhat (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g X : Q.Mx k r) :
    HasDerivAt (fun t : ℝ => (Zhat k r z z' (g * NormedSpace.exp ((t : ℂ) • X))).det)
      ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * X)).trace 0 := by
  have h := ReciprocityTheory.GeometryOfNumbersTheory.hasDerivAt_det (fun t : ℝ => Zhat k r z z' (g * NormedSpace.exp ((t : ℂ) • X)))
    (Zhat k r z z' (g * X)) 0 (fun i j =>
      (hermL (Hpk k r) (fvec k r z' j) (fvec k r z i)).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
        (hasDerivAt_mul_exp_smul_zero g X))
  simp only [curve_zero] at h
  exact h

theorem Zhat_add_smul (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (A B : Q.Mx k r) (c : ℂ) :
    Zhat k r z z' (A + c • B) = Zhat k r z z' A + c • Zhat k r z z' B := by
  ext i j
  simp [Zhat, herm, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add,
    dotProduct_smul]

theorem Zhat_mul_single (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Q.Mx k r)
    (p q : Fin (2 * r + k + 1)) (j : Fin (r + 1)) :
    (fun i => Zhat k r z z' (g * Matrix.single p q 1) i j) =
      fvec k r z' j q • fun i => herm (Hpk k r) (g *ᵥ bvec p) (fvec k r z i) := by
  have hv : Matrix.single p q (1 : ℂ) *ᵥ fvec k r z' j = fvec k r z' j q • bvec p := by
    rw [Matrix.single_mulVec]
    funext l
    by_cases h : l = p
    · subst h; simp [bvec]
    · simp [bvec, h]
  funext i
  simp only [Zhat, Pi.smul_apply, ← Matrix.mulVec_mulVec, hv, herm, Matrix.mulVec_smul, dotProduct_smul]

theorem det_leibniz : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) (D : Set (Q.Mx k r)) (a b : Fin (Q.mdim k r 0)) (f : Q.Mx k r → E), Q.SmoothLev k r 0 D f → ∀ g ∈ Q.Glev k r 0 ∩ D, Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) (fun x => (Zhat k r z z' x).det • f x) g = (Zhat k r z z' g).det • Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) f g + (∑ j : Fin (r + 1), fvec k r z' j (Q.posL k r 0 b) * (Zhat k r z z' g).cramer (fun i => herm (Hpk k r) (g.mulVec (bvec (Q.posL k r 0 a))) (fvec k r z i)) j) • f g := by
  intro E _ _ k r z z' D a b f hf g hg
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g hg
  have hgG : g ∈ Q.Glev k r 0 := hg.1
  obtain ⟨hX1, hX2⟩ := hpart_mem (k := k) (r := r) (i := 0) a b
  set Z : Q.Mx k r := Matrix.single (Q.posL k r 0 a) (Q.posL k r 0 b) 1 with hZdef
  set X1 := hpart1 (Hpk k r) Z with hX1def
  set X2 := hpart2 (Hpk k r) Z with hX2def
  have hf1 := hasDerivAt_f f F U g X1 hU hgU hgG hF hfF hX1
  have hf2 := hasDerivAt_f f F U g X2 hU hgU hgG hF hfF hX2
  have hEf : Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) f g =
      fderiv ℝ F g (g * X1) + Complex.I • fderiv ℝ F g (g * X2) := by
    show RdV X1 f g + Complex.I • RdV X2 f g = _
    rw [rdV_of_hasDerivAt X1 g f _ hf1, rdV_of_hasDerivAt X2 g f _ hf2]
  have key : ∀ (φ : Q.Mx k r → ℂ) (d1 d2 : ℂ),
      HasDerivAt (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X1))) d1 0 →
      HasDerivAt (fun t : ℝ => φ (g * NormedSpace.exp ((t : ℂ) • X2))) d2 0 →
      Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) (fun x => φ x • f x) g =
        φ g • Q.EH k r (Q.posL k r 0 a) (Q.posL k r 0 b) f g + (d1 + Complex.I * d2) • f g := by
    intro φ d1 d2 h1 h2
    rw [hEf]
    show RdV X1 (fun x => φ x • f x) g + Complex.I • RdV X2 (fun x => φ x • f x) g = _
    rw [rdV_smul_of X1 g φ f d1 _ h1 hf1, rdV_smul_of X2 g φ f d2 _ h2 hf2]
    module
  rw [key (fun x => (Zhat k r z z' x).det) _ _ (hasDerivAt_det_Zhat k r z z' g X1)
    (hasDerivAt_det_Zhat k r z z' g X2)]
  have hsum : g * X1 + Complex.I • (g * X2) = g * Z := by
    rw [← Matrix.mul_smul, ← Matrix.mul_add, hX1def, hX2def, hpart_sum]
  have hd : ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * X1)).trace +
      Complex.I * ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * X2)).trace =
      ((Zhat k r z z' g).adjugate * Zhat k r z z' (g * Z)).trace := by
    rw [← hsum, Zhat_add_smul, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul, smul_eq_mul]
  rw [hd, trace_adjugate_mul_eq_sum_cramer]
  congr 2
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [hZdef, Zhat_mul_single, map_smul, Pi.smul_apply, smul_eq_mul]

end GlobalTheory.HatNF.DetLeibniz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsPassGeneratorsStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.Ahatv_mul_and_R0v_mul_mem_nfSpan_hats : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ b ∈ bset d, ∀ y : ℂ, d.L.Ahatv y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0v y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  first | exact @GlobalTheory.HatNF.GenMinus.minus_hats_pass_generators | exact GlobalTheory.HatNF.GenMinus.minus_hats_pass_generators | (intros; apply GlobalTheory.HatNF.GenMinus.minus_hats_pass_generators <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.MinusHatsTaylorCoeffLeibnizRuleStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.minusHats_taylorCoeff_leibniz_rule : ∀ (A : Type) [Ring A] [Algebra ℂ A] (r : ℕ) (L : LevelData A r), ∀ Y : ℂ, ∃ Xa Xr : ℕ → A, (∀ s : ℂ, L.Ahatv (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xa j) ∧ (∀ s : ℂ, L.R0v (Y - s) = ∑ j ∈ Finset.range (r + 2), s ^ j • Xr j) ∧ ∀ m : ℕ → A, MulRel L m → ∀ q, L.Ahatv Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xa j ∧ L.R0v Y * m q = ∑ j ∈ Finset.range (r + 2), m (q + j) * Xr j := by
  first | exact @GlobalTheory.HatNF.TaylorMinus.taylor_minus | exact GlobalTheory.HatNF.TaylorMinus.taylor_minus | (intros; apply GlobalTheory.HatNF.TaylorMinus.taylor_minus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NormalFormEntriesCommutatorMultiplierStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalForm_entries_commutator_multiplier : ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (X : Q.ActualOps P.k P.r Bs.z Bs.z' Bs.π Bs.π') (μ : Measure (Mt P.k P.r)) (L : LevelData (RA P Bs) P.r) (st : Start (RA P Bs)) (l0 : ℕ) (d : Q.NFData P (RA P Bs)), P5.IsData P Bs.z Bs.z' Bs.π Bs.π' X μ L st l0 → IsNF X d → ∀ (φ : ℝ → ℝ) (W : ℕ → Module.End ℂ (Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')), LE.SmoothLog φ → IsMulG P Bs φ W → ∀ (q : ℕ) (Y : ℂ), X.t Y 1 0 * W q = W q * X.t Y 1 0 - X.fn 2 * X.fn 5 * W (q + 1) * X.t Y 1 1 ∧ X.t Y 1 1 * W q = W q * X.t Y 1 1 ∧ X.t Y 0 1 * W q = W q * X.t Y 0 1 + X.fn 0 * X.fn 5 * W (q + 1) * X.t Y 1 1 := by
  first | exact @GlobalTheory.HatNF.nf_t_mul_mulG | exact GlobalTheory.HatNF.nf_t_mul_mulG | (intros; apply GlobalTheory.HatNF.nf_t_mul_mulG <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.PlusHatsPassGeneratorsStatement
section
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.R Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.Fr Formalism.REAL Formalism.QuantumDeterminants MeasureTheory GlobalTheory.HatNF
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.Ahat_mul_and_R0_mul_mem_nfSpan_hats : ∀ (P : M.Par) (A : Type) [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A] (d : Q.NFData P A), HatHyp d → ∀ b ∈ bset d, ∀ y : ℂ, d.L.Ahat y * b ∈ nfSpan d (hats d.L) 0 0 1 ∧ d.L.R0 y * b ∈ nfSpan d (hats d.L) 0 0 1 := by
  first | exact @GlobalTheory.HatNF.GenPlus.plus_hats_pass_generators | exact GlobalTheory.HatNF.GenPlus.plus_hats_pass_generators | (intros; apply GlobalTheory.HatNF.GenPlus.plus_hats_pass_generators <;> assumption)
end

