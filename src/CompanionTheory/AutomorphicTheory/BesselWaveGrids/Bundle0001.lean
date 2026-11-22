import Formalism.HermitianCurvature.BesselNonvanishingReduction
import Formalism.HermitianCurvature.StatementD

-- bundled from CompanionTheory.AutomorphicTheory.BesselWaveGrids.GapSizes
section
noncomputable section

namespace CompanionTheory.WaveGrid.GapSizes

theorem sizes (Cg m N P s : ℝ) (hCg : 1000 ≤ Cg) (hm2 : 2 ≤ m) (hmN : m ≤ N) (hPN : N ^ 3 ≤ P) (hs : 1 ≤ s) :
    120 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P / 4 ∧ 125 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P / 32 := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN3 : (0 : ℝ) ≤ N ^ 3 := by positivity
  have hm2' : (4 : ℝ) ≤ m ^ 2 := by nlinarith
  have hm4e : m ^ 4 = m ^ 2 * m ^ 2 := by ring
  have hm4 : (16 : ℝ) ≤ m ^ 4 := by rw [hm4e]; nlinarith
  have hm4' : 4 * m ^ 2 ≤ m ^ 4 := by rw [hm4e]; nlinarith
  have hCg0 : (0 : ℝ) ≤ Cg := by linarith
  constructor
  · have a : (16 : ℝ) ≤ m ^ 4 * s := le_trans hm4 (le_mul_of_one_le_right (by positivity) hs)
    have b : (16000 : ℝ) ≤ Cg * (m ^ 4 * s) := by nlinarith
    have c : 16000 * N ^ 3 ≤ Cg * (m ^ 4 * s) * P :=
      le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))
    linarith
  · have b : 4000 * m ^ 2 ≤ Cg * m ^ 4 := by nlinarith
    have c : 4000 * m ^ 2 * N ^ 3 ≤ Cg * m ^ 4 * P :=
      le_trans (mul_le_mul_of_nonneg_right b hN3) (mul_le_mul_of_nonneg_left hPN (by positivity))
    linarith

theorem consts (k r : ℕ) (hk : 1 ≤ k) :
    Formalism.FourierDecayAlt.ThreeDimData.Mexp r ≤ (2 * (r : ℝ) + 2) ^ 2 / 2 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.Mexp r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AS k r ≤ 2 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AS k r ∧
    Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 4 * (2 * (r : ℝ) + k + 1) ^ 3 ∧ 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.AG k r := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  set N : ℝ := 2 * (r : ℝ) + k + 1 with hN
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN2 : N ^ 2 ≤ N ^ 3 := by nlinarith
  have hdN : Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ 2 * N ^ 2 := by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; rw [hN]; nlinarith
  have hdN0 : 0 ≤ Formalism.FourierDecayAlt.ThreeDimData.dN k r := by unfold Formalism.FourierDecayAlt.ThreeDimData.dN; nlinarith
  have hnk : ((2 * r + k : ℕ) : ℝ) ≤ N := by rw [hN]; push_cast; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.Mexp; positivity
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AS
    have : ((2 * r + k : ℕ) : ℝ) * Formalism.FourierDecayAlt.ThreeDimData.dN k r ≤ N * (2 * N ^ 2) :=
      mul_le_mul hnk hdN hdN0 (by linarith)
    nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AS; positivity
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AG
    have e1 : ((k : ℝ) + r) ≤ N := by rw [hN]; linarith
    have e2 : ((r : ℝ) + 1) ≤ N := by rw [hN]; linarith
    have e3 : ((k : ℝ) + r) * ((r : ℝ) + 1) ≤ N * N := mul_le_mul e1 e2 (by linarith) (by linarith)
    nlinarith
  · unfold Formalism.FourierDecayAlt.ThreeDimData.AG; positivity

theorem gapOK_of (k r : ℕ) (hk : 1 ≤ k) (Cg : ℝ) (hCg : 1000 ≤ Cg) :
    Formalism.FourierDecayAlt.ThreeDimData.GapOK k r (Cg * ((2 * r + 2 : ℕ) : ℝ) ^ ((9 : ℝ) / 2) *
      (((3 * (r + 1) : ℕ) : ℝ) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) / 4) := by
  have hr0 : (0 : ℝ) ≤ r := Nat.cast_nonneg _
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have em : ((2 * r + 2 : ℕ) : ℝ) = 2 * (r : ℝ) + 2 := by push_cast; ring
  have eN : ((2 * r + k + 1 : ℕ) : ℝ) = 2 * (r : ℝ) + k + 1 := by push_cast; ring
  have e3 : ((3 * (r + 1) : ℕ) : ℝ) = 3 * ((r : ℝ) + 1) := by push_cast; ring
  unfold Formalism.FourierDecayAlt.ThreeDimData.GapOK
  rw [em, eN, e3]
  generalize hm : 2 * (r : ℝ) + 2 = m
  generalize hN : 2 * (r : ℝ) + k + 1 = N
  have hm2 : (2 : ℝ) ≤ m := by rw [← hm]; linarith
  have hmN : m ≤ N := by rw [← hm, ← hN]; linarith
  have hmpos : (0 : ℝ) < m := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hsq : Real.sqrt (2 * ((r : ℝ) + 1)) = Real.sqrt m := by rw [← hm]; ring_nf
  have h92 : m ^ ((9 : ℝ) / 2) = m ^ 4 * Real.sqrt m := by
    rw [show (9 : ℝ) / 2 = ((4 : ℕ) : ℝ) + 1 / 2 by norm_num, Real.rpow_add hmpos, Real.rpow_natCast,
      Real.sqrt_eq_rpow]
  have hs1 : (1 : ℝ) ≤ Real.sqrt m := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by linarith)
  have hspos : (0 : ℝ) < Real.sqrt m := by linarith
  have hN3 : (1 : ℝ) ≤ N ^ 3 := one_le_pow₀ hN1
  have hPN : N ^ 3 ≤ 3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3 := by
    have : (0 : ℝ) ≤ 3 * ((r : ℝ) + 1) * N ^ 2 := by positivity
    linarith
  obtain ⟨s1, s2⟩ := sizes Cg m N (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) (Real.sqrt m) hCg hm2 hmN hPN hs1
  have hA : Formalism.FourierDecayAlt.ThreeDimData.aOf r (Cg * m ^ ((9 : ℝ) / 2) * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 4) =
      Cg * m ^ 4 * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 32 := by
    unfold Formalism.FourierDecayAlt.ThreeDimData.aOf
    rw [hsq, h92]
    field_simp
    ring
  obtain ⟨cM, cM0, cS, cS0, cG, cG0⟩ := consts k r hk
  rw [hm] at cM
  rw [hN] at cS cG
  have hm2' : (4 : ℝ) ≤ m ^ 2 := by nlinarith
  have hN3' : (0 : ℝ) ≤ N ^ 3 := by positivity
  have hmm : m ^ 2 * N ^ 3 ≥ 4 * N ^ 3 := by nlinarith
  have hX : 4 * N ^ 3 ≤ m ^ 2 * N ^ 3 := by nlinarith
  have hX1 : (4 : ℝ) ≤ m ^ 2 * N ^ 3 := by linarith
  refine ⟨hk, ?_, ?_, ?_⟩
  · rw [h92]; linarith
  · rw [hA]
    have hsum : Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r ≤ 6 * N ^ 3 := by linarith
    have hL : 2 * Formalism.FourierDecayAlt.ThreeDimData.Mexp r * (Formalism.FourierDecayAlt.ThreeDimData.AS k r + Formalism.FourierDecayAlt.ThreeDimData.AG k r) ≤ 2 * (m ^ 2 / 2) * (6 * N ^ 3) :=
      mul_le_mul (by linarith) hsum (by positivity) (by positivity)
    have hL' : 2 * (m ^ 2 / 2) * (6 * N ^ 3) = 6 * (m ^ 2 * N ^ 3) := by ring
    have s2' : 125 * (m ^ 2 * N ^ 3) ≤ Cg * m ^ 4 * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 32 := by
      have : 125 * m ^ 2 * N ^ 3 = 125 * (m ^ 2 * N ^ 3) := by ring
      linarith
    linarith only [hL, hL', s2', cG, hX, hX1]
  · rw [hA]
    have hN23 : N ^ 2 ≤ N ^ 3 := by
      have : N ^ 3 = N ^ 2 * N := by ring
      rw [this]; exact le_mul_of_one_le_right (by positivity) hN1
    have h9 : 9 * ((r : ℝ) + 1) = 4.5 * m := by rw [← hm]; ring
    have e1 : 9 * ((r : ℝ) + 1) * N ^ 2 ≤ 4.5 * m * N ^ 3 := by
      rw [h9]; exact mul_le_mul_of_nonneg_left hN23 (by positivity)
    have hq : 4.5 * m ≤ 3 * m ^ 2 := by nlinarith only [hm2]
    have e2 : 4.5 * m * N ^ 3 ≤ 3 * (m ^ 2 * N ^ 3) := by
      have := mul_le_mul_of_nonneg_right hq hN3'
      linarith only [this]
    have s2' : 125 * (m ^ 2 * N ^ 3) ≤ Cg * m ^ 4 * (3 * ((r : ℝ) + 1) * N ^ 2 + N ^ 3) / 32 := by
      have : 125 * m ^ 2 * N ^ 3 = 125 * (m ^ 2 * N ^ 3) := by ring
      linarith
    linarith only [e1, e2, hX, hX1, s2', cG]

end CompanionTheory.WaveGrid.GapSizes
end
end

-- bundled from CompanionTheory.AutomorphicTheory.BesselWaveGrids.QwBound
section
namespace CompanionTheory.WaveGrid

open Formalism.FourierDecayAlt

noncomputable def fac (l : C.Letter) (y : ℝ) : ℝ :=
  if l.1 then (y - l.2 + 1) / (y - l.2) else (l.2 - y) / (l.2 - y - 1)

noncomputable def facW {S : Type} (l : Wd.Letter ℂ S) (Y : ℂ) : ℂ :=
  if l.plus then (Y - l.pt + 1) / (Y - l.pt) else (l.pt - Y) / (l.pt - Y - 1)

theorem qw_eq_prod {S : Type} [Fintype S] [DecidableEq S] (q : ℂ → ℂ) (L : List (Wd.Letter ℂ S)) (Y : ℂ) :
    Wd.qw q L Y = q Y * (L.map fun l => facW l Y).prod := by
  induction L with
  | nil => simp [Wd.qw]
  | cons l L ih =>
    by_cases h : l.plus
    · simp only [Wd.qw, h, if_true, List.map_cons, List.prod_cons, ih, facW]
      ring
    · simp only [Wd.qw, h, List.map_cons, List.prod_cons, ih, facW]
      simp only [Bool.false_eq_true, if_false]
      ring

theorem positioned_map_facW (w : List C.Letter) (y : ℝ) :
    (D.positionted w).map (fun l => facW l (y : ℂ)) = w.map fun l => ((fac l y : ℝ) : ℂ) := by
  apply List.ext_getElem
  · simp [D.positionted]
  · intro n h1 h2
    simp only [D.positionted, List.getElem_map, List.getElem_ofFn, facW, fac]
    by_cases h : (w[n]'(by simpa using h2)).1
    · simp [h]
    · simp [h]

theorem ofReal_prod_map (w : List C.Letter) (f : C.Letter → ℝ) :
    (((w.map f).prod : ℝ) : ℂ) = (w.map fun l => ((f l : ℝ) : ℂ)).prod := by
  induction w with
  | nil => simp
  | cons l w ih => simp [ih]

theorem qC_ofReal (P : M.Par) (y : ℝ) :
    M.qC P (y : ℂ) = ((I.qpoly P.k P.T P.T' P.u P.u' y : ℝ) : ℂ) := by
  simp [M.qC, I.qpoly]

theorem qw_indexed_ofReal (P : M.Par) (w : List C.Letter) (y : ℝ) :
    Wd.qw (M.qC P) (D.positionted w) (y : ℂ) =
      ((I.qpoly P.k P.T P.T' P.u P.u' y * (w.map fun l => fac l y).prod : ℝ) : ℂ) := by
  rw [qw_eq_prod, positioned_map_facW, qC_ofReal, Complex.ofReal_mul]
  congr 1
  exact (ofReal_prod_map w fun l => fac l y).symm

theorem fac_ge (l : C.Letter) (y : ℝ) (h : 4 ≤ |y - l.2|) : 3 / 4 ≤ fac l y := by
  unfold fac
  split_ifs
  · rcases le_abs'.1 h with h' | h'
    · have hneg : y - l.2 < 0 := by linarith
      rw [le_div_iff_of_neg hneg]
      linarith
    · have hpos : 0 < y - l.2 := by linarith
      rw [le_div_iff₀ hpos]
      linarith
  · rcases le_abs'.1 h with h' | h'
    · have hpos : 0 < l.2 - y - 1 := by linarith
      rw [le_div_iff₀ hpos]
      linarith
    · have hneg : l.2 - y - 1 < 0 := by linarith
      rw [le_div_iff_of_neg hneg]
      linarith

theorem prod_fac_ge (w : List C.Letter) (y : ℝ) (h : ∀ l ∈ w, 4 ≤ |y - l.2|) :
    (3 / 4 : ℝ) ^ w.length ≤ (w.map fun l => fac l y).prod := by
  induction w with
  | nil => simp
  | cons l w ih =>
    simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]
    have h1 := fac_ge l y (h l (by simp))
    have h2 := ih fun l' hl' => h l' (by simp [hl'])
    rw [mul_comm]
    exact mul_le_mul h1 h2 (by positivity) (by linarith)

theorem qw_re_ge (P : M.Par) (w : List C.Letter) (y : ℝ) (hq : 0 ≤ I.qpoly P.k P.T P.T' P.u P.u' y)
    (h : ∀ l ∈ w, 4 ≤ |y - l.2|) :
    (3 / 4 : ℝ) ^ w.length * I.qpoly P.k P.T P.T' P.u P.u' y ≤ (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re := by
  rw [qw_indexed_ofReal, Complex.ofReal_re, mul_comm]
  exact mul_le_mul_of_nonneg_left (prod_fac_ge w y h) hq

theorem qw_re_pos (P : M.Par) (w : List C.Letter) (y : ℝ) (hq : 0 < I.qpoly P.k P.T P.T' P.u P.u' y)
    (h : ∀ l ∈ w, 4 ≤ |y - l.2|) : 0 < (Wd.qw (M.qC P) (D.positionted w) (y : ℂ)).re :=
  lt_of_lt_of_le (by positivity) (qw_re_ge P w y hq.le h)

end CompanionTheory.WaveGrid
end

