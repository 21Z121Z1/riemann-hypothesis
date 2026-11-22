import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle0005
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.Bundle0007
import Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TCNumDef

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.RestSegCoreOfNum
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.Joints.StandardMonomialSpace

theorem jE_mono {s : ℕ} (S : SegData s) {f g : Fin S.t → ℕ} (h : ∀ l, f l ≤ g l) (i : ℕ) : jE S f i ≤ jE S g i := by
  unfold jE
  split_ifs
  · exact h _
  · exact le_rfl

theorem jE_add {s : ℕ} (S : SegData s) (f g : Fin S.t → ℕ) (i : ℕ) : jE S (fun l => f l + g l) i = jE S f i + jE S g i := by
  unfold jE
  split_ifs <;> rfl

theorem jE_uTop {s : ℕ} (S : SegData s) (g : Fin s → ℕ) (i : Fin s) (h : S.sigma ≤ i.val) :
    jE S (fun l => g (uTop S l)) i.val = g i := by
  unfold jE
  rw [dif_pos ⟨h, i.2⟩]
  have e : uTop S ⟨i.val - S.sigma, by unfold SegData.t; have := i.2; omega⟩ = i := by
    apply Fin.ext
    show S.sigma + (i.val - S.sigma) = i.val
    omega
  show g (uTop S ⟨i.val - S.sigma, _⟩) = g i
  rw [e]

theorem ch_cases {s : ℕ} (a : Fin (2 * s + 1)) : a = chU s ∨ (∃ i : Fin s, a = chW i) ∨ ∃ i : Fin s, a = chE i := by
  have ha := a.2
  by_cases h : a.val = 2 * s
  · exact Or.inl (Fin.ext h)
  · by_cases h2 : a.val % 2 = 0
    · exact Or.inr (Or.inl ⟨⟨a.val / 2, by omega⟩, Fin.ext (by show a.val = 2 * (a.val / 2); omega)⟩)
    · exact Or.inr (Or.inr ⟨⟨a.val / 2, by omega⟩, Fin.ext (by show a.val = 2 * (a.val / 2) + 1; omega)⟩)

set_option maxHeartbeats 1600000 in
theorem segCoreAt_of_num {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (hN : NumCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    SegCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ _ O _ _ _ _ S hSq hD hH hc mm hmm n hn1 hnc β hβ L e he1 hen j
  intro (ju : Fin (X.seg C0 CE1 CE2 j).t → ℕ)
  intro hju Gu du hGI hGP hdu hGY A hcz hcw hcy hcx hy0 hγ dz dy dx
  classical
  have hp : 0 < X.p := hD.1.pos
  have hKz : CharZero (KK O) := Formalism.MainNotions.G.GLWeightTheory.dvr_fraction_field_charZero_prime S hD.1
  have hsN : segS X.TT j ≤ X.N1 := (hH.1.2.2.2.2.1 j).2
  have hQ1 : 1 ≤ X.p ^ X.G' * e := Nat.mul_pos (pow_pos hp _) he1
  obtain ⟨hroom, hnum⟩ := hN X hD hH hc mm hmm n hn1 hnc e he1 hen j (β j) (hβ j)
  obtain ⟨hdig, hU, hSt, hoP, -⟩ := hβ j
  have hA' := nb_coarseA C0 CE1 CE2 X j ju (L.jp j) du A hp dz
  have hC' := nb_coarseC C0 CE1 CE2 X j ju (L.jp j) du A hp dy
  have hdig' := nb_digits C0 CE1 CE2 X j ju (L.jp j) du A hp dz dy
  have hez : ∀ i, ∑ c, ezA C0 CE1 CE2 X j A i c ≤ X.p ^ X.G' * e := fun i =>
    nb_ez_le C0 CE1 CE2 X j A hp (β j) hdig _ i (hcw i)
  have hlb := level_bounds X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j) (L.lv j) (L.jp j) (L.ok j)
  have hjE : ∀ i : ℕ, jE (X.seg C0 CE1 CE2 j) ju i ≤ jE (X.seg C0 CE1 CE2 j) (L.lv j) i := fun i => jE_mono _ hju i

  have hduW : ∀ i : Fin (segS X.TT j), du (chW i) ≤
      (if i.val < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i) - jE (X.seg C0 CE1 CE2 j) (L.lv j) i.val := by
    intro i
    have h1 := hdu (chW i)
    have h2 := lev_deg X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j) (L.lv j) (L.jp j) (chW i)
    have h3 := segment_chain_degree_even X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j) (chW i) i rfl
    have q : (chW i).val / 2 = i.val := by show 2 * i.val / 2 = _; omega
    rw [h3, q] at h2
    have h1' : du (chW i) ≤ ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).lettersAt (L.lv j) (L.jp j)).deg (chW i) := h1
    omega
  have hduU : du (chU _) ≤ (β j).oPlus - L.jp j := by
    have h1 := hdu (chU _)
    have h2 := lev_deg X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j) (L.lv j) (L.jp j) (chU _)
    have h3 := chain_deg_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (β j) (chU _) rfl
    rw [h3, if_pos (show (chU (segS X.TT j)).val = 2 * segS X.TT j from rfl)] at h2
    have h1' : du (chU _) ≤ ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).lettersAt (L.lv j) (L.jp j)).deg (chU _) := h1
    omega

  have hy0U : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).sigma ≤ i.val → y0A C0 CE1 CE2 X j A i ≤ X.p ^ X.G' * e := by
    intro i hi
    have h := hcy i
    rw [if_neg (by omega)] at h
    have := block_y_zero_le_of_bound C0 CE1 CE2 X j A hp (β j) hdig _ hQ1 i 0 h
    omega
  have hy0S : ∀ i : Fin (segS X.TT j), i.val < (X.seg C0 CE1 CE2 j).sigma → y0A C0 CE1 CE2 X j A i ≤ (β j).sg i + X.p ^ X.G' * e := by
    intro i hi
    have h := hcy i
    rw [if_pos hi] at h
    exact block_y_zero_le_of_bound C0 CE1 CE2 X j A hp (β j) hdig _ hQ1 i _ h
  have hyz : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).sigma ≤ i.val → y0A C0 CE1 CE2 X j A i ≤ z0A C0 CE1 CE2 X j A i := by
    intro i hi
    have h1 := hcz i
    rw [if_neg (by omega)] at h1
    have h2 := hcy i
    rw [if_neg (by omega), mul_zero, add_zero] at h2
    have h3 := hroom i hi
    exact block_y_zero_le_z_zero C0 CE1 CE2 X j A hp (β j) hdig _ hQ1 i _ (by omega) h1 h2

  have oU : ∀ i : Fin (segS X.TT j), (X.seg C0 CE1 CE2 j).sigma ≤ i.val → (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A).o i =
      jE (X.seg C0 CE1 CE2 j) ju i.val + du (chW i) + y0A C0 CE1 CE2 X j A i + ∑ c, ezA C0 CE1 CE2 X j A i c := by
    intro i hi
    show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then 0 else _) = _
    rw [if_neg (by omega)]
  have wS : ∀ i : Fin (segS X.TT j), i.val < (X.seg C0 CE1 CE2 j).sigma → (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A).w i = du (chW i) + ∑ c, ezA C0 CE1 CE2 X j A i c := by
    intro i hi
    show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then _ else 0) = _
    rw [if_pos hi]
  have sgS : ∀ i : Fin (segS X.TT j), i.val < (X.seg C0 CE1 CE2 j).sigma → (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A).sg i = y0A C0 CE1 CE2 X j A i := by
    intro i hi
    show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then _ else 0) = _
    rw [if_pos hi]
  have oP : (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A).oPlus = L.jp j + du (chU _) + ∑ c, axA X j A c := rfl
  have dx' : L.jp j + du (chU _) + (A ((topEnd X j, true), 0) + ∑ c, axA X j A c) = (segAPlus X.TT X.aT j) := by
    rw [← dx, Fin.sum_univ_succ]
    rfl
  have hcx' : ∑ c, axA X j A c ≤ X.p ^ X.G' * e := hcx
  obtain ⟨hBL', hthr⟩ := hnum (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A) hdig' (fun i => nb_coarseA_ge C0 CE1 CE2 X j ju (L.jp j) du A hp (β j) i)
    (by
      intro i hi
      have a1 := hA' i
      have a2 := oU i hi
      have a3 := hyz i hi
      have a4 := hy0U i hi
      have a5 := hez i
      have a6 := hduW i
      rw [if_neg (by omega)] at a6
      have a7 := hjE i.val
      have a8 := (hlb.1 i hi).1
      refine ⟨by omega, by omega, ?_, ?_⟩
      · show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then _ else 0) = 0
        rw [if_neg (by omega)]
      · show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then _ else 0) = 0
        rw [if_neg (by omega)])
    (by
      intro i hi
      have a1 := hA' i
      have a2 := wS i hi
      have a3 := sgS i hi
      have a4 := hy0S i hi
      have a5 := hez i
      have a6 := hduW i
      rw [if_pos hi] at a6
      have a7 := hC' i
      refine ⟨?_, by omega, by omega, by omega, by omega⟩
      show (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then 0 else _) = 0
      rw [if_pos hi])
    (by omega) (by have := hlb.2; omega)
  refine ⟨(segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A), hBL', nb_ord C0 CE1 CE2 X j ju (L.jp j) du A,
    uTot O X.m (X.seg C0 CE1 CE2 j) ju (L.jp j) (Gu * (mEps (KK O) (ezA C0 CE1 CE2 X j A) (eyA C0 CE1 CE2 X j A) (axA X j A)))
      (fun l => z0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l)) (fun l => y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l))
      (A ((topEnd X j, true), 0)) (L.γ j), ?_, ?_⟩
  · refine uTot_mem (fun l => hyz _ (Nat.le_add_right _ _)) ?_ (by omega) (du + (dEps (ezA C0 CE1 CE2 X j A) (eyA C0 CE1 CE2 X j A) (axA X j A)))
      (intPol_mul' hGI (mEps_int _ _ _)) (hom_Pol_mul (KK O) hGP (mEps_pol (KK O) _ _ _)) ?_ ?_ ?_
    · intro l
      have hi : (X.seg C0 CE1 CE2 j).sigma ≤ (uTop (X.seg C0 CE1 CE2 j) l).val := Nat.le_add_right _ _
      have a1 := hA' (uTop (X.seg C0 CE1 CE2 j) l)
      have a2 := oU _ hi
      have a3 := hyz _ hi
      omega
    · intro a
      rw [jE_add]
      simp only [Pi.add_apply]
      rcases ch_cases a with rfl | ⟨i, rfl⟩ | ⟨i, rfl⟩
      · rw [chain_deg_U X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) _ (chU _) rfl, dEps_U,
          if_pos (show (chU (segS X.TT j)).val = 2 * segS X.TT j from rfl)]
        have q : (chU (segS X.TT j)).val / 2 = segS X.TT j := by show 2 * segS X.TT j / 2 = _; omega
        rw [q, jE_top, jE_top, oP]
        omega
      · have q : (chW i).val / 2 = i.val := by show 2 * i.val / 2 = _; omega
        have hne : ¬ (chW i).val = 2 * segS X.TT j := by have := i.2; show ¬ 2 * i.val = _; omega
        rw [segment_chain_degree_even X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) _ (chW i) i rfl, dEps_chW_eq_sum, q, if_neg hne]
        by_cases hi : i.val < (X.seg C0 CE1 CE2 j).sigma
        · rw [if_pos hi, wS i hi, jE_S _ _ hi, jE_S _ _ hi]
          omega
        · rw [if_neg hi, oU i (by omega), jE_uTop (X.seg C0 CE1 CE2 j) (y0A C0 CE1 CE2 X j A) i (by omega)]
          omega
      · have q : (chE i).val / 2 = i.val := by show (2 * i.val + 1) / 2 = _; omega
        have hne : ¬ (chE i).val = 2 * segS X.TT j := by show ¬ 2 * i.val + 1 = _; omega
        rw [chain_deg_E X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) _ (chE i) i rfl, dEps_E, q, if_neg hne, hC' i]
        by_cases hi : i.val < (X.seg C0 CE1 CE2 j).sigma
        · rw [if_pos hi, sgS i hi, jE_S _ _ hi, jE_S _ _ hi]
          omega
        · rw [if_neg hi, jE_uTop (X.seg C0 CE1 CE2 j) (y0A C0 CE1 CE2 X j A) i (by omega)]
          omega
    · have h1 := L.hγ j
      have h2 : L.jp j ≤ (X.seg C0 CE1 CE2 j).bPlus := le_trans (L.ok j).2 (min_le_right _ _)
      have h1' : ∑ c, L.γ j c = (X.seg C0 CE1 CE2 j).bPlus - L.jp j := h1
      omega
    · intro m hm k
      have hW : ∀ i : Fin (segS X.TT j), (L.LL j).vec (chW i) = true := by
        intro i
        show decide ((2 * i.val) % 2 = 0) = true
        simp
      have hE : ∀ i : Fin (segS X.TT j), (L.LL j).vec (chE i) = false := by
        intro i
        show decide ((2 * i.val + 1) % 2 = 0) = false
        simp
      have g0 := hGY k
      have g1 := ycond_mEps (K := KK O) (L.LL j) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k) hE
        (ezA C0 CE1 CE2 X j A) (eyA C0 CE1 CE2 X j A) (axA X j A)
      have g2 := ycond_pairs (K := KK O) (r := X.m) (X.seg C0 CE1 CE2 j) (L.LL j) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k) hW hE
        (fun l => y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l) - m l)
      have g3 := ycond_mul (L.LL j) _ _ _ (ycond_mul (L.LL j) _ _ _ g0 g1) g2
      have hinc := rowInc_le (r := X.m) (X.seg C0 CE1 CE2 j) (L.LL j) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k)
        (ezA C0 CE1 CE2 X j A) (axA X j A) (fun l => y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l) - m l) (X.p ^ X.G' * e) hez hcx'
        (fun l => le_trans (Nat.sub_le _ _) (hy0U _ (Nat.le_add_right _ _)))
      have hcong := ycond_congr (K := KK O) (r := X.m)
        (LL := (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + ((n - e : ℕ) : ℝ) * ka1 X) (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A)).lettersAt (fun l => ju l + m l) (L.jp j)) (LL' := L.LL j) rfl
        ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + ((n - e : ℕ) : ℝ) * ka1 X) (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A)).T.J k) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + ((n - e : ℕ) : ℝ) * ka1 X) (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A)).T.thr k)
      rw [hcong]
      refine ycond_mono (L.LL j) _ ?_ g3
      have t1 := thr_eq X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j) k
      have t2 := thr_eq X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + ((n - e : ℕ) : ℝ) * ka1 X) (segmentBlockOfMonomial C0 CE1 CE2 X j ju (L.jp j) du A) k
      have hV : ((∑ i, ((∑ c, ezA C0 CE1 CE2 X j A i c : ℕ) : ℤ) *
            (vWt (L.LL j) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k) (chW i) : ℤ)) +
          ((∑ c, axA X j A c : ℕ) : ℤ) * (vWt (L.LL j) ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k) (chU _) : ℤ)) +
          ∑ l, ((y0A C0 CE1 CE2 X j A (uTop (X.seg C0 CE1 CE2 j) l) - m l : ℕ) : ℤ) *
            (pWt ((blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j) (mm + (n : ℝ) * ka1 X) (β j)).T.J k) (chW (uTop (X.seg C0 CE1 CE2 j) l)) (chE (uTop (X.seg C0 CE1 CE2 j) l)) : ℤ) ≤
          ((X.N1 : ℤ) + 1) * (((X.m : ℤ) + 1) + (X.p : ℤ) ^ X.G' * e) := by
        refine le_trans hinc ?_
        have b1 : ((segS X.TT j : ℕ) : ℤ) ≤ X.N1 := by exact_mod_cast hsN
        have b2 : (0 : ℤ) ≤ ((X.p ^ X.G' * e : ℕ) : ℤ) := Int.natCast_nonneg _
        have b3 : ((X.p ^ X.G' * e : ℕ) : ℤ) = (X.p : ℤ) ^ X.G' * e := by push_cast; ring
        have b4 : (0 : ℤ) ≤ (X.m : ℤ) := Int.natCast_nonneg _
        have b5 : (0 : ℤ) ≤ (X.N1 : ℤ) := Int.natCast_nonneg _
        rw [← b3]
        nlinarith
      have hfin := hthr (capIdx (X.seg C0 CE1 CE2 j) k) _ hV
      have t1' : (BDk C0 CE1 CE2 (mm + (n : ℝ) * ka1 X) X β j).T.thr k = _ := t1
      rw [t1', t2, ← WithTop.coe_add, ← WithTop.coe_add, ← WithTop.coe_add, WithTop.coe_le_coe]
      linarith
  · have hhead : L.head O j ju Gu = ioA (KK O) X.p C0 CE1 CE2 X j
        ((∏ l, EhS O X.m (X.seg C0 CE1 CE2 j) l ^ ju l) * EpS O X.m (X.seg C0 CE1 CE2 j) ^ L.jp j *
          rename (chainEmb (2 * segS X.TT j + 1) X.m (X.seg C0 CE1 CE2 j).t) Gu) := rfl
    rw [hhead, segMon_eq O C0 CE1 CE2 X j ju (L.jp j) du A (L.γ j) ?_ hy0 hγ, ioBlock_eq]
    · unfold uTot
      simp only [map_mul]
      ring
    · intro i hi
      have a1 := hA' i
      have a2 := wS i hi
      rw [jE_S _ _ hi] at a1
      omega

theorem restSegCore_of_num (h : RestNumCore) : RestSegCore :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => segCoreAt_of_num h) h

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.StandardPolynomials.TCGlue
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial

section Eval

variable {C0 CE1 CE2 mu : ℝ} {X : Loc} [NeZero X.m] {β : GlobalTheory X}

theorem tg_odd_ne_end (X : Loc) (j j' : Fin (numSeg X.TT)) (i : Fin (segS X.TT j)) : topOdd X j i ≠ topEnd X j' := by
  intro h
  have e : segPos X.TT j i = segNext X.TT j' := congrArg Subtype.val h
  exact (pos_mem X.TT j i).2 (e ▸ (next_mem X.TT j').2)

theorem tg_eval_odd (L : LvDat C0 CE1 CE2 mu X β) (ju : ∀ j, Fin (X.seg C0 CE1 CE2 j).t → ℕ)
    (du : ∀ j, Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X) (j : Fin (numSeg X.TT)) (i0 : Fin (segS X.TT j)) (b0 : Bool) :
    ∑ j', (tgHD L j' (ju j') (du j') (wLet X (topOdd X j i0, b0)) + tgWM X j' A (wLet X (topOdd X j i0, b0))) =
      (X.seg C0 CE1 CE2 j).P X.p i0 * (jE (X.seg C0 CE1 CE2 j) (ju j) i0.val + du j (if b0 then chW i0 else chE i0)) +
        ∑ c, A ((topOdd X j i0, b0), c) := by
  classical
  have hoth : ∀ j', j' ≠ j → ∀ (i' : Fin (segS X.TT j')) (b : Bool) (c : Fin (X.m + 1)),
      wLet X (topOdd X j i0, b0) ((topOdd X j' i', b), c) = 0 := by
    intro j' hne i' b c
    unfold wLet
    rw [if_neg]
    intro h
    have h1 : topOdd X j' i' = topOdd X j i0 := congrArg Prod.fst h
    have h2 := tgTop_inj X (a₁ := ⟨j', some i'⟩) (a₂ := ⟨j, some i0⟩) h1
    exact hne (congrArg Sigma.fst h2)
  have hend : ∀ j' (b : Bool) (c : Fin (X.m + 1)), wLet X (topOdd X j i0, b0) ((topEnd X j', b), c) = 0 := by
    intro j' b c
    unfold wLet
    rw [if_neg]
    intro h
    exact tg_odd_ne_end X j j' i0 (congrArg Prod.fst h).symm
  have hsame : ∀ (i : Fin (segS X.TT j)) (b : Bool) (c : Fin (X.m + 1)),
      wLet X (topOdd X j i0, b0) ((topOdd X j i, b), c) = if i = i0 ∧ b = b0 then 1 else 0 := by
    intro i b c
    unfold wLet
    simp only [Prod.mk.injEq, (topOdd_inj X j).eq_iff]
  rw [Finset.sum_eq_single j]
  · unfold tgHD tgWM
    simp only [hend, hsame, mul_zero, add_zero, Finset.sum_const_zero]
    rw [Finset.sum_eq_single i0, Finset.sum_eq_single i0]
    · cases b0 <;> simp
    · intro i _ hi; simp [hi]
    · intro h; exact absurd (Finset.mem_univ _) h
    · intro i _ hi; simp [hi]
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro j' _ hj'
    unfold tgHD tgWM
    simp only [hoth j' hj', hend, mul_zero, add_zero, Finset.sum_const_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem tg_eval_end (L : LvDat C0 CE1 CE2 mu X β) (ju : ∀ j, Fin (X.seg C0 CE1 CE2 j).t → ℕ)
    (du : ∀ j, Fin (2 * segS X.TT j + 1) → ℕ) (A : MonH X) (j : Fin (numSeg X.TT)) :
    ∑ j', (tgHD L j' (ju j') (du j') (wLet X (topEnd X j, true)) + tgWM X j' A (wLet X (topEnd X j, true))) =
      L.jp j + du j (chU _) + ∑ c, A ((topEnd X j, true), c) := by
  classical
  have hodd : ∀ j' (i' : Fin (segS X.TT j')) (b : Bool) (c : Fin (X.m + 1)),
      wLet X (topEnd X j, true) ((topOdd X j' i', b), c) = 0 := by
    intro j' i' b c
    unfold wLet
    rw [if_neg]
    intro h
    exact tg_odd_ne_end X j' j i' (congrArg Prod.fst h)
  have hend : ∀ j' (b : Bool) (c : Fin (X.m + 1)),
      wLet X (topEnd X j, true) ((topEnd X j', b), c) = if j' = j ∧ b = true then 1 else 0 := by
    intro j' b c
    unfold wLet
    have e : topEnd X j' = topEnd X j ↔ j' = j := by
      constructor
      · intro h
        exact congrArg Sigma.fst (tgTop_inj X (a₁ := ⟨j', none⟩) (a₂ := ⟨j, none⟩) h)
      · intro h; rw [h]
    simp only [Prod.mk.injEq, e]
  rw [Finset.sum_eq_single j]
  · unfold tgHD tgWM
    simp [hodd, hend]
  · intro j' _ hj'
    unfold tgHD tgWM
    simp [hodd, hend, hj']
  · intro h; exact absurd (Finset.mem_univ _) h

end Eval

theorem tcoreAt_of_seg {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ} (h : SegCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc) :
    TCoreAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X _ _ O _ _ _ _ S hSq hD hH hc mm hmm n hn1 hnc β hβ L Std hStd e he1 hen ju hju Gu du hGI hGP hdu hY A hA1 hA2 hA3
    hPol hnd
  classical
  have h2 : 2 ≤ numSeg X.TT := hH.1.2.2.2.1
  by_cases hT0 : (∏ j, L.head O j (ju j) (Gu j)) * monomial A 1 = 0
  · rw [hT0]; exact Submodule.zero_mem _
  have hS := tg_std_eq O h2 L Std hStd
  have sv : ∀ (pl : TgPlace X) (b : Bool) (c : Fin (X.m + 1)), Std ((tgTop X pl, b), c) = tgStdE L pl b c := by
    intro pl b c
    rw [hS]
    exact tgStdX_at h2 L pl b c
  have hsplit : (∏ j, L.head O j (ju j) (Gu j)) * monomial A 1 = ∏ j, (L.head O j (ju j) (Gu j) * segMon O X j A) := by
    rw [tg_mono_split O X h2, Finset.prod_mul_distrib]
  have hwh : ∀ ω : (X.TT × Bool) × Fin (X.m + 1) → ℕ, (∀ x (c c' : Fin X.m), ω (x, c.succ) = ω (x, c'.succ)) →
      (∀ j (i : Fin (segS X.TT j)), ω ((topOdd X j i, true), 0) + ω ((topOdd X j i, false), 0) =
        ω ((topOdd X j i, true), Fin.succ 0) + ω ((topOdd X j i, false), Fin.succ 0)) →
      (∀ j, ω ((topEnd X j, true), 0) + ω ((topEnd X j, false), 0) =
        ω ((topEnd X j, true), Fin.succ 0) + ω ((topEnd X j, false), Fin.succ 0)) →
      IsWeightedHomogeneous ω ((∏ j, L.head O j (ju j) (Gu j)) * monomial A 1)
        (∑ j, (tgHD L j (ju j) (du j) ω + tgWM X j A ω)) := by
    intro ω a1 a2 a3
    rw [hsplit]
    exact IsWeightedHomogeneous.prod _ _ _ fun j _ =>
      (tg_head_wh O L j (ju j) (Gu j) (du j) (hGP j) ω a1 (a2 j) (a3 j)).mul (tg_segMon_wh O j A ω)
  obtain ⟨m0, hm0⟩ := MvPolynomial.ne_zero_iff.1 hT0
  have hdeg : ∀ x : X.TT × Bool, ∑ j, (tgHD L j (ju j) (du j) (wLet X x) + tgWM X j A (wLet X x)) =
      hhDegs X.TT X.aT X.bT x := by
    intro x
    have a1 := hwh (wLet X x) (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl) hm0
    have a2 : multideg m0 x = hhDegs X.TT X.aT X.bT x :=
      ((mem_restrictSupport_iff _).1 hPol) (Finset.mem_coe.2 (mem_support_iff.2 hm0)) x
    rw [← a1, weight_wLet, a2]
  have hA0 : ∀ j, A ((topEnd X j, false), 0) = 0 := by
    intro j
    rw [hA3 j 0]
    exact sv ⟨j, none⟩ false 0
  have hnu : ∑ j, nuSeg C0 CE1 CE2 X j (ju j) (L.jp j) (du j) A ≤ ordFam C0 CE1 CE2 X β + e := by
    have a1 := hwh (tgWN X)
      (fun x c c' => by obtain ⟨t, b⟩ := x; cases b <;> simp [tgWN_ts, tgWN_fs])
      (fun j i => by rw [tgWN_true_zero_eq_zero, top_weight_false_zero_eq_one, tgWN_ts, tgWN_fs])
      (fun j => by rw [tgWN_true_zero_eq_zero, top_weight_false_zero_eq_one, tgWN_ts, tgWN_fs]) hm0
    have a2 := hnd m0 (mem_support_iff.2 hm0)
    rw [← weight_tgWN, a1] at a2
    refine le_trans (le_of_eq ?_) a2
    refine Finset.sum_congr rfl fun j _ => ?_
    have t := tg_nd_eval L j (ju j) (du j) A
    rw [hA0 j, add_zero] at t
    exact t.symm
  have key : ∀ j, ∃ b' : SegBlock (segS X.TT j) X.m,
        BLk C0 Cde CE1 CE2 X (((X.c - (n - e) : ℕ) : ℝ) * ka1 X) j b' ∧
        blockOrd X.p (X.seg C0 CE1 CE2 j) b' = nuSeg C0 CE1 CE2 X j (ju j) (L.jp j) (du j) A ∧
        ∃ u ∈ (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
            (mm + ((n - e : ℕ) : ℝ) * ka1 X) b').SSZ O (r := X.m),
          L.head O j (ju j) (Gu j) * segMon O X j A = ioBlock (KK O) X.p C0 CE1 CE2 X j b' u := by
    intro j
    refine h X O S hSq hD hH hc mm hmm n hn1 hnc β hβ L e he1 hen j (ju j) (hju j) (Gu j) (du j) (hGI j) (hGP j) (hdu j)
      (hY j) A ?_ ?_ ?_ ?_ (hA0 j) ?_ ?_ ?_ ?_
    · intro i
      have a := hA1 (topOdd X j i, true)
      have b : Std ((topOdd X j i, true), 0) - A ((topOdd X j i, true), 0) ≤
          ∑ c, (Std ((topOdd X j i, true), c) - A ((topOdd X j i, true), c)) :=
        Finset.single_le_sum (f := fun c => Std ((topOdd X j i, true), c) - A ((topOdd X j i, true), c))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      have v : Std ((topOdd X j i, true), 0) = (β j).rz i 0 + (X.seg C0 CE1 CE2 j).P X.p i *
          (coarseA X.p (X.seg C0 CE1 CE2 j) (β j) i -
            (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).w i else (β j).o i)) := by
        have := sv ⟨j, some i⟩ true 0
        simpa [tgStdE, tgTop] using this
      omega
    · intro i
      have a := hA2 (topOdd X j i, true)
      rw [Fin.sum_univ_succ] at a
      have v : ∀ c : Fin X.m, Std ((topOdd X j i, true), c.succ) = (β j).rz i c.succ := by
        intro c
        have := sv ⟨j, some i⟩ true c.succ
        simpa [tgStdE, tgTop, Fin.succ_ne_zero] using this
      simp only [v] at a
      omega
    · intro i
      have a := hA2 (topOdd X j i, false)
      have b : A ((topOdd X j i, false), 0) - Std ((topOdd X j i, false), 0) ≤
          ∑ c, (A ((topOdd X j i, false), c) - Std ((topOdd X j i, false), c)) :=
        Finset.single_le_sum (f := fun c => A ((topOdd X j i, false), c) - Std ((topOdd X j i, false), c))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ 0)
      have v : Std ((topOdd X j i, false), 0) = (β j).ry i 0 + (X.seg C0 CE1 CE2 j).P X.p i *
          (if (i : ℕ) < (X.seg C0 CE1 CE2 j).sigma then (β j).sg i else 0) := by
        have := sv ⟨j, some i⟩ false 0
        simpa [tgStdE, tgTop] using this
      omega
    · have a := hA2 (topEnd X j, true)
      rw [Fin.sum_univ_succ] at a
      have v : ∀ c : Fin X.m, Std ((topEnd X j, true), c.succ) = 0 := by
        intro c
        have := sv ⟨j, none⟩ true c.succ
        simpa [tgStdE, tgTop, Fin.succ_ne_zero] using this
      simp only [v, Nat.sub_zero] at a
      omega
    · intro c
      rw [hA3 j c.succ]
      exact sv ⟨j, none⟩ false c.succ
    · intro i
      have a := hdeg (topOdd X j i, true)
      rw [tg_eval_odd L ju du A j i true] at a
      have hb : hhDegs X.TT X.aT X.bT (topOdd X j i, true) = (X.seg C0 CE1 CE2 j).bTop i := by
        show hhDeg X.aT X.bT (segPos X.TT j i) true = X.bT (segPos X.TT j i)
        unfold hhDeg
        rw [if_pos rfl, if_neg (pos_mem X.TT j i).2]
      rw [hb] at a
      exact a
    · intro i
      have a := hdeg (topOdd X j i, false)
      rw [tg_eval_odd L ju du A j i false] at a
      have hb : hhDegs X.TT X.aT X.bT (topOdd X j i, false) = segATop X.TT X.aT j i := by
        show hhDeg X.aT X.bT (segPos X.TT j i) false = X.aT (segPos X.TT j i)
        unfold hhDeg
        rw [if_neg (by simp), if_neg (pos_mem X.TT j i).2]
      rw [hb] at a
      exact a
    · have a := hdeg (topEnd X j, true)
      rw [tg_eval_end L ju du A j] at a
      have hb : hhDegs X.TT X.aT X.bT (topEnd X j, true) = segAPlus X.TT X.aT j := by
        show hhDeg X.aT X.bT (segNext X.TT j) true = X.aT (segNext X.TT j)
        unfold hhDeg
        rw [if_pos rfl, if_pos (next_mem X.TT j).2]
      rw [hb] at a
      exact a
  choose β' hBL hord u hu hEq using key
  rw [hsplit, Finset.prod_congr rfl fun j _ => hEq j]
  show symFam (KK O) X.p C0 CE1 CE2 X β' u ∈ _
  refine symFam_span β' (fun j => genSet O (r := X.m)
    (blockData X.p (X.seg C0 CE1 CE2 j) (segATop X.TT X.aT j) (segAPlus X.TT X.aT j)
      (mm + ((n - e : ℕ) : ℝ) * ka1 X) (β' j))) _ ?_ u (fun j => hu j)
  intro s hs
  refine Submodule.subset_span ⟨β', hBL, ?_, s, hs, rfl⟩
  unfold ordFam
  rw [Finset.sum_congr rfl fun j _ => hord j]
  exact hnu

theorem restTCore_of_seg (h : RestSegCore) : RestTCore :=
  TransportedAlt.mono (fun _ _ _ _ _ _ _ _ _ _ h => tcoreAt_of_seg h) h

end Formalism.MainNotions.ColumnSystems.Pf
end
end

