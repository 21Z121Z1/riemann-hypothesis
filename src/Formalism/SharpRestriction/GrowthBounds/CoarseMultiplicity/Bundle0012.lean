import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0009
import Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.Bundle0010

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.LettersAtUpdate
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G MvPolynomial Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.CovariantDegrees

section GlobalTheory

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero (KK O)] {N r : ℕ} [NeZero r]

def tieW {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) : Fin N := ⟨D.T.pos i, by have := hT.lt i; omega⟩

def tieE {D : BlockData N} (hT : TieOK D) (i : Fin D.T.t) : Fin N := ⟨D.T.pos i + 1, hT.lt i⟩

theorem lettersAt_update {D : BlockData N} (hT : TieOK D) {j : Fin D.T.t → ℕ} {jp : ℕ} (hL : D.LevelOK j jp)
    (i : Fin D.T.t) (l : ℕ) (hl : l ≤ j i) :
    D.lettersAt (Function.update j i (j i - l)) jp =
      ⟨D.LL.vec, fun a => (D.lettersAt j jp).deg a + if a = tieW hT i ∨ a = tieE hT i then l else 0⟩ := by
  classical
  unfold BlockData.lettersAt
  simp only [ChainLetters.mk.injEq, true_and]
  funext a
  have hW : a = tieW hT i ↔ (a : ℕ) = D.T.pos i := by unfold tieW; rw [Fin.ext_iff]
  have hE : a = tieE hT i ↔ (a : ℕ) = D.T.pos i + 1 := by unfold tieE; rw [Fin.ext_iff]
  simp only [hW, hE]
  by_cases ha : (a : ℕ) = D.T.pos i ∨ (a : ℕ) = D.T.pos i + 1
  · have hoth : ∀ i', i' ≠ i → ¬ ((a : ℕ) = D.T.pos i' ∨ (a : ℕ) = D.T.pos i' + 1) := by
      intro i' hi' h
      rcases ha with ha | ha <;> rcases h with h | h
      · exact hi' (hT.inj _ _ (h.symm.trans ha))
      · exact hT.sep i' i (h.symm.trans ha)
      · exact hT.sep i i' (ha.symm.trans h)
      · exact hi' (hT.inj _ _ (by omega))
    have s1 : (∑ i', if (a : ℕ) = D.T.pos i' ∨ (a : ℕ) = D.T.pos i' + 1 then
        Function.update j i (j i - l) i' else 0) = j i - l := by
      rw [Finset.sum_eq_single i (fun i' _ hi' => if_neg (hoth i' hi')) (fun h => absurd (Finset.mem_univ i) h),
        if_pos ha, Function.update_self]
    have s2 : (∑ i', if (a : ℕ) = D.T.pos i' ∨ (a : ℕ) = D.T.pos i' + 1 then j i' else 0) = j i := by
      rw [Finset.sum_eq_single i (fun i' _ hi' => if_neg (hoth i' hi')) (fun h => absurd (Finset.mem_univ i) h),
        if_pos ha]
    have hu : a ≠ D.uPos := by
      intro h
      rcases ha with ha | ha
      · exact (hT.uW i).1 (by rw [← ha, h])
      · exact (hT.uW i).2 (by rw [← ha, h])
    have hdeg : j i ≤ D.LL.deg a := by
      have hN := hT.lt i
      rcases ha with ha | ha
      · have : D.letterAt (D.T.pos i) = a := by
          unfold BlockData.letterAt
          apply Fin.ext
          simp only
          omega
        rw [← this]; exact (hL.1 i).1
      · have : D.letterAt (D.T.pos i + 1) = a := by
          unfold BlockData.letterAt
          apply Fin.ext
          simp only
          omega
        rw [← this]; exact (hL.1 i).2
    rw [s1, s2, if_neg hu, if_pos ha]
    omega
  · rw [if_neg ha, add_zero]
    congr 2
    refine Finset.sum_congr rfl fun i' _ => ?_
    by_cases hi' : i' = i
    · subst hi'
      rw [if_neg ha, if_neg ha]
    · rw [Function.update_of_ne hi']

theorem levelOK_update {D : BlockData N} {j : Fin D.T.t → ℕ} {jp : ℕ} (hL : D.LevelOK j jp) (i : Fin D.T.t) (l : ℕ) :
    D.LevelOK (Function.update j i (j i - l)) jp := by
  classical
  refine ⟨fun i' => ?_, hL.2⟩
  have : Function.update j i (j i - l) i' ≤ j i' := by
    by_cases h : i' = i
    · subst h; rw [Function.update_self]; omega
    · rw [Function.update_of_ne h]
  exact ⟨this.trans (hL.1 i').1, this.trans (hL.1 i').2⟩

theorem tailP_mul (D : BlockData N) (jp : ℕ) (q y : MvPolynomial (Fin N × Fin r) (KK O))
    (g : MvPolynomial (BVar N r D.T.t) (KK O)) :
    tailP O r D jp (q * y) g = rename (chainEmb N r D.T.t) q * tailP O r D jp y g := by
  unfold tailP
  rw [map_mul]
  ring

open Classical in

def otherE (O : Type) [CommRing O] [IsDomain O] (r : ℕ) (D : BlockData N) (j : Fin D.T.t → ℕ) (i : Fin D.T.t) :
    MvPolynomial (BVar N r D.T.t) (KK O) :=
  ∏ i' ∈ Finset.univ.erase i, D.Ehat O (r := r) i' ^ j i'

theorem prodE_split (D : BlockData N) (j : Fin D.T.t → ℕ) (i : Fin D.T.t) :
    (∏ i', D.Ehat O (r := r) i' ^ j i') = D.Ehat O (r := r) i ^ j i * otherE O r D j i := by
  classical
  unfold otherE
  exact (Finset.mul_prod_erase Finset.univ (fun i' => D.Ehat O (r := r) i' ^ j i') (Finset.mem_univ i)).symm

theorem prodE_update (D : BlockData N) (j : Fin D.T.t → ℕ) (i : Fin D.T.t) (e : ℕ) :
    (∏ i', D.Ehat O (r := r) i' ^ Function.update j i e i') = D.Ehat O (r := r) i ^ e * otherE O r D j i := by
  classical
  unfold otherE
  rw [← Finset.mul_prod_erase Finset.univ (fun i' => D.Ehat O (r := r) i' ^ Function.update j i e i')
    (Finset.mem_univ i), Function.update_self]
  congr 1
  refine Finset.prod_congr rfl fun i' hi' => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hi')]

theorem shift_mem {D : BlockData N} (hT : TieOK D) {thr0 thr' : Fin D.T.q → WithTop ℤ} {j : Fin D.T.t → ℕ} {jp : ℕ}
    (hL : D.LevelOK j jp) (i : Fin D.T.t) (l : ℕ) (hl : l ≤ j i)
    (hthr : ∀ k, thr0 k + ((l : ℤ) : WithTop ℤ) ≤ thr' k)
    {q0 : MvPolynomial (Fin N × Fin r) (KK O)} (hq0 : IsMult O r D.LL.vec D.T.J (tieW hT i) (tieE hT i) q0)
    {y : MvPolynomial (Fin N × Fin r) (KK O)} (hy : y ∈ YjtZ O (r := r) (D.lettersAt j jp) D.T.J thr0)
    {g : MvPolynomial (BVar N r D.T.t) (KK O)} (hg : g ∈ XiPolZ O N r D.T.t (D.B - jp)) :
    D.Ehat O (r := r) i ^ (j i - l) * rename (chainEmb N r D.T.t) q0 ^ l * otherE O r D j i * tailP O r D jp y g ∈
      SSt O r D thr' := by
  have h1 := hq0.pow l (D.lettersAt j jp).deg thr0 y hy
  rw [← lettersAt_update hT hL i l hl] at h1
  have h2 := gen_mem D (fun k => thr0 k + ((l : ℤ) : WithTop ℤ)) (levelOK_update hL i l) h1 hg
  rw [prodE_update, tailP_mul, map_pow] at h2
  have h3 := SSt_mono (O := O) (r := r) D hthr h2
  convert h3 using 1
  ring

def FreeV {K σ : Type} [CommSemiring K] (v : σ) (F : MvPolynomial σ K) : Prop := ∀ μ ∈ F.support, μ v = 0

theorem freeV_of_vars {K σ : Type} [CommSemiring K] {v : σ} {F : MvPolynomial σ K} (h : v ∉ F.vars) : FreeV v F := by
  classical
  intro μ hμ
  by_contra h0
  exact h ((mem_vars_iff_mem_support v).2 ⟨μ, hμ, Finsupp.mem_support_iff.2 h0⟩)

theorem cth_lin {K σ : Type} [Field K] {v : σ} {E m' E' : MvPolynomial σ K} (hE : E = X v * m' + E')
    (hm' : FreeV v m') (hE' : FreeV v E') : cth v 1 E = X v * m' ∧ ∀ a, 2 ≤ a → cth v a E = 0 := by
  have hX : ∀ a, cth v a (X v * m') = m' * cth v a (X v : MvPolynomial σ K) := by
    intro a
    rw [mul_comm, cth_mul_free v a hm']
  have hXa : ∀ a, cth v a (X v : MvPolynomial σ K) = monomial (Finsupp.single v 1) (((Nat.choose 1 a : ℕ) : K)) := by
    intro a
    show cth v a (monomial (Finsupp.single v 1) (1 : K)) = _
    rw [cth_monomial, Finsupp.single_eq_same, one_mul]
  constructor
  · rw [hE, cth_add, cth_free v hE' one_ne_zero, add_zero, hX, hXa]
    simp only [Nat.choose_self, Nat.cast_one]
    rw [mul_comm]
    rfl
  · intro a ha
    rw [hE, cth_add, cth_free v hE' (by omega), add_zero, hX, hXa, Nat.choose_eq_zero_of_lt (by omega)]
    simp

theorem tie_mem {D : BlockData N} (hT : TieOK D) {thr thr' : Fin D.T.q → WithTop ℤ} (n : ℕ)
    (hthr : ∀ k, thr k + ((n : ℤ) : WithTop ℤ) ≤ thr' k) {j : Fin D.T.t → ℕ} {jp : ℕ} (hL : D.LevelOK j jp)
    (i : Fin D.T.t) (v : BVar N r D.T.t) {m' E' : MvPolynomial (BVar N r D.T.t) (KK O)}
    (hE : D.Ehat O (r := r) i = X v * m' + E') (hm' : FreeV v m') (hE' : FreeV v E')
    {q0 : MvPolynomial (Fin N × Fin r) (KK O)} (hq0 : IsMult O r D.LL.vec D.T.J (tieW hT i) (tieE hT i) q0)
    (δ : Bool) (hq : X v * m' = (if δ then D.Ehat O (r := r) i else 0) + rename (chainEmb N r D.T.t) q0)
    (hPE : FreeV v (otherE O r D j i))
    {y : MvPolynomial (Fin N × Fin r) (KK O)} {g : MvPolynomial (BVar N r D.T.t) (KK O)}
    (hg : g ∈ XiPolZ O N r D.T.t (D.B - jp))
    (H : ∀ b, b ≤ n → ∃ (cb : ℕ) (yb : MvPolynomial (Fin N × Fin r) (KK O)),
      yb ∈ YjtZ O (r := r) (D.lettersAt j jp) D.T.J (fun k => thr k + ((b : ℤ) : WithTop ℤ)) ∧
      cth v b (tailP O r D jp y g) = cb • tailP O r D jp yb g) :
    cth v n ((∏ i, D.Ehat O (r := r) i ^ j i) * tailP O r D jp y g) ∈ SSt O r D thr' := by
  classical
  obtain ⟨h1, h2⟩ := cth_lin hE hm' hE'
  rw [prodE_split D j i, mul_comm (D.Ehat O (r := r) i ^ j i), mul_assoc, cth_mul_free v n hPE, cth_mul, Finset.mul_sum]
  refine Submodule.sum_mem _ ?_
  rintro ⟨l, b⟩ hlb
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hlb
  simp only at hlb ⊢
  obtain ⟨cb, yb, hyb, hcb⟩ := H b (by omega)
  rw [cth_pow v h1 h2, hcb, Nat.cast_smul_eq_nsmul]
  by_cases hl : l ≤ j i
  · have key : D.Ehat O (r := r) i ^ (j i - l) * (X v * m') ^ l * otherE O r D j i * tailP O r D jp yb g ∈
        SSt O r D thr' := by
      cases δ with
      | false =>
        simp only [Bool.false_eq_true, if_false, zero_add] at hq
        rw [hq]
        refine shift_mem hT hL i l hl (fun k => ?_) hq0 hyb hg
        refine le_trans (le_of_eq ?_) (hthr k)
        rw [add_assoc, ← hlb]
        push_cast
        rw [add_comm (l : WithTop ℤ)]
      | true =>
        simp only [if_true] at hq
        rw [hq, add_pow, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
        refine Submodule.sum_mem _ fun a ha => ?_
        have ha' : a ≤ l := Nat.lt_succ_iff.1 (Finset.mem_range.1 ha)
        have h3 := shift_mem (thr' := thr') hT hL i (l - a) (by omega) (fun k => ?_) hq0 hyb hg
        · have h4 := (SSt O r D thr').smul_of_tower_mem (l.choose a) h3
          convert h4 using 1
          have e : j i - (l - a) = (j i - l) + a := by omega
          rw [e, pow_add, nsmul_eq_mul]
          ring
        · refine le_trans ?_ (hthr k)
          rw [add_assoc]
          gcongr
          have : ((b : ℤ) + ((l - a : ℕ) : ℤ)) ≤ (n : ℤ) := by omega
          exact_mod_cast this
    have h5 := (SSt O r D thr').smul_of_tower_mem ((j i).choose l) ((SSt O r D thr').smul_of_tower_mem cb key)
    convert h5 using 1
    simp only [nsmul_eq_mul]
    ring
  · rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp

end GlobalTheory

end Formalism.MainNotions.ColumnSystems.Pf
end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.CoarseMultiplicity.OPlusAtOf
section
noncomputable section

namespace Formalism.MainNotions.ColumnSystems.Pf

open Formalism.MainNotions.G

theorem oPlusAt_of {C0 CYb Cde Ck CD Cb CE1 CE2 Cc : ℝ}
    (hstd : ∀ X : Loc, D1num X → HIext C0 CYb Cde Ck CD Cb X → CBound Cc X → Std C0 Cde CE1 CE2 1 X) :
    OPlusAt C0 CYb Cde Ck CD Cb CE1 CE2 Cc := by
  intro X hD hH hC j b hk
  have St := hstd X hD hH hC
  have hO := (segHyp_of St j).oplus b
  have hk4 := hk.2.2.2

  have hSa : (((X.seg C0 CE1 CE2 j).a : ℕ) : ℝ) = (X.a : ℝ) := rfl
  have hSLa : (X.seg C0 CE1 CE2 j).La = X.La C0 := rfl
  rw [hSa, hSLa] at hO
  set A : ℝ := (X.a : ℝ) with hA
  set P : ℝ := (X.p : ℝ) with hPdef
  set La : ℝ := X.La C0 with hLadef
  set s : ℝ := (segS X.TT j : ℝ) with hsdef
  set q : ℝ := (X.m : ℝ) + 1 with hq
  have hP5 : (5 : ℝ) ≤ P := by
    show (5 : ℝ) ≤ (X.p : ℝ)
    exact_mod_cast St.p5
  have hP : (0 : ℝ) < P := by linarith
  have ha : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  have hb : 0 < X.b' := St.bpos
  have hbp : X.b' * P < A := by
    have h1 : P < A / X.b' := St.pab
    rw [lt_div_iff₀ hb] at h1
    linarith
  have hY := St.Y1
  have hk2 : X.k ^ 2 ≤ P := by
    have h1 : X.k ^ 2 * X.Y ^ 2 ≤ P := St.pk
    have hY2 : (1 : ℝ) ≤ X.Y ^ 2 := one_le_pow₀ hY
    have h2 : X.k ^ 2 * 1 ≤ X.k ^ 2 * X.Y ^ 2 := mul_le_mul_of_nonneg_left hY2 (sq_nonneg X.k)
    linarith
  have hN1 : (1 : ℝ) ≤ X.N1 := by exact_mod_cast St.N1pos
  have hk5 : 5 ≤ X.k := by linarith [St.N1k]
  have hkP : 5 * X.k ≤ P := by nlinarith
  have hN2 : (2 : ℝ) ≤ X.N := by exact_mod_cast St.N2
  have hLa1 : 1 ≤ La := St.La1
  have hLaN : 2 * X.N * La ≤ X.k := St.LaN
  have hLa : 4 * La ≤ X.k := by nlinarith
  have hsN : s ≤ X.N1 := by
    show ((segS X.TT j : ℕ) : ℝ) ≤ (X.N1 : ℝ)
    exact_mod_cast (St.segB j).2
  have hs0 : 0 ≤ s := Nat.cast_nonneg _
  have hs2 : 2 * s ≤ X.k := by linarith [St.N1k]
  have hq1 : 1 ≤ q := by rw [hq]; linarith [(Nat.cast_nonneg X.m : (0 : ℝ) ≤ X.m)]

  have e1 : A / P ^ 2 ≤ A / 25 := div_le_div_of_nonneg_left ha (by norm_num) (by nlinarith)
  have e2 : s * (2 * (X.b' / P)) ≤ A / 25 := by
    rw [show s * (2 * (X.b' / P)) = 2 * s * X.b' / P by ring, div_le_div_iff₀ hP (by norm_num)]
    have f1 := mul_le_mul_of_nonneg_right hs2 hb.le
    have f2 := mul_le_mul_of_nonneg_right hkP hb.le
    have f3 := mul_le_mul_of_nonneg_right hP5 ha
    nlinarith
  have e3 : (La / q + 4 / P ^ 2) * (s * (2 * A / P)) ≤ A / 4 + 4 * A / 125 := by
    have hsA : 0 ≤ s * (2 * A / P) := by positivity
    have g1 : (La / q + 4 / P ^ 2) * (s * (2 * A / P)) ≤ (La + 4 / P ^ 2) * (s * (2 * A / P)) :=
      mul_le_mul_of_nonneg_right (by
        have := div_le_self (show (0 : ℝ) ≤ La by linarith) hq1
        linarith) hsA
    have g2 : (La + 4 / P ^ 2) * (s * (2 * A / P)) = 2 * La * s * A / P + 8 * s * A / P ^ 3 := by
      field_simp
      ring
    have g3 : 2 * La * s * A / P ≤ A / 4 := by
      rw [div_le_div_iff₀ hP (by norm_num)]
      have hm := mul_le_mul hLa hs2 (by positivity) (by linarith)
      have h8 : 8 * (La * s) ≤ P := by
        have e : X.k * X.k = X.k ^ 2 := by ring
        linarith
      have h9 := mul_le_mul_of_nonneg_right h8 ha
      linarith
    have g4 : 8 * s * A / P ^ 3 ≤ 4 * A / 125 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      have h1 : 8 * s ≤ 4 * P / 5 := by linarith
      have h2 : (25 : ℝ) ≤ P ^ 2 := by
        have := mul_le_mul hP5 hP5 (by norm_num) hP.le
        rw [sq]
        linarith
      have h3 : 8 * s * A * 125 ≤ 100 * P * A := by
        have := mul_le_mul_of_nonneg_right h1 ha
        linarith
      have h4 : 100 * P * A ≤ 4 * A * P ^ 3 := by
        have h5 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 4 * A * P)
        have e : 4 * A * P * P ^ 2 = 4 * A * P ^ 3 := by ring
        linarith
      linarith
    linarith
  have e4 : 2 * (La * X.b' / q) ≤ A / 10 := by
    have g1 : La * X.b' / q ≤ La * X.b' := div_le_self (by positivity) hq1
    have g2 : 20 * (La * X.b') ≤ A := by
      have f1 := mul_le_mul_of_nonneg_right hLa hb.le
      have f2 := mul_le_mul_of_nonneg_right hkP hb.le
      linarith
    linarith
  have hwin := ((St.winA _ (next_mem X.TT j).1).1)
  have hfin : (b.oPlus : ℝ) ≤ (X.aT (segNext X.TT j) : ℝ) := by
    have := hO
    linarith
  unfold segAPlus
  exact_mod_cast hfin

theorem restOPlus : RestOPlus := by
  exact TransportedAlt.mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cm Cc h => oPlusAt_of h.2) thr_std

end Formalism.MainNotions.ColumnSystems.Pf
end
end

