import Formalism.LocalToGlobal.CharacterGerms.LemmaMLin
import Formalism.IncomingBounds.FlowDegreeBounds.Bundle0002
import Formalism.LocalToGlobal.CharacterGerms.Bundle0007

-- bundled from Formalism.LocalToGlobal.CharacterGerms.LemmaMJet
section
noncomputable section

open scoped BigOperators
open Classical
open MvPowerSeries

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (OrdGE)

variable {C : Type} [Field C] {σ τ : Type}

theorem jet_add_right (P : MvPolynomial σ C) (G H : MvPowerSeries σ C) :
    jetAt0 P (G + H) = jetAt0 P G + jetAt0 P H := by
  simp only [jetAt0, map_add, mul_add, Finset.sum_add_distrib]

theorem jet_smul_right (P : MvPolynomial σ C) (a : C) (G : MvPowerSeries σ C) :
    jetAt0 P (a • G) = a * jetAt0 P G := by
  simp only [jetAt0, map_smul, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m _ => by ring

theorem jet_zero_right (P : MvPolynomial σ C) : jetAt0 P (0 : MvPowerSeries σ C) = 0 := by
  simp [jetAt0]

theorem jet_sum_right {ι : Type} (s : Finset ι) (P : MvPolynomial σ C)
    (G : ι → MvPowerSeries σ C) : jetAt0 P (∑ j ∈ s, G j) = ∑ j ∈ s, jetAt0 P (G j) := by
  simp only [jetAt0, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem jet_C (a : C) (G : MvPowerSeries σ C) :
    jetAt0 (MvPolynomial.C a) G = a * constantCoeff G := by
  by_cases ha : a = 0
  · subst ha
    simp [jetAt0]
  · simp [jetAt0, MvPolynomial.support_C, ha, mfact, MvPowerSeries.coeff_zero_eq_constantCoeff]

theorem mfact_add_single (m : σ →₀ ℕ) (x : σ) :
    mfact (m + Finsupp.single x 1) = (m x + 1) * mfact m := by
  unfold mfact
  set s := insert x m.support with hs
  have hsub : (m + Finsupp.single x 1).support ⊆ s := by
    intro y hy
    rcases Finset.mem_union.1 (Finsupp.support_add hy) with h | h
    · exact Finset.mem_insert_of_mem h
    · rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at h
      rw [h]
      exact Finset.mem_insert_self _ _
  rw [Finsupp.prod_of_support_subset (m + Finsupp.single x 1) hsub _ (fun _ _ => Nat.factorial_zero),
    Finsupp.prod_of_support_subset m (Finset.subset_insert _ _) _ (fun _ _ => Nat.factorial_zero)]
  have hx : x ∈ s := Finset.mem_insert_self _ _
  rw [← Finset.mul_prod_erase s _ hx, ← Finset.mul_prod_erase s (fun y => (m y).factorial) hx]
  have hrest : ∏ y ∈ s.erase x, ((m + Finsupp.single x 1 : σ →₀ ℕ) y).factorial = ∏ y ∈ s.erase x, (m y).factorial :=
    Finset.prod_congr rfl fun y hy => by
      rw [Finset.mem_erase] at hy
      simp [Finsupp.single_apply, Ne.symm hy.1]
  rw [hrest]
  simp [Nat.factorial_succ]
  ring

theorem jet_mul_X (p : MvPolynomial σ C) (x : σ) (G : MvPowerSeries σ C) :
    jetAt0 (p * MvPolynomial.X x) G = jetAt0 p (dVar x G) := by
  unfold jetAt0
  rw [MvPolynomial.support_mul_X, Finset.sum_map]
  refine Finset.sum_congr rfl fun n _ => ?_
  have hd : MvPowerSeries.coeff n (dVar x G) =
      ((n x + 1 : ℕ) : C) * MvPowerSeries.coeff (n + Finsupp.single x 1) G := rfl
  simp only [addRightEmbedding_apply]
  rw [MvPolynomial.coeff_mul_X, mfact_add_single, hd]
  push_cast
  ring

theorem jet_mul_C (p : MvPolynomial σ C) (a : C) (G : MvPowerSeries σ C) :
    jetAt0 (p * MvPolynomial.C a) G = a * jetAt0 p G := by
  rw [mul_comm p]
  unfold jetAt0
  rw [Finset.mul_sum]
  refine (Finset.sum_subset ?_ ?_).trans (Finset.sum_congr rfl fun m _ => ?_)
  · intro m hm
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_C_mul] at hm
    rw [MvPolynomial.mem_support_iff]
    intro h
    apply hm
    rw [h, mul_zero]
  · intro m _ hm
    rw [MvPolynomial.notMem_support_iff.1 hm, zero_mul, zero_mul]
  · rw [MvPolynomial.coeff_C_mul]
    ring

def linT [Fintype σ] (M : τ → σ → C) : MvPolynomial τ C →ₐ[C] MvPolynomial σ C :=
  MvPolynomial.aeval fun c => ∑ w, MvPolynomial.C (M c w) * MvPolynomial.X w

theorem jet_subst_linS [Fintype σ] [Fintype τ] (M : τ → σ → C) (Q : MvPolynomial τ C)
    (F : MvPowerSeries σ C) :
    jetAt0 Q (subst (linS M) F) = jetAt0 (linT M Q) F := by
  induction Q using MvPolynomial.induction_on generalizing F with
  | C a =>
    have h : linT M (MvPolynomial.C a) = MvPolynomial.C a := by
      unfold linT; rw [MvPolynomial.aeval_C]; rfl
    rw [h, jet_C, jet_C]
    congr 1
    have h0 := coeff_subst_linS_congr M (F := F) (G := MvPowerSeries.C (constantCoeff F)) (N := 0)
      (fun μ hμ => by
        have : μ = 0 := by
          rw [← Finsupp.degree_eq_zero_iff]; omega
        subst this
        simp) 0 (by simp)
    rw [subst_linS_C] at h0
    simpa using h0
  | add p q hp hq => rw [map_add, tpjet_jetAt0_add, tpjet_jetAt0_add, hp, hq]
  | mul_X p c hp =>
    rw [jet_mul_X, dVar_subst_linS, jet_sum_right, map_mul]
    have h : linT M (MvPolynomial.X c) = ∑ w, MvPolynomial.C (M c w) * MvPolynomial.X w := by
      unfold linT; rw [MvPolynomial.aeval_X]
    rw [h, Finset.mul_sum, tpjet_jetAt0_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [jet_smul_right, hp, ← mul_assoc, jet_mul_X, jet_mul_C]

theorem coeff_mvExp_partial {h : MvPowerSeries σ C} (hh : OrdGE 1 h) (N : ℕ) (m : σ →₀ ℕ)
    (hm : m.degree ≤ N) :
    coeff m (mvExp h) = coeff m (∑ k ∈ Finset.range (N + 1), ((k.factorial : C)⁻¹) • h ^ k) := by
  have hpow : ∀ k, OrdGE k (h ^ k) := by
    intro k
    have := ordGE_finset_prod (Finset.range k) (fun _ => 1) (fun _ => h) (fun _ _ => hh)
    simpa [Finset.prod_const, Finset.card_range] using this
  show (∑ k ∈ Finset.range (m.degree + 1), coeff m (h ^ k) / (k.factorial : C)) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [Finset.sum_subset (Finset.range_mono (by omega : m.degree + 1 ≤ N + 1)) ?_]
  · exact Finset.sum_congr rfl fun k _ => by rw [div_eq_inv_mul]
  · intro k hk hk'
    rw [Finset.mem_range] at hk hk'
    rw [hpow k m (by omega), zero_div]

theorem subst_mvExp [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, OrdGE 1 (a s))
    {h : MvPowerSeries σ C} (hh : OrdGE 1 h) : subst a (mvExp h) = mvExp (subst a h) := by
  ext e
  have hsh : OrdGE 1 (subst a h) := ordGE_subst ha hh
  rw [coeff_subst_congr ha (F := mvExp h)
      (G := ∑ k ∈ Finset.range (e.degree + 1), ((k.factorial : C)⁻¹) • h ^ k) (N := e.degree)
      (fun d hd => coeff_mvExp_partial hh e.degree d hd) e le_rfl,
    coeff_mvExp_partial hsh e.degree e le_rfl]
  congr 1
  rw [← MvPowerSeries.coe_substAlgHom (hasSubst_of_ordGE ha), map_sum]
  simp only [map_smul, map_pow]

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieAdm
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds

section Jet

variable {C : Type} [Field C] {σ : Type}

theorem cc_mvExp (x : MvPowerSeries σ C) : MvPowerSeries.constantCoeff (mvExp x) = 1 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show (∑ k ∈ Finset.range ((0 : σ →₀ ℕ).degree + 1), MvPowerSeries.coeff 0 (x ^ k) / (k.factorial : C)) = 1
  simp

theorem jetAt0_one (G : MvPowerSeries σ C) : jetAt0 (1 : MvPolynomial σ C) G = MvPowerSeries.constantCoeff G := by
  unfold jetAt0
  rw [MvPolynomial.support_one, Finset.sum_singleton]
  simp [mfact]

end Jet

section Par

theorem odd_sub_val {d : ℕ} [NeZero d] (hd : Even d) (x y : ZMod d) (h : ¬ (Even x.val ↔ Even y.val)) :
    Odd (y - x).val := by
  have h2 : 2 ∣ d := hd.two_dvd
  have e : y = x + (y - x) := by ring
  have e1 : y.val = (x.val + (y - x).val) % d := by
    conv_lhs => rw [e]
    exact ZMod.val_add _ _
  have e2 : y.val % 2 = (x.val + (y - x).val) % 2 := by rw [e1, Nat.mod_mod_of_dvd _ h2]
  rw [Nat.even_iff, Nat.even_iff] at h
  rw [Nat.odd_iff]
  omega

end Par

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  (X : RowData C V d I J) (F : Flag X)

theorem vars_letter {g : Fin 2} {a : ZMod d} {N : ℕ} {Q : MvPolynomial (Fin N × Fin (X.rkF g a)) C} {ρ : Fin N} {w : WV I}
    (h : (ρ, w) ∈ (MvPolynomial.rename (F.letter g a) Q).vars) : w.1 = g ∧ tyW X.G w = a := by
  obtain ⟨x, -, e⟩ := Finset.mem_image.1 (MvPolynomial.vars_rename _ _ h)
  have e2 : (⟨g, F.en g a x.2⟩ : WV I) = w := congrArg Prod.snd e
  subst e2
  exact ⟨rfl, F.en_ty g a x.2⟩

theorem big_of_le_rk (hj : X.j' < X.n) {g : Fin 2} {a : ZMod d} (h : X.n ≤ X.rkF g a) : X.big g a := by
  by_contra hb
  have := X.rk_small g a hb
  unfold RowData.rkF at h
  omega

theorem big_one_iff (a : ZMod d) : X.big 1 a ↔ ¬ X.big 0 a := by
  simpa using X.big_compl 0 a

theorem alt_odd_of_big (hdich : X.Alt ∨ ∀ a, X.big 0 a) {g : Fin 2} {a a' : ZMod d} (h1 : X.big g a)
    (h2 : X.big (1 - g) a') : X.Alt ∧ Odd (a' - a).val := by
  have h3 : ¬ X.big g a' := (X.big_compl g a').1 h2
  rcases hdich with hA | hB
  · refine ⟨hA, odd_sub_val hA.1 a a' ?_⟩
    have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp
    rcases hg with rfl | rfl
    · rw [← hA.2 a, ← hA.2 a']
      tauto
    · rw [big_one_iff] at h1 h3
      rw [← hA.2 a, ← hA.2 a']
      tauto
  · exfalso
    have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp
    rcases hg with rfl | rfl
    · exact h3 (hB a')
    · rw [big_one_iff] at h1
      exact h1 (hB a)

theorem attainsOK_of (hdich : X.Alt ∨ ∀ a, X.big 0 a) (hj : X.j' < X.n) (b : GlobalTheory d) (c : ℝ)
    (hwt : ∀ g a k, b.wt X g a k ≠ 0 → k ≤ X.rkF g a) (h : b.Attains X F c) : b.AttainsOK X F c := by
  cases b with
  | ch g a u =>
    refine ⟨(GlobalTheory.ch g a u).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, h⟩
    · intro ρ g' a1 a2 hk
      exact absurd hk (by simp [GlobalTheory.kind])
    · intro ρ _
      refine ⟨g, fun w hw => ?_⟩
      exact (vars_letter X F (MvPolynomial.vars_pow _ _ hw)).1
  | mon g e N =>
    refine ⟨(GlobalTheory.mon g e N).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, h⟩
    · intro ρ g' a1 a2 hk
      exact absurd hk (by simp [GlobalTheory.kind])
    · intro ρ _
      refine ⟨g, fun w hw => ?_⟩
      obtain ⟨a, -, ha⟩ := Finset.mem_biUnion.1 (MvPolynomial.vars_prod _ hw)
      exact (vars_letter X F ha).1
  | bi g a i y =>
    by_cases hy : y = 0
    · subst hy
      have hp : (GlobalTheory.bi g a i 0).poly X F = 1 := by
        simp [GlobalTheory.poly]
        rfl
      obtain ⟨S, t, ht, gr, hg, hc⟩ := h
      refine ⟨fun _ => none, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, S, t, ht, gr, hg, ?_⟩
      · intro ρ g' a1 a2 hk
        exact absurd hk (by simp)
      · intro ρ _
        refine ⟨0, fun w hw => ?_⟩
        rw [hp] at hw
        simp at hw
      · refine le_of_eq_of_le ?_ hc
        congr 1
        unfold ValOf
        rw [hp, jetAt0_one, jetAt0_one, map_prod, map_prod]
        refine Finset.prod_congr rfl fun ρ _ => ?_
        rw [map_mul, map_mul, cc_mvExp, cc_mvExp]
    · have hl : 0 < V.l ^ i * y := Nat.mul_pos (pow_pos V.l_prime.pos i) (Nat.pos_of_ne_zero hy)
      have w1 : X.n ≤ X.rkF g a := by
        apply hwt g a X.n
        simp only [GlobalTheory.wt, and_self, if_true]
        omega
      have w2 : X.n ≤ X.rkF (1 - g) (a + (i : ZMod d)) := by
        apply hwt (1 - g) (a + (i : ZMod d)) X.n
        simp only [GlobalTheory.wt, and_self, if_true]
        omega
      have hao := alt_odd_of_big X hdich (big_of_le_rk X hj w1) (big_of_le_rk X hj w2)
      refine ⟨(GlobalTheory.bi g a i y).kind X.n, (rowsOK_iff _ _ _ _).2 ⟨?_, ?_⟩, h⟩
      · intro ρ g' a1 a2 hk
        have hk' : (g, a, a + (i : ZMod d)) = (g', a1, a2) := by simpa [GlobalTheory.kind] using hk
        obtain ⟨rfl, rfl, rfl⟩ : g = g' ∧ a = a1 ∧ a + (i : ZMod d) = a2 := by simpa using hk'
        refine ⟨hao.1, hao.2, fun w hw => ?_⟩
        rcases Finset.mem_union.1 (MvPolynomial.vars_mul _ _ hw) with h1 | h1
        · exact Or.inl (vars_letter X F (MvPolynomial.vars_pow _ _ h1))
        · exact Or.inr (vars_letter X F (MvPolynomial.vars_pow _ _ h1))
      · intro ρ hk
        exact absurd hk (by simp [GlobalTheory.kind])

theorem le_sum_map {α : Type} (l : List α) (f : α → ℕ) {q : α} (hq : q ∈ l) : f q ≤ (l.map f).sum := by
  induction l with
  | nil => exact absurd hq (by simp)
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons]
    rcases List.mem_cons.1 hq with rfl | h
    · omega
    · have := ih h
      omega

variable {X F} in
theorem rkF_eq_of_big_iff {g g' : Fin 2} {a a' : ZMod d} (h : X.big g a ↔ X.big g' a') : X.rkF g a = X.rkF g' a' := by
  unfold RowData.rkF
  by_cases hb : X.big g a
  · rw [X.rk_big g a hb, X.rk_big g' a' (h.1 hb)]
  · rw [X.rk_small g a hb, X.rk_small g' a' (fun h' => hb (h.2 h'))]

end Formalism.L2.FormalSeriesBounds.RF

namespace Formalism.L2.FormalSeriesBounds.RF

open Formalism.IncomingBounds

section G

variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V d (I o) (J o)) (F : ∀ o, Flag (X o)) (Z : Finset Orb) (ga : Orb → Fin 2 → ZMod d → ℕ → ℕ)

theorem blkAdm (hdich : ∀ o ∈ Z, (X o).Alt ∨ ∀ a, (X o).big 0 a) (hj : ∀ o ∈ Z, (X o).j' < (X o).n)
    (hga : ∀ o ∈ Z, ∀ g a k, ga o g a k ≠ 0 → k ≤ (X o).rkF g a) : BlockAdmissible X F Z ga := by
  intro L hwt o ho q hq hatt
  refine attainsOK_of _ _ (hdich o ho) (hj o ho) q.1 q.2 (fun g a k hk => hga o ho g a k ?_) hatt
  rw [← hwt o ho g a k]
  have := le_sum_map (L o) (fun q => q.1.wt (X o) g a k) hq
  omega

end G

section Cc

theorem zmod_two_add_one_add_one (a : ZMod 2) : a + 1 + 1 = a := by revert a; decide

theorem zmod_two_even_succ_iff (a : ZMod 2) : Even (a + 1).val ↔ ¬ Even a.val := by revert a; decide

variable {C : Type} [Field C] {V : VF C}
  {Orb : Type} [Fintype Orb] {I J : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)] [∀ o g, Fintype (J o g)]
  (X : ∀ o, RowData C V 2 (I o) (J o)) (F : ∀ o, Flag (X o)) (gaC : Orb → ZMod 2 → ℕ → ℕ)

theorem blkAdmC (hA : ∀ o, (X o).Alt) (hj : ∀ o, (X o).j' < (X o).n)
    (hga : ∀ o s k, gaC o s k ≠ 0 → k ≤ (X o).rkF 0 s) : BlockAdmissibleSelfConjugate X F gaC := by
  intro L hwt o q hq hatt
  refine attainsOK_of _ _ (Or.inl (hA o)) (hj o) q.1 q.2 (fun g a k hk => ?_) hatt
  have hg : g = 0 ∨ g = 1 := by fin_cases g <;> simp
  rcases hg with rfl | rfl
  · apply hga o a k
    rw [← hwt o a k]
    have h : q.1.wt (X o) 0 a k + q.1.wt (X o) 1 (a + 1) k ≤ _ :=
      le_sum_map (L o) (fun q => q.1.wt (X o) 0 a k + q.1.wt (X o) 1 (a + 1) k) hq
    omega
  · have hk' : q.1.wt (X o) 1 (a + 1 + 1) k ≠ 0 := by rwa [zmod_two_add_one_add_one]
    have h1 : k ≤ (X o).rkF 0 (a + 1) := by
      apply hga o (a + 1) k
      rw [← hwt o (a + 1) k]
      have h : q.1.wt (X o) 0 (a + 1) k + q.1.wt (X o) 1 (a + 1 + 1) k ≤ _ :=
        le_sum_map (L o) (fun q => q.1.wt (X o) 0 (a + 1) k + q.1.wt (X o) 1 (a + 1 + 1) k) hq
      omega
    have h2 : (X o).big 0 (a + 1) ↔ (X o).big 1 a := by
      rw [big_one_iff, (hA o).2 (a + 1), (hA o).2 a]
      exact zmod_two_even_succ_iff a
    rwa [rkF_eq_of_big_iff h2] at h1

end Cc

end Formalism.L2.FormalSeriesBounds.RF
end
end

