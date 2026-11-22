import Formalism.LocalToGlobal.CharacterGerms.FirstPartialLawAtPoints
import Formalism.LocalToGlobal.CharacterGerms.CharacterHypothesisUnramified
import Formalism.LocalToGlobal.CharacterGerms.Bundle0040

-- bundled from Formalism.LocalToGlobal.CharacterGerms.CoordinateChangeComp1IntertwinesAction
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj

namespace VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {τ : Type}

variable (Y : FBChart C V O dd)

theorem coordinateChange_comp1_intertwines_action {n : ℕ} (x : O) (a : Pt C n dd) : comp1 (Y.B.A.act x) a = actAt Y x a := by
  unfold actAt
  unfold comp1
  funext i
  unfold ev
  first
  | rfl
  | (congr 1; funext q; simp)
  | (congr 1; funext q; skip)

theorem addOf_eq' {n : ℕ} (a b : Pt C n dd) : addOf Y.B.G.F a b = addAt Y a b := by
  unfold addAt
  unfold addOf
  funext i
  unfold ev
  first
  | rfl
  | (congr 1; funext q; unfold P2; rfl)
  | (congr 1; funext q; unfold P2; obtain ⟨j, k⟩ := q; fin_cases j <;> simp)

theorem actAt_addAt (x : O) {a b : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (hb : ∀ i, MvPowerSeries.constantCoeff (b i) = 0) :
    actAt Y x (addAt Y a b) = addAt Y (actAt Y x a) (actAt Y x b) := by
  have h := Y.B.A.hom x
  rw [show Y.B.G.add (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) = addAt Y (pt C dd 0) (pt C dd 1) from addOf_eq' Y _ _,
    show Y.B.G.add (comp1 (Y.B.A.act x) (pt C (n := 2) dd 0)) (comp1 (Y.B.A.act x) (pt C (n := 2) dd 1)) =
      addAt Y (comp1 (Y.B.A.act x) (pt C dd 0)) (comp1 (Y.B.A.act x) (pt C dd 1)) from addOf_eq' Y _ _,
    coordinateChange_comp1_intertwines_action, coordinateChange_comp1_intertwines_action, coordinateChange_comp1_intertwines_action] at h
  have k0 := cc_pt (C := C) (dd := dd) (0 : Fin 2)
  have k1 := cc_pt (C := C) (dd := dd) (1 : Fin 2)
  have hP := constantCoeff_pair_substitution ha hb
  have e0 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (0 : Fin 2) i)) = a := funext fun i => pair_subst_coordinate ha hb 0 i
  have e1 : (fun i => MvPowerSeries.subst (P2 a b) (pt C dd (1 : Fin 2) i)) = b := funext fun i => pair_subst_coordinate ha hb 1 i
  funext i
  have h2 := congrArg (MvPowerSeries.subst (P2 a b)) (congrFun h i)
  rw [actAt_subst Y hP (cc_addAt Y k0 k1), addAt_subst Y hP (cc_actAt Y x k0) (cc_actAt Y x k1)] at h2
  have e2 : (fun i => MvPowerSeries.subst (P2 a b) (addAt Y (pt C dd (0 : Fin 2)) (pt C dd (1 : Fin 2)) i)) =
      addAt Y a b := by
    funext j
    rw [addAt_subst Y hP k0 k1, e0, e1]
  have e3 : (fun i => MvPowerSeries.subst (P2 a b) (actAt Y x (pt C dd (0 : Fin 2)) i)) = actAt Y x a := by
    funext j
    rw [actAt_subst Y hP k0, e0]
  have e4 : (fun i => MvPowerSeries.subst (P2 a b) (actAt Y x (pt C dd (1 : Fin 2)) i)) = actAt Y x b := by
    funext j
    rw [actAt_subst Y hP k1, e1]
  rw [e2, e3, e4] at h2
  exact h2

theorem actAt_zero (x : O) : actAt Y x (fun _ : Fin dd => (0 : MvPowerSeries τ C)) = fun _ => 0 := by
  funext i
  unfold actAt
  rw [subst_zeroPt, Y.B.A.const, map_zero]

theorem actAt_sumL (x : O) : ∀ l : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l, GoodPt V a) →
    actAt Y x (sumL Y l) = sumL Y (l.map (actAt Y x))
  | [], _ => actAt_zero Y x
  | a :: l, h => by
      show actAt Y x (addAt Y a (sumL Y l)) = addAt Y (actAt Y x a) (sumL Y (l.map (actAt Y x)))
      rw [actAt_addAt Y x (h a List.mem_cons_self).1
        (good_sumL Y l fun b hb => h b (List.mem_cons_of_mem _ hb)).1,
        actAt_sumL x l fun b hb => h b (List.mem_cons_of_mem _ hb)]

theorem biadd_right_list (l2 : List (Fin dd → MvPowerSeries τ C)) (h2 : ∀ a ∈ l2, GoodPt V a) :
    ∀ l1 : List (Fin dd → MvPowerSeries τ C), (∀ a ∈ l1, GoodPt V a) →
      ∃ U : MvPowerSeries τ C, IsIU V U ∧ (l1.map fun a => mvExp (hAt Y a (sumL Y l2))).prod * U =
        (l1.map fun a => (l2.map fun b => mvExp (hAt Y a b)).prod).prod
  | [], _ => ⟨1, IsIU.one, by simp⟩
  | a :: l1, h => by
      obtain ⟨U, hU, e⟩ := biadd_right_list l2 h2 l1 fun b hb => h b (List.mem_cons_of_mem _ hb)
      obtain ⟨U', hU', e'⟩ := biadd_right Y (h a List.mem_cons_self) l2 h2
      refine ⟨U' * U, hU'.mul hU, ?_⟩
      rw [List.map_cons, List.prod_cons, List.map_cons, List.prod_cons, ← e, ← e']
      ring

theorem biadd_both (x : O) (l : List (Fin dd → MvPowerSeries τ C)) (h : ∀ a ∈ l, GoodPt V a) :
    ∃ U : MvPowerSeries τ C, IsIU V U ∧ mvExp (hAt Y (sumL Y l) (actAt Y x (sumL Y l))) * U =
      (l.map fun a => (l.map fun b => mvExp (hAt Y a (actAt Y x b))).prod).prod := by
  have hx : ∀ a ∈ l.map (actAt Y x), GoodPt V a := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := List.mem_map.1 ha
    exact (h b hb).act Y x
  obtain ⟨U, hU, e⟩ := biadd_left Y (good_sumL Y _ hx) l h
  obtain ⟨U', hU', e'⟩ := biadd_right_list Y (l.map (actAt Y x)) hx l h
  refine ⟨U * U', hU.mul hU', ?_⟩
  rw [actAt_sumL Y x l h, ← mul_assoc, e, e']
  simp only [List.map_map]
  rfl

end VP

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} [NeZero d]
  {Orb : Type} [Fintype Orb] {I : Orb → Fin 2 → Type} [∀ o g, Fintype (I o g)]

def projList (π : Orb → Fin 2 → Fin dd → PS C 1 dd) : List (Fin dd → PS C 1 dd) :=
  (Finset.univ : Finset (Orb × Fin 2)).toList.map fun s => π s.1 s.2

def SumProjSt (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) : Prop :=
  PairsSep Y p → ∀ π, IsProj Y p π → ∀ i, pull1 Y p (pt C dd (0 : Fin 1) i) = pull1 Y p (VP.sumL Y (projList π) i)

theorem biadd_of_sum (Y : FBChart C V O dd) (p : ∀ o, PairData Y d (I o)) (hS : SumProjSt Y p) : BiaddSt Y p := by
  intro hs π hπ
  have hgood : ∀ a ∈ projList π, VP.GoodPt V a := by
    intro a ha
    obtain ⟨s, -, rfl⟩ := List.mem_map.1 ha
    exact ⟨hπ.cc s.1 s.2, hπ.int s.1 s.2⟩
  have hσ := VP.good_sumL Y _ hgood
  obtain ⟨U, hU, e⟩ := VP.biadd_both Y Y.w0 (projList π) hgood
  obtain ⟨U', hU'i, hUU⟩ := VP.intInv (hU.1.pow Y.k) (by rw [map_pow, V.v.map_pow, hU.2, smul_zero])
  have hU'0 : V.v (MvPowerSeries.constantCoeff U') = 0 := by
    have h1 := congrArg (fun x => V.v (MvPowerSeries.constantCoeff x)) hUU
    simp only [map_mul, map_pow, map_one, V.v.map_mul, V.v.map_pow, V.v.map_one, hU.2, smul_zero, add_zero] at h1
    exact h1
  refine ⟨U', ⟨hU'i, hU'0⟩, ?_⟩
  set σ := VP.sumL Y (projList π) with hσd
  have cσ := VP.cc_hAt Y hσ.1 (VP.cc_actAt Y Y.w0 hσ.1)

  have e1 : mvExp ((Y.k : C) • VP.hAt Y σ (VP.actAt Y Y.w0 σ)) =
      U' * ∏ s : Orb × Fin 2, ∏ s' : Orb × Fin 2, Aterm Y π s s' := by
    have e2 : (∏ s : Orb × Fin 2, ∏ s' : Orb × Fin 2, Aterm Y π s s') =
        (mvExp (VP.hAt Y σ (VP.actAt Y Y.w0 σ)) * U) ^ Y.k := by
      rw [e]
      unfold projList
      simp only [List.map_map]
      rw [Finset.prod_map_toList, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun s _ => ?_
      show _ = ((((Finset.univ : Finset (Orb × Fin 2)).toList.map _).prod) ^ Y.k)
      rw [Finset.prod_map_toList, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun s' _ => ?_
      rw [VP.Aterm_eq Y π hπ.cc, VP.exp_nsmul (VP.cc_hAt Y (hπ.cc _ _) (VP.cc_actAt Y _ (hπ.cc _ _)))]
      rfl
    rw [e2, mul_pow, ← VP.exp_nsmul cσ]
    calc mvExp ((Y.k : C) • VP.hAt Y σ (VP.actAt Y Y.w0 σ))
        = (U' * U ^ Y.k) * mvExp ((Y.k : C) • VP.hAt Y σ (VP.actAt Y Y.w0 σ)) := by rw [hUU, one_mul]
      _ = U' * (mvExp ((Y.k : C) • VP.hAt Y σ (VP.actAt Y Y.w0 σ)) * U ^ Y.k) := by ring

  have hA := VP.cc_pull1Pt Y p
  have k0 := VP.cc_pt (C := C) (dd := dd) (0 : Fin 1)
  have hLeq : Y.B.hL C Y.h Y.w0 = VP.hAt Y (pt C dd (0 : Fin 1)) (VP.actAt Y Y.w0 (pt C dd (0 : Fin 1))) := by
    unfold FB.hL
    rw [VP.eval_two_points_eq_subst _ _ _ rfl, VP.compose_one_action_eq_actAt]
    rfl
  have hpt : (fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2) (pt C dd (0 : Fin 1) i)) =
      fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2) (σ i) := funext fun i => hS hs π hπ i
  have e3 : pull1 Y p (FB.expS C ((Y.k : C) • Y.B.hL C Y.h Y.w0)) =
      pull1 Y p (mvExp ((Y.k : C) • VP.hAt Y σ (VP.actAt Y Y.w0 σ))) := by
    rw [VP.expS_eq _ (VP.cc_smul _ (VP.cc_hL Y)), hLeq]
    unfold pull1
    rw [VP.subst_exp hA (VP.cc_smul _ (VP.cc_hAt Y k0 (VP.cc_actAt Y _ k0))), VP.subst_exp hA (VP.cc_smul _ cσ),
      VP.subst_smul hA, VP.subst_smul hA, VP.hAt_subst Y hA k0 (VP.cc_actAt Y _ k0),
      VP.hAt_subst Y hA hσ.1 (VP.cc_actAt Y _ hσ.1)]
    have a1 : (fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2)
        (VP.actAt Y Y.w0 (pt C dd (0 : Fin 1)) i)) =
        fun i => MvPowerSeries.subst (fun q : Fin 1 × Fin dd => expAll Y p q.2) (VP.actAt Y Y.w0 σ i) := by
      funext i
      rw [VP.actAt_subst Y hA k0, VP.actAt_subst Y hA hσ.1, hpt]
    rw [a1, hpt]
  rw [e3, e1, VP.pullback_one_var_mul, VP.pullback_one_var_prod]
  congr 1
  exact Finset.prod_congr rfl fun s _ => VP.pullback_one_var_prod Y p _ _

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrSf
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ CharacteristicFromRanks ValuationFitting
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (IsCh dl res HasAF)

variable {C : Type} [Field C] [CharZero C] {V : VF C} {OE : Type} [CommRing OE] [StarRing OE] {dd : ℕ} {d : ℕ} [NeZero d]
  {I0 : Type} [Fintype I0]

def UPCharSelfSt (Y : FBChart C V OE dd) (p : SelfData Y d I0) (Hc : ∀ g, (Y.rawSelf p).CartHyp V g) : Prop :=
  ∃ (h : Fin 2 → ℕ) (χ : ∀ g, Fin (h g) → Fin 2 → PS C 1 dd), (∀ g i col, Y.IsChar (χ g i col)) ∧
    ∀ g a, p.big g a →
      ∃ e : Fin (pT (fun g => RawChart.cart (Hc g)) g a) ≃ {x : I0 // (RawChart.cart (Hc g)).ty (Sum.inl x) = a},
        ((Y.rawSelf p).AltC →
          S4.lenCoker V.v (Matrix.of fun c i => p.yOf g (χ g i) (e c)) ≤
            ((upB V.l (p.n + p.j) p.j' (gam V.l) : ℝ) : WithTop ℝ)) ∧
        ((∀ b, p.big g b) →
          S4.lenCoker V.v (Matrix.of fun c i => p.yOf g (χ g i) (e c)) ≤
            ((upB V.l (p.n + p.j) p.j' 0 : ℝ) : WithTop ℝ))

theorem chStSelf_of_upChar (Y : FBChart C V OE dd) (p : SelfData Y d I0) (hr : (Y.rawSelf p).RankHyp)
    (Hc : ∀ g, (Y.rawSelf p).CartHyp V g) (h : UPCharSelfSt Y p Hc) : RawChart.CHSt Hc := by
  obtain ⟨hh, χ, hχ, hUP⟩ := h
  exact CH_of_UP (fun g => RawChart.cart (Hc g)) p.n p.j p.j' p.big hr.big_compl hh
    (fun g i x => p.yOf g (χ g i) x) (fun g i x => p.yOf_int g (hχ g i) x) hUP
    (fun g i S t ht => charGermSelf_holds C V OE dd Y d I0 p Hc (χ g i) (hχ g i) g S t ht)

theorem isChar_one (Y : FBChart C V OE dd) : Y.IsChar (1 : PS C 1 dd) := by
  refine ⟨fun mu => ?_, map_one _, ?_⟩
  · rw [MvPowerSeries.coeff_one]
    split_ifs
    · exact VF.Ge.one
    · exact VF.Ge.zero 0
  · simp only [ev_one, mul_one]

theorem dlogC_one (i : Fin dd) : dlogC (1 : PS C 1 dd) i = 0 := by
  simp [dlogC, MvPowerSeries.coeff_one]

theorem lenCoker_smul {v : AddValuation C (WithTop ℝ)} {m h : ℕ} (B : Matrix (Fin m) (Fin h) C) {γ : C} (hγ : v γ = 0) :
    S4.lenCoker v (γ • B) = S4.lenCoker v B := by
  unfold S4.lenCoker
  congr 1
  funext g
  have e : (γ • B).submatrix id g = γ • B.submatrix id g := Matrix.ext fun i j => rfl
  rw [e, Matrix.det_smul, AddValuation.map_mul, AddValuation.map_pow, hγ, smul_zero, zero_add]

def rk0 {Y : FBChart C V OE dd} (p : SelfData Y d I0) (b : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I0 => p.ty0 c = b).card

def rkS {Y : FBChart C V OE dd} (p : SelfData Y d I0) (g : Fin 2) (b : ZMod d) : ℕ :=
  (Finset.univ.filter fun c : I0 => (Y.rawSelf p).ty g c = b).card

def a0Of {Y : FBChart C V OE dd} (p : SelfData Y d I0) (g : Fin 2) (a : ZMod d) : ZMod d := if g = 0 then a else a + p.hd

theorem ty_iff {Y : FBChart C V OE dd} (p : SelfData Y d I0) (g : Fin 2) (a : ZMod d) (c : I0) :
    (Y.rawSelf p).ty g c = a ↔ p.ty0 c = a0Of p g a := by
  show (if g = 0 then p.ty0 c else p.ty0 c + p.hd) = a ↔ p.ty0 c = (if g = 0 then a else a + p.hd)
  split_ifs with hg
  · exact Iff.rfl
  · constructor
    · intro h
      rw [← h, add_assoc, p.hd_two, add_zero]
    · intro h
      rw [h, add_assoc, p.hd_two, add_zero]

theorem rk_shift {Y : FBChart C V OE dd} (p : SelfData Y d I0) (g : Fin 2) (a k : ZMod d) :
    rk0 p (a0Of p g a + k + p.hd) = rkS p (1 - g) (a + k) := by
  have h : a0Of p g a + k + p.hd = a0Of p (1 - g) (a + k) := by
    have h2 := p.hd_two
    fin_cases g <;> simp [a0Of] <;> linear_combination h2
  unfold rk0 rkS
  simp only [ty_iff, h]

def AFBoundS (Y : FBChart C V OE dd) (p : SelfData Y d I0) (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (FR : Fin dd → PS R 2 dd) : Prop :=
  ∀ a0 : ZMod d, ∃ (s : ℕ) (e : Fin s ≃ {x : I0 // p.ty0 x = a0}) (W : Fin s → Fin dd → R) (xs : NNReal),
    (∀ c i, algebraMap R C (W c i) = p.e (e c) i) ∧ HasAF vm FR W xs ∧
      vm (V.l : C) ^ (S4.frobSum V.l (fun b => rk0 p (b + p.hd)) a0) ≤ xs

theorem exists_unit_col {Y : FBChart C V OE dd} (p : SelfData Y d I0) (a0 : ZMod d) (g : Fin 2) :
    ∃ col : Fin 2, V.v (p.gm a0 col g) = 0 := by
  by_contra hno
  push Not at hno
  have hpos : ∀ col, V.MM (p.gm a0 col g) := fun col =>
    lt_of_le_of_ne (SelfConjugateGermZero.gm_int Y p a0 col g) (Ne.symm (hno col))
  have h1 := p.gm_hyp a0 (1 - g) g
  have hne : (1 - g : Fin 2) ≠ g := by fin_cases g <;> decide
  rw [if_neg hne] at h1
  have h2 : V.MM (∑ r, p.gm (a0 + p.hd) r (1 - g) * p.gm a0 r g) := by
    rw [Fin.sum_univ_two]
    have t : ∀ r, V.MM (p.gm (a0 + p.hd) r (1 - g) * p.gm a0 r g) := fun r => by
      unfold VF.MM
      rw [V.v.map_mul]
      exact lt_of_lt_of_le (hpos r) (le_add_of_nonneg_left (SelfConjugateGermZero.gm_int Y p _ r _))
    exact lt_of_lt_of_le (lt_min (t 0) (t 1)) (V.v.map_add _ _)
  rw [h1] at h2
  unfold VF.MM at h2
  rw [V.v.map_one] at h2
  exact lt_irrefl _ h2

theorem upCharS_of_afBound (Y : FBChart C V OE dd) (p : SelfData Y d I0) (hr : (Y.rawSelf p).RankHyp)
    (Hc : ∀ g, (Y.rawSelf p).CartHyp V g) (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C]
    (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ)) (h1 : (vm (V.l : C) : ℝ) < 1)
    (FR : Fin dd → PS R 2 dd) (hF : ∀ i, Y.B.G.F i = toC (FR i))
    (hF0 : ∀ i, MvPowerSeries.constantCoeff (FR i) = 0) (h : AFBoundS Y p vm R FR) : UPCharSelfSt Y p Hc := by
  have hR : ∀ x : R, V.Ge 0 (algebraMap R C x) := fun x => vA_nonneg hT hv h0 h1 x
  have hl1 : 1 < V.l := V.l_prime.one_lt
  have key : ∀ g a, ∃ (N : ℕ) (u : Fin N → Fin 2 → PS C 1 dd), (∀ k col, Y.IsChar (u k col)) ∧
      ∃ e : Fin (pT (fun g => RawChart.cart (Hc g)) g a) ≃ {x : I0 // (RawChart.cart (Hc g)).ty (Sum.inl x) = a},
        S4.lenCoker V.v (Matrix.of fun c k => p.yOf g (u k) (e c)) ≤
          ((S4.frobSum V.l (rkS p (1 - g)) a : ℝ) : WithTop ℝ) := by
    intro g a
    obtain ⟨s, e0, W, xs, hW, ⟨N, u, hu, hx⟩, hS⟩ := h (a0Of p g a)
    let e1 : Fin s ≃ {x : I0 // (Y.rawSelf p).ty g x = a} :=
      e0.trans (Equiv.subtypeEquivRight fun x => (ty_iff p g a x).symm)
    have he1 : ∀ c, ((e1 c : {x : I0 // (Y.rawSelf p).ty g x = a}) : I0) = e0 c := fun _ => rfl
    have hs : s = pT (fun g => RawChart.cart (Hc g)) g a := by
      have := Fintype.card_congr e1
      rw [Fintype.card_fin, Fintype.card_subtype] at this
      exact this
    subst hs
    obtain ⟨col0, hcol⟩ := exists_unit_col p (a0Of p g a) g
    refine ⟨N, fun k col => if col = col0 then toC (u k) else 1, fun k col => ?_, e1, ?_⟩
    · show Y.IsChar (if col = col0 then toC (u k) else 1)
      split_ifs
      · exact isChar_of_isCh Y hR FR hF hF0 (hu k)
      · exact isChar_one Y
    · have hb := lenCoker_le_of_hasLen hT hv h0 h1 W u hx hS
      have hsum : S4.frobSum V.l (fun b => rk0 p (b + p.hd)) (a0Of p g a) = S4.frobSum V.l (rkS p (1 - g)) a := by
        unfold S4.frobSum
        exact tsum_congr fun k => by beta_reduce; rw [rk_shift]
      rw [hsum] at hb
      have hm : (Matrix.of fun c k => p.yOf g (fun col => if col = col0 then toC (u k) else 1) (e1 c)) =
          p.gm (a0Of p g a) col0 g •
            (Matrix.of fun c k => ∑ i, dlogC (toC (C := C) (u k)) i * algebraMap R C (W c i)) := by
        ext c k
        simp only [Matrix.of_apply, Matrix.smul_apply, smul_eq_mul]
        unfold SelfData.yOf
        rw [Finset.sum_eq_single col0]
        · beta_reduce
          rw [if_pos rfl, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          show _ * (p.gm (p.ty0 (e1 c)) col0 g * p.e (e1 c) i) = _
          rw [he1, (e0 c).2, hW]
          ring
        · intro col _ hne
          beta_reduce
          rw [if_neg hne]
          exact Finset.sum_eq_zero fun i _ => by rw [dlogC_one, zero_mul]
        · intro hne
          exact absurd (Finset.mem_univ _) hne
      have hfin : S4.lenCoker V.v
          (Matrix.of fun c k => p.yOf g (fun col => if col = col0 then toC (u k) else 1) (e1 c)) ≤
          ((S4.frobSum V.l (rkS p (1 - g)) a : ℝ) : WithTop ℝ) := by
        rw [hm, lenCoker_smul _ hcol]
        exact hb
      exact hfin
  choose N u hu e he using key
  let eq : ∀ g, (Σ a : ZMod d, Fin (N g a)) ≃ Fin (Fintype.card (Σ a : ZMod d, Fin (N g a))) := fun g => Fintype.equivFin _
  refine ⟨fun g => Fintype.card (Σ a : ZMod d, Fin (N g a)),
    fun g i => u g ((eq g).symm i).1 ((eq g).symm i).2, fun g i col => hu g _ _ col, fun g a hb => ?_⟩
  have hle' : S4.lenCoker V.v (Matrix.of fun c i => p.yOf g (u g ((eq g).symm i).1 ((eq g).symm i).2) (e g a c)) ≤
      ((S4.frobSum V.l (rkS p (1 - g)) a : ℝ) : WithTop ℝ) := by
    refine le_trans (lenCoker_mono V.v _ (fun k : Fin (N g a) => eq g ⟨a, k⟩)) ?_
    have e3 : (Matrix.of fun c i => p.yOf g (u g ((eq g).symm i).1 ((eq g).symm i).2) (e g a c)).submatrix id
        (fun k : Fin (N g a) => eq g ⟨a, k⟩) = Matrix.of fun c k => p.yOf g (u g a k) (e g a c) := by
      ext c k
      simp only [Matrix.submatrix_apply, Matrix.of_apply, id]
      rw [Equiv.symm_apply_apply]
    rw [e3]
    exact he g a
  have hc1 : ∀ b, p.big g b → rkS p (1 - g) b = p.j' := fun b hb' =>
    hr.rk_small (1 - g) b (fun hh => (hr.big_compl g b).mp hh hb')
  have hc2 : ∀ b, ¬ p.big g b → rkS p (1 - g) b = p.n + p.j := fun b hb' =>
    hr.rk_big (1 - g) b ((hr.big_compl g b).mpr hb')
  refine ⟨e g a, fun hA => ?_, fun hB => ?_⟩
  · rw [← frobSum_conj_alt hl1 p.n p.j p.j' (p.big g) (alt_step p.big hr.big_compl hA g) (rkS p (1 - g)) hc1 hc2 a hb]
    exact hle'
  · rw [← frobSum_conj_all hl1 p.n p.j p.j' (rkS p (1 - g)) (fun b => hc1 b (hB b)) a]
    exact hle'

end UpFBr

end Formalism.L2.FormalSeriesBounds
end
end

