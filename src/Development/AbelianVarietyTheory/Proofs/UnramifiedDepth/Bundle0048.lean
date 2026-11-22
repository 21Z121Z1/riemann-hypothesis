import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.Bundle0016
import Formalism.LocalToGlobal.CharacterGerms.Bundle0006
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ProdFactorialDiag
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0042
import Formalism.LocalToGlobal.CharacterGerms.ValuationChoiceHypothesis
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0009
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MulFlowValLe
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0010
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MonomialBlockSupplyBothTypings
section
noncomputable section
open scoped BigOperators
open Classical

namespace GlobalTheory.MonBlock

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds MvPowerSeries GlobalTheory.MinorGerm

variable {C : Type} [Field C]

def Tan {σ : Type} (x : σ) (F : MvPowerSeries σ C) : Prop :=
  ∀ m : σ →₀ ℕ, m.degree ≤ 1 → coeff m F = coeff m (X x : MvPowerSeries σ C)

theorem Tan.subst {σ τ : Type} [Finite σ] {x : σ} {F : MvPowerSeries σ C} (h : Tan x F) (e : σ → τ) :
    Tan (e x) (F.subst fun j => (X (e j) : MvPowerSeries τ C)) := by
  intro m hm
  have h1 : rename e F = F.subst fun j => (X (e j) : MvPowerSeries τ C) := rename_eq_subst e F
  rw [← h1, ← rename_X e x, coeff_rename, coeff_rename]
  refine Finset.sum_congr rfl fun y hy => h y ?_
  have : Finsupp.mapDomain e y = m := by simpa using hy
  rw [← this, Finsupp.degree_mapDomain] at hm
  exact hm

variable {V : VF C} {d : ℕ}

theorem tan_std {I J : Type} [Fintype I] [Fintype J] (X : Cart V d I J)
    {t : I → MvPowerSeries I C} (ht : (GlobalTheory.CharBlock.stdSys X).IsT t) (x : I) : Tan x (t x) := by
  intro m hm
  have h := ht.2 x m
  rw [Sys.eqn_eq] at h
  have h2 : (GlobalTheory.CharBlock.stdSys X).Rr t x m = 0 := by
    unfold Sys.Rr
    refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun c _ => ?_
    have h3 := le_order_pow_of_constantCoeff_eq_zero (V.l ^ (s + 1)) (ht.1 c)
    have h4 := Sys.two_le_pow (V := V) s
    rw [coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast (by omega)) h3), mul_zero]
  have h5 : (GlobalTheory.CharBlock.stdSys X).Mt = 1 := by
    ext a b
    simp [Sys.Mt, GlobalTheory.CharBlock.stdSys, Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [h2, h5, Matrix.vecMul_one, add_zero] at h
  rw [coeff_X]
  convert h

variable {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]

theorem cc_upG (g : Fin 2) (F : MvPowerSeries (I g) C) :
    constantCoeff (upG g F) = constantCoeff F := by
  have h1 : rename (fun x : I g => (⟨g, x⟩ : WV I)) F = upG g F := rename_eq_subst _ F
  rw [← h1, constantCoeff_rename]

def IsMon (t : ∀ g, I g → MvPowerSeries (I g) C) (F : MvPowerSeries (WV I) C) : Prop :=
  ∃ m : WV I →₀ ℕ, F = subst (fun w : WV I => upG w.1 (t w.1 w.2)) (monomial m (1 : C))

section
variable {t : ∀ g, I g → MvPowerSeries (I g) C} (h0 : ∀ g c, constantCoeff (t g c) = 0)
include h0

theorem hasSubst_upG_curveSystem : HasSubst (fun w : WV I => upG w.1 (t w.1 w.2)) :=
  hasSubst_of_constantCoeff_zero fun w => by rw [cc_upG, h0]

theorem isMon_one : IsMon t 1 :=
  ⟨0, by rw [← coe_substAlgHom (hasSubst_upG_curveSystem h0)]; exact (map_one _).symm⟩

theorem IsMon.mul {F G : MvPowerSeries (WV I) C} (hF : IsMon t F) (hG : IsMon t G) :
    IsMon t (F * G) := by
  obtain ⟨m, rfl⟩ := hF
  obtain ⟨m', rfl⟩ := hG
  refine ⟨m + m', ?_⟩
  rw [← subst_mul (hasSubst_upG_curveSystem h0), monomial_mul_monomial, one_mul]

theorem isMon_pow (g : Fin 2) (c : I g) (n : ℕ) : IsMon t (upG g (t g c) ^ n) := by
  induction n with
  | zero => simpa using isMon_one h0
  | succ n ih =>
    rw [pow_succ]
    refine ih.mul h0 ⟨Finsupp.single ⟨g, c⟩ 1, ?_⟩
    exact (subst_X (hasSubst_upG_curveSystem h0) (⟨g, c⟩ : WV I)).symm

theorem isMon_prod {ι : Type} (s : Finset ι) (F : ι → MvPowerSeries (WV I) C)
    (h : ∀ i, IsMon t (F i)) : IsMon t (∏ i ∈ s, F i) :=
  Finset.prod_induction _ _ (fun _ _ => IsMon.mul h0) (isMon_one h0) fun i _ => h i

omit h0 in
theorem IsMon.mem {F : MvPowerSeries (WV I) C} (hF : IsMon t F) : F ∈ IntGerm V t := by
  obtain ⟨m, rfl⟩ := hF
  refine ⟨_, fun μ => ?_, rfl⟩
  rw [coeff_monomial]
  split_ifs
  · exact VF.Ge.one
  · exact VF.Ge.zero 0

end

theorem degree_dg {σ : Type} {N N' : ℕ} (j : Fin N × Fin N' → σ) (e : ℕ → ℕ) :
    (dg j (monAl N N' e)).degree = monDeg N N' e := by
  rw [← sum_monAl, Fin.sum_univ_eq_sum_range (fun ρ => monAl N N' e ρ) N, dg, map_sum]
  refine Finset.sum_congr rfl fun ρ hρ => ?_
  unfold dgOne
  split_ifs with h
  · simp
  · rw [monAl_eq_zero e fun h' => h ⟨Finset.mem_range.1 hρ, h'⟩, map_zero]

variable [NeZero d]

theorem core (X : RowData C V d I J) (g : Fin 2) (r : ZMod d → ℕ) (en : ∀ a, Fin (r a) → I g)
    (hinj : ∀ a, Function.Injective (en a)) (hty : ∀ a c, (X.G g).ty (Sum.inl (en a c)) = a)
    (e : ZMod d → ℕ → ℕ) (N : ℕ) :
    ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) C), (∀ g, (S g).IsT (t g)) ∧
      ∃ gr : Fin N → MvPowerSeries (WV I) C, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
        V.v (ValOf X.hL (∏ a : ZMod d, MvPolynomial.rename
          (fun x : Fin N × Fin (r a) => ((x.1, ⟨g, en a x.2⟩) : Fin N × WV I))
          (monP C N (r a) (e a))) (fun _ => none) gr) ≤
          (((((∑ a, monDeg N (r a) (e a) : ℕ) : ℝ) / ((V.l : ℝ) - 1)) : ℝ) : WithTop ℝ) ∧
        ((∀ a ρ, monAl N (r a) (e a) ρ < V.l) → V.v (ValOf X.hL (∏ a : ZMod d, MvPolynomial.rename
          (fun x : Fin N × Fin (r a) => ((x.1, ⟨g, en a x.2⟩) : Fin N × WV I))
          (monP C N (r a) (e a))) (fun _ => none) gr) ≤ ((0 : ℝ) : WithTop ℝ)) := by
  choose t ht _ using fun g => tExistsUnique (X.G g) (GlobalTheory.CharBlock.stdSys (X.G g))
  have h0 : ∀ g c, constantCoeff (t g c) = 0 := fun g => (ht g).1
  let j : ∀ a, Fin N × Fin (r a) → Fin N × WV I := fun a x => (x.1, ⟨g, en a x.2⟩)
  have hj : ∀ a a' y y', j a y = j a' y' → a = a' := by
    intro a a' y y' h
    have h1 : en a y.2 = en a' y'.2 := eq_of_heq (Sigma.mk.inj (Prod.mk.inj h).2).2
    rw [← hty a y.2, h1, hty]
  have hj' : ∀ a, Function.Injective (j a) := by
    intro a y y' h
    exact Prod.ext (Prod.mk.inj h).1 (hinj a (eq_of_heq (Sigma.mk.inj (Prod.mk.inj h).2).2))
  let T : Fin N × WV I → MvPowerSeries (Fin N × WV I) C :=
    fun x => rowCopy x.1 (upG x.2.1 (t x.2.1 x.2.2))
  have hT : TangentId T := fun x =>
    ((tan_std _ (ht x.2.1) x.2.2).subst (fun c : I x.2.1 => (⟨x.2.1, c⟩ : WV I))).subst
      fun w : WV I => (x.1, w)
  let gr : Fin N → MvPowerSeries (WV I) C := fun ρ => ∏ a : ZMod d,
    if h : ρ.val < r a then upG g (t g (en a ⟨ρ.val, h⟩)) ^ monAl N (r a) (e a) ρ.val else 1
  have hgr : ∀ ρ, gr ρ ∈ IntGerm V t := fun ρ => IsMon.mem <| isMon_prod h0 _ _ fun a => by
    split_ifs
    · exact isMon_pow h0 _ _ _
    · exact isMon_one h0
  have hlead := lead_prod (C := C)
    (p := fun x : Fin N × WV I => ∃ a y, x = j a y ∧ y.1.val = y.2.val) Finset.univ _ _
    fun a _ => lead_monP (j a) (fun b c => ⟨fun ⟨a', y, h1, h2⟩ => by
      obtain rfl := hj _ _ _ _ h1
      obtain rfl := hj' _ h1
      exact h2, fun h => ⟨a, (b, c), rfl, h⟩⟩) (e a)
  have hlow := low_prod Finset.univ _ _ fun a _ => low_monG (j a) hT (e a)
  have hval : ValOf X.hL (∏ a : ZMod d, MvPolynomial.rename (j a) (monP C N (r a) (e a)))
      (fun _ => none) gr = (mfact (∑ a, dg (j a) (monAl N (r a) (e a))) : C) := by
    rw [← jet_eq hlead hlow]
    unfold ValOf
    congr 1
    have hs : ∀ ρ : Fin N, HasSubst
        (fun w : WV I => (MvPowerSeries.X (ρ, w) : MvPowerSeries (Fin N × WV I) C)) :=
      fun ρ => hasSubst_of_constantCoeff_zero (by simp)
    unfold monG
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun ρ _ => ?_
    have hc : ∀ F, rowCopy ρ F = substAlgHom (hs ρ) F := fun F => by
      rw [coe_substAlgHom]; rfl
    rw [hc, hc, map_zero, GlobalTheory.CharBlock.mvExp_zero, mul_one, map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    split_ifs
    · rw [map_pow, ← hc]
    · rw [map_one]
  refine ⟨fun g => GlobalTheory.CharBlock.stdSys (X.G g), t, ht, gr, hgr, ?_, fun h => ?_⟩
  · rw [hval, GlobalTheory.LegendreFacts.mfact_eq_prod,
      val_nat V.v V.l_prime V.v_l (Finset.prod_ne_zero_iff.2 fun _ _ => Nat.factorial_ne_zero _),
      WithTop.coe_le_coe, GlobalTheory.LegendreBounds.padicValNat_prod_factorial V.l V.l_prime]
    have hd : ∑ a, monDeg N (r a) (e a) = ∑ x, (∑ a, dg (j a) (monAl N (r a) (e a))) x := by
      rw [← Finsupp.degree_eq_sum, map_sum]
      exact Finset.sum_congr rfl fun a _ => (degree_dg _ _).symm
    rw [hd, Nat.cast_sum, Finset.sum_div]
    exact Finset.sum_le_sum fun ρ _ => GlobalTheory.LegendreBounds.upper V.l V.l_prime _
  · rw [hval, GlobalTheory.LegendreFacts.mfact_eq_prod]
    refine le_of_eq (val_coprime V.v V.l_prime V.v_l fun hd => ?_)
    obtain ⟨x, -, hx⟩ := (Prime.dvd_finset_prod_iff V.l_prime.prime _).1 hd
    refine absurd ((V.l_prime.dvd_factorial).1 hx) (not_le.2 ?_)
    rw [Finsupp.finset_sum_apply]
    by_cases hx' : ∃ a y, x = j a y
    · obtain ⟨a, y, rfl⟩ := hx'
      rw [Finset.sum_eq_single a, dg_apply (j a) (hj' a) _ y.1 y.2]
      · split_ifs
        · exact h _ _
        · exact V.l_prime.pos
      · intro a' _ ha
        exact dg_apply_of_notMem _ _ _ fun y' h' => ha (hj _ _ _ _ h').symm
      · simp
    · rw [Finset.sum_eq_zero fun a _ => dg_apply_of_notMem _ _ _ fun y' h' => hx' ⟨a, y', h'⟩]
      exact V.l_prime.pos

theorem monSupply : MONSupply ∧ RF.MONSupply := by
  constructor
  · intro C _ V d _ I J _ _ X F g e N
    obtain ⟨S, t, ht, gr, hgr, h1, h2⟩ :=
      core X g (X.rk g) (F.en g) (F.en_inj g) (F.en_ty g) e N
    exact ⟨⟨S, t, ht, gr, hgr, h1⟩, fun h => ⟨S, t, ht, gr, hgr, h2 h⟩⟩
  · intro C _ V d _ I J _ _ X F g e N
    obtain ⟨S, t, ht, gr, hgr, h1, h2⟩ :=
      core X g (X.rkF g) (F.en g) (F.en_inj g) (F.en_ty g) e N
    exact ⟨⟨S, t, ht, gr, hgr, h1⟩, fun h => ⟨S, t, ht, gr, hgr, h2 h⟩⟩

end GlobalTheory.MonBlock
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.OrbitSumFiftyOne
section
open scoped BigOperators
open Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.OrbitPlan

theorem exists_good {S : ℕ} {G : Set ℕ} (h : Windows S G) {r : ℝ} (hr : 0 ≤ r) :
    ∃ y ∈ G, (y : ℝ) ≤ r ∧ r - y ≤ S := by
  have h1 := Nat.floor_le hr
  have h2 := Nat.lt_floor_add_one r
  by_cases hS : S ≤ ⌊r⌋₊ + 1
  · obtain ⟨y, hy, hy1, hy2⟩ := h.2 (⌊r⌋₊ + 1 - S)
    have a1 : y ≤ ⌊r⌋₊ := by omega
    have a2 : ⌊r⌋₊ + 1 ≤ y + S := by omega
    have b1 : (y : ℝ) ≤ ⌊r⌋₊ := by exact_mod_cast a1
    have b2 : (⌊r⌋₊ : ℝ) + 1 ≤ y + S := by exact_mod_cast a2
    exact ⟨y, hy, by linarith, by linarith⟩
  · have a2 : ⌊r⌋₊ + 1 ≤ S := by omega
    have b2 : (⌊r⌋₊ : ℝ) + 1 ≤ S := by exact_mod_cast a2
    exact ⟨0, h.1, by simpa using hr, by simp only [Nat.cast_zero]; linarith⟩

theorem logTerm_nonneg {l n : ℕ} (hl : 5 ≤ l) (hn : 1 ≤ n) :
    0 ≤ (n : ℝ) * (Real.logb l n + 1) := by
  have h1 : (1 : ℝ) < l := by exact_mod_cast (by omega : 1 < l)
  have h2 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have := Real.logb_nonneg h1 h2
  positivity

theorem orbit_sum_fifty_one : WindowedChoiceExistsWithBound := by
  intro l d _ hp hl hd he n m k S hn hk hS W Good hG
  classical
  have hW0 : (0 : ZMod d → ℝ) ≤ fun a => (W a : ℝ) := fun a => Nat.cast_nonneg _
  obtain ⟨ys, hflow, hsupp, hcard, hval⟩ :=
    GlobalTheory.BasicFlow.main.1 l d (by omega) (fun a => (W a : ℝ)) hW0 (i0 k l)
  obtain ⟨hodd, h3, -, hthl⟩ := GlobalTheory.T.levelsUsed_balancedValue_orbitSums.1 k l hk (by omega)
  have hex : ∀ a i, ∃ y : ℕ, (y ≠ 0 → y ∈ Good a i) ∧ (y : ℝ) ≤ ys a i ∧
      ys a i - y ≤ (S : ℝ) + 1 := by
    intro a i
    by_cases hc : i ∈ oddLevels d ∧ i < i0 k l
    · obtain ⟨y, hy, h1, h2⟩ := exists_good (hG a i hc.1 hc.2) (hflow.1 a i)
      exact ⟨y, fun _ => hy, h1, by linarith⟩
    · have : ys a i = 0 := hsupp a i (by
        by_cases h : i ∈ oddLevels d
        · left; by_contra h'; exact hc ⟨h, by omega⟩
        · right; exact h)
      refine ⟨0, fun h => absurd rfl h, by simp [this], ?_⟩
      simp only [this, Nat.cast_zero, sub_zero]; positivity
  choose y hyG hyle hyge using hex
  have hy0 : ∀ a i, ys a i = 0 → y a i = 0 := by
    intro a i h
    have := hyle a i
    rw [h] at this
    exact_mod_cast le_antisymm this (Nat.cast_nonneg _)
  have hl0 : (0 : ℝ) < l := by exact_mod_cast (by omega : 0 < l)
  have hl1 : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (5 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hle : ∀ a, (∑ i ∈ oddLevels d, l ^ i * y a i) +
      (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i) ≤ W a := by
    intro a
    have h1 : (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) ≤ ∑ i ∈ oddLevels d, (l : ℝ) ^ i * ys a i :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hyle a i) (by positivity)
    have h2 : (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) ≤
        ∑ i ∈ oddLevels d, ys (a - (i : ZMod d)) i :=
      Finset.sum_le_sum fun i _ => hyle _ i
    have h3 := hflow.2 a
    have : (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
        (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) ≤ (W a : ℝ) := by
      simp only at h3
      linarith
    exact_mod_cast this
  let p : Plan l d W :=
    { y := y
      u := fun a => W a - ((∑ i ∈ oddLevels d, l ^ i * y a i) +
        (∑ i ∈ oddLevels d, y (a - (i : ZMod d)) i))
      supp := fun a i hi => hy0 a i (hsupp a i (Or.inr hi))
      bal := fun a => by have := hle a; omega }
  have hcard' : (((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d).filter
      fun x => y x.1 x.2 ≠ 0).card ≤ d := by
    refine le_trans (Finset.card_le_card ?_) hcard
    intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hx.1, fun h => hx.2 (hy0 _ _ h)⟩
  refine ⟨p, ⟨fun a i hi => hy0 a i (hsupp a i (Or.inl hi)), hyG, hcard'⟩, ?_⟩
  have hbal : ∀ a, (W a : ℝ) = (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) +
      (∑ i ∈ oddLevels d, (y (a - (i : ZMod d)) i : ℝ)) + (p.u a : ℝ) := by
    intro a
    have := p.bal a
    exact_mod_cast this
  set L : ℝ := (n : ℝ) * (Real.logb l n + 1) with hL
  have hL0 : 0 ≤ L := logTerm_nonneg hl hn
  have key := GlobalTheory.T.sizeData_small_bound l d (by omega) hd n m (thl k l) ((S : ℝ) + 1) (fun a => (W a : ℝ)) ys y
    (fun a => (p.u a : ℝ)) (fun _ => 0) (fun a => chBd l n m (p.u a)) (fun _ => 0)
    (fun a i => blockBd l n m i (y a i))
    (fun a i => (if y a i ≠ 0 then L else 0) +
      ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y a i / ((l : ℝ) - 1))
    hW0 hflow (by rw [hthl, inv_mul_eq_div]; exact hval) hyle hyge hy0
    (fun a => Nat.cast_nonneg _) (fun _ => le_rfl) (fun a => by rw [add_zero]; exact hbal a)
    (fun a i _ => by
      by_cases h : y a i = 0
      · simp [blockBd, h]
      · simp only [blockBd, bdP, h, if_false, ne_eq, not_false_eq_true, if_true, hL]
        linarith)
    (fun a => le_rfl) (fun _ => by simp)
  simp only [Finset.sum_const_zero, add_zero, zero_div, Finset.sum_add_distrib] at key

  have e1 : (∑ a, ∑ i ∈ oddLevels d, (if y a i ≠ 0 then L else 0)) ≤ d * L := by
    rw [← Finset.sum_product' (f := fun a i => if y a i ≠ 0 then L else 0), ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard') hL0
  have e2 : (n : ℝ) * ((S : ℝ) + 1) * (((Finset.univ : Finset (ZMod d)) ×ˢ oddLevels d).filter
      (fun p => ys p.1 p.2 ≠ 0)).card ≤ n * ((S : ℝ) + 1) * d :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) (by positivity)
  have hi3 : (3 : ℝ) ≤ i0 k l := by exact_mod_cast h3
  have hrow : ∀ a, (∑ i ∈ oddLevels d,
      ((i : ℝ) + 1) * m * ((l : ℝ) ^ i + 1) * y a i / ((l : ℝ) - 1)) ≤
      (2 * ((i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1)) * W a := by
    intro a
    have c0 : 0 ≤ 2 * ((i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1) :=
      div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) hl1.le
    have h1 : (∑ i ∈ oddLevels d, (l : ℝ) ^ i * y a i) ≤ W a := by
      have : (∑ i ∈ oddLevels d, l ^ i * y a i) ≤ W a := le_trans (Nat.le_add_right _ _) (hle a)
      exact_mod_cast this
    refine le_trans ?_ (mul_le_mul_of_nonneg_left h1 c0)
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    by_cases h : y a i = 0
    · simp [h]
    have hi1 : i < i0 k l := by
      by_contra h'
      exact h (hy0 a i (hsupp a i (Or.inl (by omega))))
    have hio : Odd i := (Finset.mem_filter.1 hi).2
    have hi2 : i + 2 ≤ i0 k l := by
      obtain ⟨s, hs⟩ := hio
      obtain ⟨t, ht⟩ := hodd
      omega
    have hi2' : (i : ℝ) + 1 ≤ (i0 k l : ℝ) - 1 := by
      have : (i : ℝ) + 2 ≤ i0 k l := by exact_mod_cast hi2
      linarith
    have hpow : (1 : ℝ) ≤ (l : ℝ) ^ i := one_le_pow₀ (by linarith)
    rw [div_mul_eq_mul_div]
    refine div_le_div_of_nonneg_right ?_ hl1.le
    have q : ((i : ℝ) + 1) * ((l : ℝ) ^ i + 1) ≤ ((i0 k l : ℝ) - 1) * (2 * (l : ℝ) ^ i) :=
      mul_le_mul hi2' (by linarith) (by positivity) (by linarith)
    have := mul_le_mul_of_nonneg_right q (show (0 : ℝ) ≤ (m : ℝ) * y a i by positivity)
    linarith
  have e3 := Finset.sum_le_sum fun a (_ : a ∈ (Finset.univ : Finset (ZMod d))) => hrow a
  rw [← Finset.mul_sum] at e3
  have e4 : (m : ℝ) * (∑ a, (p.u a : ℝ)) / ((l : ℝ) - 1) ≤ m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) := by
    refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum fun a _ => ?_) (Nat.cast_nonneg _)) hl1.le
    exact_mod_cast Nat.sub_le _ _
  have e5 : (2 * (i0 k l : ℝ) - 1) * m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) =
      (2 * ((i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1)) * (∑ a, (W a : ℝ)) +
        m * (∑ a, (W a : ℝ)) / ((l : ℝ) - 1) := by ring
  rw [e5]
  change (∑ a, ∑ i ∈ oddLevels d, blockBd l n m i (y a i)) + ∑ a, chBd l n m (p.u a) ≤ _
  linarith

theorem contentOrbit : ContentOrbit := by
  intro l d _ hp hl hd he n m k S hn hk hS W Good T θ w th hG hT hw hTW hth hθ
  obtain ⟨p, hok, hb⟩ := orbit_sum_fifty_one l d hp hl hd he n m k S hn hk hS W Good hG
  refine ⟨p, hok, ?_⟩
  have hs := GlobalTheory.FlowScaling.main.2.1 l d (by omega) hd he n T θ w (fun a => (W a : ℝ)) th hT hw hTW
    hth hθ
  obtain ⟨-, h3, -, hthl⟩ := GlobalTheory.T.levelsUsed_balancedValue_orbitSums.1 k l hk (by omega)
  have hi3 : (3 : ℝ) ≤ i0 k l := by exact_mod_cast h3
  have hl1 : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (5 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have ht0 : 0 ≤ thl k l := by rw [hthl]; positivity
  have hsum : T * (∑ a, (W a : ℝ)) ≤ ∑ a, w a := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    rw [hTW a]
    have := mul_nonneg (hw a).le (hth a).1
    linarith
  have c0 : 0 ≤ (2 * (i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1) :=
    div_nonneg (mul_nonneg (by linarith) (Nat.cast_nonneg _)) hl1.le
  have e1 := mul_le_mul_of_nonneg_left hsum c0
  have e2 := mul_le_mul_of_nonneg_left hsum (mul_nonneg ht0 (Nat.cast_nonneg n : (0 : ℝ) ≤ n))
  have e3 := mul_le_mul_of_nonneg_left hb hT.le
  have e4 : ∀ x : ℝ, (2 * (i0 k l : ℝ) - 1) * m * x / ((l : ℝ) - 1) =
      (2 * (i0 k l : ℝ) - 1) * m / ((l : ℝ) - 1) * x := fun x => by ring
  rw [e4] at e3 ⊢
  nlinarith

theorem main : WindowedChoiceExistsWithBound ∧ ContentOrbit := ⟨orbit_sum_fifty_one, contentOrbit⟩

end GlobalTheory.OrbitPlan
end

