import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
import Formalism.LocalToGlobal.CharacterGerms.Bundle0018
import Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmall

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePCartSelfSt
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

section Col

variable {dd : ℕ}

theorem hasSubst_col (col : Fin 2) :
    HasSubst (fun x : Fin dd => (X (col, x) : MvPowerSeries (Fin 2 × Fin dd) C)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem col_inj (col : Fin 2) : Function.Injective (fun x : Fin dd => (col, x)) :=
  fun _ _ h => (Prod.ext_iff.1 h).2

theorem subst_inCol {τ : Type} {a : Fin 2 × Fin dd → MvPowerSeries τ C} (ha : ∀ x, constantCoeff (a x) = 0)
    (col : Fin 2) (f : MvPowerSeries (Fin dd) C) :
    subst a (inCol col f) = subst (fun i => a (col, i)) f := by
  have hS := hasSubst_of_constantCoeff_zero ha
  unfold inCol
  rw [subst_comp_subst_apply (hasSubst_col col) hS]
  congr 1
  funext i
  rw [subst_X hS]

theorem inCol_X (col : Fin 2) (i : Fin dd) : inCol col (X i : MvPowerSeries (Fin dd) C) = X (col, i) := by
  unfold inCol
  rw [subst_X (hasSubst_col col)]

theorem coeff_subst_rename_out {σ τ : Type} [Finite σ] (φ : σ → τ) (F : MvPowerSeries σ C) (e : τ →₀ ℕ)
    (he : ∀ e' : σ →₀ ℕ, e'.mapDomain φ ≠ e) :
    coeff e (subst (fun s => (X (φ s) : MvPowerSeries τ C)) F) = 0 := by
  rw [coeff_subst (hasSubst_of_constantCoeff_zero fun s => constantCoeff_X _)]
  apply finsum_eq_zero_of_forall_eq_zero
  intro e'
  rw [prod_X_rename, coeff_monomial, if_neg (fun h => he e' h.symm), smul_zero]

theorem coeff_inCol_lin (col : Fin 2) (f f' : MvPowerSeries (Fin dd) C)
    (h : ∀ μ : Fin dd →₀ ℕ, μ.degree ≤ 1 → coeff μ f = coeff μ f') (μ : Fin 2 × Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    coeff μ (inCol col f) = coeff μ (inCol col f') := by
  unfold inCol
  by_cases hr : ∃ μ' : Fin dd →₀ ℕ, μ'.mapDomain (fun x => (col, x)) = μ
  · obtain ⟨μ', rfl⟩ := hr
    rw [coeff_subst_rename_inj _ (col_inj col), coeff_subst_rename_inj _ (col_inj col)]
    exact h μ' (by rw [Finsupp.degree_mapDomain] at hμ; exact hμ)
  · push_neg at hr
    rw [coeff_subst_rename_out _ _ _ hr, coeff_subst_rename_out _ _ _ hr]

end Col

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd) {d : ℕ}
  {I0 : Type} [Fintype I0] (p : SelfData Y d I0)

theorem FBChart.self_chart_log_constantCoeff (x : Fin 2 × Fin dd) : constantCoeff ((Y.rawSelf p).lg x) = 0 := by
  show constantCoeff (inCol x.1 (un1 (Y.lg x.2))) = 0
  apply constantCoeff_inCol
  rw [constantCoeff_uncurry]
  exact Y.lg_const x.2

theorem FBChart.self_chart_exp_constantCoeff (x : Fin 2 × Fin dd) : constantCoeff ((Y.rawSelf p).ex x) = 0 := by
  show constantCoeff (inCol x.1 (un1 (Y.ex x.2))) = 0
  apply constantCoeff_inCol
  rw [constantCoeff_uncurry]
  exact Y.ex_const x.2

theorem FBChart.rawSelf_axis0 (e : Fin 2 × (Fin 2 × Fin dd) →₀ ℕ) (he : ∀ s ∈ e.support, s.1 ≠ 0) :
    coeff e (Y.rawSelf p).h = 0 := by
  show coeff e (∑ col, hCol col Y.h) = 0
  exact van_sum Finset.univ _ (fun col _ => van_hCol col 0 Y.h (gauge_axes Y 0)) e he

theorem FBChart.rawSelf_exlg (x : Fin 2 × Fin dd) :
    subst (Y.rawSelf p).lg ((Y.rawSelf p).ex x) = (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  obtain ⟨col, i⟩ := x
  show subst (Y.rawSelf p).lg (inCol col (un1 (Y.ex i))) = _
  rw [subst_inCol (Y.self_chart_log_constantCoeff p)]
  show subst (fun j => inCol col (un1 (Y.lg j))) (un1 (Y.ex i)) = _
  have hL : HasSubst (fun j => un1 (Y.lg j)) :=
    hasSubst_of_constantCoeff_zero fun j => by rw [constantCoeff_uncurry, Y.lg_const]
  have hx : un1 (comp1 Y.ex Y.lg i) = (X i : MvPowerSeries (Fin dd) C) := by rw [Y.ex_lg]; exact uncurry_X i
  unfold inCol
  rw [← subst_comp_subst_apply hL (hasSubst_col col), uncurry_comp Y.lg_const, hx, subst_X (hasSubst_col col)]

theorem FBChart.rawSelf_lgex (x : Fin 2 × Fin dd) :
    subst (Y.rawSelf p).ex ((Y.rawSelf p).lg x) = (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  obtain ⟨col, i⟩ := x
  show subst (Y.rawSelf p).ex (inCol col (un1 (Y.lg i))) = _
  rw [subst_inCol (Y.self_chart_exp_constantCoeff p)]
  show subst (fun j => inCol col (un1 (Y.ex j))) (un1 (Y.lg i)) = _
  have hL : HasSubst (fun j => un1 (Y.ex j)) :=
    hasSubst_of_constantCoeff_zero fun j => by rw [constantCoeff_uncurry, Y.ex_const]
  have hx : un1 (comp1 Y.lg Y.ex i) = (X i : MvPowerSeries (Fin dd) C) := by rw [Y.lg_ex]; exact uncurry_X i
  unfold inCol
  rw [← subst_comp_subst_apply hL (hasSubst_col col), uncurry_comp Y.ex_const, hx, subst_X (hasSubst_col col)]

theorem FBChart.rawSelf_lin (x : Fin 2 × Fin dd) (μ : Fin 2 × Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    coeff μ ((Y.rawSelf p).lg x) = coeff μ (X x : MvPowerSeries (Fin 2 × Fin dd) C) := by
  obtain ⟨col, i⟩ := x
  show coeff μ (inCol col (un1 (Y.lg i))) = _
  rw [← inCol_X col i]
  refine coeff_inCol_lin col _ _ (fun ν hν => ?_) μ hμ
  show coeff (ν.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg i) = _
  rw [Y.lg_lin i _ (by rw [Finsupp.degree_mapDomain]; exact hν), ← uncurry_X i]
  rfl

theorem SelfData.gm_int (a : ZMod d) (r s : Fin 2) : V.Ge 0 (p.gm a r s) := by
  obtain ⟨M, hM⟩ := p.gm_lim 0
  have h := hM a r s
  rw [Nat.cast_zero] at h
  have e : p.gm a r s = (p.gm a r s - p.em a (M r s)) + p.em a (M r s) := by ring
  rw [e]
  exact h.add (p.em_int a _)

theorem FBChart.rawSelf_u_integral (g : Fin 2) (c : I0) (x : Fin 2 × Fin dd) : V.Ge 0 ((Y.rawSelf p).u g c x) :=
  VF.Ge.mul_int (SelfData.gm_int Y p _ _ _) (p.e_int c x.2)

theorem SelfData.gm_pair (a : ZMod d) (g : Fin 2) :
    ∑ col, p.gm a col g * p.gm (a + p.hd) col (1 - g) = 1 := by
  have h := p.gm_hyp (a + p.hd) g (1 - g)
  rw [add_assoc, p.hd_two, add_zero, if_neg (by fin_cases g <;> decide)] at h
  exact h

theorem FBChart.exists_integral_right_inverse (g : Fin 2) :
    ∃ w : Fin 2 × Fin dd → I0 → C, (∀ x c, V.Ge 0 (w x c)) ∧
      ∀ c c' : I0, ∑ x, (Y.rawSelf p).u g c x * w x c' = if c = c' then 1 else 0 := by
  obtain ⟨w0, hw0, huw⟩ := p.e_sat
  refine ⟨fun x c' => p.gm (p.ty0 c' + p.hd) x.1 (1 - g) * w0 x.2 c',
    fun x c' => VF.Ge.mul_int (SelfData.gm_int Y p _ _ _) (hw0 _ _), fun c c' => ?_⟩
  show ∑ x : Fin 2 × Fin dd, (p.gm (p.ty0 c) x.1 g * p.e c x.2) * (p.gm (p.ty0 c' + p.hd) x.1 (1 - g) * w0 x.2 c') = _
  have e1 : ∀ x : Fin 2 × Fin dd, (p.gm (p.ty0 c) x.1 g * p.e c x.2) * (p.gm (p.ty0 c' + p.hd) x.1 (1 - g) * w0 x.2 c') =
      (p.gm (p.ty0 c) x.1 g * p.gm (p.ty0 c' + p.hd) x.1 (1 - g)) * (p.e c x.2 * w0 x.2 c') := fun x => by ring
  simp_rw [e1]
  rw [Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum, huw c c']
  by_cases hc : c = c'
  · subst hc
    rw [if_pos rfl]
    simp only [mul_one]
    exact SelfData.gm_pair Y p _ g
  · simp [hc]

def PTSelfSt : Prop :=
  AllSelf fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) →
    (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) →
    ∃ x ∈ X.TySet V g, x 0 = Sum.elim w 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x i n = 0

def AddCvSelfSt : Prop := AllSelf fun _ _ V _ _ _ _ X => X.AddCvSt V

def HStabSelfSt : Prop :=
  AllSelf fun _ _ V _ I _ _ X => ∀ (g : Fin 2) (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q →
    V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q))

theorem cartSelf_of (hPT : PTSelfSt) (hAdd : AddCvSelfSt) (hStab : HStabSelfSt) : CartSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p g
  have := Y.algClosed
  have : NeZero (V.l : C) := ⟨VF.l_ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C V.l
  have h0 := (Y.rawSelf p).zero_mem (Y.self_chart_log_constantCoeff p) (Y.rawSelf_axis0 p) V g
  have hadd := (Y.rawSelf p).add_mem V g (hAdd C V O dd Y d I0 p) (fun g c x => Y.rawSelf_u_integral p g c x)
  exact
    { zero := h0
      add := hadd
      neg := (Y.rawSelf p).neg_mem V g Y.l_odd
      teich := (Y.rawSelf p).teich_mem V g
      Vm := (Y.rawSelf p).V_mem V g
      Fm := (Y.rawSelf p).F_mem V g (Y.self_chart_log_constantCoeff p) (Y.rawSelf_exlg p) hζ h0 hadd
      sumV := (Y.rawSelf p).sumV_mem V g (Y.self_chart_log_constantCoeff p) (Y.self_chart_exp_constantCoeff p) (Y.rawSelf_exlg p) (Y.rawSelf_lgex p) h0 hadd
      t2 := (Y.rawSelf p).val_nonneg_leading_coeff_of_mem_tySet V g (Y.rawSelf_lin p) (Y.rawSelf_axis0 p) (Y.exists_integral_right_inverse p g) (hStab C V O dd Y d I0 p g)
      t3 := (Y.rawSelf p).const_mem_type_set_of_nonneg (Y.self_chart_log_constantCoeff p) (Y.rawSelf_axis0 p) V g
      t4 := hPT C V O dd Y d I0 p g }

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePLSmallMain
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePLSmall

open PartialDerivEval RowTiePE0 RowTiePProj

section Main

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem subst_zero_of {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C} (ha : ∀ s, a s = 0)
    {f : MvPowerSeries σ C} (hf : constantCoeff f = 0) : MvPowerSeries.subst a f = 0 := by
  have h0 : a = 0 := funext ha
  subst h0
  have hs : MvPowerSeries.HasSubst (0 : σ → MvPowerSeries τ C) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun _ => by simp)
  ext e
  rw [MvPowerSeries.coeff_subst hs, map_zero]
  apply finsum_eq_zero_of_forall_eq_zero
  intro d
  by_cases hd : d = 0
  · subst hd
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf, zero_smul]
  · obtain ⟨s, hsd⟩ : ∃ s, d s ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      exact hd (Finsupp.ext hcon)
    have hp : (d.prod fun s n => (0 : σ → MvPowerSeries τ C) s ^ n) = 0 := by
      apply Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hsd)
      simp [zero_pow hsd]
    rw [hp, map_zero, smul_zero]

private theorem ev_C_mul' {m n : ℕ} {a : Fin m → Pt C n dd} (ha : Z0 a) (c : C) (f : PS C m dd) :
    ev a (MvPowerSeries.C c * f) = MvPowerSeries.C c * ev a f := by
  rw [← MvPowerSeries.smul_eq_C_mul, ← MvPowerSeries.smul_eq_C_mul, ev_eq_alg ha, ev_eq_alg ha, map_smul]

theorem act_nat_mul (Y : FBChart C V O dd) (k : ℕ) (w : O) (j : Fin dd) :
    Y.B.A.act ((k : O) * w) j =
      ev ![fun j' => MvPowerSeries.C (k : C) * ev ![Y.B.A.act w] (Y.lg j')] (Y.ex j) := by
  have hk : ∀ i, Y.B.A.act (k : O) i = ev ![fun j' => MvPowerSeries.C (k : C) * Y.lg j'] (Y.ex i) := by
    intro i
    have h := ex_lg_comp Y (Y.B.A.act (k : O)) (Y.B.A.const _) i
    simp only [lg_act_nat] at h
    exact h.symm
  have hw : Z0 ![Y.B.A.act w] := by
    intro k' i'
    fin_cases k'
    simp [Y.B.A.const]
  have hb : Z0 ![fun j' => MvPowerSeries.C (k : C) * Y.lg j'] := by
    intro k' i'
    fin_cases k'
    simp [lg_const]
  rw [Y.B.A.mul_act]
  show ev ![Y.B.A.act w] (Y.B.A.act (k : O) j) = _
  rw [hk, ev_ev hb hw]
  congr 1
  funext k' i'
  fin_cases k'
  show ev ![Y.B.A.act w] (MvPowerSeries.C (k : C) * Y.lg i') = MvPowerSeries.C (k : C) * ev ![Y.B.A.act w] (Y.lg i')
  exact ev_C_mul' hw _ _

theorem tends_lpow : Tends V (fun n => ((V.l ^ (n + 1) : ℕ) : C)) 0 := by
  apply tends_of_nat
  intro N
  refine ⟨N, fun n hn => ?_⟩
  show ((N : ℝ) : WithTop ℝ) ≤ V.v (0 - ((V.l ^ (n + 1) : ℕ) : C))
  rw [zero_sub, AddValuation.map_neg, Nat.cast_pow, AddValuation.map_pow, V.v_l, nsmul_one]
  have h2 : ((N : ℝ) : WithTop ℝ) ≤ (((n + 1 : ℕ) : ℝ) : WithTop ℝ) := by
    rw [WithTop.coe_le_coe]
    exact_mod_cast (by omega : N ≤ n + 1)
  simpa using h2

theorem lSmall_holds : LSmallSt := by
  intro C _ _ V O _ _ dd Y x x' hx N i μ
  have hx' : ∀ n, ∃ c, x n - x' n = (V.l : O) ^ (n + 1) * c := fun n => hx n
  choose y hy using hx'
  have hsmall : ∀ (z : ℕ → O) (j : Fin dd),
      TendsS V (fun n => Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * z n) j) 0 := by
    intro z j
    have hw : ∀ n, Z0 ![Y.B.A.act (z n)] := by
      intro n k' i'
      fin_cases k'
      simp [Y.B.A.const]
    have hg : ∀ s2 : Fin dd, BddS V (fun n => ev ![Y.B.A.act (z n)] (Y.lg s2)) := by
      intro s2
      exact BddS.subst (a := fun n (p : Fin 1 × Fin dd) => (![Y.B.A.act (z n)] p.1) p.2)
        (f := fun _ => Y.lg s2)
        (by
          rintro n ⟨t1, t2⟩
          fin_cases t1
          simp [Y.B.A.const])
        (by
          rintro ⟨t1, t2⟩
          fin_cases t1
          exact BddS.of_int (fun n => Y.intAct _ _))
        (BddS.const _)
    have hcl := Close.subst (V := V)
      (a := fun n (p : Fin 1 × Fin dd) =>
        (![fun j' => MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C)) * ev ![Y.B.A.act (z n)] (Y.lg j')] p.1) p.2)
      (b := fun _ _ => 0)
      (by
        rintro n ⟨s1, s2⟩
        fin_cases s1
        simp [const_ev (hw n) (lg_const Y s2)])
      (by intros; simp)
      (by
        rintro ⟨s1, s2⟩
        fin_cases s1
        show BddS V (fun n => MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C)) * ev ![Y.B.A.act (z n)] (Y.lg s2))
        apply BddS.mul _ (hg s2)
        intro ν
        refine ⟨0, fun n => ?_⟩
        show V.Ge 0 (MvPowerSeries.coeff ν (MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C))))
        rw [MvPowerSeries.coeff_C]
        split_ifs
        · exact ge_natCast _
        · show ((0 : ℝ) : WithTop ℝ) ≤ V.v 0
          simp)
      (fun _ => BddS.const 0)
      (by
        rintro ⟨s1, s2⟩
        fin_cases s1
        show TendsS V (fun n => MvPowerSeries.C (((V.l ^ (n + 1) : ℕ) : C)) * ev ![Y.B.A.act (z n)] (Y.lg s2) - 0) 0
        simp only [sub_zero]
        simp only [mul_comm (MvPowerSeries.C _)]
        apply TendsS.mul_bdd (hg s2)
        intro ν
        simp only [MvPowerSeries.coeff_C, map_zero]
        split_ifs
        · exact tends_lpow
        · exact tends_const 0)
      (Y.ex j)
    have h0 : MvPowerSeries.subst (fun _ : Fin 1 × Fin dd => (0 : MvPowerSeries (Fin 1 × Fin dd) C)) (Y.ex j) = 0 :=
      subst_zero_of (fun _ => rfl) (Y.ex_const j)
    intro ν
    have h1 := hcl ν
    simp only [h0, sub_zero] at h1
    simp only [act_nat_mul]
    exact h1
  have heq : ∀ n, MvPowerSeries.subst (fun p : Fin 2 × Fin dd =>
      (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * y n)] p.1) p.2) (Y.B.G.F i) =
        Y.B.A.act (x n) i := by
    intro n
    have hxn : x n = x' n + ((V.l ^ (n + 1) : ℕ) : O) * y n := by
      rw [Nat.cast_pow, ← hy n]
      ring
    rw [hxn, Y.B.A.add_act]
    rfl
  have heq' : ∀ n, MvPowerSeries.subst (fun p : Fin 2 × Fin dd =>
      (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * (fun _ => (0 : O)) n)] p.1) p.2) (Y.B.G.F i) =
        Y.B.A.act (x' n) i := by
    intro n
    have hxn : Y.B.A.act (x' n) i =
        Y.B.A.act (x' n + ((V.l ^ (n + 1) : ℕ) : O) * (fun _ => (0 : O)) n) i := by
      simp
    rw [hxn, Y.B.A.add_act]
    rfl
  have hcl := Close.subst (V := V)
    (a := fun n (p : Fin 2 × Fin dd) =>
      (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * y n)] p.1) p.2)
    (b := fun n (p : Fin 2 × Fin dd) =>
      (![Y.B.A.act (x' n), Y.B.A.act (((V.l ^ (n + 1) : ℕ) : O) * (fun _ => (0 : O)) n)] p.1) p.2)
    (by
      rintro n ⟨s1, s2⟩
      fin_cases s1 <;> simp [Y.B.A.const])
    (by
      rintro n ⟨s1, s2⟩
      fin_cases s1 <;> simp [Y.B.A.const])
    (by
      rintro ⟨s1, s2⟩
      fin_cases s1 <;> exact BddS.of_int (fun n => Y.intAct _ _))
    (by
      rintro ⟨s1, s2⟩
      fin_cases s1 <;> exact BddS.of_int (fun n => Y.intAct _ _))
    (by
      rintro ⟨s1, s2⟩
      fin_cases s1
      · exact Close.refl (fun n => Y.B.A.act (x' n) s2)
      · intro ν
        have h1 := hsmall y s2 ν
        have h2 := hsmall (fun _ => 0) s2 ν
        have h3 := h1.sub h2
        simp only [map_zero, sub_zero] at h3
        rw [map_zero]
        simp only [map_sub]
        exact h3)
    (Y.B.G.F i)
  obtain ⟨n0, hn0⟩ := hcl μ (N : ℝ)
  refine ⟨n0, fun n hn => ?_⟩
  have h4 := hn0 n hn
  simp only [heq, heq', map_zero, zero_sub, map_sub] at h4
  show ((N : ℝ) : WithTop ℝ) ≤ V.v _
  have h5 : ((N : ℝ) : WithTop ℝ) ≤ V.v (-(MvPowerSeries.coeff μ (Y.B.A.act (x n) i) -
      MvPowerSeries.coeff μ (Y.B.A.act (x' n) i))) := h4
  rwa [AddValuation.map_neg] at h5

end Main

end RowTiePLSmall

end Formalism.L2.FormalSeriesBounds
end
end

