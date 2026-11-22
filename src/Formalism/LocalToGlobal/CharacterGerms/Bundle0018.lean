import Formalism.LocalToGlobal.CharacterGerms.Bundle0013
import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
import Formalism.LocalToGlobal.CharacterGerms.Bundle0014

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieCartFB
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

section Rename

theorem prod_X_rename {σ τ : Type} (φ : σ → τ) (e : σ →₀ ℕ) :
    (e.prod fun s m => (MvPowerSeries.X (φ s) : MvPowerSeries τ C) ^ m) =
      MvPowerSeries.monomial (e.mapDomain φ) 1 := by
  refine Finsupp.induction_linear e ?_ ?_ ?_
  · simp
  · intro f g hf hg
    rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _), hf, hg,
      Finsupp.mapDomain_add, MvPowerSeries.monomial_mul_monomial, one_mul]
  · intro a b
    rw [Finsupp.prod_single_index (h := fun s m => (MvPowerSeries.X (φ s) : MvPowerSeries τ C) ^ m) (pow_zero _),
      Finsupp.mapDomain_single]
    simp only [MvPowerSeries.X_pow_eq]

theorem coeff_subst_rename_inj {σ τ : Type} [Finite σ] (φ : σ → τ) (hφ : Function.Injective φ)
    (F : MvPowerSeries σ C) (e : σ →₀ ℕ) :
    MvPowerSeries.coeff (e.mapDomain φ)
      (MvPowerSeries.subst (fun s => (MvPowerSeries.X (φ s) : MvPowerSeries τ C)) F) = MvPowerSeries.coeff e F := by
  have hA : MvPowerSeries.HasSubst (fun s => (MvPowerSeries.X (φ s) : MvPowerSeries τ C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun s => by simp)
  rw [MvPowerSeries.coeff_subst hA, finsum_eq_single _ e]
  · rw [prod_X_rename, MvPowerSeries.coeff_monomial_same, smul_eq_mul, mul_one]
  · intro d hd
    rw [prod_X_rename, MvPowerSeries.coeff_monomial, if_neg, smul_zero]
    intro h
    exact hd (Finsupp.mapDomain_injective hφ h).symm

variable {dd : ℕ}

theorem snd_injective_fin_one : Function.Injective (fun p : Fin 1 × Fin dd => p.2) := fun p q h => Prod.ext (Subsingleton.elim _ _) h

theorem hasSubst_snd : MvPowerSeries.HasSubst
    (fun p : Fin 1 × Fin dd => (MvPowerSeries.X p.2 : MvPowerSeries (Fin dd) C)) := MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => by simp)

theorem uncurry_eq_subst (f : PS C 1 dd) :
    un1 f = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => (MvPowerSeries.X p.2 : MvPowerSeries (Fin dd) C)) f := by
  ext μ
  have h := coeff_subst_rename_inj (C := C) (fun p : Fin 1 × Fin dd => p.2) snd_injective_fin_one f
    (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x))
  have e1 : (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)).mapDomain (fun p : Fin 1 × Fin dd => p.2) = μ := by
    rw [← Finsupp.mapDomain_comp]
    exact Finsupp.mapDomain_id
  rw [e1] at h
  exact h.symm

theorem subst_singlePointUncurry {τ : Type} {a : Fin dd → MvPowerSeries τ C} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (f : PS C 1 dd) :
    MvPowerSeries.subst a (un1 f) = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  have hA : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  rw [uncurry_eq_subst, MvPowerSeries.subst_comp_subst_apply hasSubst_snd hA]
  congr 1
  funext p
  show MvPowerSeries.subst a (MvPowerSeries.X p.2) = a p.2
  rw [MvPowerSeries.subst_X hA]

theorem subst_oneVariableUncurry_eq_subst {σ : Type} [Finite σ] {b : σ → PS C 1 dd} (hb : ∀ s, MvPowerSeries.constantCoeff (b s) = 0)
    (f : MvPowerSeries σ C) :
    un1 (MvPowerSeries.subst b f) = MvPowerSeries.subst (fun s => un1 (b s)) f := by
  have hB : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb
  rw [uncurry_eq_subst, MvPowerSeries.subst_comp_subst_apply hB hasSubst_snd]
  congr 1
  funext s
  rw [uncurry_eq_subst]

theorem uncurry_X (i : Fin dd) : un1 (MvPowerSeries.X ((0 : Fin 1), i) : PS C 1 dd) = MvPowerSeries.X i := by
  rw [uncurry_eq_subst, MvPowerSeries.subst_X hasSubst_snd]

theorem eval_single_eq_subst {n : ℕ} (a : Pt C n dd) (f : PS C 1 dd) :
    ev ![a] f = MvPowerSeries.subst (fun p : Fin 1 × Fin dd => a p.2) f := by
  simp only [ev]
  congr 1
  funext p
  rw [Subsingleton.elim p.1 0]
  rfl

theorem uncurry_comp {φ a : Pt C 1 dd} (ha : ∀ i, MvPowerSeries.constantCoeff (a i) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => un1 (a j)) (un1 (φ i)) = un1 (comp1 φ a i) := by
  have hu : ∀ j, MvPowerSeries.constantCoeff (un1 (a j)) = 0 := by
    intro j
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (a j) = 0
    rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact ha j
  rw [subst_singlePointUncurry hu]
  show _ = un1 (ev ![a] (φ i))
  rw [eval_single_eq_subst, subst_oneVariableUncurry_eq_subst (b := fun p : Fin 1 × Fin dd => a p.2) (fun s => ha s.2)]

end Rename

def PTFBSt : Prop :=
  AllFB fun C _ V d I _ _ X => ∀ (g : Fin 2) (a : ZMod d) (w : I g → C), (∀ c, V.Ge 0 (w c)) →
    (∀ c, X.tyC g (Sum.inl c) ≠ a → w c = 0) →
    ∃ x ∈ X.TySet V g, x 0 = Sum.elim w 0 ∧ ∀ (i : ℕ) n, X.tyC g n ≠ a + i → x i n = 0

def AddCvFBSt : Prop := AllFB fun _ _ V _ _ _ _ X => X.AddCvSt V

def HStabFBSt : Prop :=
  AllFB fun _ _ V _ I _ _ X => ∀ (g : Fin 2) (c : I g) (q : JJ I g), X.ty g c ≠ X.ty (1 - g) q →
    V.Ge 0 (X.sg1 (X.u g c) (X.u (1 - g) q))

section Inst

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} {d : ℕ} {I : Fin 2 → Type}
  [∀ g, Fintype (I g)] (Y : FBChart C V O dd) (p : PairData Y d I)

theorem FBChart.lg_const (i : Fin dd) : MvPowerSeries.constantCoeff (Y.lg i) = 0 := by
  have h := Y.lg_lin i 0 (by simp)
  rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_zero_X] at h
  exact h

theorem FBChart.chart_log_constantCoeff (i : Fin dd) : MvPowerSeries.constantCoeff ((Y.raw p).lg i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg i) = 0
  rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact Y.lg_const i

theorem FBChart.chart_exp_constantCoeff (i : Fin dd) : MvPowerSeries.constantCoeff ((Y.raw p).ex i) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  show MvPowerSeries.coeff ((0 : Fin dd →₀ ℕ).mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.ex i) = 0
  rw [Finsupp.mapDomain_zero, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact Y.ex_const i

theorem FBChart.raw_exlg (i : Fin dd) :
    MvPowerSeries.subst (Y.raw p).lg ((Y.raw p).ex i) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  show MvPowerSeries.subst (fun j => un1 (Y.lg j)) (un1 (Y.ex i)) = _
  rw [uncurry_comp (fun j => Y.lg_const j), Y.ex_lg]
  exact uncurry_X i

theorem FBChart.raw_lgex (i : Fin dd) :
    MvPowerSeries.subst (Y.raw p).ex ((Y.raw p).lg i) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  show MvPowerSeries.subst (fun j => un1 (Y.ex j)) (un1 (Y.lg i)) = _
  rw [uncurry_comp (fun j => Y.ex_const j), Y.lg_ex]
  exact uncurry_X i

theorem FBChart.raw_lin (i : Fin dd) (μ : Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    MvPowerSeries.coeff μ ((Y.raw p).lg i) =
      MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  show MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg i) = _
  rw [Y.lg_lin i _ ?_, ← uncurry_X i]
  · rfl
  · have hd : ∀ ν : Fin dd →₀ ℕ, (ν.mapDomain fun x : Fin dd => ((0 : Fin 1), x)).degree = ν.degree := by
      intro ν
      refine Finsupp.induction_linear ν ?_ ?_ ?_
      · simp
      · intro f g hf hg
        rw [Finsupp.mapDomain_add, map_add, map_add, hf, hg]
      · intro a b
        rw [Finsupp.mapDomain_single]
        simp
    rw [hd]
    exact hμ

theorem FBChart.raw_axis0 (e : Fin 2 × Fin dd →₀ ℕ) (he : ∀ s ∈ e.support, s.1 ≠ 0) :
    MvPowerSeries.coeff e (Y.raw p).h = 0 := by
  refine coeff_of_ev_zero Y.h 0 ![0, pt C dd 0] rfl ?_ Y.gauge.ax0 e he
  intro g' hg'
  rw [fin_two_eq_one_sub_of_ne' 0 g' hg']
  rfl

end Inst

theorem cartFB_of (hPT : PTFBSt) (hAdd : AddCvFBSt) (hStab : HStabFBSt) : CartFBSt := by
  intro C _ _ V O _ _ dd Y d _ I _ p g
  show RawChart.CartHyp (Y.raw p) V g
  haveI := Y.algClosed
  haveI : NeZero (V.l : C) := ⟨Nat.cast_ne_zero.2 V.l_prime.ne_zero⟩
  obtain ⟨ζ, hζr⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic V.l C)
    (Polynomial.degree_cyclotomic_pos V.l C V.l_prime.pos).ne'
  have hζ : IsPrimitiveRoot ζ V.l := (Polynomial.isRoot_cyclotomic_iff).1 hζr
  have hA : (Y.raw p).AddCvSt V := hAdd C V O dd Y d I p
  have h0 : (0 : ℕ → I g ⊕ JJ I g → C) ∈ (Y.raw p).TySet V g :=
    RawChart.zero_mem (Y.raw p) (Y.chart_log_constantCoeff p) (Y.raw_axis0 p) V g
  have hadd : ∀ x y, x ∈ (Y.raw p).TySet V g → y ∈ (Y.raw p).TySet V g → x + y ∈ (Y.raw p).TySet V g :=
    fun x y hx hy => RawChart.add_mem (Y.raw p) V g hA p.u_int x y hx hy
  exact
    { zero := h0
      add := hadd
      neg := fun x hx => RawChart.neg_mem (Y.raw p) V g Y.l_odd x hx
      teich := fun c hc x hx => RawChart.teich_mem (Y.raw p) V g c hc x hx
      Vm := fun x hx => RawChart.Vpow_mem' (Y.raw p) V g 1 x hx
      Fm := fun x hx => RawChart.F_mem (Y.raw p) V g (Y.chart_log_constantCoeff p) (Y.raw_exlg p) hζ h0 hadd x hx
      sumV := fun y hy => RawChart.sumV_mem (Y.raw p) V g (Y.chart_log_constantCoeff p) (Y.chart_exp_constantCoeff p) (Y.raw_exlg p)
        (Y.raw_lgex p) h0 hadd y hy
      t2 := fun x hx s hs n => RawChart.val_nonneg_leading_coeff_of_mem_tySet (Y.raw p) V g (Y.raw_lin p) (Y.raw_axis0 p) (p.u_sat g)
        (hStab C V O dd Y d I p g) x hx s hs n
      t3 := fun ζ' hζ' => RawChart.const_mem_type_set_of_nonneg (Y.raw p) (Y.chart_log_constantCoeff p) (Y.raw_axis0 p) V g ζ' hζ'
      t4 := hPT C V O dd Y d I p g }

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTieLab
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem ge_of_isIntegral {C : Type} [Field C] (V : VF C) {x : C} (hx : IsIntegral ℤ x) : V.Ge 0 x := by
  obtain ⟨p, hpm, hp⟩ := hx
  have hZ : ∀ z : ℤ, V.Ge 0 (algebraMap ℤ C z) := by
    intro z
    rw [eq_intCast]
    refine Int.induction_on z ?_ ?_ ?_
    · rw [Int.cast_zero]; exact VF.Ge.zero 0
    · intro i ih
      rw [Int.cast_add, Int.cast_one]
      exact VF.Ge.add ih VF.Ge.one
    · intro i ih
      rw [Int.cast_sub, Int.cast_one, sub_eq_add_neg]
      exact VF.Ge.add ih (VF.Ge.neg VF.Ge.one)
  by_contra hneg
  have hlt : V.v x < ((0 : ℝ) : WithTop ℝ) := not_le.mp hneg
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  have hr0 : r < 0 := by
    rw [← hr] at hlt
    exact WithTop.coe_lt_coe.mp hlt
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at hr
    exact WithTop.coe_ne_top hr
  set yv := x⁻¹ with hyv
  have hy0 : yv ≠ 0 := inv_ne_zero hx0
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (fun h => hy0 ((AddValuation.top_iff V.v).mp h))
  have hrs : r + s = 0 := by
    have h1 : V.v (x * yv) = 0 := by rw [hyv, mul_inv_cancel₀ hx0, AddValuation.map_one]
    rw [AddValuation.map_mul, ← hr, ← hs] at h1
    exact_mod_cast h1
  have hy : V.Ge (-r) yv := by
    unfold VF.Ge
    rw [← hs]
    exact WithTop.coe_le_coe.mpr (by linarith)
  have hy0' : V.Ge 0 yv := by
    unfold VF.Ge
    rw [← hs]
    exact WithTop.coe_le_coe.mpr (by linarith)
  have hpow : ∀ k : ℕ, V.Ge 0 (yv ^ k) := by
    intro k
    induction k with
    | zero => rw [pow_zero]; exact VF.Ge.one
    | succ k ih => rw [pow_succ]; exact VF.Ge.mul_int ih hy0'
  rw [hpm.as_sum] at hp
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, Polynomial.eval₂_finset_sum,
    Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_X_pow] at hp
  set n := p.natDegree
  have hsum : 1 + ∑ i ∈ Finset.range n, algebraMap ℤ C (p.coeff i) * yv ^ (n - i) = 0 := by
    have h2 := congrArg (· * yv ^ n) hp
    simp only [add_mul, Finset.sum_mul, zero_mul] at h2
    rw [← h2]
    congr 1
    · rw [← mul_pow, hyv, mul_inv_cancel₀ hx0, one_pow]
    · refine Finset.sum_congr rfl fun i hi => ?_
      have hi' : i ≤ n := le_of_lt (Finset.mem_range.mp hi)
      conv_rhs => rw [show n = (n - i) + i from (Nat.sub_add_cancel hi').symm]
      rw [pow_add, mul_assoc, mul_left_comm (x ^ i), ← mul_pow, hyv, mul_inv_cancel₀ hx0, one_pow, mul_one]
  have hS : V.Ge (-r) (∑ i ∈ Finset.range n, algebraMap ℤ C (p.coeff i) * yv ^ (n - i)) := by
    refine Finset.sum_induction _ (fun z => V.Ge (-r) z) (fun _ _ ha hb => VF.Ge.add ha hb) (VF.Ge.zero _) ?_
    intro i hi
    have hi' : n - i = (n - i - 1) + 1 := by
      have := Finset.mem_range.mp hi
      omega
    rw [hi', pow_succ, ← mul_assoc]
    exact VF.Ge.mul_int (VF.Ge.mul_int (hZ _) (hpow _)) hy
  have h1 : (1 : C) = -∑ i ∈ Finset.range n, algebraMap ℤ C (p.coeff i) * yv ^ (n - i) :=
    eq_neg_of_add_eq_zero_left hsum
  have hS' := VF.Ge.neg hS
  rw [← h1] at hS'
  unfold VF.Ge at hS'
  rw [AddValuation.map_one] at hS'
  have : (-r : ℝ) ≤ 0 := by exact_mod_cast hS'
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]
variable {C : Type} [Field C] [CharZero C] {V : VF C}
variable {T : CDVR} {io : c.F →+* T.Fr} {y : IntFr Xo c T io}

theorem embedding_integral (ι : T.Fr →+* C) (τ : E →+* ℂ) (x : 𝓞 E) : V.Ge 0 (emA3 io ι τ x) := by
  exact ge_of_isIntegral V ((Algebra.IsIntegral.isIntegral (R := ℤ) x).map (emA3 io ι τ).toIntAlgHom)

theorem embK_conj (hstar : ∀ a : 𝓞 E, star a = H.bar a) (τ : E →+* ℂ) (x : 𝓞 E) :
    embK c (ComplexEmbedding.conjugate τ) x = embK c τ (star x) := by
  unfold embK
  apply Subtype.ext
  simp [embF]
  rw [hstar]
  rw [show (algebraMap (𝓞 E) E) (H.bar x) = ((H.bar x : 𝓞 E) : E) from rfl, H.bar_eq x,
    IsCMField.complexEmbedding_complexConj]

theorem embedding_conjugate (hstar : ∀ a : 𝓞 E, star a = H.bar a) (ι : T.Fr →+* C) (τ : E →+* ℂ) (x : 𝓞 E) :
    emA3 io ι (ComplexEmbedding.conjugate τ) x = emA3 io ι τ (star x) := by
  simp only [emA3, RingHom.coe_comp, Function.comp_apply, embK_conj hstar]

theorem a3uvec_int (C3 : IntChart T io y) {ι : T.Fr →+* C} (hι : EmbOK T V ι) (ℓ : Lt1 Dw) (i : Fin (chD C3.ch)) :
    V.Ge 0 (ι (chartUnitVectors C3 ℓ i)) := by
  obtain ⟨⟨-, -, -, -, -, -, hu⟩, -⟩ := C3.gen
  rw [show chartUnitVectors C3 ℓ i = _ from hu ℓ i]
  exact embIntSt_holds T C V ι hι _

section Core

variable {Orb : Type} {d : ℕ} [NeZero d]

structure LabGeoCore (C3 : IntChart T io y) (ι : T.Fr →+* C) (Y : FBChart C V (𝓞 E) (chD C3.ch)) (lab : Lab E Orb d) :
    Prop where
  u_eig : ∀ o g (x : lab.II Dw o g) a, linAct (Y.B.A.act a) (lieBasisVector C3 ι lab o g x) =
    emA3 io ι (lab.tau o g x.1) a • lieBasisVector C3 ι lab o g x
  u_sat : ∀ o g, ∃ w : Fin (chD C3.ch) → lab.II Dw o g → C, (∀ x q, V.Ge 0 (w x q)) ∧
    ∀ q q' : lab.II Dw o g, ∑ x, lieBasisVector C3 ι lab o g q x * w x q' = if q = q' then 1 else 0
  u_full : ∀ o g a (v : Fin (chD C3.ch) → C), (∀ x, linAct (Y.B.A.act x) v = emA3 io ι (lab.tau o g a) x • v) →
    ∃ b : lab.II Dw o g → C, (∀ q, q.1 ≠ a → b q = 0) ∧ v = ∑ q, b q • lieBasisVector C3 ι lab o g q

end Core

variable (Xo c)

def LabGeoCoreSt : Prop :=
  (∀ a : 𝓞 E, star a = H.bar a) →
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C3 : IntChart T io y)
    (C : Type) [Field C] [CharZero C] (V : VF C) (ι : T.Fr →+* C), EmbOK T V ι →
    ∀ (k : ℕ) (Y : FBChart C V (𝓞 E) (chD C3.ch)), IsBC C3 ι k Y →
    ∀ (Orb : Type) (d : ℕ) [NeZero d] (lab : Lab E Orb d), LabArith V io ι lab → LabGeoCore C3 ι Y lab

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePDescSpanSt
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds Formalism.L2.Pj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def HaSpanSt : Prop :=
  ∀ (Ty : Type) [Fintype Ty] (r : Ty → ℕ) (n : ℕ) (cc : Ty → Ty) (isX : Ty → Prop) (a : Ty → ℕ → ℕ)
    (K : Type) [Field K] [CharZero K] (O : Subring K), ∀ P ∈ HaO r n K O cc isX a,
    ∃ (m : ℕ) (c : Fin m → K) (Z : Fin m → MvPolynomial (Letter Ty r n) ℤ), (∀ i, c i ∈ O) ∧
      (∀ i (K' : Type) [Field K'] [CharZero K'], MvPolynomial.map (Int.castRingHom K') (Z i) ∈ HHa r n K' cc isX a) ∧
      P = ∑ i, c i • MvPolynomial.map (Int.castRingHom K) (Z i)

section Nab

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

def gofY (Y : FBChart C V O dd) (n : ℕ) : PS C n dd :=
  FB.expS C (((Y.k : ℕ) : C) • ∑ b : Fin n, ev (n := n) ![pt C dd b] (Y.B.hL C Y.h Y.w0))

theorem nab_eq_nabL (Y : FBChart C V O dd) (Ls : LetSys C dd) (n : ℕ) (g : PS C n dd) (P : MvPolynomial (Ls.ι n) C) :
    Y.nab Ls n g P = DescP.nabL (Y.B.FK C) (Ls.cp n) (Ls.uv n) P (gofY Y n) g :=
  rfl

end Nab

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l} [StarRing (𝓞 E)]

theorem descSpanSt_of (hS : HaSpanSt) : DescSpanSt Xo c := by
  intro T io y C3 C _ _ V ι _hι k Y _hY a n P hP f hf
  have : CharZero T.Fr := charZero_of_inj_zero fun x hx => by
    have h1 := congrArg ι hx
    rwa [map_natCast, map_zero, Nat.cast_eq_zero] at h1
  obtain ⟨m, cc, Z, hc, hZ, hPe⟩ :=
    hS (E →+* ℂ) Dw.mult n ComplexEmbedding.conjugate (InPsi H) (fun τ i => a (τ, i)) C V.RR P hP
  let Q : Fin m → MvPolynomial (LtN Dw n) T.Fr := fun i => MvPolynomial.map (Int.castRingHom T.Fr) (Z i)
  have hmap : ∀ i, MvPolynomial.map ι (Q i) = MvPolynomial.map (Int.castRingHom C) (Z i) := by
    intro i
    simp only [Q]
    rw [MvPolynomial.map_map, RingHom.ext_int (ι.comp (Int.castRingHom T.Fr)) (Int.castRingHom C)]
  let Ls := chartLetterSystem C3 V ι a
  let tc : (Fin n × Fin (chD C3.ch) →₀ ℕ) → C := fun μ =>
    MvPolynomial.coeff μ (MvPowerSeries.trunc' C (DescP.cst P.totalDegree) f)
  have hP2 : ∀ g : PS C n (chD C3.ch),
      Y.nab Ls n g P = ∑ i, cc i * Y.nab Ls n g (MvPolynomial.map ι (Q i)) := by
    intro g
    have hg : ∀ i, Y.nab Ls n g (MvPolynomial.map ι (Q i)) = Y.nab Ls n g (MvPolynomial.map (Int.castRingHom C) (Z i)) :=
      fun i => congrArg (Y.nab Ls n g) (hmap i)
    simp only [hg, nab_eq_nabL]
    show MvPowerSeries.constantCoeff (DpolyN (Y.B.FK C) (Ls.cp n) (Ls.uv n) P (g * gofY Y n)) =
      ∑ i, cc i * MvPowerSeries.constantCoeff
        (DpolyN (Y.B.FK C) (Ls.cp n) (Ls.uv n) (MvPolynomial.map (Int.castRingHom C) (Z i)) (g * gofY Y n))
    rw [hPe]
    exact DescP.const_dpolyN_lin (Y.B.FK C) (Ls.cp n) (Ls.uv n) Finset.univ cc _ (g * gofY Y n)
  have hmono : ∀ μ : Fin n × Fin (chD C3.ch) →₀ ℕ,
      (MvPowerSeries.monomial μ (1 : C) : PS C n (chD C3.ch)) =
        MvPowerSeries.map ι (MvPowerSeries.monomial μ (1 : T.Fr)) := by
    intro μ
    rw [MvPowerSeries.map_monomial, ι.map_one]
  let S := (MvPowerSeries.trunc' C (DescP.cst P.totalDegree) f).support
  let g' : (Fin n × Fin (chD C3.ch) →₀ ℕ) × Fin m → C := fun x =>
    (tc x.1 * cc x.2) * Y.nab Ls n (MvPowerSeries.map ι (MvPowerSeries.monomial x.1 (1 : T.Fr)))
      (MvPolynomial.map ι (Q x.2))
  have hmain : Y.nab Ls n f P = ∑ x ∈ S ×ˢ (Finset.univ : Finset (Fin m)), g' x := by
    rw [Finset.sum_product, nab_eq_nabL, DescP.nabL_trunc]
    refine Finset.sum_congr rfl fun μ _ => ?_
    rw [← nab_eq_nabL, hP2, hmono μ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [g', tc]
    ring
  obtain ⟨N, e, _he, hsum⟩ := DescP.exists_fin_sum (S ×ˢ (Finset.univ : Finset (Fin m))) g'
  refine ⟨N, fun j => tc (e j).1 * cc (e j).2, fun j => Q (e j).2,
    fun j => MvPowerSeries.monomial (e j).1 (1 : T.Fr), ?_, ?_, ?_, ?_⟩
  · intro j
    have htc : V.Ge 0 (tc (e j).1) := by
      simp only [tc]
      rw [MvPowerSeries.coeff_trunc']
      split_ifs
      · exact hf _
      · exact VF.Ge.zero 0
    exact VF.Ge.mul_int htc (hc (e j).2)
  · intro j
    refine ⟨hZ (e j).2 T.Fr, fun μ => ?_⟩
    simp only [Q]
    rw [MvPolynomial.coeff_map, eq_intCast]
    exact ⟨((MvPolynomial.coeff μ (Z (e j).2) : ℤ) : T.V), map_intCast _ _⟩
  · intro j μ
    rw [MvPowerSeries.coeff_monomial]
    split_ifs
    · exact Subring.one_mem _
    · exact Subring.zero_mem _
  · rw [hmain, hsum]

end Formalism.L2.FormalSeriesBounds
end
end

