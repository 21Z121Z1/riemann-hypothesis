import Formalism.LocalToGlobal.CharacterGerms.Bundle0020
import Formalism.LocalToGlobal.CharacterGerms.Bundle0024
import Formalism.LocalToGlobal.CharacterGerms.RowTiePProjLie
import Lemmata.PowMulVecEigen.PowMulVecEig

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePAddCvSelf
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C]

theorem coeff_rename_zero {σ τ : Type} [Finite σ] (φ : σ → τ) (F : MvPowerSeries σ C) (e : τ →₀ ℕ) (s : τ)
    (hs : e s ≠ 0) (hsr : ∀ a, φ a ≠ s) :
    coeff e (subst (fun a => (X (φ a) : MvPowerSeries τ C)) F) = 0 := by
  have hA : MvPowerSeries.HasSubst (fun a => (MvPowerSeries.X (φ a) : MvPowerSeries τ C)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun a => by simp)
  rw [MvPowerSeries.coeff_subst hA]
  refine finsum_eq_zero_of_forall_eq_zero fun d => ?_
  rw [prod_X_rename, MvPowerSeries.coeff_monomial, if_neg, smul_zero]
  intro h
  apply hs
  rw [h, Finsupp.mapDomain_notin_range]
  rintro ⟨a, ha⟩
  exact hsr a ha

variable [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ} (Y : FBChart C V O dd)

def FBChart.rawCol : RawChart C 1 (fun _ => Empty) (Fin dd) where
  lg := fun i => un1 (Y.lg i)
  ex := fun i => un1 (Y.ex i)
  h := Y.h
  k := Y.k
  u := fun _ c => c.elim
  ty := fun _ c => c.elim
  n := 0
  j := 0
  j' := 0
  big := fun _ _ => False

theorem FBChart.rawCol_sg (v : Fin dd → C) : Y.rawCol.sg v = un1 (Y.sgP v) := by
  ext μ
  show -∑ i, v i * MvPowerSeries.coeff (μ.mapDomain (fun x : Fin dd => ((0 : Fin 2), x)) +
      Finsupp.single ((1 : Fin 2), i) 1) Y.h =
    MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.sgP v)
  simp only [FBChart.sgP, map_neg, map_sum, MvPowerSeries.coeff_C_mul, coeff_eval_second_zero]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  rw [MvPowerSeries.coeff_pderiv, Finsupp.mapDomain_notin_range]
  · simp
  · rintro ⟨x, hx⟩
    simp at hx

theorem FBChart.addCvCol (hG : GermISt Y) : Y.rawCol.AddCvSt V := by
  intro γ γ' hγ hγ'
  set ρ : Fin 2 × Fin dd → PowerSeries C := fun q => ![γ, γ'] q.1 q.2 with hρ
  have hρ0 : ∀ q, MvPowerSeries.constantCoeff (ρ q) = 0 := by
    rintro ⟨b, j⟩
    fin_cases b
    · exact (hγ j).1
    · exact (hγ' j).1
  have hρI : ∀ q, IntS V (ρ q) := by
    rintro ⟨b, j⟩
    fin_cases b
    · exact intS_ps.2 (hγ j).2
    · exact intS_ps.2 (hγ' j).2
  have hρS := MvPowerSeries.hasSubst_of_constantCoeff_zero hρ0
  set γ'' : Fin dd → PowerSeries C := fun j => MvPowerSeries.subst ρ (Y.B.G.F j) with hγ''
  have hγ''0 : ∀ j, MvPowerSeries.constantCoeff (γ'' j) = 0 := fun j =>
    constantCoeff_subst_zero hρ0 (Y.B.G.const j)
  have hγ''I : IsCv V γ'' := fun j => ⟨hγ''0 j, intS_ps.1 (IntS.subst hρ0 hρI (Y.intF j))⟩
  have hev : ∀ (a : Pt C 2 dd), (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → ∀ f : PS C 1 dd,
      MvPowerSeries.subst ρ (ev ![a] f) = alongCv (fun j => MvPowerSeries.subst ρ (a j)) (un1 f) := by
    intro a ha f
    unfold alongCv
    rw [eval_single_eq_subst, MvPowerSeries.subst_comp_subst_apply
      (MvPowerSeries.hasSubst_of_constantCoeff_zero fun q : Fin 1 × Fin dd => ha q.2) hρS,
      subst_singlePointUncurry (fun j => constantCoeff_subst_zero hρ0 (ha j))]
  have hp0 : (fun j => MvPowerSeries.subst ρ (pt C (n := 2) dd 0 j)) = γ := by
    funext j
    show MvPowerSeries.subst ρ (MvPowerSeries.X ((0 : Fin 2), j)) = γ j
    rw [MvPowerSeries.subst_X hρS]
    rfl
  have hp1 : (fun j => MvPowerSeries.subst ρ (pt C (n := 2) dd 1 j)) = γ' := by
    funext j
    show MvPowerSeries.subst ρ (MvPowerSeries.X ((1 : Fin 2), j)) = γ' j
    rw [MvPowerSeries.subst_X hρS]
    rfl
  have hpa : (fun j => MvPowerSeries.subst ρ (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j)) = γ'' := by
    funext j
    rw [addOf_pts]
  have hc0 : ∀ j, MvPowerSeries.constantCoeff (pt C (n := 2) dd 0 j) = 0 := fun j => MvPowerSeries.constantCoeff_X _
  have hc1 : ∀ j, MvPowerSeries.constantCoeff (pt C (n := 2) dd 1 j) = 0 := fun j => MvPowerSeries.constantCoeff_X _
  have hca : ∀ j, MvPowerSeries.constantCoeff (addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C (n := 2) dd 1) j) = 0 :=
    fun j => by rw [addOf_pts]; exact Y.B.G.const j
  refine ⟨γ'', hγ''I, ?_, ?_⟩
  · intro i
    have h := congrArg (MvPowerSeries.subst ρ) (Y.lg_add i)
    rw [← MvPowerSeries.coe_substAlgHom hρS, map_add, MvPowerSeries.coe_substAlgHom hρS, hev _ hca, hev _ hc0,
      hev _ hc1, hpa, hp0, hp1] at h
    exact h
  · intro v hv
    have hsg0 : MvPowerSeries.constantCoeff (Y.rawCol.sg v) = 0 := Y.rawCol.constantCoeff_sg (gauge_axes Y 0) v
    refine ⟨?_, ?_⟩
    · rw [map_sub, map_sub]
      have e1 : PowerSeries.constantCoeff (alongCv γ'' (Y.rawCol.sg v)) = 0 := constantCoeff_subst_zero hγ''0 hsg0
      have e2 : PowerSeries.constantCoeff (alongCv γ (Y.rawCol.sg v)) = 0 :=
        constantCoeff_subst_zero (fun i => (hγ i).1) hsg0
      have e3 : PowerSeries.constantCoeff (alongCv γ' (Y.rawCol.sg v)) = 0 :=
        constantCoeff_subst_zero (fun i => (hγ' i).1) hsg0
      rw [e1, e2, e3]
      simp
    · have h := IntS.subst hρ0 hρI (hG v hv)
      rw [← MvPowerSeries.coe_substAlgHom hρS, map_sub, map_sub, MvPowerSeries.coe_substAlgHom hρS, hev _ hca,
        hev _ hc0, hev _ hc1, hpa, hp0, hp1, ← Y.rawCol_sg v] at h
      exact intS_ps.1 h

variable {d : ℕ} {I0 : Type} [Fintype I0] (p : SelfData Y d I0)

theorem hCol_inj (c : Fin 2) : Function.Injective (fun q : Fin 2 × Fin dd => (q.1, (c, q.2))) := by
  intro p q h
  simp only [Prod.mk.injEq] at h
  exact Prod.ext h.1 h.2.2

theorem coeff_inCol_sg (c : Fin 2) (v : Fin 2 × Fin dd → C) (μ : Fin 2 × Fin dd →₀ ℕ) :
    coeff μ (inCol c (Y.rawCol.sg fun i => v (c, i))) =
      -∑ x, v x * coeff (μ.mapDomain (fun x => ((0 : Fin 2), x)) + Finsupp.single ((1 : Fin 2), x) 1) (hCol c Y.h) := by
  unfold inCol hCol
  by_cases hr : ∀ x, μ x ≠ 0 → x.1 = c
  · have hμ : (μ.mapDomain Prod.snd).mapDomain (fun x : Fin dd => (c, x)) = μ := by
      rw [← Finsupp.mapDomain_comp]
      conv_rhs => rw [← Finsupp.mapDomain_id (v := μ)]
      apply Finsupp.mapDomain_congr
      intro x hx
      exact Prod.ext (hr x (Finsupp.mem_support_iff.1 hx)).symm rfl
    rw [← hμ, coeff_subst_rename_inj _ (col_inj c)]
    show -∑ i, v (c, i) * MvPowerSeries.coeff
      ((μ.mapDomain Prod.snd).mapDomain (fun x : Fin dd => ((0 : Fin 2), x)) + Finsupp.single ((1 : Fin 2), i) 1) Y.h = _
    rw [Fintype.sum_prod_type, Finset.sum_eq_single c]
    · congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      congr 1
      have hE : ((μ.mapDomain Prod.snd).mapDomain (fun x : Fin dd => (c, x))).mapDomain (fun x => ((0 : Fin 2), x)) +
          Finsupp.single ((1 : Fin 2), (c, i)) 1 =
          ((μ.mapDomain Prod.snd).mapDomain (fun x : Fin dd => ((0 : Fin 2), x)) +
            Finsupp.single ((1 : Fin 2), i) 1).mapDomain (fun q : Fin 2 × Fin dd => (q.1, (c, q.2))) := by
        rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
        simp only [← Finsupp.mapDomain_comp]
        rfl
      rw [hE, coeff_subst_rename_inj _ (hCol_inj c)]
    · intro c' _ hc'
      apply Finset.sum_eq_zero
      intro i _
      rw [coeff_rename_zero (fun q : Fin 2 × Fin dd => (q.1, (c, q.2))) _ _ ((1 : Fin 2), (c', i)) (by simp), mul_zero]
      intro q hq
      simp only [Prod.mk.injEq] at hq
      exact hc' hq.2.1.symm
    · intro h
      exact absurd (Finset.mem_univ c) h
  · push_neg at hr
    obtain ⟨x0, hx0, hx0c⟩ := hr
    rw [coeff_rename_zero (fun x : Fin dd => (c, x)) _ μ x0 hx0 (fun a ha => hx0c (by rw [← ha]))]
    symm
    rw [neg_eq_zero]
    apply Finset.sum_eq_zero
    intro x _
    have hne : (μ.mapDomain (fun x => ((0 : Fin 2), x)) + Finsupp.single ((1 : Fin 2), x) 1 : Fin 2 × (Fin 2 × Fin dd) →₀ ℕ)
        ((0 : Fin 2), x0) ≠ 0 := by
      rw [Finsupp.add_apply, Finsupp.mapDomain_apply (fun a b h => (Prod.ext_iff.1 h).2), Finsupp.single_apply,
        if_neg (by simp)]
      simpa using hx0
    rw [coeff_rename_zero (fun q : Fin 2 × Fin dd => (q.1, (c, q.2))) _ _ ((0 : Fin 2), x0) hne, mul_zero]
    intro q hq
    simp only [Prod.mk.injEq] at hq
    exact hx0c (by rw [← hq.2])

theorem FBChart.rawSelf_sg (v : Fin 2 × Fin dd → C) :
    (Y.rawSelf p).sg v = ∑ c, inCol c (Y.rawCol.sg fun i => v (c, i)) := by
  ext μ
  rw [map_sum]
  simp only [coeff_inCol_sg, Finset.sum_neg_distrib]
  show -∑ x, v x * MvPowerSeries.coeff (μ.mapDomain (fun x : Fin 2 × Fin dd => ((0 : Fin 2), x)) +
      Finsupp.single ((1 : Fin 2), x) 1) (∑ col, hCol col Y.h) = _
  congr 1
  simp only [map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem addCvSelf_of (hG : GermIAllSt) : AddCvSelfSt := by
  intro C _ _ V O _ _ dd Y d _ I0 _ p γ γ' hγ hγ'
  have hA := Y.addCvCol (hG C V O dd Y)
  choose G hGcv hGlg hGsg using fun c : Fin 2 =>
    hA (fun i => γ (c, i)) (fun i => γ' (c, i)) (fun i => hγ (c, i)) (fun i => hγ' (c, i))
  have hcv : IsCv V (fun x : Fin 2 × Fin dd => G x.1 x.2) := fun x => hGcv x.1 x.2
  have along : ∀ δ : Fin 2 × Fin dd → PowerSeries C, IsCv V δ → ∀ c (f : MvPowerSeries (Fin dd) C),
      alongCv δ (inCol c f) = alongCv (fun i => δ (c, i)) f :=
    fun δ hδ c f => subst_inCol (fun x => (hδ x).1) c f
  have hsum : ∀ δ : Fin 2 × Fin dd → PowerSeries C, IsCv V δ → ∀ f : Fin 2 → MvPowerSeries (Fin dd) C,
      alongCv δ (∑ c, inCol c (f c)) = ∑ c, alongCv (fun i => δ (c, i)) (f c) := by
    intro δ hδ f
    have hS := hasSubst_of_constantCoeff_zero fun x => (hδ x).1
    unfold alongCv
    rw [← MvPowerSeries.coe_substAlgHom hS, map_sum, MvPowerSeries.coe_substAlgHom hS]
    exact Finset.sum_congr rfl fun c _ => along δ hδ c (f c)
  refine ⟨fun x => G x.1 x.2, hcv, ?_, ?_⟩
  · rintro ⟨c, i⟩
    show alongCv _ (inCol c (un1 (Y.lg i))) = alongCv γ (inCol c (un1 (Y.lg i))) + alongCv γ' (inCol c (un1 (Y.lg i)))
    rw [along _ hcv c, along γ hγ c, along γ' hγ' c]
    exact hGlg c i
  · intro v hv
    rw [Y.rawSelf_sg p v, hsum _ hcv, hsum γ hγ, hsum γ' hγ', ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine ⟨?_, fun n => ?_⟩
    · rw [map_sum]
      exact Finset.sum_eq_zero fun c _ => (hGsg c _ (fun i => hv (c, i))).1
    · rw [map_sum]
      exact VF.Ge.sum fun c _ => (hGsg c _ (fun i => hv (c, i))).2 n

theorem cartesian_self_conj_of_germs (hPT : PTSelfSt) (hG : GermIAllSt) (hStab : HStabSelfSt) : CartSelfSt := cartSelf_of hPT (addCvSelf_of hG) hStab

theorem addCvSelf_holds : AddCvSelfSt := addCvSelf_of germIAll_holds

theorem cartesian_self_conj_of_stability (hPT : PTSelfSt) (hStab : HStabSelfSt) : CartSelfSt := cartesian_self_conj_of_germs hPT germIAll_holds hStab

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePKeyDef
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace Formalism.L2.FormalSeriesBounds

namespace RowTiePKey

open PartialDerivEval RowTiePE0 RowTiePProj RowTiePLSmall RowTiePLie

structure KeyData (C : Type) [Field C] (V : VF C) (O : Type) [CommRing O] (n d : ℕ) where
  ρ : O →+* Matrix (Fin n) (Fin n) C
  ρ_int : ∀ x i j, V.Ge 0 (ρ x i j)
  P : Matrix (Fin n) (Fin n) C
  em : ZMod d → (O →+* C)
  em_int : ∀ a x, V.Ge 0 (em a x)
  em_frob : ∀ a x, V.MM (em (a + 1) x - em a x ^ V.l)
  ε : O
  ε_idem : ∃ y, ε * ε - ε = (V.l : O) * y
  ε_one : ∀ a, V.MM (em a ε - 1)
  ε_ann : ∀ x : O, (∀ a, V.MM (em a x)) → ∃ y, ε * x = (V.l : O) * y
  P_lim : ∀ (N : ℕ) i j, ∃ n0 : ℕ, ∀ n ≥ n0, V.Ge N (P i j - ρ (ε ^ V.l ^ n) i j)

def KeyEigSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C), IsAlgClosed C →
    (∀ s : ℕ → C, (∀ n : ℕ, V.Ge n (s (n + 1) - s n)) → ∃ x, ∀ n : ℕ, V.Ge n (x - s n)) →
    ∀ (O : Type) [CommRing O] (n d : ℕ) [NeZero d] (K : KeyData C V O n d) (v : Fin n → C),
      ∃ (m : ℕ) (w : Fin m → Fin n → C) (χ : Fin m → (O →+* C)),
        Matrix.mulVec K.P v = ∑ j, w j ∧ ∀ j, Matrix.mulVec K.P (w j) = w j ∧
          ∀ x, Matrix.mulVec (K.ρ x) (w j) = χ j x • w j

def KeyResSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] (n d : ℕ) [NeZero d]
    (K : KeyData C V O n d) (χ : O →+* C), (∀ y, V.Ge 0 (χ y)) →
    (∀ z, (∀ a, V.MM (K.em a z)) → V.MM (χ z)) → ∃ c, ∀ y, V.MM (χ y - K.em c y)

def KeyDeltaSt : Prop :=
  ∀ (C : Type) [Field C] [CharZero C] (V : VF C) (O : Type) [CommRing O] (n d : ℕ) [NeZero d]
    (K : KeyData C V O n d) (χ : O →+* C) (c : ZMod d), (∀ y, V.Ge 0 (χ y)) →
    (∀ y, V.MM (χ y - K.em c y)) → ∀ y, χ y = K.em c y

section Lemmas

variable {C : Type} [Field C] {V : VF C}

theorem aeval_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) C) (w : Fin n → C) (lam : C)
    (h : Matrix.mulVec A w = lam • w) (f : Polynomial C) :
    Matrix.mulVec (Polynomial.aeval A f) w = f.eval lam • w := by
  first | exact Bl.PowMulVecEigen.goal1 .. | (apply Bl.PowMulVecEigen.goal1 <;> assumption) | (intros; apply Bl.PowMulVecEigen.goal1 <;> assumption) | (apply @Bl.PowMulVecEigen.goal1 <;> assumption) | (intros; apply @Bl.PowMulVecEigen.goal1 <;> assumption) | (apply @Bl.PowMulVecEigen.goal1 <;> first | assumption | infer_instance)

theorem eig_int {n : ℕ} (A : Matrix (Fin n) (Fin n) C) (hA : ∀ i j, V.Ge 0 (A i j)) (w : Fin n → C) (hw : w ≠ 0)
    (lam : C) (h : Matrix.mulVec A w = lam • w) : V.Ge 0 lam := by
  obtain ⟨i0, hi0⟩ : ∃ i, w i ≠ 0 := by
    by_contra hc; push_neg at hc; exact hw (funext hc)

  obtain ⟨i, -, hi⟩ := Finset.exists_min_image Finset.univ (fun i => V.v (w i)) ⟨i0, Finset.mem_univ _⟩
  have hwi : w i ≠ 0 := by
    intro h0
    have := hi i0 (Finset.mem_univ _)
    rw [h0, AddValuation.map_zero, top_le_iff, AddValuation.top_iff] at this
    exact hi0 this
  have hrow : lam * w i = ∑ j, A i j * w j := by
    have := congrFun h i
    simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hge : V.v (w i) ≤ V.v (lam * w i) := by
    rw [hrow]
    refine AddValuation.map_le_sum V.v fun j _ => ?_
    rw [AddValuation.map_mul]
    have h1 := hA i j
    unfold VF.Ge at h1
    calc V.v (w i) ≤ V.v (w j) := hi j (Finset.mem_univ _)
      _ = 0 + V.v (w j) := (zero_add _).symm
      _ ≤ V.v (A i j) + V.v (w j) := add_le_add (by exact_mod_cast h1) le_rfl
  rw [AddValuation.map_mul] at hge
  unfold VF.Ge
  have hne : V.v (w i) ≠ ⊤ := (AddValuation.ne_top_iff V.v).mpr hwi
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  rw [← hr] at hge
  by_contra hlt
  push_neg at hlt
  have h2 : V.v lam + (r : WithTop ℝ) < 0 + (r : WithTop ℝ) := by
    exact WithTop.add_lt_add_right (WithTop.coe_ne_top) hlt
  rw [zero_add] at h2
  exact absurd (lt_of_le_of_lt hge h2) (lt_irrefl _)

end Lemmas

end RowTiePKey

end Formalism.L2.FormalSeriesBounds
end
end

