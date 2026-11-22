import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.SubstOps

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.PowerSeriesDiagonalLinear
section
noncomputable section

open Classical

namespace PI.BeDiagZp.SubstW

def Rint (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    rw [norm_mul]
    have := norm_nonneg a
    have := norm_nonneg b
    nlinarith
  one_mem' := by simp
  add_mem' := by
    intro a b ha hb
    simp only [Set.mem_ofPred_eq] at *
    exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by simp
  neg_mem' := by
    intro a ha
    simpa using ha

def SerS {K : Type*} [CommRing K] (S : Subring K) (σ : Type*) : Subring (MvPowerSeries σ K) :=
  (MvPowerSeries.map S.subtype).range

theorem mem_SerS {K : Type*} [CommRing K] (S : Subring K) {σ : Type*} (f : MvPowerSeries σ K) :
    f ∈ SerS S σ ↔ ∀ e, MvPowerSeries.coeff e f ∈ S := by
  constructor
  · rintro ⟨g, rfl⟩ e
    rw [MvPowerSeries.coeff_map]
    exact (MvPowerSeries.coeff e g).2
  · intro h
    obtain ⟨g, hg⟩ : ∃ g : MvPowerSeries σ S, ∀ e, MvPowerSeries.coeff e g = ⟨MvPowerSeries.coeff e f, h e⟩ :=
      ⟨fun e => ⟨MvPowerSeries.coeff e f, h e⟩, fun e => rfl⟩
    refine ⟨g, ?_⟩
    ext e
    rw [MvPowerSeries.coeff_map, hg]
    rfl

theorem constantCoeff_lift {K : Type*} [CommRing K] (S : Subring K) {σ : Type*}
    (g : MvPowerSeries σ S) {c : S}
    (h : MvPowerSeries.constantCoeff (MvPowerSeries.map S.subtype g) = (c : K)) :
    MvPowerSeries.constantCoeff g = c := by
  apply Subtype.ext
  rw [← h, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
    ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_map]
  rfl

theorem mvsubst_mem_SerS {K : Type*} [CommRing K] (S : Subring K) {σ τ : Type*} [Finite σ]
    {a : σ → MvPowerSeries τ K} {f : MvPowerSeries σ K}
    (ha0 : ∀ i, MvPowerSeries.constantCoeff (a i) = 0)
    (ha : ∀ i, a i ∈ SerS S τ) (hf : f ∈ SerS S σ) : MvPowerSeries.subst a f ∈ SerS S τ := by
  choose b hb using ha
  obtain ⟨g, rfl⟩ := hf
  have hb0 : ∀ i, MvPowerSeries.constantCoeff (b i) = 0 := by
    intro i
    exact constantCoeff_lift S (b i) (c := 0) (by rw [hb i, ha0 i]; rfl)
  have hsub : MvPowerSeries.HasSubst b := MvPowerSeries.hasSubst_of_constantCoeff_zero hb0
  refine ⟨MvPowerSeries.subst b g, ?_⟩
  rw [MvPowerSeries.map_subst hsub]
  congr 1
  funext i
  exact hb i

theorem integral_iff {p : ℕ} [Fact p.Prime] {σ : Type*} (f : MvPowerSeries σ ℂ_[p]) :
    IntegralMv f ↔ f ∈ SerS (Rint p) σ := by
  rw [mem_SerS]
  exact Iff.rfl

end PI.BeDiagZp.SubstW

namespace PI.BeDiagZp

open SubstW

theorem intSubst_holds : ∀ (p : ℕ) [Fact p.Prime] (σ τ : Type) [Finite σ] (f : MvPowerSeries σ ℂ_[p])
    (s : σ → MvPowerSeries τ ℂ_[p]), (∀ i, MvPowerSeries.constantCoeff (s i) = 0) →
    (∀ i, IntegralMv (s i)) → IntegralMv f → IntegralMv (MvPowerSeries.subst s f) := by
  intro p _ σ τ _ f s h0 hs hf
  rw [integral_iff] at hf ⊢
  exact mvsubst_mem_SerS (Rint p) h0 (fun i => (integral_iff (s i)).1 (hs i)) hf

end PI.BeDiagZp

namespace PI.BeDiagZp.SubstW

variable {p : ℕ} [Fact p.Prime]

theorem deg_eq {σ : Type*} (α : σ →₀ ℕ) : (α.sum fun _ k => k) = α.degree := by
  rw [Finsupp.degree_apply]
  rfl

theorem coeff_pow_eq_zero {σ : Type*} {F : MvPowerSeries σ ℂ_[p]}
    (hF : MvPowerSeries.constantCoeff F = 0) {n : ℕ} {d : σ →₀ ℕ} (h : d.degree < n) :
    MvPowerSeries.coeff d (F ^ n) = 0 :=
  MvPowerSeries.coeff_of_lt_order
    ((Nat.cast_lt.mpr h).trans_le (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero n hF))

theorem coeff_expMv_eq {σ : Type*} {F : MvPowerSeries σ ℂ_[p]}
    (hF : MvPowerSeries.constantCoeff F = 0) (d : σ →₀ ℕ) {N : ℕ} (hN : d.degree < N) :
    MvPowerSeries.coeff d (expMv F) =
      ∑ n ∈ Finset.range N, MvPowerSeries.coeff d (F ^ n) / (n.factorial : ℂ_[p]) := by
  have e1 : MvPowerSeries.coeff d (expMv F) = ∑ n ∈ Finset.range ((d.sum fun _ k => k) + 1),
      MvPowerSeries.coeff d (F ^ n) / (n.factorial : ℂ_[p]) := rfl
  rw [e1, deg_eq]
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_range] at *
    omega
  · intro n hn hn'
    simp only [Finset.mem_range, not_lt] at hn hn'
    rw [coeff_pow_eq_zero hF (by omega), zero_div]

def expTr {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) (N : ℕ) : MvPowerSeries σ ℂ_[p] :=
  ∑ n ∈ Finset.range N, ((n.factorial : ℂ_[p])⁻¹) • F ^ n

theorem coeff_expTr {σ : Type*} (F : MvPowerSeries σ ℂ_[p]) (N : ℕ) (d : σ →₀ ℕ) :
    MvPowerSeries.coeff d (expTr F N) =
      ∑ n ∈ Finset.range N, MvPowerSeries.coeff d (F ^ n) / (n.factorial : ℂ_[p]) := by
  simp only [expTr, map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_eq_inv_mul]

theorem expMv_subst {σ τ : Type*} [Finite σ] {s : σ → MvPowerSeries τ ℂ_[p]}
    (hs0 : ∀ i, MvPowerSeries.constantCoeff (s i) = 0) {F : MvPowerSeries σ ℂ_[p]}
    (hF : MvPowerSeries.constantCoeff F = 0) :
    expMv (MvPowerSeries.subst s F) = MvPowerSeries.subst s (expMv F) := by
  have hs : MvPowerSeries.HasSubst s := MvPowerSeries.hasSubst_of_constantCoeff_zero hs0
  have hE : MvPowerSeries.constantCoeff (MvPowerSeries.subst s F) = 0 :=
    MvPowerSeries.constantCoeff_subst_eq_zero hs hs0 hF
  ext e
  have hD : ((e.degree + 1 : ℕ) : ℕ∞) ≤ (expMv F - expTr F (e.degree + 1)).order := by
    apply MvPowerSeries.le_order
    intro d hd
    have hd' : d.degree < e.degree + 1 := by exact_mod_cast hd
    rw [map_sub, coeff_expMv_eq hF d hd', coeff_expTr, sub_self]
  have h1 : (1 : ℕ∞) ≤ ⨅ i, (s i).order :=
    le_iInf fun i => MvPowerSeries.one_le_order_iff_constCoeff_eq_zero.mpr (hs0 i)
  have hsD : ((e.degree + 1 : ℕ) : ℕ∞) ≤
      (MvPowerSeries.subst s (expMv F - expTr F (e.degree + 1))).order := by
    refine le_trans ?_ (MvPowerSeries.le_order_subst hs _)
    calc ((e.degree + 1 : ℕ) : ℕ∞) ≤ (expMv F - expTr F (e.degree + 1)).order := hD
      _ = 1 * (expMv F - expTr F (e.degree + 1)).order := (one_mul _).symm
      _ ≤ _ := by
        first
          | exact mul_le_mul_right' h1 _
          | exact mul_le_mul_right h1 _
          | gcongr
  have h0 : MvPowerSeries.coeff e (MvPowerSeries.subst s (expMv F - expTr F (e.degree + 1))) = 0 :=
    MvPowerSeries.coeff_of_lt_order (lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self _) hsD)
  rw [MvPowerSeries.subst_sub hs, map_sub, sub_eq_zero] at h0
  rw [h0, coeff_expMv_eq hE e (Nat.lt_succ_self _), expTr, ← MvPowerSeries.coe_substAlgHom hs]
  simp only [map_sum, map_smul, map_pow, smul_eq_mul]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_eq_inv_mul]

end PI.BeDiagZp.SubstW

namespace PI.BeDiagZp

open SubstW

theorem power_series_diagonal_linear : S1 := by
  intro p _ σ τ _ f g s hs0 hsi hfg
  have hs : MvPowerSeries.HasSubst s := MvPowerSeries.hasSubst_of_constantCoeff_zero hs0
  obtain ⟨h0, hI⟩ := hfg
  unfold Simeq
  rw [← MvPowerSeries.subst_sub hs]
  refine ⟨MvPowerSeries.constantCoeff_subst_eq_zero hs hs0 h0, ?_⟩
  rw [expMv_subst hs0 h0]
  exact intSubst_holds p σ τ (expMv (f - g)) s hs0 hsi hI

end PI.BeDiagZp
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DiagonalPadicSubstitution.SimeqCongr
section
noncomputable section

open Classical

namespace PI.BeDiagZp

def IntSubst : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ τ : Type) [Finite σ] (f : MvPowerSeries σ ℂ_[p])
    (s : σ → MvPowerSeries τ ℂ_[p]),
    (∀ i, MvPowerSeries.constantCoeff (s i) = 0) → (∀ i, IntegralMv (s i)) →
    IntegralMv f → IntegralMv (MvPowerSeries.subst s f)

namespace Asm

variable {p : ℕ} [Fact p.Prime]

theorem simeq_congr {σ : Type} {f g f' g' : MvPowerSeries σ ℂ_[p]} (e : f - g = f' - g')
    (h : Simeq f g) : Simeq f' g' := by
  unfold Simeq at *
  rw [← e]
  exact h

theorem intX {σ : Type} (i : σ) : IntegralMv (Xv i : MvPowerSeries σ ℂ_[p]) := by
  intro n
  simp only [IsIntP, Xv, MvPowerSeries.coeff_X]
  split_ifs <;> simp

theorem int0 {σ : Type} : IntegralMv (0 : MvPowerSeries σ ℂ_[p]) := by
  intro n
  simp [IsIntP]

theorem ccX {σ : Type} (i : σ) : MvPowerSeries.constantCoeff (Xv i : MvPowerSeries σ ℂ_[p]) = 0 := by
  simp [Xv]

end Asm

open Asm

theorem beDiagZp_of (h0 : S0) (h1 : S1) (h2 : SubstOps) (h3 : Ident) (h4 : Cont) (h5 : IntSubst) :
    Target := by
  intro p _ l ex ph S hex hlex hswap hint hgrp hz hphi hconj hbi
  obtain ⟨hl0, hI⟩ := h3 p l ex hex hlex

  have rfl' : ∀ {σ : Type} (f : MvPowerSeries σ ℂ_[p]), Simeq f f := fun f => (h0 p _ f f f f f).1
  have symm' : ∀ {σ : Type} {f g : MvPowerSeries σ ℂ_[p]}, Simeq f g → Simeq g f :=
    fun {σ} {f g} h => (h0 p σ f g g g g).2.1 h
  have trans' : ∀ {σ : Type} {f g k : MvPowerSeries σ ℂ_[p]}, Simeq f g → Simeq g k → Simeq f k :=
    fun {σ} {f g k} a b => (h0 p σ f g k f f).2.2.1 a b
  have add' : ∀ {σ : Type} {f g f' g' : MvPowerSeries σ ℂ_[p]}, Simeq f g → Simeq f' g' →
      Simeq (f + f') (g + g') :=
    fun {σ} {f g f' g'} a b => (h0 p σ f g f f' g').2.2.2 a b

  have cA : ∀ {σ : Type} (a b : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff b = 0 → MvPowerSeries.constantCoeff (add l ex a b) = 0 :=
    fun a b ha hb => (hI _ a b ha hb).1
  have cM : ∀ {σ : Type} (c : ℂ_[p]) (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff (mulBy l ex c a) = 0 :=
    fun c a ha => (hI _ a a ha ha).2.1 c
  have comm : ∀ {σ : Type} (a b : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff b = 0 → add l ex a b = add l ex b a :=
    fun a b ha hb => (hI _ a b ha hb).2.2.1
  have add2 : ∀ {σ : Type} (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      add l ex a a = mulBy l ex 2 a :=
    fun a ha => (hI _ a a ha ha).2.2.2.1
  have addM : ∀ {σ : Type} (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      ∀ c d, add l ex (mulBy l ex c a) (mulBy l ex d a) = mulBy l ex (c + d) a :=
    fun a ha => (hI _ a a ha ha).2.2.2.2.1
  have addS : ∀ {σ : Type} (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      ∀ c, add l ex (mulBy l ex c a) a = mulBy l ex (c + 1) a :=
    fun a ha => (hI _ a a ha ha).2.2.2.2.2.1
  have mul1 : ∀ {σ : Type} (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      mulBy l ex 1 a = a :=
    fun a ha => (hI _ a a ha ha).2.2.2.2.2.2.1
  have mul0 : ∀ {σ : Type} (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      mulBy l ex 0 a = 0 :=
    fun a ha => (hI _ a a ha ha).2.2.2.2.2.2.2
  have bsym : ∀ {σ : Type} (a b : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff b = 0 → be l ex ph a b = be l ex ph b a := by
    intro σ a b ha hb
    simp only [be]
    rw [comm a b ha hb]
    abel

  have addZ : ∀ {σ : Type} (a : MvPowerSeries σ ℂ_[p]), MvPowerSeries.constantCoeff a = 0 →
      add l ex a 0 = a := by
    intro σ a ha
    have e := addM a ha 1 0
    rw [mul1 a ha, mul0 a ha, add_zero, mul1 a ha] at e
    exact e
  have ccU : MvPowerSeries.constantCoeff (Xv () : MvPowerSeries Unit ℂ_[p]) = 0 := ccX ()

  have K1 : ∀ α ∈ S, Simeq (be l ex ph (mulBy l ex α.1 (Xv ())) (Xv ()) : MvPowerSeries Unit ℂ_[p])
      (be l ex ph (Xv ()) (mulBy l ex α.2 (Xv ()))) := by
    intro α hα
    have H := h1 p (Fin 2) Unit _ _ (fun _ => (Xv () : MvPowerSeries Unit ℂ_[p])) (fun _ => ccU)
      (fun _ => intX ()) (hconj α hα)
    obtain ⟨hsX, -, -, hr⟩ := h2 p l ex ph hex hl0 (Fin 2) Unit
      (fun _ => (Xv () : MvPowerSeries Unit ℂ_[p])) (fun _ => ccU)
    have e1 := (hr _ _ (cM α.1 _ (ccX (0 : Fin 2))) (ccX (1 : Fin 2))).2.2.2.2
    have e2 := (hr _ _ (ccX (0 : Fin 2)) (cM α.2 _ (ccX (1 : Fin 2)))).2.2.2.2
    have e3 := (hr _ _ (ccX (0 : Fin 2)) (ccX (0 : Fin 2))).2.2.1 α.1
    have e4 := (hr _ _ (ccX (1 : Fin 2)) (ccX (1 : Fin 2))).2.2.1 α.2
    simp only [e1, e2, e3, e4, hsX] at H
    exact H

  have K2 : ∀ a b c : MvPowerSeries Unit ℂ_[p], MvPowerSeries.constantCoeff a = 0 →
      MvPowerSeries.constantCoeff b = 0 → MvPowerSeries.constantCoeff c = 0 →
      IntegralMv a → IntegralMv b → IntegralMv c →
      Simeq (be l ex ph (add l ex a b) c) (be l ex ph a c + be l ex ph b c) := by
    intro a b c ha hb hc ia ib ic
    have hs : ∀ i, MvPowerSeries.constantCoeff (![a, b, c] i) = 0 := by
      intro i; fin_cases i <;> simpa
    have is : ∀ i, IntegralMv (![a, b, c] i) := by
      intro i; fin_cases i <;> simpa
    have H := h1 p (Fin 3) Unit _ _ ![a, b, c] hs is hbi
    obtain ⟨hsX, -, hsA, hr⟩ := h2 p l ex ph hex hl0 (Fin 3) Unit ![a, b, c] hs
    have e1 := (hr _ _ (cA _ _ (ccX (0 : Fin 3)) (ccX (1 : Fin 3))) (ccX (2 : Fin 3))).2.2.2.2
    have e2 := (hr _ _ (ccX (0 : Fin 3)) (ccX (1 : Fin 3))).2.1
    have e3 := (hr _ _ (ccX (0 : Fin 3)) (ccX (2 : Fin 3))).2.2.2.2
    have e4 := (hr _ _ (ccX (1 : Fin 3)) (ccX (2 : Fin 3))).2.2.2.2
    simp only [hsA, e1, e2, e3, e4, hsX] at H
    simpa using H

  have K0 : Simeq (be l ex ph (Xv ()) (mulBy l ex ((0 : ℕ) : ℂ_[p]) (Xv ())) : MvPowerSeries Unit ℂ_[p])
      (MvPowerSeries.C ((0 : ℕ) : ℂ_[p]) * be l ex ph (Xv ()) (Xv ())) := by
    have H := symm' (K2 0 0 0 (map_zero _) (map_zero _) (map_zero _) int0 int0 int0)
    have z00 : add l ex (0 : MvPowerSeries Unit ℂ_[p]) 0 = 0 := addZ 0 (map_zero _)
    refine simeq_congr ?_ H
    rw [Nat.cast_zero, mul0 _ ccU, map_zero, zero_mul, sub_zero]
    simp only [be, z00, addZ _ ccU]
    abel

  have K3 : ∀ n : ℕ, IntegralMv (mulBy l ex (n : ℂ_[p]) (Xv ()) : MvPowerSeries Unit ℂ_[p]) ∧
      Simeq (be l ex ph (Xv ()) (mulBy l ex (n : ℂ_[p]) (Xv ())) : MvPowerSeries Unit ℂ_[p])
        (MvPowerSeries.C (n : ℂ_[p]) * be l ex ph (Xv ()) (Xv ())) := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, K0⟩
      rw [Nat.cast_zero, mul0 _ ccU]
      exact int0
    | succ n ih =>
      obtain ⟨iN, hN⟩ := ih
      have cN := cM (n : ℂ_[p]) _ ccU
      have eS : mulBy l ex ((n + 1 : ℕ) : ℂ_[p]) (Xv ()) =
          add l ex (mulBy l ex (n : ℂ_[p]) (Xv ())) (Xv () : MvPowerSeries Unit ℂ_[p]) := by
        rw [addS _ ccU, Nat.cast_succ]
      rw [eS]
      refine ⟨?_, ?_⟩
      · have hs : ∀ i, MvPowerSeries.constantCoeff
            (![mulBy l ex (n : ℂ_[p]) (Xv ()), (Xv () : MvPowerSeries Unit ℂ_[p])] i) = 0 := by
          intro i; fin_cases i <;> simpa
        have is : ∀ i, IntegralMv
            (![mulBy l ex (n : ℂ_[p]) (Xv ()), (Xv () : MvPowerSeries Unit ℂ_[p])] i) := by
          intro i; fin_cases i
          · simpa using iN
          · simpa using (intX () : IntegralMv (Xv () : MvPowerSeries Unit ℂ_[p]))
        have H := h5 p (Fin 2) Unit _ _ hs is hgrp
        obtain ⟨hsX, -, -, hr⟩ := h2 p l ex ph hex hl0 (Fin 2) Unit _ hs
        rw [(hr _ _ (ccX (0 : Fin 2)) (ccX (1 : Fin 2))).2.1, hsX, hsX] at H
        simpa using H
      · rw [bsym _ _ ccU (cA _ _ cN ccU)]
        have H := K2 _ _ _ cN ccU ccU iN (intX ()) (intX ())
        rw [bsym _ _ cN ccU] at H
        have H2 := trans' H (add' hN (rfl' (be l ex ph (Xv ()) (Xv ()))))
        have e : MvPowerSeries.C (n : ℂ_[p]) * be l ex ph (Xv ()) (Xv ()) + be l ex ph (Xv ()) (Xv ()) =
            (MvPowerSeries.C ((n + 1 : ℕ) : ℂ_[p]) * be l ex ph (Xv ()) (Xv ()) : MvPowerSeries Unit ℂ_[p]) := by
          rw [Nat.cast_succ, map_add, map_one, add_mul, one_mul]
        rw [e] at H2
        exact H2
  have K4 := h4 p l ex ph hex hl0 (fun n => (K3 n).2)
  refine ⟨?_, ?_⟩
  · intro γ hγ
    obtain ⟨n, hn⟩ := hz γ hγ
    have ia : IntegralMv (mulBy l ex γ.1 (Xv ()) : MvPowerSeries Unit ℂ_[p]) := hint γ hγ
    have ib : IntegralMv (mulBy l ex γ.2 (Xv ()) : MvPowerSeries Unit ℂ_[p]) := hint γ.swap (hswap γ hγ)
    have ca := cM γ.1 _ ccU
    have cb := cM γ.2 _ ccU

    have C1 := K1 γ.swap (hswap γ hγ)
    simp only [Prod.fst_swap, Prod.snd_swap] at C1
    rw [bsym _ _ cb ccU] at C1

    have H := K2 _ _ _ ca cb ccU ia ib (intX ())
    rw [addM _ ccU, hn, bsym _ _ (cM _ _ ccU) ccU, bsym _ _ ca ccU, bsym _ _ cb ccU] at H
    have A := add' (rfl' (be l ex ph (Xv ()) (mulBy l ex γ.1 (Xv ())))) (symm' C1)
    have B := trans' (trans' A (symm' H)) (K4 n)
    rw [← hn] at B
    rw [two_mul]
    exact B
  · refine simeq_congr ?_ hphi
    simp only [be, add2 _ ccU]
    rw [map_mul, map_ofNat]
    ring

end PI.BeDiagZp
end
end

