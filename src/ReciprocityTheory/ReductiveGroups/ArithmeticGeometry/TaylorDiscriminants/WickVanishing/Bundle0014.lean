import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.PderivSecondEvFirstPointEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0008

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConstantCoeffAddFirstSecond
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.LogPf

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

section Gen

variable {k : Type} [CommRing k] {d : ℕ}

theorem cc_pderiv' {n : ℕ} (f : PS k n d) (v : Fin n × Fin d) :
    constantCoeff (pderiv k v f) = coeff (Finsupp.single v 1) f := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

theorem zero_constant_first_point : CZ (![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) := fun j i => by simp [pt]

theorem zp (h : PS k 2 d) (i : Fin d) (p : Pt k 3 d) (hp : ∀ c, constantCoeff (p c) = 0)
    (hpz : ∀ c, pderiv k ((2 : Fin 3), i) (p c) = 0) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), i) (ev (n := 3) ![p, pt k d 2] h)) =
      -ev (n := 2) ![fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (p c)]
        (-ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) h)) := by
  have hq : CZ (![p, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons hp (CZ.cons (cc_pt 2) CZ.nil)
  have hp' : CZ (![fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (p c)] : Fin 1 → Pt k 2 d) :=
    CZ.cons (fun c => constantCoeff_ev czZ (hp c)) CZ.nil
  rw [pderiv_ev hq, Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hpz, mul_zero, Finset.sum_const_zero,
    zero_add, pderiv_pt, Prod.mk.injEq, true_and, mul_ite, mul_one, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  rw [ev_neg hp', neg_neg, ev_ev czZ hq, ev_ev hp' cz1]
  congr 1
  funext j c
  fin_cases j
  · simp [pt_apply, ev_X hp']
  · simp [pt_apply, ev_X czZ, ev_zero' hp']

end Gen

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem lawK_F (B : FB R d O) : (lawK k B).F = B.FK k := rfl

theorem cc_h {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) : constantCoeff h = 0 := by
  have h0 := congrArg constantCoeff hc.ax0
  rw [cc_ev' (by intro j i; fin_cases j <;> simp [pt]), map_zero] at h0
  exact h0

theorem constantCoeff_first_factor (B : FB R d O) : constantCoeff B.ph1 = 1 := by
  have h := congrArg constantCoeff B.cocycleLeft_zero_fst
  rw [cc_ev' (by intro j i; fin_cases j <;> simp [pt]), map_one] at h
  exact h

theorem constantCoeff_add_first_second (B : FB R d O) (l : Fin d) :
    constantCoeff (addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1) l) = 0 := by
  unfold addOf
  rw [cc_ev' (by intro j i; fin_cases j <;> simp [pt])]
  show constantCoeff (MvPowerSeries.map (algebraMap R k) (B.G.F l)) = 0
  rw [MvPowerSeries.constantCoeff_map, B.G.const l, map_zero]

theorem sig_add {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (i : Fin d) :
    ev (n := 2) ![(lawK k B).F] (sgOf k h i) - ev (n := 2) ![pt k d 0] (sgOf k h i) -
      ev (n := 2) ![pt k d 1] (sgOf k h i) ∈ Ig R k (Fin 2 × Fin d) := by
  have c02 : CZ (![pt k (n := 3) d 0, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt 0) (CZ.cons (cc_pt 2) CZ.nil)
  have c12 : CZ (![pt k (n := 3) d 1, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt 1) (CZ.cons (cc_pt 2) CZ.nil)
  have cA : CZ (![addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1), pt k d 2] : Fin 2 → Pt k 3 d) :=
    CZ.cons (constantCoeff_add_first_second B) (CZ.cons (cc_pt 2) CZ.nil)
  have hH0 : constantCoeff (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h -
      ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h) = 0 := by
    rw [map_sub, map_add, cc_ev' c02, cc_ev' c12, cc_ev' cA, cc_h hc]
    simp
  have hH := ig_dlog B.ph1 (constantCoeff_first_factor B) _ hH0 hc.ph1 ((2 : Fin 3), i)
  have h2 := ig_ev czZ integral_family_pair_zero hH
  have z0 : ∀ c, pderiv k ((2 : Fin 3), i) (pt k (n := 3) d 0 c) = 0 := fun c => by simp [pderiv_pt]
  have z1 : ∀ c, pderiv k ((2 : Fin 3), i) (pt k (n := 3) d 1 c) = 0 := fun c => by simp [pderiv_pt]
  have zA : ∀ c, pderiv k ((2 : Fin 3), i) (addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1) c) = 0 := fun c =>
    pderiv_ev_zero cz01 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])
  rw [map_sub, map_add, ev_sub czZ, ev_add czZ, zp h i _ (cc_pt 0) z0, zp h i _ (cc_pt 1) z1,
    zp h i _ (constantCoeff_add_first_second B) zA] at h2
  have f0 : (fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (pt k (n := 3) d 0 c)) = pt k (n := 2) d 0 := by
    funext c; simp [pt_apply, ev_X czZ]
  have f1 : (fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (pt k (n := 3) d 1 c)) = pt k (n := 2) d 1 := by
    funext c; simp [pt_apply, ev_X czZ]
  have fA : (fun c => ev (n := 2) ![pt k d 0, pt k d 1, 0] (addOf (B.FK k) (pt k (n := 3) d 0) (pt k d 1) c)) =
      (lawK k B).F := by
    funext c
    show ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 0, pt k d 1] (B.FK k c)) = B.FK k c
    rw [ev_ev czZ cz01]
    have : (fun j c => ev (n := 2) ![pt k d 0, pt k d 1, 0] ((![pt k (n := 3) d 0, pt k d 1] : Fin 2 → Pt k 3 d) j c)) =
        fun j => pt k (n := 2) d j := by
      funext j c; fin_cases j <;> simp [pt_apply, ev_X czZ]
    rw [this, ev_pt]
  have es : -ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) h) = sgOf k h i := rfl
  rw [f0, f1, fA, es] at h2
  have e : ev (n := 2) ![(lawK k B).F] (sgOf k h i) - ev (n := 2) ![pt k d 0] (sgOf k h i) -
      ev (n := 2) ![pt k d 1] (sgOf k h i) =
      -ev (n := 2) ![pt k d 0] (sgOf k h i) + -ev (n := 2) ![pt k d 1] (sgOf k h i) -
        -ev (n := 2) ![(lawK k B).F] (sgOf k h i) := by ring
  rw [e]
  exact h2

theorem sig_lin {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (i b : Fin d) :
    ∑ c, pderiv k ((0 : Fin 1), c) (sgOf k h i) * Jac (lawK k B) c b - C (sg1 k h i b) ∈ Ig R k (Fin 1 × Fin d) := by
  have h3 := ig_ev cz1 integral_family_point_zero (ig_pderiv (sig_add hc i) ((1 : Fin 2), b))
  have d0 : pderiv k ((1 : Fin 2), b) (ev (n := 2) ![pt k d 0] (sgOf k h i)) = 0 :=
    pderiv_ev_zero zero_constant_first_point _ _ (fun j l => by fin_cases j; simp [pderiv_pt])
  rw [map_sub, map_sub, d0, sub_zero, ev_sub cz1, d_F, d_y, ez_y, ev_sum cz1] at h3
  simp only [ev_mul cz1, ezF, ez_dF, cc_pderiv'] at h3
  exact h3

theorem dof_sig {B : FB R d O} {h : PS k 2 d} (hc : B.IsCanonGauge k h) (u : Fin d → R) (i : Fin d) :
    Dof (B.FK k) (fun j => algebraMap R k (u j)) (sgOf k h i) -
      C (∑ j, sg1 k h i j * algebraMap R k (u j)) ∈ Ig R k (Fin 1 × Fin d) := by
  have e1 : Dof (B.FK k) (fun j => algebraMap R k (u j)) (sgOf k h i) =
      ∑ b, C (algebraMap R k (u b)) * ∑ c, pderiv k ((0 : Fin 1), c) (sgOf k h i) * Jac (lawK k B) c b := by
    simp only [Dof, Jac, lawK_F, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  have e2 : (C (∑ j, sg1 k h i j * algebraMap R k (u j)) : PS k 1 d) =
      ∑ b, C (algebraMap R k (u b)) * C (sg1 k h i b) := by
    simp only [map_sum, map_mul]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  rw [e1, e2, ← Finset.sum_sub_distrib]
  refine sum_mem fun b _ => ?_
  rw [← mul_sub]
  exact mul_mem (ig_C _) (sig_lin hc i b)

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HarmonicValueIntegral
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val

open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

private theorem hasSubst_lemma {σ τ k : Type} [CommRing k] [Finite σ] {a : σ → MvPowerSeries τ k}
    (ha : ∀ s, constantCoeff (a s) = 0) : HasSubst a := by
  first
  | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
  | exact MvPowerSeries.HasSubst.of_constantCoeff_zero' ha
  | exact ⟨fun s => by simp [ha s], fun d => Set.toFinite _⟩

private theorem mvPowerSeries_subst_C {σ τ k : Type} [CommRing k] {a : σ → MvPowerSeries τ k} (hs : HasSubst a) (c : k) :
    subst a (C c : MvPowerSeries σ k) = (C c : MvPowerSeries τ k) := by
  have e : ∀ (ρ : Type), (C c : MvPowerSeries ρ k) = c • (1 : MvPowerSeries ρ k) := fun ρ => by
    first
    | rw [MvPowerSeries.smul_eq_C_mul, mul_one]
    | simp [MvPowerSeries.smul_eq_C_mul]
  rw [e σ, e τ, ← coe_substAlgHom hs, map_smul, map_one]

theorem const_subst {σ τ k : Type} [CommRing k] [Finite σ] {a : σ → MvPowerSeries τ k}
    (ha : ∀ s, constantCoeff (a s) = 0) (G : MvPowerSeries σ k) : constantCoeff (subst a G) = constantCoeff G := by
  have hs : HasSubst a := hasSubst_lemma ha
  have h0 : constantCoeff (G - C (constantCoeff G)) = 0 := by simp
  have h1 : constantCoeff (subst a (G - C (constantCoeff G))) = 0 := by
    first
    | exact constantCoeff_subst_eq_zero hs _ h0
    | exact constantCoeff_subst_eq_zero hs h0
    | (apply constantCoeff_subst_eq_zero <;> assumption)
  have e : subst a (G - C (constantCoeff G)) = subst a G - C (constantCoeff G) := by
    rw [← coe_substAlgHom hs, map_sub, coe_substAlgHom hs, mvPowerSeries_subst_C hs]
  rw [e, map_sub, constantCoeff_C, sub_eq_zero] at h1
  exact h1

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

def bE (h : PS k 2 d) : Fin d ⊕ Fin d → PS k 1 d := Sum.elim (fun j => X ((0 : Fin 1), j)) (fun i => sgOf k h i)

theorem sg_const (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) (i : Fin d) :
    constantCoeff (sgOf k h i) = 0 := by
  unfold sgOf
  rw [map_neg, ← coeff_zero_eq_constantCoeff_apply, coeff_ev_zero_right, Finsupp.embDomain_zero, coeff_pderiv]
  rw [coeff_eq_zero_of_vanish_first_axis h hax _ (fun i' => by simp [Finsupp.single_apply])]
  simp

theorem bE_const (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) : ∀ t, constantCoeff (bE k h t) = 0 := by
  intro t
  rcases t with j | i
  · show constantCoeff (X ((0 : Fin 1), j) : PS k 1 d) = 0
    simp
  · exact sg_const k h hax i

theorem E_liftX (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) (f : PS k 1 d) :
    subst (bE k h) (liftX k f) = f := by
  have hb : HasSubst (bE k h) := hasSubst_lemma (bE_const k h hax)
  have hl : HasSubst (fun p : Fin 1 × Fin d => (X (Sum.inl p.2) : AA k d)) := hasSubst_lemma (fun p => by simp)
  unfold liftX
  first
  | rw [subst_comp_subst_apply hl hb]
  | rw [subst_comp_subst_apply hb hl]
  have e : (fun p : Fin 1 × Fin d => subst (bE k h) (X (Sum.inl p.2) : AA k d)) =
      (X : Fin 1 × Fin d → PS k 1 d) := by
    funext p
    rw [subst_X hb]
    rcases p with ⟨q, j⟩
    have hq : q = 0 := Subsingleton.elim _ _
    subst hq
    rfl
  rw [e]
  first
  | (rw [subst_self]; rfl)
  | exact congrFun subst_self f
  | simp [subst_self]
  | (rw [← map_algebraMap_eq_subst_X]; simp)

section Inter

variable {k}

theorem E_nabla (B : FB R d O) (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) (m : ℕ) (u : Fin d → k)
    (G : AA k d) : subst (bE k h) (nabla k B h m u 0 G) = Dof (B.FK k) u (subst (bE k h) G) := by
  have hc := bE_const k h hax
  have hb : HasSubst (bE k h) := hasSubst_of_constantCoeff_zero hc
  have hfm : subst (bE k h) (fm k h u) = 0 := by
    unfold fm
    rw [← coe_substAlgHom hb, map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul, map_sub, coe_substAlgHom hb, subst_X hb, E_liftX k h hax]
    simp [bE]
  have hE : ∀ t, subst (bE k h) (cf k B h u 0 t) = Dof (B.FK k) u (bE k h t) := by
    rintro (j | i)
    · rw [cf_inl, E_liftX k h hax]
      exact (Dof_X k (B.FK k) u j).symm
    · rw [cf_inr, Pi.zero_apply, map_zero, add_zero, E_liftX k h hax]
      rfl
  rw [nabla_eq, vf, ← coe_substAlgHom hb, map_sub, map_sum]
  simp only [map_mul, coe_substAlgHom hb, hfm, hE, mul_zero, zero_mul, sub_zero]
  unfold Dof
  simp only [LogPf.pderiv_subst hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem E_iter (B : FB R d O) (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) (m : ℕ) (u : Fin d → k)
    (n : ℕ) (G : AA k d) :
    subst (bE k h) ((nabla k B h m u 0)^[n] G) = (Dof (B.FK k) u)^[n] (subst (bE k h) G) := by
  induction n generalizing G with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', E_nabla B h hax m u, ih]

theorem E_foldr (B : FB R d O) (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) (m : ℕ) {ι : Type}
    (u : ι → Fin d → k) (n : ι →₀ ℕ) (L : List ι) (G : AA k d) :
    subst (bE k h) (L.foldr (fun l g => (nabla k B h m (u l) 0)^[n l] g) G) =
      L.foldr (fun l g => (Dof (B.FK k) (u l))^[n l] g) (subst (bE k h) G) := by
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [List.foldr_cons]
    rw [E_iter B h hax m (u l) (n l), ih]

theorem E_nablaPoly (B : FB R d O) (h : PS k 2 d) (hax : ev (n := 1) ![0, pt k d 0] h = 0) (m : ℕ) {ι : Type}
    [Fintype ι] (u : ι → Fin d → k) (P : MvPolynomial ι k) (G : AA k d) :
    subst (bE k h) (nablaPoly k B h m u P G) = DpolyOf (B.FK k) u P (subst (bE k h) G) := by
  have hb : HasSubst (bE k h) := hasSubst_lemma (bE_const k h hax)
  unfold nablaPoly DpolyOf DmonOf
  rw [← coe_substAlgHom hb, map_sum]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [map_mul, coe_substAlgHom hb, mvPowerSeries_subst_C hb, E_foldr B h hax m u n]

end Inter

theorem harmonic_value_integral : ReciprocityTheory.ChartRestriction.G.TB.ValueSt := by
  intro R _ d O _ _ k _ _ _ B h hax m ι _ u P g
  rw [← const_subst (bE_const k h hax) (nablaPoly k B h m u P (liftX k g)), E_nablaPoly B h hax m u P,
    E_liftX k h hax g]

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Val
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.HomUniq
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

def HomUniqSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (G : FGLaw k d) (ψ ψ' : Pt k 1 d),
    (∀ i, constantCoeff (ψ i) = 0) → (∀ i, constantCoeff (ψ' i) = 0) →
    comp1 ψ (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      G.add (comp1 ψ (pt k (n := 2) d 0)) (comp1 ψ (pt k (n := 2) d 1)) →
    comp1 ψ' (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      G.add (comp1 ψ' (pt k (n := 2) d 0)) (comp1 ψ' (pt k (n := 2) d 1)) →
    dLin ψ = dLin ψ' → ψ = ψ'

namespace HomUniqPf

open ReciprocityTheory.ChartRestriction.G.TB.LogPf Formalism.FG.SolveVAux

variable {k : Type} [CommRing k] {d : ℕ}

theorem cz1 {n : ℕ} (a : Pt k n d) (ha : ∀ i, constantCoeff (a i) = 0) : CZ (![a] : Fin 1 → Pt k n d) := by
  intro j i
  fin_cases j
  exact ha i

theorem cz_pt {n : ℕ} (j : Fin n) : ∀ i, constantCoeff (pt k (n := n) d j i) = 0 := fun i => by
  unfold pt
  exact MvPowerSeries.constantCoeff_X _

private theorem cc_ev_lemma {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  unfold ev
  have hs : MvPowerSeries.HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := by
    first
      | exact MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)
      | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent
          (fun p => by rw [ha p.1 p.2]; exact IsNilpotent.zero)
  rw [MvPowerSeries.constantCoeff_subst hs, finsum_eq_single _ 0]
  · simp
  · intro e he
    obtain ⟨s, hs'⟩ : ∃ s, e s ≠ 0 := by
      by_contra h
      push_neg at h
      exact he (Finsupp.ext h)
    rw [Finsupp.prod, map_prod, Finset.prod_eq_zero (i := s) (Finsupp.mem_support_iff.mpr hs'),
      smul_zero]
    rw [map_pow, ha s.1 s.2, zero_pow hs']

theorem cz_comp1 {n : ℕ} (φ : Pt k 1 d) (hφ : ∀ i, constantCoeff (φ i) = 0) (a : Pt k n d)
    (ha : ∀ i, constantCoeff (a i) = 0) : ∀ i, constantCoeff (comp1 φ a i) = 0 := by
  unfold comp1
  intro i
  rw [cc_ev_lemma (cz1 a ha), hφ i]

end HomUniqPf

end ReciprocityTheory.ChartRestriction.G.TB
end
end

