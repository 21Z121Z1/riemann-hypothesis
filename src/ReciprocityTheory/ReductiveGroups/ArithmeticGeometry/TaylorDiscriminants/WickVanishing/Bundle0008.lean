import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ExpLaw
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ActLin
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB

def ActLinSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB k d O)
    (ℓ ε : Pt k 1 d), (∀ i, constantCoeff (ℓ i) = 0) → dLin ℓ = 1 →
    comp1 ℓ (B.G.add (pt k (n := 2) d 0) (pt k (n := 2) d 1)) =
      comp1 ℓ (pt k (n := 2) d 0) + comp1 ℓ (pt k (n := 2) d 1) →
    IsInvPair ε ℓ → ∀ (a : O) (i : Fin d),
      comp1 ℓ (comp1 (B.A.act a) ε) i = ∑ j, C (dLin (B.A.act a) i j) * X ((0 : Fin 1), j)

namespace WickVanishing

variable {k : Type} [CommRing k] [Algebra ℚ k]

theorem hom_at {d : ℕ} {O : Type} [CommRing O] (G : FGLaw k d) (A : OAct O G) (a : O) {n : ℕ}
    (u v : Pt k n d) (hu : ∀ i, constantCoeff (u i) = 0) (hv : ∀ i, constantCoeff (v i) = 0) :
    comp1 (A.act a) (addOf G.F u v) = addOf G.F (comp1 (A.act a) u) (comp1 (A.act a) v) := by
  have huv : ∀ j i, constantCoeff ((![u, v] : Fin 2 → Pt k n d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact hu i
    · exact hv i
  have hpt : ∀ (m : ℕ) (j : Fin m) (i : Fin d), constantCoeff (pt k (n := m) d j i) = 0 := fun m j i =>
    MvPowerSeries.constantCoeff_X _
  have hp01 : ∀ j i, constantCoeff ((![pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 2 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j <;> exact hpt _ _ _
  have hp0 : ∀ j i, constantCoeff ((![pt k (n := 2) d 0] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact hpt _ _ _
  have hp1 : ∀ j i, constantCoeff ((![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact hpt _ _ _
  have hadd01 : ∀ j i, constantCoeff ((![addOf G.F (pt k (n := 2) d 0) (pt k (n := 2) d 1)] :
      Fin 1 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    exact cc_ev _ hp01 (G.const i)
  have hc01 : ∀ j i, constantCoeff ((![comp1 (A.act a) (pt k (n := 2) d 0), comp1 (A.act a) (pt k (n := 2) d 1)] :
      Fin 2 → Pt k 2 d) j i) = 0 := by
    intro j i
    fin_cases j
    · exact cc_ev _ hp0 (A.const a i)
    · exact cc_ev _ hp1 (A.const a i)
  have hev2 : ∀ (j : Fin 2) (l : Fin d), ev (![u, v] : Fin 2 → Pt k n d)
      ((![pt k (n := 2) d 0, pt k (n := 2) d 1] : Fin 2 → Pt k 2 d) j l) = (![u, v] : Fin 2 → Pt k n d) j l := by
    intro j l
    fin_cases j
    · exact ev_X _ huv 0 l
    · exact ev_X _ huv 1 l
  funext i
  have h := congrArg (ev (![u, v] : Fin 2 → Pt k n d)) (congrFun (A.hom a) i)
  simp only [comp1, FGLaw.add, addOf] at h ⊢
  rw [ev_ev _ _ hadd01 huv, ev_ev _ _ hc01 huv] at h
  convert h using 2
  · funext j l
    fin_cases j
    simp only [addOf, Matrix.cons_val_zero, Fin.zero_eta, Fin.isValue]
    rw [ev_ev _ _ hp01 huv]
    congr 1
    funext j' l'
    exact (hev2 j' l').symm
  · funext j l
    fin_cases j
    · simp only [comp1, Matrix.cons_val_zero, Fin.zero_eta, Fin.isValue]
      rw [ev_ev _ _ hp0 huv]
      congr 1
      funext j' l'
      fin_cases j'
      exact (ev_X _ huv 0 l').symm
    · simp only [comp1, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero, Fin.mk_one, Fin.isValue]
      rw [ev_ev _ _ hp1 huv]
      congr 1
      funext j' l'
      fin_cases j'
      exact (ev_X _ huv 1 l').symm

theorem dLin_pt {d : ℕ} : dLin (pt k (n := 1) d 0) = 1 := by
  ext i j
  simp only [dLin, pt, Matrix.one_apply, MvPowerSeries.coeff_X]
  by_cases h : i = j
  · subst h
    simp
  · rw [if_neg, if_neg h]
    intro h2
    apply h
    have h3 := (Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)).mp h2
    exact (Prod.mk.inj h3).2.symm

open Formalism.FG.SolveVAux in
theorem action_linear : ActLinSt := by
  have single_of_degree : ∀ {σ : Type} (n : σ →₀ ℕ), n.degree = 1 → ∃ p, n = Finsupp.single p 1 := by
    intro σ n h
    classical
    have hc : Multiset.card (Finsupp.toMultiset n) = 1 := by
      rw [Finsupp.card_toMultiset, ← h]
      rfl
    obtain ⟨p, hp⟩ := Multiset.card_eq_one.mp hc
    refine ⟨p, ?_⟩
    have h2 := congrArg Multiset.toFinsupp hp
    rw [Finsupp.toMultiset_toFinsupp, Multiset.toFinsupp_singleton] at h2
    exact h2
  intro k _ _ d O _ _ B ℓ ε hℓ0 hℓ1 hadd hinv a i
  obtain ⟨hε0, -, hεℓ, hℓε⟩ := hinv
  have hA0 : ∀ i, constantCoeff (B.A.act a i) = 0 := B.A.const a
  have hcc1 : ∀ {n : ℕ} (φ : Pt k 1 d) (w : Pt k n d), (∀ i, constantCoeff (φ i) = 0) →
      (∀ i, constantCoeff (w i) = 0) → ∀ i, constantCoeff (comp1 φ w i) = 0 := fun φ w hφ hw i =>
    cc_ev _ (fun j l => by fin_cases j; exact hw l) (hφ i)
  have hccA : ∀ {n : ℕ} (u v : Pt k n d), (∀ i, constantCoeff (u i) = 0) → (∀ i, constantCoeff (v i) = 0) →
      ∀ i, constantCoeff (addOf B.G.F u v i) = 0 := fun u v hu hv i =>
    cc_ev _ (fun j l => by
      fin_cases j
      · exact hu l
      · exact hv l) (B.G.const i)
  have hpt : ∀ {n : ℕ} (w : Pt k n d), (∀ i, constantCoeff (w i) = 0) → comp1 (pt k (n := 1) d 0) w = w := by
    intro n w hw
    funext i
    exact ev_X _ (fun j l => by fin_cases j; exact hw l) 0 i
  have hx : ∀ i, constantCoeff (pt k (n := 2) d 0 i) = 0 := fun i => MvPowerSeries.constantCoeff_X _
  have hy : ∀ i, constantCoeff (pt k (n := 2) d 1 i) = 0 := fun i => MvPowerSeries.constantCoeff_X _
  have hxy : ∀ i, constantCoeff ((pt k (n := 2) d 0 + pt k (n := 2) d 1) i) = 0 := fun i => by
    simp [pt]
  have hεx := hcc1 ε _ hε0 hx
  have hεy := hcc1 ε _ hε0 hy
  have hAε : ∀ i, constantCoeff (comp1 (B.A.act a) ε i) = 0 := hcc1 _ _ hA0 hε0
  have S1 : comp1 ℓ (addOf B.G.F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1))) =
      pt k (n := 2) d 0 + pt k (n := 2) d 1 := by
    rw [add_at B.G ℓ hadd _ _ hεx hεy, germComp1_germComp1_eq_substitute ℓ ε _ hε0 hx, germComp1_germComp1_eq_substitute ℓ ε _ hε0 hy, hℓε, hpt _ hx, hpt _ hy]
  have S2 : comp1 ε (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      addOf B.G.F (comp1 ε (pt k (n := 2) d 0)) (comp1 ε (pt k (n := 2) d 1)) := by
    rw [← S1, germComp1_germComp1_eq_substitute ε ℓ _ hℓ0 (hccA _ _ hεx hεy), hεℓ, hpt _ (hccA _ _ hεx hεy)]
  have S4 : comp1 ℓ (comp1 (B.A.act a) (comp1 ε (pt k (n := 2) d 0 + pt k (n := 2) d 1))) =
      comp1 ℓ (comp1 (B.A.act a) (comp1 ε (pt k (n := 2) d 0))) +
        comp1 ℓ (comp1 (B.A.act a) (comp1 ε (pt k (n := 2) d 1))) := by
    rw [S2, hom_at B.G B.A a _ _ hεx hεy, add_at B.G ℓ hadd _ _ (hcc1 _ _ hA0 hεx) (hcc1 _ _ hA0 hεy)]
  have hF : ∀ w : Pt k 2 d, (∀ i, constantCoeff (w i) = 0) →
      comp1 (comp1 ℓ (comp1 (B.A.act a) ε)) w = comp1 ℓ (comp1 (B.A.act a) (comp1 ε w)) := by
    intro w hw
    rw [← germComp1_germComp1_eq_substitute _ _ _ hAε hw, ← germComp1_germComp1_eq_substitute _ _ _ hε0 hw]
  have hfadd : comp1 (comp1 ℓ (comp1 (B.A.act a) ε)) (pt k (n := 2) d 0 + pt k (n := 2) d 1) =
      comp1 (comp1 ℓ (comp1 (B.A.act a) ε)) (pt k (n := 2) d 0) +
        comp1 (comp1 ℓ (comp1 (B.A.act a) ε)) (pt k (n := 2) d 1) := by
    rw [hF _ hxy, hF _ hx, hF _ hy]
    exact S4
  have hlin := addition_linear k d (comp1 ℓ (comp1 (B.A.act a) ε) i) (congrFun hfadd i)
  have hdε : dLin ε = 1 := by
    have h := dLin_comp1 ε ℓ hℓ0
    rw [hεℓ, dLin_pt, hℓ1, mul_one] at h
    exact h.symm
  have hdf : dLin (comp1 ℓ (comp1 (B.A.act a) ε)) = dLin (B.A.act a) := by
    rw [dLin_comp1 ℓ _ hAε, dLin_comp1 _ ε hε0, hℓ1, hdε, one_mul, mul_one]
  ext n
  rw [map_sum]
  simp only [MvPowerSeries.coeff_C_mul, MvPowerSeries.coeff_X]
  by_cases hn : n.degree = 1
  · obtain ⟨p, rfl⟩ := single_of_degree n hn
    obtain ⟨z, j0⟩ := p
    obtain rfl : z = 0 := Subsingleton.elim _ _
    have h1 : MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j0) 1) (comp1 ℓ (comp1 (B.A.act a) ε) i) =
        dLin (B.A.act a) i j0 := by
      rw [← hdf]
      rfl
    rw [h1, Finset.sum_eq_single j0]
    · simp
    · intro j _ hj
      rw [if_neg, mul_zero]
      intro h
      apply hj
      have h2 := (Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0)).mp h
      exact (Prod.mk.inj h2).2.symm
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [hlin n hn]
    symm
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg, mul_zero]
    rintro rfl
    exact hn (Finsupp.degree_single _ _)

end WickVanishing

end ReciprocityTheory.ChartRestriction.G.TB
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConnectionKillsSeries
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab

section VF

variable {k : Type} [CommRing k] {τ : Type} [Fintype τ]

def vf (c : τ → MvPowerSeries τ k) (G : MvPowerSeries τ k) : MvPowerSeries τ k := ∑ t, c t * pderiv k t G

theorem vf_add (c : τ → MvPowerSeries τ k) (f G : MvPowerSeries τ k) : vf c (f + G) = vf c f + vf c G := by
  simp only [vf, map_add, mul_add, Finset.sum_add_distrib]

theorem vf_sub (c : τ → MvPowerSeries τ k) (f G : MvPowerSeries τ k) : vf c (f - G) = vf c f - vf c G := by
  simp only [vf, map_sub, mul_sub, Finset.sum_sub_distrib]

theorem vf_sum {ι : Type} (s : Finset ι) (c : τ → MvPowerSeries τ k) (f : ι → MvPowerSeries τ k) :
    vf c (∑ i ∈ s, f i) = ∑ i ∈ s, vf c (f i) := by
  simp only [vf, map_sum, Finset.mul_sum]
  exact Finset.sum_comm

theorem vf_C (c : τ → MvPowerSeries τ k) (a : k) : vf c (C a) = 0 := by
  simp [vf, MvPowerSeries.pderiv_C]

theorem vf_zeroc (G : MvPowerSeries τ k) : vf (fun _ => (0 : MvPowerSeries τ k)) G = 0 := by
  simp [vf]

theorem vf_mul (c : τ → MvPowerSeries τ k) (f G : MvPowerSeries τ k) :
    vf c (f * G) = vf c f * G + f * vf c G := by
  simp only [vf, Derivation.leibniz, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem vf_X (c : τ → MvPowerSeries τ k) (s : τ) : vf c (X s) = c s := by
  classical
  simp [vf, MvPowerSeries.pderiv_X, Pi.single_apply]

end VF

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

theorem liftX_hs : HasSubst (fun p : Fin 1 × Fin d => (X (Sum.inl p.2) : AA k d)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun _ => MvPowerSeries.constantCoeff_X _

def liftHom : PS k 1 d →+* AA k d := (substAlgHom (liftX_hs (d := d) k)).toRingHom

theorem liftHom_apply (f : PS k 1 d) : liftHom k f = liftX k f := by
  simp only [liftHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, MvPowerSeries.substAlgHom_apply]
  rfl

theorem liftX_zero : liftX k (0 : PS k 1 d) = 0 := by
  rw [← liftHom_apply, map_zero]

theorem liftX_mul (f g : PS k 1 d) : liftX k (f * g) = liftX k f * liftX k g := by
  simp only [← liftHom_apply, map_mul]

theorem liftX_sum {ι : Type} (s : Finset ι) (f : ι → PS k 1 d) :
    liftX k (∑ i ∈ s, f i) = ∑ i ∈ s, liftX k (f i) := by
  simp only [← liftHom_apply, map_sum]

theorem pderiv_inl_liftX (f : PS k 1 d) (j : Fin d) :
    pderiv k (Sum.inl j) (liftX k f) = liftX k (pderiv k ((0 : Fin 1), j) f) := by
  classical
  unfold liftX
  rw [LogPf.pderiv_subst (fun _ => MvPowerSeries.constantCoeff_X _) f (Sum.inl j)]
  rw [Finset.sum_eq_single ((0 : Fin 1), j)]
  · simp [MvPowerSeries.pderiv_X]
  · intro p _ hp
    have hp' : p.2 ≠ j := by
      intro h
      exact hp (Prod.ext (Subsingleton.elim _ _) h)
    simp [MvPowerSeries.pderiv_X, Pi.single_apply, hp']
  · simp

theorem pderiv_inr_liftX (f : PS k 1 d) (i : Fin d) : pderiv k (Sum.inr i) (liftX k f) = 0 := by
  classical
  unfold liftX
  rw [LogPf.pderiv_subst (fun _ => MvPowerSeries.constantCoeff_X _) f (Sum.inr i)]
  simp [MvPowerSeries.pderiv_X, Pi.single_apply]

def cf (B : FB R d O) (h : PS k 2 d) (u φ : Fin d → k) : Fin d ⊕ Fin d → AA k d :=
  Sum.elim (fun j => liftX k (∑ i : Fin d, C (u i) * ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) (B.FK k j))))
    (fun i => liftX k (Dof (B.FK k) u (sgOf k h i)) + C (φ i))

def fm (h : PS k 2 d) (u : Fin d → k) : AA k d := ∑ i : Fin d, (X (Sum.inr i) - liftX k (sgOf k h i)) * C (u i)

theorem cf_inl (B : FB R d O) (h : PS k 2 d) (u φ : Fin d → k) (j : Fin d) :
    cf k B h u φ (Sum.inl j) =
      liftX k (∑ i : Fin d, C (u i) * ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i) (B.FK k j))) := rfl

theorem cf_inr (B : FB R d O) (h : PS k 2 d) (u φ : Fin d → k) (i : Fin d) :
    cf k B h u φ (Sum.inr i) = liftX k (Dof (B.FK k) u (sgOf k h i)) + C (φ i) := rfl

theorem nabla_eq (B : FB R d O) (h : PS k 2 d) (m : ℕ) (u φ : Fin d → k) (G : AA k d) :
    nabla k B h m u φ G = vf (cf k B h u φ) G - (C (m : k) * fm k h u) * G := by
  unfold nabla vf fm Dx
  rw [Fintype.sum_sum_type]
  simp only [cf_inl, cf_inr, add_mul, Finset.sum_add_distrib]
  ring

theorem vf_cf_liftX (B : FB R d O) (h : PS k 2 d) (u φ : Fin d → k) (g : PS k 1 d) :
    vf (cf k B h u φ) (liftX k g) = liftX k (Dof (B.FK k) u g) := by
  unfold vf
  rw [Fintype.sum_sum_type]
  simp only [cf_inl, pderiv_inl_liftX, pderiv_inr_liftX, mul_zero, Finset.sum_const_zero, add_zero]
  unfold Dof
  rw [liftX_sum]
  simp only [liftX_mul]

theorem connection_kills_series : ConnectionKillsSeries := by
  intro R _ d O _ _ k _ _ _ B h m φ f
  rw [nabla_eq, vf_cf_liftX]
  simp [fm, Dof, liftX_zero]

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing.Nab
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.ConstantCoeffEv
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.LogPf

variable {k : Type} [CommRing k] {d m n : ℕ}

def CZ (a : Fin m → Pt k n d) : Prop := ∀ j i, constantCoeff (a j i) = 0

theorem CZ.hasSubst {a : Fin m → Pt k n d} (ha : CZ a) : HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha p.1 p.2)

theorem ev_add {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f + g) = ev a f + ev a g := by
  have h : ∀ F : PS k m d, ev a F = MvPowerSeries.substAlgHom ha.hasSubst F := fun F => by
    rw [MvPowerSeries.coe_substAlgHom]
    rfl
  rw [h, h, h, map_add]

theorem ev_mul {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f * g) = ev a f * ev a g := by
  have h : ∀ F : PS k m d, ev a F = MvPowerSeries.substAlgHom ha.hasSubst F := fun F => by
    rw [MvPowerSeries.coe_substAlgHom]
    rfl
  rw [h, h, h, map_mul]

def evHom {a : Fin m → Pt k n d} (ha : CZ a) : PS k m d →+* PS k n d :=
  (substAlgHom ha.hasSubst).toRingHom

theorem evHom_apply {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) : evHom ha f = ev a f := by
  exact congrFun (MvPowerSeries.coe_substAlgHom ha.hasSubst) f

theorem ev_sub {a : Fin m → Pt k n d} (ha : CZ a) (f g : PS k m d) : ev a (f - g) = ev a f - ev a g := by
  rw [← evHom_apply ha, ← evHom_apply ha, ← evHom_apply ha, map_sub]

theorem ev_neg {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) : ev a (-f) = -ev a f := by
  rw [← evHom_apply ha, ← evHom_apply ha, map_neg]

theorem ev_sum {a : Fin m → Pt k n d} (ha : CZ a) {ι : Type} (s : Finset ι) (f : ι → PS k m d) :
    ev a (∑ x ∈ s, f x) = ∑ x ∈ s, ev a (f x) := by
  rw [← evHom_apply ha, map_sum]
  exact Finset.sum_congr rfl (fun x _ => evHom_apply ha (f x))

theorem ev_C {a : Fin m → Pt k n d} (ha : CZ a) (c : k) : ev a (C c : PS k m d) = C c := by
  have h : ∀ F : PS k m d, ev a F = MvPowerSeries.substAlgHom ha.hasSubst F := fun F => by
    rw [MvPowerSeries.coe_substAlgHom]
    rfl
  rw [h, show (C c : PS k m d) = algebraMap k (PS k m d) c from rfl, AlgHom.commutes]
  rfl

theorem ev_X {a : Fin m → Pt k n d} (ha : CZ a) (j : Fin m) (i : Fin d) : ev a (X (j, i) : PS k m d) = a j i :=
  MvPowerSeries.subst_X ha.hasSubst (j, i)

theorem ev_zero' {a : Fin m → Pt k n d} (ha : CZ a) : ev a (0 : PS k m d) = 0 := by
  rw [← evHom_apply ha, map_zero]

theorem constantCoeff_ev {a : Fin m → Pt k n d} (ha : CZ a) {f : PS k m d} (hf : constantCoeff f = 0) :
    constantCoeff (ev a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero ha.hasSubst (fun p => ha p.1 p.2) hf

theorem CZ.ev {a : Fin m → Pt k n d} (ha : CZ a) {l : ℕ} {b : Fin l → Pt k m d} (hb : CZ b) :
    CZ (fun j i => ev a (b j i)) := fun j i => constantCoeff_ev ha (hb j i)

theorem ev_ev {l : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) {b : Fin l → Pt k m d} (hb : CZ b) (f : PS k l d) :
    ev a (ev b f) = ev (fun j i => ev a (b j i)) f := by
  exact MvPowerSeries.subst_comp_subst_apply hb.hasSubst ha.hasSubst f

theorem ev_pt (f : PS k m d) : ev (fun j => pt k (n := m) d j) f = f := by
  show MvPowerSeries.subst (fun p : Fin m × Fin d => (X p : PS k m d)) f = f
  rw [show (fun p : Fin m × Fin d => (X p : PS k m d)) = X from rfl, MvPowerSeries.subst_self]
  rfl

theorem CZ.pt : CZ (fun j => pt k (n := n) d j) := fun j i => MvPowerSeries.constantCoeff_X _

theorem pderiv_ev {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) (v : Fin n × Fin d) :
    pderiv k v (ev a f) = ∑ p : Fin m × Fin d, ev a (pderiv k p f) * pderiv k v (a p.1 p.2) := by
  unfold ev
  exact pderiv_subst (a := fun p : Fin m × Fin d => a p.1 p.2) (fun p => ha p.1 p.2) f v

theorem ev_zeroFam (f : PS k m d) : ev (fun _ _ => (0 : PS k n d)) f = C (constantCoeff f) := by
  classical
  have hz : CZ (fun (_ : Fin m) (_ : Fin d) => (0 : PS k n d)) := fun _ _ => map_zero _
  ext e
  unfold ev
  rw [coeff_subst hz.hasSubst, finsum_eq_single _ 0]
  · simp [coeff_C, coeff_one]
  · intro x hx
    obtain ⟨p, hp⟩ : ∃ p, x p ≠ 0 := by
      by_contra hc; push Not at hc; exact hx (Finsupp.ext hc)
    rw [Finsupp.prod, Finset.prod_eq_zero (Finsupp.mem_support_iff.2 hp) (zero_pow hp), map_zero, smul_zero]

end ReciprocityTheory.ChartRestriction.G.TB.LogPf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.LemmaH
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

abbrev kapH (m : ℕ) {ι π : Type} [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k) (l l' : ι) : k :=
  if c l = c l' ∧ s l = true ∧ s l' = false then (m : k) * betaH k (0, φ l) (u l', 0) else 0

theorem kapW_eq_kapH (m : ℕ) {ι π : Type} [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k)
    (hFU : OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0))) :
    kapW m s (fun l => (u l, 0)) (fun l => (0, φ l)) = kapH m c s u φ := by
  funext l l'
  show (if s l = true ∧ s l' = false then (m : k) * betaH k (0, φ l) (u l', 0) else 0) =
    (if c l = c l' ∧ s l = true ∧ s l' = false then (m : k) * betaH k (0, φ l) (u l', 0) else 0)
  by_cases hs : s l = true ∧ s l' = false
  · rw [if_pos hs]
    by_cases hc : c l = c l'
    · rw [if_pos ⟨hc, hs⟩]
    · rw [if_neg (fun h => hc h.1), hFU l l' (fun h => hc h.1), mul_zero]
  · rw [if_neg hs, if_neg (fun h => hs h.2)]

theorem rename_qsmul {ι τ : Type} (e : ι → τ) (q : ℚ) (X : MvPolynomial ι k) :
    MvPolynomial.rename e (q • X) = q • MvPolynomial.rename e X := by
  exact map_rat_smul (MvPolynomial.rename e) q X

theorem ordNabla_expand (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι π : Type}
    [Fintype ι] [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k)
    (hUF : OppositePairVanishing k c s (fun l => (u l, 0)) (fun l => (0, φ l)))
    (hFU : OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0))) (Q : MvPolynomial ι k) (g : PS k 1 d) :
    ordNabla k B h m s (fun l => (u l, φ l)) Q (liftX k g) =
      ∑ n ∈ Finset.range (Q.totalDegree + 1),
        nablaPoly k B h m u (((n.factorial : ℚ)⁻¹) • (secondOrder k (kapH m c s u φ))^[n] Q) (liftX k g) := by
  classical
  have hb0 : ∀ l, ((fun l => ((0 : Fin d → k), φ l)) l).1 = 0 := fun l => rfl
  have haa : ∀ l l', s l = s l' → betaH k (u l, (0 : Fin d → k)) (u l', 0) = 0 := by
    intro l l' _
    simp [betaH]
  have hab : ∀ l l', s l = s l' → betaH k (u l, (0 : Fin d → k)) (0, φ l') = 0 :=
    fun l l' hs => hUF l l' (fun h => h.2 hs)
  have hw := ordNabla_wick hN2 hN3 B h m s (fun l => (u l, 0)) (fun l => (0, φ l)) hb0 haa hab Q g
  simp only [Prod.mk_add_mk, add_zero, zero_add] at hw
  have hdeg : (MvPolynomial.rename (sideE s) Q).totalDegree = Q.totalDegree :=
    MvPolynomial.totalDegree_renameEquiv (R := k) (sideE s) Q
  rw [hw, kapW_eq_kapH m c s u φ hFU, hdeg]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← rename_qsmul, ← ordNabla_eq B h m s (fun l => (u l, 0)) ?_, ordNabla_u hN2]
  intro l l' _
  exact nablaL_comm hN2 B h m _ _ (by simp [betaH])

theorem ordNabla_value_expand (hV : ValueSt) (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d)
    (hax : ev (n := 1) ![0, pt k d 0] h = 0) (m : ℕ) {ι π : Type} [Fintype ι] [DecidableEq π] (c : ι → π)
    (s : ι → Bool) (u φ : ι → Fin d → k) (hUF : OppositePairVanishing k c s (fun l => (u l, 0)) (fun l => (0, φ l)))
    (hFU : OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0))) (Q : MvPolynomial ι k) (g : PS k 1 d) :
    constantCoeff (ordNabla k B h m s (fun l => (u l, φ l)) Q (liftX k g)) =
      ∑ n ∈ Finset.range (Q.totalDegree + 1),
        constantCoeff (DpolyOf (B.FK k) u (((n.factorial : ℚ)⁻¹) • (secondOrder k (kapH m c s u φ))^[n] Q) g) := by
  rw [ordNabla_expand hN2 hN3 B h m c s u φ hUF hFU Q g, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  exact hV R d O k B h hax m ι u _ g

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
end
end

