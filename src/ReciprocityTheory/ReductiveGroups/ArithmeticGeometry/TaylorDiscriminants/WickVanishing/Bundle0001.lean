import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Bundle0001

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.CalcAdd
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

variable {k : Type} [CommRing k] [Algebra ℚ k]

theorem coeff_zero_of_scale {σ : Type} [Fintype σ] (w : σ → ℕ) (f : MvPowerSeries σ k)
    (h : subst ((fun s => (2 : k) ^ w s) • (X : σ → MvPowerSeries σ k)) f = (2 : k) • f) (n : σ →₀ ℕ)
    (hn : (∑ s, w s * n s) ≠ 1) : coeff n f = 0 := by
  have h2 := congrArg (coeff n) h
  rw [← MvPowerSeries.rescale_eq_subst, MvPowerSeries.coeff_rescale,
    Finsupp.prod_fintype _ _ (fun s => by simp), map_smul, smul_eq_mul] at h2
  simp only [← pow_mul, Finset.prod_pow_eq_pow_sum] at h2
  have hr : ((2 : ℚ) ^ (∑ s, w s * n s) - 2) ≠ 0 := by
    intro h0
    apply hn
    have h3 : (2 : ℕ) ^ (∑ s, w s * n s) = 2 := by exact_mod_cast sub_eq_zero.1 h0
    exact Nat.pow_right_injective (le_refl 2) (h3.trans (pow_one 2).symm)
  have hk : algebraMap ℚ k ((2 : ℚ) ^ (∑ s, w s * n s) - 2) * coeff n f = 0 := by
    rw [map_sub, map_pow, map_ofNat]
    linear_combination h2
  calc coeff n f
      = algebraMap ℚ k (((2 : ℚ) ^ (∑ s, w s * n s) - 2)⁻¹ * ((2 : ℚ) ^ (∑ s, w s * n s) - 2))
          * coeff n f := by rw [inv_mul_cancel₀ hr, map_one, one_mul]
    _ = 0 := by rw [map_mul, mul_assoc, hk, mul_zero]

theorem hasSubst_pts {n m d : ℕ} (a : Fin m → Pt k n d) (h : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) := MvPowerSeries.hasSubst_of_constantCoeff_zero fun p => h p.1 p.2

theorem ev_ev {n m l d : ℕ} (a : Fin m → Pt k n d) (b : Fin n → Pt k l d) (ha : ∀ j i, constantCoeff (a j i) = 0)
    (hb : ∀ j i, constantCoeff (b j i) = 0) (f : PS k m d) :
    ev b (ev a f) = ev (fun j i => ev b (a j i)) f := by
  unfold ev
  exact MvPowerSeries.subst_comp_subst_apply (hasSubst_pts a ha) (hasSubst_pts b hb) f

theorem ev_X {n m d : ℕ} (a : Fin m → Pt k n d) (ha : ∀ j i, constantCoeff (a j i) = 0) (j : Fin m) (i : Fin d) :
    ev a (X (j, i) : PS k m d) = a j i := by
  unfold ev
  exact MvPowerSeries.subst_X (hasSubst_pts a ha) (j, i)

theorem const_pt {n d : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt k d j i) = 0 := by
  simp [pt]

def AddLinSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (f : PS k 1 d),
    ev (n := 2) ![pt k d 0 + pt k d 1] f = ev (n := 2) ![pt k d 0] f + ev (n := 2) ![pt k d 1] f →
      ∀ n : Fin 1 × Fin d →₀ ℕ, n.degree ≠ 1 → coeff n f = 0

theorem ev_pt {n d : ℕ} (f : PS k n d) : ev (fun j => pt k d j) f = f := by
  have e : (fun p : Fin n × Fin d => pt k d p.1 p.2) = MvPowerSeries.X := by
    funext p
    rfl
  unfold ev
  rw [e, MvPowerSeries.subst_self]
  rfl

theorem sum_degree {σ : Type} [Fintype σ] (n : σ →₀ ℕ) : n.degree = ∑ s, 1 * n s := by
  rw [Finsupp.degree_eq_sum]
  simp

theorem ev_add' {n m d : ℕ} (b : Fin m → Pt k n d) (hb : ∀ j i, constantCoeff (b j i) = 0) (f g : PS k m d) :
    ev b (f + g) = ev b f + ev b g := by
  unfold ev
  exact MvPowerSeries.subst_add (hasSubst_pts b hb) f g

theorem addition_linear : AddLinSt := by
  intro k _ _ d f hf n hn
  let b : Fin 2 → Pt k 1 d := ![pt k d 0, pt k d 0]
  have hb0 : ∀ j i, constantCoeff (b j i) = 0 := fun j i => by
    fin_cases j <;> simp [b, pt]
  have hA : ev b (ev (n := 2) ![pt k d 0 + pt k d 1] f)
      = ev (fun (j : Fin 1) i => (2 : k) ^ 1 • (X (j, i) : PS k 1 d)) f := by
    rw [ev_ev _ _ (fun j i => by fin_cases j; simp [pt]) hb0]
    congr 1
    funext j i
    fin_cases j
    simp [b, pt, ev_add' b hb0, ev_X b hb0, two_smul]
  have hB : ∀ c : Fin 2, ev b (ev (n := 2) ![pt k d c] f) = f := by
    intro c
    calc ev b (ev (n := 2) ![pt k d c] f) = ev (fun j => pt k d j) f := by
          rw [ev_ev _ _ (fun j i => by fin_cases j; simp [pt]) hb0]
          congr 1
          funext j i
          fin_cases j
          fin_cases c <;> simp [b, pt, ev_X b hb0]
      _ = f := ev_pt f
  have h1 := congrArg (ev b) hf
  rw [ev_add' b hb0, hA, hB 0, hB 1] at h1
  refine coeff_zero_of_scale (fun _ => 1) f ?_ n ?_
  · rw [two_smul]
    exact h1
  · rw [← sum_degree]
    exact hn

theorem scale_two {d : ℕ} (f : PS k 2 d) (c0 c1 : ℕ)
    (h : ev (n := 2) (![fun i => (2 : k) ^ c0 • (X ((0 : Fin 2), i) : PS k 2 d),
      fun i => (2 : k) ^ c1 • (X ((1 : Fin 2), i) : PS k 2 d)] : Fin 2 → Pt k 2 d) f = (2 : k) • f)
    (n : Fin 2 × Fin d →₀ ℕ) (hn : c0 * (∑ i, n (0, i)) + c1 * (∑ i, n (1, i)) ≠ 1) : coeff n f = 0 := by
  let w : Fin 2 × Fin d → ℕ := fun p => if p.1 = 0 then c0 else c1
  have hfam : ((fun s => (2 : k) ^ w s) • (X : Fin 2 × Fin d → PS k 2 d)) = fun p =>
      (![fun i => (2 : k) ^ c0 • (X ((0 : Fin 2), i) : PS k 2 d),
        fun i => (2 : k) ^ c1 • (X ((1 : Fin 2), i) : PS k 2 d)] : Fin 2 → Pt k 2 d) p.1 p.2 := by
    funext p
    rcases p with ⟨j, i⟩
    fin_cases j <;> simp [w]
  refine coeff_zero_of_scale w f ?_ n ?_
  · rw [hfam]
    exact h
  · rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    simpa [w, Finset.mul_sum] using hn

def AddLinFstSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (f : PS k 2 d),
    ev (n := 3) ![pt k d 0 + pt k d 1, pt k d 2] f = ev (n := 3) ![pt k d 0, pt k d 2] f + ev (n := 3) ![pt k d 1, pt k d 2] f →
      ∀ n : Fin 2 × Fin d →₀ ℕ, (∑ i, n (0, i)) ≠ 1 → coeff n f = 0

def AddLinSndSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (f : PS k 2 d),
    ev (n := 3) ![pt k d 0, pt k d 1 + pt k d 2] f = ev (n := 3) ![pt k d 0, pt k d 1] f + ev (n := 3) ![pt k d 0, pt k d 2] f →
      ∀ n : Fin 2 × Fin d →₀ ℕ, (∑ i, n (1, i)) ≠ 1 → coeff n f = 0

def BiaddBilinSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (f : PS k 2 d),
    ev (n := 3) ![pt k d 0 + pt k d 1, pt k d 2] f = ev (n := 3) ![pt k d 0, pt k d 2] f + ev (n := 3) ![pt k d 1, pt k d 2] f →
    ev (n := 3) ![pt k d 0, pt k d 1 + pt k d 2] f = ev (n := 3) ![pt k d 0, pt k d 1] f + ev (n := 3) ![pt k d 0, pt k d 2] f →
      ∀ n : Fin 2 × Fin d →₀ ℕ, ¬ ((∑ i, n (0, i)) = 1 ∧ (∑ i, n (1, i)) = 1) → coeff n f = 0

theorem addition_linear_fst : AddLinFstSt := by
  intro k _ _ d f hf n hn
  let b : Fin 3 → Pt k 2 d := ![pt k d 0, pt k d 0, pt k d 1]
  have hb0 : ∀ j i, constantCoeff (b j i) = 0 := fun j i => by
    fin_cases j <;> simp [b, pt]
  have hA : ev b (ev (n := 3) ![pt k d 0 + pt k d 1, pt k d 2] f)
      = ev (![fun i => (2 : k) ^ 1 • (X ((0 : Fin 2), i) : PS k 2 d),
        fun i => (2 : k) ^ 0 • (X ((1 : Fin 2), i) : PS k 2 d)] : Fin 2 → Pt k 2 d) f := by
    rw [ev_ev _ _ (fun j i => by fin_cases j <;> simp [pt]) hb0]
    congr 1
    funext j i
    fin_cases j <;> simp [b, pt, ev_add' b hb0, ev_X b hb0, two_smul]
  have hB : ∀ c : Fin 3, c ≠ 2 → ev b (ev (n := 3) ![pt k d c, pt k d 2] f) = f := by
    intro c hc
    calc ev b (ev (n := 3) ![pt k d c, pt k d 2] f) = ev (fun j => pt k d j) f := by
          rw [ev_ev _ _ (fun j i => by fin_cases j <;> simp [pt]) hb0]
          congr 1
          funext j i
          fin_cases c <;> fin_cases j <;> simp_all [b, pt, ev_X b hb0]
      _ = f := ev_pt f
  have h1 := congrArg (ev b) hf
  rw [ev_add' b hb0, hA, hB 0 (by decide), hB 1 (by decide)] at h1
  refine scale_two f 1 0 ?_ n ?_
  · rw [two_smul]
    exact h1
  · simpa using hn

theorem addition_linear_snd : AddLinSndSt := by
  intro k _ _ d f hf n hn
  let b : Fin 3 → Pt k 2 d := ![pt k d 0, pt k d 1, pt k d 1]
  have hb0 : ∀ j i, constantCoeff (b j i) = 0 := fun j i => by
    fin_cases j <;> simp [b, pt]
  have hA : ev b (ev (n := 3) ![pt k d 0, pt k d 1 + pt k d 2] f)
      = ev (![fun i => (2 : k) ^ 0 • (X ((0 : Fin 2), i) : PS k 2 d),
        fun i => (2 : k) ^ 1 • (X ((1 : Fin 2), i) : PS k 2 d)] : Fin 2 → Pt k 2 d) f := by
    rw [ev_ev _ _ (fun j i => by fin_cases j <;> simp [pt]) hb0]
    congr 1
    funext j i
    fin_cases j <;> simp [b, pt, ev_add' b hb0, ev_X b hb0, two_smul]
  have hB : ∀ c : Fin 3, c ≠ 0 → ev b (ev (n := 3) ![pt k d 0, pt k d c] f) = f := by
    intro c hc
    calc ev b (ev (n := 3) ![pt k d 0, pt k d c] f) = ev (fun j => pt k d j) f := by
          rw [ev_ev _ _ (fun j i => by fin_cases j <;> simp [pt]) hb0]
          congr 1
          funext j i
          fin_cases c <;> fin_cases j <;> simp_all [b, pt, ev_X b hb0]
      _ = f := ev_pt f
  have h1 := congrArg (ev b) hf
  rw [ev_add' b hb0, hA, hB 1 (by decide), hB 2 (by decide)] at h1
  refine scale_two f 0 1 ?_ n ?_
  · rw [two_smul]
    exact h1
  · simpa using hn

theorem biadditive_bilinear : BiaddBilinSt := by
  intro k _ _ d f h1 h2 n hn
  by_cases h : (∑ i, n (0, i)) = 1
  · exact addition_linear_snd k d f h2 n fun h' => hn ⟨h, h'⟩
  · exact addition_linear_fst k d f h1 n h

end ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.JetGlue
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace ReciprocityTheory.ChartRestriction.G.TB.JGPf

universe u

theorem specMap_stalkCongr {X : Scheme.{u}} {x y : X} (e : x = y) :
    Spec.map (X.presheaf.stalkCongr (Inseparable.of_eq e)).hom ≫ X.fromSpecStalk x = X.fromSpecStalk y := by
  subst e
  simp

set_option maxHeartbeats 1000000 in

theorem ext_of_fromSpecStalk {Y X : Scheme.{u}} (f g : Y ⟶ X)
    (h : ∀ y, Y.fromSpecStalk y ≫ f = Y.fromSpecStalk y ≫ g) : f = g := by
  have hb : ∀ y, f y = g y := fun y => by
    have := congr($(h y) (IsLocalRing.closedPoint (Y.presheaf.stalk y)))
    change f (Y.fromSpecStalk y (IsLocalRing.closedPoint _)) = g (Y.fromSpecStalk y (IsLocalRing.closedPoint _)) at this
    rwa [Scheme.fromSpecStalk_closedPoint] at this
  have hbase : f.base = g.base := by ext y; exact hb y
  have hs : ∀ y, f.stalkMap y = (X.presheaf.stalkCongr (Inseparable.of_eq (hb y))).hom ≫ g.stalkMap y := by
    intro y
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (f y))]
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk, Spec.map_comp, Category.assoc, specMap_stalkCongr (hb y),
      Scheme.SpecMap_stalkMap_fromSpecStalk, h y]
  refine Scheme.Hom.ext' (LocallyRingedSpace.Hom.ext' ?_)
  have := SheafedSpace.hom_stalk_ext _ _ hbase hs
  exact congrArg InducedCategory.Hom.hom this

theorem comp_eq {A B C D : Scheme.{u}} (u : A ⟶ B) (v : B ⟶ C) (f g : C ⟶ D) (h : v ≫ f = v ≫ g) :
    (u ≫ v) ≫ f = (u ≫ v) ≫ g := by
  rw [Category.assoc, Category.assoc, h]

theorem jetGlue : JetGlueSt := by
  intro S _ κ _ m X f g h
  apply ext_of_fromSpecStalk
  intro y
  classical
  have hy := y.isPrime
  let 𝔭 : Ideal S := y.asIdeal.comap (algebraMap S (JetRing S κ m))
  have : 𝔭.IsPrime := Ideal.comap_isPrime _ _
  let ψ := (Scheme.ΓSpecIso (CommRingCat.of (JetRing S κ m))).inv ≫
    (Spec (CommRingCat.of (JetRing S κ m))).presheaf.germ ⊤ y trivial
  have hM : ∀ a : Algebra.algebraMapSubmonoid (JetRing S κ m) 𝔭.primeCompl, IsUnit (ψ.hom a) := by
    rintro ⟨a, ⟨s, hs, rfl⟩⟩
    refine (Scheme.mem_basicOpen _ ((Scheme.ΓSpecIso (CommRingCat.of (JetRing S κ m))).inv.hom
      (algebraMap S (JetRing S κ m) s)) y trivial).1 ?_
    rw [basicOpen_eq_of_affine]
    exact (PrimeSpectrum.mem_basicOpen _ _).2 hs
  let φ := IsLocalization.lift (S := JetLoc S κ m 𝔭) hM
  have hfac : ψ = CommRingCat.ofHom (algebraMap (JetRing S κ m) (JetLoc S κ m 𝔭)) ≫ CommRingCat.ofHom φ := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    simp [φ]
  have e : (Spec (CommRingCat.of (JetRing S κ m))).fromSpecStalk y =
      Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap (JetRing S κ m) (JetLoc S κ m 𝔭))) := by
    rw [Spec.fromSpecStalk_eq, ← Spec.map_comp, ← hfac]
  rw [e]
  exact comp_eq _ _ f g (h 𝔭)

end ReciprocityTheory.ChartRestriction.G.TB.JGPf
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.MonoVal
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.TB.MV

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

def addF (k : Type) [CommRing k] (d : ℕ) : Fin d → PS k 2 d :=
  fun j => MvPowerSeries.X ((0 : Fin 2), j) + MvPowerSeries.X ((1 : Fin 2), j)

def MonoValSt : Prop :=
  ∀ (k : Type) [CommRing k] (d : ℕ) (ι : Type) [Fintype ι] (j : ι → Fin d), Function.Injective j →
    ∀ (α : ι →₀ ℕ) (g : PS k 1 d),
      constantCoeff (DpolyOf (addF k d) (fun l => Pi.single (j l) 1) (MvPolynomial.monomial α 1) g) =
        (∏ l, ((α l).factorial : k)) * coeff (∑ l, α l • Finsupp.single ((0 : Fin 1), j l) 1) g

section Pair

variable {k : Type} [CommRing k] {σ : Type}

theorem coeff_iter_pderiv (i : σ) (c : ℕ) (g : MvPowerSeries σ k) (n : σ →₀ ℕ) :
    coeff n ((pderiv k i)^[c] g) =
      coeff (n + c • Finsupp.single i 1) g * ((n i + 1).ascFactorial c : k) := by
  induction c generalizing n g with
  | zero => simp
  | succ c ih =>
    rw [Function.iterate_succ_apply, ih, MvPowerSeries.coeff_pderiv]
    have h1 : n + c • Finsupp.single i 1 + Finsupp.single i 1 = n + (c + 1) • Finsupp.single i 1 := by
      rw [add_smul, one_smul, add_assoc]
    have h2 : ((n + c • Finsupp.single i 1 : σ →₀ ℕ)) i = n i + c := by simp
    rw [h1, h2, Nat.ascFactorial_succ]
    push_cast
    ring

theorem coeff_fold {ι : Type} (cd : ι → σ) (hc : Function.Injective cd) (m : ι → ℕ) (f : MvPowerSeries σ k) :
    ∀ (L : List ι), L.Nodup → ∀ n : σ →₀ ℕ,
      coeff n (L.foldr (fun l g => (pderiv k (cd l))^[m l] g) f) =
        coeff (n + (L.map fun l => m l • Finsupp.single (cd l) 1).sum) f *
          (L.map fun l => ((n (cd l) + 1).ascFactorial (m l) : k)).prod := by
  intro L
  induction L with
  | nil => intro _ n; simp
  | cons l L ih =>
    intro hnd n
    rw [List.nodup_cons] at hnd
    rw [List.foldr_cons, coeff_iter_pderiv, ih hnd.2]
    have hprod : (L.map fun l' => (((n + m l • Finsupp.single (cd l) 1 : σ →₀ ℕ) (cd l') + 1).ascFactorial (m l') : k)).prod
        = (L.map fun l' => ((n (cd l') + 1).ascFactorial (m l') : k)).prod := by
      congr 1
      apply List.map_congr_left
      intro l' hl'
      have hne : cd l ≠ cd l' := fun h => hnd.1 (by rw [hc h]; exact hl')
      simp [Finsupp.single_apply, hne]
    rw [hprod, List.map_cons, List.sum_cons, List.map_cons, List.prod_cons, add_assoc]
    ring

end Pair

section Pair2

variable {k : Type} [CommRing k]

theorem ev_zero {d m n : ℕ} (a : Fin m → Pt k n d) : ev a (0 : PS k m d) = 0 := by
  have h := MvPowerSeries.subst_C (a := fun p : Fin m × Fin d => a p.1 p.2) (0 : k)
  rw [map_zero, map_zero] at h
  exact h

theorem dof_single (d : ℕ) (i : Fin d) :
    (Dof (addF k d) (Pi.single i (1 : k)) : PS k 1 d → PS k 1 d) = pderiv k ((0 : Fin 1), i) := by
  classical
  funext f
  have ev1 : ev (n := 1) ![pt k d 0, 0] (1 : PS k 2 d) = 1 := by
    have h := MvPowerSeries.subst_C (a := fun p : Fin 2 × Fin d => (![pt k d 0, 0] : Fin 2 → Pt k 1 d) p.1 p.2) (1 : k)
    rw [map_one, map_one] at h
    exact h
  have ev0 : ev (n := 1) ![pt k d 0, 0] (0 : PS k 2 d) = 0 := ev_zero _
  have hinner : ∀ j : Fin d, (∑ i' : Fin d, MvPowerSeries.C ((Pi.single i (1 : k) : Fin d → k) i') *
      ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), i') (addF k d j))) =
      if j = i then 1 else 0 := by
    intro j
    rw [Finset.sum_eq_single j]
    · have hd : pderiv k ((1 : Fin 2), j) (addF k d j) = 1 := by
        simp [addF, MvPowerSeries.pderiv_X, Pi.single_apply]
      rw [hd, ev1, mul_one]
      by_cases hji : j = i
      · subst hji; simp
      · simp [Pi.single_apply, hji]
    · intro b _ hb
      have hd : pderiv k ((1 : Fin 2), b) (addF k d j) = 0 := by
        simp [addF, MvPowerSeries.pderiv_X, Pi.single_apply, Ne.symm hb]
      rw [hd, ev0, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ j) h
  have hD : Dof (addF k d) (Pi.single i (1 : k)) f =
      ∑ j, (if j = i then (1 : PS k 1 d) else 0) * pderiv k ((0 : Fin 1), j) f := by
    simp only [Dof, hinner]
  rw [hD]
  simp [ite_mul, Finset.sum_ite_eq']

end Pair2

theorem monoVal : MonoValSt := by
  intro k _ d ι _ j hj α g
  classical
  by_cases h01 : (1 : k) = 0
  · haveI : Subsingleton k := subsingleton_of_zero_eq_one h01.symm
    exact Subsingleton.elim _ _
  · simp only [DpolyOf, MvPolynomial.support_monomial, if_neg h01, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl, map_one, one_mul, DmonOf, dof_single]
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
    simp only [ite_true, map_one, one_mul]
    have hcd : Function.Injective (fun l : ι => ((0 : Fin 1), j l)) :=
      fun a b h => hj (Prod.mk.inj h).2
    have hf := coeff_fold (k := k) (fun l : ι => ((0 : Fin 1), j l)) hcd α g
      (Finset.univ : Finset ι).toList (Finset.nodup_toList _) 0
    try simp only at hf
    rw [hf]
    simp only [zero_add, Finsupp.coe_zero, Pi.zero_apply, Nat.one_ascFactorial, Finset.sum_map_toList,
      Finset.prod_map_toList]
    rw [mul_comm]
    try push_cast
    try rfl

end ReciprocityTheory.ChartRestriction.G.TB.MV
end
end

