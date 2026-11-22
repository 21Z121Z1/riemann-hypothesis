import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.MemRamLine
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0027
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.DecGen
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.Bundle0002

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.ExtRep
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private def actM {A V J : Type} [CommRing A] [AddCommGroup V] [Module A V] (r t : A) (Y : J → V) :
    A × (J → V) →+ A × (J → V) where
  toFun u := (r * u.1, fun j => t • u.2 j + (r * u.1) • Y j)
  map_zero' := by ext <;> simp
  map_add' u v := by
    ext
    · simp [mul_add]
    · simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, smul_add, add_smul]
      abel

private def mkRep {Γ M : Type} [Group Γ] [AddCommGroup M] (n : ℕ) [Module (ZMod n) M] (T : Γ → M →+ M) (h1 : ∀ u, T 1 u = u)
    (hm : ∀ g h u, T (g * h) u = T g (T h u)) : Representation (ZMod n) Γ M where
  toFun g := ((T g).toZModLinearMap n : Module.End (ZMod n) M)
  map_one' := LinearMap.ext h1
  map_mul' g h := LinearMap.ext (hm g h)

private theorem continuous_of_right_invariant_on_nhds_one {Γ X : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [TopologicalSpace X] (U : Set Γ) (hU : U ∈ nhds (1 : Γ)) (f : Γ → X)
    (hf : ∀ g, ∀ h ∈ U, f (g * h) = f g) : Continuous f := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have ht : Filter.Tendsto (fun x => g⁻¹ * x) (nhds g) (nhds 1) := by
    have := (continuous_mul_left g⁻¹).tendsto g
    simpa using this
  have hev : ∀ᶠ x in nhds g, f x = f g := by
    filter_upwards [ht hU] with x hx
    have := hf g _ hx
    simpa using this
  exact tendsto_const_nhds.congr' (hev.mono fun x hx => hx.symm)

theorem UpperTheory.V.Ws.Gys.extRep :
    ∀ {O Γ k : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [Field k] (Φ : Fr O Γ) (a : O →+* k) (l : ℕ) [Fact l.Prime] [CharP k l], (Set.range a).Finite → (∀ i, IsLocallyConstant fun g => a (Φ.χ i g)) → ∀ (w w' : ℤ × ℤ) (J : Type) [Finite J] (y : J → Γ → k), (∀ j, Φ.Coc a w' (y j)) →
      ∃ (M : Type) (_ : AddCommGroup M) (_ : Module (ZMod (l ^ 1)) M) (_ : Finite M) (_ : TopologicalSpace M) (_ : DiscreteTopology M) (ρ : Representation (ZMod (l ^ 1)) Γ M)
        (p : M →+ k) (q : J → M →+ k) (m0 : M), ContAction ρ ∧ (∀ g, (∀ i, a (Φ.χ i g) = 1) → (∀ j, y j g = 0) → ρ g = 1) ∧
        (∀ g u, p (ρ g u) = a (Φ.rt w g) * p u) ∧ (∀ j g u, q j (ρ g u) = a (Φ.rt (w + w') g) * q j u + y j g * a (Φ.rt w g) * p u) ∧
        m0 ≠ 0 ∧ ∀ u ∈ Submodule.span (ZMod (l ^ 1)) {m0}, u ≠ 0 → p u ≠ 0 := by
  intro O Γ k _ _ _ _ _ _ Φ a l _ _ ha hχ w w' J _ y hy
  classical
  have hlp : (l ^ 1 : ℕ) = l := pow_one l
  have hA : ∀ (v : ℤ × ℤ) g, a ↑(Φ.rt v g) =
      (a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 1 g))⁻¹) ^ v.1 * (a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 2 g))⁻¹) ^ v.2 := by
    intro v g
    have e : ∀ u : Oˣ, a ↑u = ((Units.map a.toMonoidHom u : kˣ) : k) := fun u => rfl
    rw [e, e, e, e]
    simp only [Fr.rt, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_zpow, map_inv, Units.val_mul,
      Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val]
  have hsplit : ∀ g, a ↑(Φ.rt (w + w') g) = a ↑(Φ.rt w g) * a ↑(Φ.rt w' g) := by
    intro g
    rw [hA, hA, hA]
    simp only [Prod.fst_add, Prod.snd_add]
    have h0 : a ↑(Φ.χ 0 g) ≠ 0 := ((Φ.χ 0 g).isUnit.map a).ne_zero
    have h1 : a ↑(Φ.χ 1 g) ≠ 0 := ((Φ.χ 1 g).isUnit.map a).ne_zero
    have h2 : a ↑(Φ.χ 2 g) ≠ 0 := ((Φ.χ 2 g).isUnit.map a).ne_zero
    have n1 : a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 1 g))⁻¹ ≠ 0 := mul_ne_zero h0 (inv_ne_zero h1)
    have n2 : a ↑(Φ.χ 0 g) * (a ↑(Φ.χ 2 g))⁻¹ ≠ 0 := mul_ne_zero h0 (inv_ne_zero h2)
    rw [zpow_add₀ n1, zpow_add₀ n2]
    ring
  have hy1 : ∀ j, y j 1 = 0 := by
    intro j
    have := (hy j).coc 1 1
    simp only [mul_one, map_one, Units.val_one] at this
    linear_combination -this
  have hY : (⋃ j, Set.range (y j)).Finite := Set.finite_iUnion fun j => (hy j).lc.range_finite
  let A : Subring k := a.range
  haveI : Finite A := Set.Finite.to_subtype (s := (a.range : Set k)) (by rw [RingHom.coe_range]; exact ha)
  let V : Submodule A k := Submodule.span A (⋃ j, Set.range (y j))
  haveI : Module.Finite A V := Module.Finite.span_of_finite A hY
  haveI : Finite V := Module.finite_of_finite A
  haveI : NeZero (l ^ 1) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have hchar : ∀ x : k, (l ^ 1) • x = 0 := by
    intro x
    rw [nsmul_eq_mul, hlp, CharP.cast_eq_zero, zero_mul]
  letI iM : Module (ZMod (l ^ 1)) (A × (J → V)) := AddCommGroup.zmodModule (fun x => by
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      change (((l ^ 1) • x.1 : A) : k) = 0
      rw [AddSubmonoidClass.coe_nsmul]
      exact hchar _
    · funext j
      apply Subtype.ext
      change (((l ^ 1) • x.2 j : V) : k) = 0
      rw [AddSubmonoidClass.coe_nsmul]
      exact hchar _)
  letI : TopologicalSpace (A × (J → V)) := ⊥
  haveI : DiscreteTopology (A × (J → V)) := ⟨rfl⟩
  let rr : Γ → A := fun g => ⟨a ↑(Φ.rt w g), a.mem_range_self _⟩
  let tt : Γ → A := fun g => ⟨a ↑(Φ.rt (w + w') g), a.mem_range_self _⟩
  let YY : Γ → J → V := fun g j => ⟨y j g, Submodule.subset_span (Set.mem_iUnion.2 ⟨j, g, rfl⟩)⟩
  let T : Γ → (A × (J → V)) →+ (A × (J → V)) := fun g => actM (rr g) (tt g) (YY g)
  have cs : ∀ (c : A) (v : V), ((c • v : V) : k) = (c : k) * (v : k) := fun c v => rfl
  have h1 : ∀ u, T 1 u = u := by
    intro u
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      show a ↑(Φ.rt w 1) * (u.1 : k) = u.1
      simp
    · funext j
      apply Subtype.ext
      show ((tt 1 • u.2 j + (rr 1 * u.1) • YY 1 j : V) : k) = u.2 j
      rw [Submodule.coe_add, cs, cs]
      show a ↑(Φ.rt (w + w') 1) * (u.2 j : k) + (a ↑(Φ.rt w 1) * (u.1 : k)) * y j 1 = u.2 j
      simp [hy1]
  have hm : ∀ g h u, T (g * h) u = T g (T h u) := by
    intro g h u
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      show a ↑(Φ.rt w (g * h)) * (u.1 : k) = a ↑(Φ.rt w g) * (a ↑(Φ.rt w h) * (u.1 : k))
      rw [map_mul, Units.val_mul, map_mul, mul_assoc]
    · funext j
      apply Subtype.ext
      show ((tt (g * h) • u.2 j + (rr (g * h) * u.1) • YY (g * h) j : V) : k) =
        ((tt g • (tt h • u.2 j + (rr h * u.1) • YY h j) + (rr g * (rr h * u.1)) • YY g j : V) : k)
      rw [Submodule.coe_add, cs, cs, Submodule.coe_add, cs, cs, Submodule.coe_add, cs, cs]
      show a ↑(Φ.rt (w + w') (g * h)) * (u.2 j : k) + (a ↑(Φ.rt w (g * h)) * (u.1 : k)) * y j (g * h) =
        a ↑(Φ.rt (w + w') g) * (a ↑(Φ.rt (w + w') h) * (u.2 j : k) + (a ↑(Φ.rt w h) * (u.1 : k)) * y j h) +
          (a ↑(Φ.rt w g) * (a ↑(Φ.rt w h) * (u.1 : k))) * y j g
      rw [(hy j).coc g h, map_mul (Φ.rt (w + w')), map_mul (Φ.rt w), Units.val_mul, Units.val_mul,
        map_mul a, map_mul a, hsplit g, hsplit h]
      ring
  let ρ : Representation (ZMod (l ^ 1)) Γ (A × (J → V)) := mkRep (l ^ 1) T h1 hm
  have hker : ∀ g, (∀ i, a (Φ.χ i g) = 1) → (∀ j, y j g = 0) → ∀ u, T g u = u := by
    intro g hg hyg
    have hr : ∀ v : ℤ × ℤ, a ↑(Φ.rt v g) = 1 := by
      intro v
      rw [hA, hg 0, hg 1, hg 2]
      simp
    intro u
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      show a ↑(Φ.rt w g) * (u.1 : k) = u.1
      rw [hr, one_mul]
    · funext j
      apply Subtype.ext
      show ((tt g • u.2 j + (rr g * u.1) • YY g j : V) : k) = u.2 j
      rw [Submodule.coe_add, cs, cs]
      show a ↑(Φ.rt (w + w') g) * (u.2 j : k) + (a ↑(Φ.rt w g) * (u.1 : k)) * y j g = u.2 j
      rw [hr, hr, hyg]
      ring
  let p : (A × (J → V)) →+ k :=
    { toFun := fun u => (u.1 : k), map_zero' := rfl, map_add' := fun _ _ => rfl }
  let q : J → (A × (J → V)) →+ k := fun j =>
    { toFun := fun u => (u.2 j : k), map_zero' := rfl, map_add' := fun _ _ => rfl }
  let m0 : A × (J → V) := (1, 0)
  refine ⟨A × (J → V), inferInstance, iM, inferInstance, ⊥, ⟨rfl⟩, ρ, p, q, m0, ?_, fun g hg hyg => LinearMap.ext (hker g hg hyg), ?_, ?_, ?_, ?_⟩
  · unfold ReciprocityTheory.Gal.ContAction
    rw [continuous_prod_of_discrete_right]
    intro m
    let U : Set Γ := (⋂ i, (fun g => a (Φ.χ i g)) ⁻¹' {1}) ∩ ⋂ j, y j ⁻¹' {0}
    have hU : U ∈ nhds (1 : Γ) := by
      apply IsOpen.mem_nhds
      · exact (isOpen_iInter_of_finite fun i => (hχ i).isOpen_fiber 1).inter
          (isOpen_iInter_of_finite fun j => (hy j).lc.isOpen_fiber 0)
      · refine ⟨Set.mem_iInter.2 fun i => ?_, Set.mem_iInter.2 fun j => ?_⟩
        · simp
        · exact hy1 j
    apply continuous_of_right_invariant_on_nhds_one U hU
    intro g h hh
    have hh1 : ∀ i, a (Φ.χ i h) = 1 := fun i => Set.mem_iInter.1 hh.1 i
    have hh2 : ∀ j, y j h = 0 := fun j => Set.mem_iInter.1 hh.2 j
    show T (g * h) m = T g m
    rw [hm, hker h hh1 hh2 m]
  · intro g u
    rfl
  · intro j g u
    show ((tt g • u.2 j + (rr g * u.1) • YY g j : V) : k) = _
    rw [Submodule.coe_add, cs, cs]
    show a ↑(Φ.rt (w + w') g) * (u.2 j : k) + (a ↑(Φ.rt w g) * (u.1 : k)) * y j g =
      a ↑(Φ.rt (w + w') g) * (u.2 j : k) + y j g * a ↑(Φ.rt w g) * (u.1 : k)
    ring
  · intro h
    have := congrArg (fun u : A × (J → V) => (u.1 : k)) h
    simp [m0] at this
  · intro u hu hne
    rw [Submodule.mem_span_singleton] at hu
    obtain ⟨c, rfl⟩ := hu
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul] at hne ⊢
    intro hp
    apply hne
    rw [map_nsmul] at hp
    refine Prod.ext ?_ ?_
    · apply Subtype.ext
      change ((c.val • (1 : A) : A) : k) = 0
      rw [AddSubmonoidClass.coe_nsmul]
      exact hp
    · funext j
      apply Subtype.ext
      change ((c.val • (0 : V) : V) : k) = 0
      rw [smul_zero]
      rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.SplitPrimes
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.Gys.splitPrimes :
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (H : Subgroup (G ℚ Ω)), IsOpen (H : Set (G ℚ Ω)) →
      Set.Infinite {w : ℕ | w.Prime ∧ ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → Dec (F := ℚ) A ≤ H} := by
  intro Ω _ _ _ H hH
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hH H.one_mem
  set U : Subgroup (G ℚ Ω) := N.toOpenSubgroup.toSubgroup with hUdef
  haveI : U.Normal := N.isNormal'
  have hUo : IsOpen (U : Set (G ℚ Ω)) := N.isOpen'
  have hUH : U ≤ H := fun x hx => hN hx
  intro hfin
  set M : ℕ := ∏ q ∈ hfin.toFinset, q with hM
  have hM0 : M ≠ 0 := by
    rw [hM, Finset.prod_ne_zero_iff]
    intro q hq
    exact ((hfin.mem_toFinset.mp hq).1).ne_zero
  obtain ⟨w, A, p, σ, -, hp, hpM, -, hpw, hnorm, -, hpl, hIne, hfr, hσ⟩ :=
    UpperTheory.V.Loc.v00 (F := ℚ) U hUo 1 ∅ M hM0
  have hσU : σ ∈ U := by simpa using hσ
  have hDecU : Dec (F := ℚ) A ≤ U :=
    UpperTheory.V.Kum.decGen ℚ Ω A w σ U hpl (by rw [hnorm]; exact hfr) hUo hIne hσU
  have hAp : A.valuation (p : Ω) < 1 := by
    have := (hpl (p : 𝓞 ℚ)).mpr hpw
    simpa using this
  have hmem : p ∈ {w : ℕ | w.Prime ∧ ∀ A : ValuationSubring Ω, A.valuation (w : Ω) < 1 → Dec (F := ℚ) A ≤ H} := by
    refine ⟨hp, fun A' hA' y hy => ?_⟩
    obtain ⟨u, hu, -⟩ := ((UpperTheory.V.Chr.placesQ Ω).2.2) p A' A hp hA' hAp
    have h1 : u⁻¹ * y * u ∈ U := hDecU (hu y hy)
    have h2 : y ∈ U := by
      have := (inferInstance : U.Normal).conj_mem _ h1 u
      simpa [mul_assoc] using this
    exact hUH h2
  exact hpM (hM ▸ Finset.dvd_prod_of_mem _ (hfin.mem_toFinset.mpr hmem))
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.SuppMMono
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.Gys

section

variable {R : Type} [CommRing R]

private theorem gsp_uD (d : Fin 4 → R) (ν : R) (h : ∀ i, d i * d i.rev = ν) (x y t : R) :
    IsGSp ν (uQ x y t * Matrix.diagonal d) := by
  have h0 : d 0 * d 3 = ν := h 0
  have h1 : d 1 * d 2 = ν := h 1
  have hM : uQ x y t * Matrix.diagonal d =
      !![d 0, 0, 0, 0; x * d 0, d 1, 0, 0; y * d 0, 0, d 2, 0; t * d 0, y * d 1, -x * d 2, d 3] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [uQ, Matrix.mul_diagonal]
  unfold IsGSp
  rw [hM]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [adj, sgn, Matrix.mul_apply, Fin.sum_univ_four, Fin.rev] <;>
    first | exact h0 | exact h1 | ring1 | linear_combination h0 | linear_combination h1

private theorem suppM_mul {S : Finset (ℤ × ℤ)} {X : M4 R} (h : SuppM S X) (d : Fin 4 → R) :
    SuppM S (X * Matrix.diagonal d) := by
  intro i j hij hw
  simp [Matrix.mul_diagonal, h i j hij hw]

private theorem suppM_mono {S S' : Finset (ℤ × ℤ)} (hS : S ⊆ S') {X : M4 R} (h : SuppM S X) : SuppM S' X :=
  fun i j h1 h2 => h i j h1 fun h3 => h2 (hS h3)

end

section

variable {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R)

private theorem chi1 (g : Γ) : a (Φ.χ 1 g) = a (Φ.rt (-wAl) g) * a (Φ.χ 0 g) := by
  simp only [Fr.rt, wAl, MonoidHom.coe_mk, OneHom.coe_mk, zpow_neg, zpow_one, zpow_zero, mul_one, mul_inv_rev, inv_inv]
  rw [← map_mul]
  congr 1
  simp [Units.ext_iff]

private theorem chi2 (g : Γ) : a (Φ.χ 2 g) = a (Φ.rt (-wPs) g) * a (Φ.χ 0 g) := by
  simp only [Fr.rt, wPs, MonoidHom.coe_mk, OneHom.coe_mk, zpow_neg, zpow_one, zpow_zero, one_mul, mul_inv_rev, inv_inv]
  rw [← map_mul]
  congr 1
  simp [Units.ext_iff]

private theorem chi3 (h : ∀ i g, Φ.χ i g * Φ.χ i.rev g = Φ.ν g) (g : Γ) :
    a (Φ.χ 3 g) = a (Φ.rt (-wAl) g) * a (Φ.rt (-wPs) g) * a (Φ.χ 0 g) := by
  have h0 : Φ.χ 0 g * Φ.χ 3 g = Φ.ν g := h 0 g
  have h1 : Φ.χ 1 g * Φ.χ 2 g = Φ.ν g := h 1 g
  have key : Φ.χ 3 g = Φ.rt (-wAl) g * Φ.rt (-wPs) g * Φ.χ 0 g := by
    simp only [Fr.rt, wAl, wPs, MonoidHom.coe_mk, OneHom.coe_mk, Prod.fst_neg, Prod.snd_neg, neg_zero,
      zpow_neg, zpow_one, zpow_zero, mul_one, one_mul]
    rw [eq_inv_mul_of_mul_eq h0, ← h1]
    simp only [mul_inv_rev, inv_inv]
    simp only [mul_assoc]
    rw [inv_mul_cancel, mul_one, mul_left_comm]
  rw [key]
  simp

end

end UpperTheory.V.Ws.Gys

private theorem exists_hom_M4_eq_uQ_mul_diagonal_of_cup {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R]
    (Φ : Fr O Γ) (a : O →+* R) (hΦ : Φ.Ok a) (x y z : Γ → R) (m : Φ.ι → R)
    (hx : Φ.Coc a (-wAl) x) (hy : Φ.Coc a (-wPs) y) (hz : Φ.Cup a (-wAl) (-wPs) x y z m) :
    ∃ r : Γ →* M4 R, ∀ g, r g =
      uQ (x g) (y g) (2 * z g - x g * y g) * Matrix.diagonal (fun i => a ↑(Φ.χ i g)) := by
  have x1 : x 1 = 0 := by
    have h := hx.coc 1 1
    simp only [mul_one, map_one, Units.val_one, one_mul] at h
    linear_combination -h
  have y1 : y 1 = 0 := by
    have h := hy.coc 1 1
    simp only [mul_one, map_one, Units.val_one, one_mul] at h
    linear_combination -h
  have z1 : z 1 = 0 := by
    have h := hz.coc 1 1
    simp only [mul_one, map_one, Units.val_one, one_mul] at h
    linear_combination -h - y 1 * x1
  refine ⟨{ toFun := fun g => uQ (x g) (y g) (2 * z g - x g * y g) * Matrix.diagonal (fun i => a ↑(Φ.χ i g)),
            map_one' := ?_, map_mul' := ?_ }, fun g => rfl⟩
  · simp [x1, y1, z1, uQ_zero]
  · intro g h
    rw [mul_assoc, ← mul_assoc (Matrix.diagonal _),
      diag_mul_uQ (fun i => a ↑(Φ.χ i g)) _ _ (UpperTheory.V.Ws.Gys.chi1 Φ a g) (UpperTheory.V.Ws.Gys.chi2 Φ a g)
        (UpperTheory.V.Ws.Gys.chi3 Φ a hΦ.mul g),
      mul_assoc (uQ _ _ _) (Matrix.diagonal _), Matrix.diagonal_mul_diagonal, ← mul_assoc, uQ_mul]
    rw [hx.coc, hy.coc, hz.coc, Fr.rt_add, Units.val_mul, map_mul]
    congr 1
    · congr 1 <;> ring
    · congr 1
      funext i
      simp [map_mul]

private theorem adj_uQ_eq_uQ_neg {R : Type} [CommRing R] (p q u : R) : adj (uQ p q u) = uQ (-p) (-q) (-u) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj, uQ, sgn, Fin.rev]

private theorem adj_uQ_conj_uQ_mul_diagonal_eq_diagonal {O Γ R : Type} [CommRing O] [Group Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R)
    (hmul : ∀ i g, Φ.χ i g * Φ.χ i.rev g = Φ.ν g) (s : Γ) (x y z p q u : R)
    (hx : x = p - a ↑(Φ.rt (-wAl) s) * p) (hy : y = q - a ↑(Φ.rt (-wPs) s) * q)
    (hz : z = u - a ↑(Φ.rt (-wAl + -wPs) s) * u - y * a ↑(Φ.rt (-wAl) s) * p) :
    adj (uQ p q (2 * u - p * q)) * (uQ x y (2 * z - x * y) * Matrix.diagonal (fun i => a ↑(Φ.χ i s))) *
      uQ p q (2 * u - p * q) = Matrix.diagonal (fun i => a ↑(Φ.χ i s)) := by
  rw [adj_uQ_eq_uQ_neg, mul_assoc, mul_assoc,
    diag_mul_uQ (fun i => a ↑(Φ.χ i s)) _ _ (UpperTheory.V.Ws.Gys.chi1 Φ a s) (UpperTheory.V.Ws.Gys.chi2 Φ a s)
      (UpperTheory.V.Ws.Gys.chi3 Φ a hmul s),
    ← mul_assoc, ← mul_assoc, uQ_mul, uQ_mul]
  rw [Fr.rt_add, Units.val_mul, map_mul] at hz
  subst hz
  subst hx
  subst hy
  have e : ∀ A B C : R, A = 0 → B = 0 → C = 0 →
      uQ A B C * Matrix.diagonal (fun i => a ↑(Φ.χ i s)) = Matrix.diagonal (fun i => a ↑(Φ.χ i s)) := by
    intro A B C hA hB hC
    rw [hA, hB, hC, uQ_zero, one_mul]
  apply e <;> ring

theorem UpperTheory.V.Ws.Gys.ob :
    ∀ {O Γ R : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [CommRing R] (Φ : Fr O Γ) (a : O →+* R), Φ.Ok a → (∀ v, ∀ s ∈ Φ.Mu v, s ∈ Φ.Gv v ∧ ∀ i, a (Φ.χ i s) = 1) → ∀ (x y z : Γ → R) (m n : Φ.ι → R),
      Φ.Coc a (-wAl) x → x Φ.g0 = 0 → Φ.LocTriv a (-wAl) x m → Φ.Coc a (-wPs) y → y Φ.g0 = 0 → Φ.LocTriv a (-wPs) y n →
      Φ.Cup a (-wAl) (-wPs) x y z m → z Φ.g0 = 0 →
        ∃ s : PD Φ.ι Γ R, Φ.IsRes a s ∧ s.In qQ ∧ (∀ g, s.r g 1 0 = x g * a (Φ.χ 0 g)) ∧ (∀ v, s.n v 1 0 = m v) ∧
          (∀ g, s.r g 2 0 = y g * a (Φ.χ 0 g)) ∧ ∀ v, s.n v 2 0 = n v := by
  intro O Γ R _ _ _ _ Φ a hΦ hMu x y z m n hx hx0 hxl hy hy0 hyl hz hz0
  choose o ho using hz.loc
  obtain ⟨r, hr⟩ := exists_hom_M4_eq_uQ_mul_diagonal_of_cup Φ a hΦ x y z m hx hy hz
  have hconj : ∀ v, ∀ s ∈ Φ.Gv v, adj (uQ (m v) (n v) (2 * o v - m v * n v)) * r s *
      uQ (m v) (n v) (2 * o v - m v * n v) = Matrix.diagonal (fun i => a ↑(Φ.χ i s)) := by
    intro v s hs
    rw [hr]
    exact adj_uQ_conj_uQ_mul_diagonal_eq_diagonal Φ a hΦ.mul s _ _ _ _ _ _ (hxl v s hs) (hyl v s hs) (ho v s hs)
  have hlc : ∀ i j, IsLocallyConstant fun g => r g i j := by
    intro i j
    simp only [hr, Matrix.mul_diagonal]
    apply IsLocallyConstant.mul
    · fin_cases i <;> fin_cases j <;> simp [uQ] <;>
        first
        | exact IsLocallyConstant.const _
        | exact hx.lc
        | exact hy.lc
        | exact hx.lc.neg
        | exact ((IsLocallyConstant.const 2).mul hz.lc).sub (hx.lc.mul hy.lc)
    · exact hΦ.lc j
  refine ⟨⟨r, fun v => uQ (m v) (n v) (2 * o v - m v * n v)⟩,
    ⟨⟨?mult, ?kill, ?nrm, ?low, ?flag, ?mu⟩, ⟨?diag, ?char, ?shape⟩, ?cont⟩, ?inn, ?e1, ?e2, ?e3, ?e4⟩
  case mult =>
    intro g
    dsimp only
    rw [hr]
    apply UpperTheory.V.Ws.Gys.gsp_uD
    intro i
    show a ↑(Φ.χ i g) * a ↑(Φ.χ i.rev g) = a ↑(Φ.ν g)
    rw [← map_mul, ← Units.val_mul, hΦ.mul]
  case kill =>
    intro g hg
    dsimp only
    rw [hr, hx.kill g hg, hy.kill g hg, hz.kill g hg]
    simp [hΦ.kill g hg, uQ_zero]
  case nrm =>
    dsimp only
    rw [hr, hx0, hy0, hz0]
    simpa [uQ_zero] using Matrix.isDiag_diagonal (fun i => a ↑(Φ.χ i Φ.g0))
  case low =>
    intro v
    exact isLow_uQ _ _ _
  case flag =>
    intro v s hs
    dsimp only
    rw [hconj v s hs]
    intro i j hij
    exact Matrix.diagonal_apply_ne _ hij.ne'
  case mu =>
    intro v s hs i
    obtain ⟨hg, h1⟩ := hMu v s hs
    show (adj (uQ (m v) (n v) (2 * o v - m v * n v)) * r s * uQ (m v) (n v) (2 * o v - m v * n v)) i i = 1
    rw [hconj v s hg]
    simp [h1 i]
  case diag =>
    intro g i
    dsimp only
    rw [hr]
    fin_cases i <;> simp [uQ, Matrix.mul_diagonal]
  case char =>
    intro v s hs i
    show (adj (uQ (m v) (n v) (2 * o v - m v * n v)) * r s * uQ (m v) (n v) (2 * o v - m v * n v)) i i = _
    rw [hconj v s hs]
    simp
  case shape =>
    left
    constructor
    · intro g
      show SuppM nP (r g)
      rw [hr]
      exact UpperTheory.V.Ws.Gys.suppM_mono (by decide)
        (UpperTheory.V.Ws.Gys.suppM_mul (suppM_uQ _ _ _) _)
    · intro v
      exact suppM_uQ _ _ _
  case cont =>
    intro i j N
    exact (hlc i j).comp _
  case inn =>
    constructor
    · intro g
      show SuppM qQ (r g)
      rw [hr]
      exact UpperTheory.V.Ws.Gys.suppM_mul (suppM_uQ _ _ _) _
    · intro v
      exact suppM_uQ _ _ _
  case e1 =>
    intro g
    show r g 1 0 = _
    rw [hr]
    simp [uQ, Matrix.mul_diagonal]
  case e2 =>
    intro v
    simp [uQ]
  case e3 =>
    intro g
    show r g 2 0 = _
    rw [hr]
    simp [uQ, Matrix.mul_diagonal]
  case e4 =>
    intro v
    simp [uQ]
end

