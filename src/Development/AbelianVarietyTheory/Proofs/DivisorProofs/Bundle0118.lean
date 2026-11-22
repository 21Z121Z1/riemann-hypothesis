import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedNormFixedDecomposition
section
open scoped Classical

namespace GlobalTheory.TwistStab

variable {H : Type} [Group H]

theorem commensurable_comap {f : H →* H} (hf : Function.Surjective f) {A B : Subgroup H}
    (h : A.Commensurable B) : (A.comap f).Commensurable (B.comap f) :=
  ⟨by rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hf]; exact h.1,
   by rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hf]; exact h.2⟩

theorem finite_cover {A B : Subgroup H} (h : A.relIndex B ≠ 0) :
    ∃ R : Finset H, (∀ f ∈ R, f ∈ B) ∧ ∀ b ∈ B, ∃ f ∈ R, ∃ a ∈ A, b = f * a := by
  haveI : (A.subgroupOf B).FiniteIndex := ⟨h⟩
  haveI : Finite (B ⧸ A.subgroupOf B) := Subgroup.finite_quotient_of_finiteIndex
  refine ⟨(Set.finite_range (fun q : B ⧸ A.subgroupOf B => ((Quotient.out q : B) : H))).toFinset,
    ?_, ?_⟩
  · intro f hf
    simp only [Set.Finite.mem_toFinset, Set.mem_range] at hf
    obtain ⟨q, rfl⟩ := hf
    exact (Quotient.out q).2
  · intro b hb
    obtain ⟨a, ha⟩ := QuotientGroup.mk_out_eq_mul (A.subgroupOf B) (⟨b, hb⟩ : B)
    refine ⟨((Quotient.out (QuotientGroup.mk (⟨b, hb⟩ : B) : B ⧸ A.subgroupOf B) : B) : H), ?_,
      ((a : B) : H)⁻¹, ?_, ?_⟩
    · simp only [Set.Finite.mem_toFinset, Set.mem_range]
      exact ⟨_, rfl⟩
    · exact A.inv_mem (Subgroup.mem_subgroupOf.mp a.2)
    · rw [ha]
      simp

def iterComap (T : H →* H) (K : Subgroup H) (n : ℕ) : Subgroup H :=
  (fun C : Subgroup H => C.comap T)^[n] K

theorem iterComap_succ (T : H →* H) (K : Subgroup H) (n : ℕ) :
    iterComap T K (n + 1) = (iterComap T K n).comap T :=
  Function.iterate_succ_apply' _ n K

theorem mem_iterComap (T : H →* H) (K : Subgroup H) :
    ∀ (n : ℕ) (x : H), x ∈ iterComap T K n ↔ (⇑T)^[n] x ∈ K
  | 0, _ => Iff.rfl
  | n + 1, x => by
    rw [iterComap_succ, Subgroup.mem_comap, mem_iterComap T K n, Function.iterate_succ_apply]

theorem stable_subgroup : ∀ {H : Type} [Group H] (θ : H →* H) (K₀ : Subgroup H) (δ : H) (r : ℕ), 0 < r → (∀ h, (⇑θ)^[r] h = h) →
    (∀ k ∈ K₀, θ k ∈ K₀) → (∀ g : H, Subgroup.Commensurable (K₀.map (MulAut.conj g).toMonoidHom) K₀) →
    ∀ Z : Subgroup H, (∀ z ∈ Z, δ * θ z * δ⁻¹ ∈ Z) → (∀ z ∈ Z, (⇑((MulAut.conj δ).toMonoidHom.comp θ))^[r] z = z) →
    (∃ G : Finset H, (∀ g ∈ G, g ∈ Z) ∧ Z ≤ Subgroup.closure ((G : Set H) ∪ ((Z ⊓ K₀ : Subgroup H) : Set H))) →
    ∃ U : Subgroup H, U ≤ Z ∧ U ≤ K₀ ∧ (∀ u ∈ U, δ * θ u * δ⁻¹ ∈ U) ∧
      (∃ G : Finset H, (∀ g ∈ G, g ∈ Z) ∧ Z ≤ Subgroup.closure ((G : Set H) ∪ (U : Set H))) ∧
      (∀ h g : H, ∃ F : Finset H, ∀ z ∈ Z, ∀ k ∈ K₀, z = h * k * g → ∃ f ∈ F, ∃ u ∈ U, z = f * u) := by
  intro H _ θ K₀ δ r hr hθr hθK hcomm Z hZ hZr hG
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  set T : H →* H := (MulAut.conj δ).toMonoidHom.comp θ with hT
  have hTapp : ∀ x, T x = δ * θ x * δ⁻¹ := fun x => by
    simp [T, MulAut.conj_apply]
  have hθs : Function.Surjective θ := fun y =>
    ⟨(⇑θ)^[s] y, by rw [← Function.iterate_succ_apply' (⇑θ) s y]; exact hθr y⟩
  have hTs : Function.Surjective T := fun y => by
    obtain ⟨x, hx⟩ := hθs (δ⁻¹ * y * δ)
    exact ⟨x, by rw [hTapp, hx]; group⟩
  have hθK' : ∀ n : ℕ, ∀ k ∈ K₀, (⇑θ)^[n] k ∈ K₀ := by
    intro n
    induction n with
    | zero => intro k hk; exact hk
    | succ n ih => intro k hk; rw [Function.iterate_succ_apply']; exact hθK _ (ih k hk)
  have hcθ : K₀.comap θ = K₀ := by
    ext x
    rw [Subgroup.mem_comap]
    constructor
    · intro hx
      have e : (⇑θ)^[s] (θ x) = x := by rw [← Function.iterate_succ_apply]; exact hθr x
      rw [← e]
      exact hθK' s _ hx
    · exact hθK x
  have hconj : K₀.comap (MulAut.conj δ).toMonoidHom = K₀.map (MulAut.conj δ⁻¹).toMonoidHom := by
    ext x
    simp only [Subgroup.mem_comap, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · intro hx
      exact ⟨δ * x * δ⁻¹, hx, by group⟩
    · rintro ⟨k, hk, rfl⟩
      convert hk using 1
      group
  have hTK : (K₀.comap T).Commensurable K₀ := by
    have h1 : (K₀.comap (MulAut.conj δ).toMonoidHom).Commensurable K₀ := hconj ▸ hcomm δ⁻¹
    have := commensurable_comap hθs h1
    rw [Subgroup.comap_comap, hcθ] at this
    exact this
  have hW : ∀ n, (iterComap T K₀ n).Commensurable K₀ := by
    intro n
    induction n with
    | zero => exact Subgroup.Commensurable.refl _
    | succ n ih => rw [iterComap_succ]; exact (commensurable_comap hTs ih).trans hTK
  set V : Subgroup H := ⨅ i : Fin (s + 1), iterComap T K₀ i with hV
  set U : Subgroup H := Z ⊓ V with hU
  have hfin : ∀ g : H, U.relIndex (Z ⊓ K₀.map (MulAut.conj g).toMonoidHom) ≠ 0 := by
    intro g
    apply Subgroup.relIndex_inf_ne_zero
    · rw [Subgroup.relIndex_eq_one.mpr inf_le_left]
      exact one_ne_zero
    · apply Subgroup.relIndex_iInf_ne_zero
      intro i
      exact Subgroup.relIndex_ne_zero_trans ((hW i).trans (hcomm g).symm).1
        (by rw [Subgroup.relIndex_eq_one.mpr inf_le_right]; exact one_ne_zero)
  have hUK : U ≤ K₀ := by
    intro u hu
    have := Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp hu).2 ⟨0, Nat.succ_pos s⟩
    exact this
  refine ⟨U, inf_le_left, hUK, ?_, ?_, ?_⟩
  · intro u hu
    obtain ⟨huZ, huV⟩ := Subgroup.mem_inf.mp hu
    rw [← hTapp]
    refine Subgroup.mem_inf.mpr ⟨by rw [hTapp]; exact hZ u huZ, ?_⟩
    rw [Subgroup.mem_iInf]
    intro i
    rw [mem_iterComap, ← Function.iterate_succ_apply]
    show (⇑T)^[(i : ℕ) + 1] u ∈ K₀
    rcases Nat.lt_or_ge ((i : ℕ) + 1) (s + 1) with h | h
    · have := Subgroup.mem_iInf.mp huV ⟨(i : ℕ) + 1, h⟩
      rw [mem_iterComap] at this
      exact this
    · have e : (i : ℕ) + 1 = s + 1 := by omega
      rw [e, hZr u huZ]
      exact hUK hu
  · obtain ⟨R, hRB, hR⟩ := finite_cover (hfin 1)
    obtain ⟨G, hGZ, hGcl⟩ := hG
    refine ⟨G ∪ R, ?_, ?_⟩
    · intro g hg
      rcases Finset.mem_union.mp hg with h | h
      · exact hGZ g h
      · exact (Subgroup.mem_inf.mp (hRB g h)).1
    · refine hGcl.trans ((Subgroup.closure_le _).mpr ?_)
      rintro x (hx | hx)
      · exact Subgroup.subset_closure (Or.inl (Finset.mem_coe.mpr (Finset.mem_union_left _ hx)))
      · have hx' := Subgroup.mem_inf.mp hx
        have hx1 : x ∈ Z ⊓ K₀.map (MulAut.conj (1 : H)).toMonoidHom :=
          Subgroup.mem_inf.mpr ⟨hx'.1, ⟨x, hx'.2, by simp [MulAut.conj_apply]⟩⟩
        obtain ⟨f, hf, a, ha, rfl⟩ := hR x hx1
        exact Subgroup.mul_mem _
          (Subgroup.subset_closure (Or.inl (Finset.mem_coe.mpr (Finset.mem_union_right _ hf))))
          (Subgroup.subset_closure (Or.inr ha))
  · intro h g
    obtain ⟨R, -, hR⟩ := finite_cover (hfin g⁻¹)
    by_cases hex : ∃ z₀ ∈ Z, ∃ k₀ ∈ K₀, z₀ = h * k₀ * g
    · obtain ⟨z₀, hz₀, k₀, hk₀, rfl⟩ := hex
      refine ⟨R.image (fun f => h * k₀ * g * f), ?_⟩
      intro z hz k hk hzk
      have hmem : (h * k₀ * g)⁻¹ * z ∈ Z ⊓ K₀.map (MulAut.conj g⁻¹).toMonoidHom := by
        refine Subgroup.mem_inf.mpr ⟨Z.mul_mem (Z.inv_mem hz₀) hz,
          ⟨k₀⁻¹ * k, K₀.mul_mem (K₀.inv_mem hk₀) hk, ?_⟩⟩
        rw [hzk]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      obtain ⟨f, hf, a, ha, hfa⟩ := hR _ hmem
      refine ⟨h * k₀ * g * f, Finset.mem_image.mpr ⟨f, hf, rfl⟩, a, ha, ?_⟩
      rw [mul_assoc (h * k₀ * g) f a, ← hfa]
      group
    · exact ⟨∅, fun z hz k hk hzk => absurd ⟨z, hz, k, hk, hzk⟩ hex⟩

end GlobalTheory.TwistStab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldPoincareSeriesLatticeFourier
section
open MeasureTheory
open scoped Pointwise

namespace GlobalTheory.PoincareUnfold

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure]

open MeasureTheory in
open scoped Pointwise in
private lemma setIntegral_exp_linear_fundamentalDomain_eq_zero {V : Type}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V]
    [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] (L : Submodule ℤ V)
    [VAddInvariantMeasure L V μ] [Countable L] {D : Set V} (hD : IsAddFundamentalDomain L D μ)
    (hDm : MeasurableSet D) (φ : V →ₗ[ℝ] ℝ) (hφ : φ ≠ 0) (hint : ∀ y ∈ L, ∃ z : ℤ, φ y = z) :
    ∫ v in D, Complex.exp (2 * Real.pi * Complex.I * (φ v : ℝ)) ∂μ = 0 := by
  set f : V → ℂ := fun v => Complex.exp (2 * Real.pi * Complex.I * (φ v : ℝ)) with hf
  have hper : ∀ (g : L) (v : V), f (g +ᵥ v) = f v := by
    intro g v
    obtain ⟨z, hz⟩ := hint g g.2
    have hgv : (g +ᵥ v : V) = (g : V) + v := rfl
    simp only [hf, hgv, map_add, hz]
    push_cast
    rw [mul_add, Complex.exp_add]
    have : Complex.exp (2 * Real.pi * Complex.I * (z : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I z]; ring_nf
    rw [this, one_mul]
  obtain ⟨u, hu⟩ : ∃ u, φ u ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ (LinearMap.ext h)
  set w : V := (1 / (2 * φ u)) • u with hw
  have hφw : φ w = 1 / 2 := by
    rw [hw, map_smul, smul_eq_mul]; field_simp
  have hshift : ∀ v, f (w + v) = -f v := by
    intro v
    simp only [hf, map_add, hφw]
    push_cast
    rw [mul_add, Complex.exp_add]
    have : Complex.exp (2 * Real.pi * Complex.I * (1 / 2 : ℂ)) = -1 := by
      rw [show 2 * (Real.pi : ℂ) * Complex.I * (1 / 2) = Real.pi * Complex.I by ring]
      exact Complex.exp_pi_mul_I
    rw [this, neg_one_mul]
  have hD' : IsAddFundamentalDomain L (w +ᵥ D) μ := hD.vadd_of_comm w
  have h1 : ∫ v in D, f v ∂μ = ∫ v in w +ᵥ D, f v ∂μ := hD.setIntegral_eq hD' hper
  have h2 : ∫ v in w +ᵥ D, f v ∂μ = ∫ v in D, f (w + v) ∂μ := by
    rw [← integral_indicator (hDm.const_vadd w), ← integral_indicator hDm]
    · rw [← integral_add_left_eq_self (μ := μ) _ w]
      congr 1
      ext v
      by_cases hv : v ∈ D
      · rw [Set.indicator_of_mem hv, Set.indicator_of_mem (show w + v ∈ w +ᵥ D from Set.vadd_mem_vadd_set hv)]
      · rw [Set.indicator_of_notMem hv, Set.indicator_of_notMem]
        rwa [← vadd_eq_add, Set.vadd_mem_vadd_set_iff]

  have h3 : ∫ v in D, f v ∂μ = -∫ v in D, f v ∂μ := by
    calc ∫ v in D, f v ∂μ = ∫ v in D, f (w + v) ∂μ := h1.trans h2
      _ = ∫ v in D, -f v ∂μ := setIntegral_congr_fun hDm fun v _ => hshift v
      _ = -∫ v in D, f v ∂μ := integral_neg _
  have h4 : (2 : ℂ) * ∫ v in D, f v ∂μ = 0 := by
    rw [two_mul]; nth_rewrite 2 [h3]; ring
  simpa using h4

open MeasureTheory in
open scoped Pointwise in

theorem _root_.GlobalTheory.PoincareUnfold.unfold_poincare_fourier : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure]
    (Γ : Type) [AddCommGroup Γ] (j : Γ →+ V), Function.Injective j → ∀ C : AddSubgroup Γ,
    (∀ R : ℝ, {c : Γ | c ∈ C ∧ ‖j c‖ ≤ R}.Finite) → Submodule.span ℝ (j '' (C : Set Γ)) = ⊤ →
    ∀ (n : ℕ) (t : Fin n → Γ) (Q : Γ → ℂ), (∀ x, Q x ≠ 0 → ∃ k, x - t k ∈ C) →
    (∀ k k', t k - t k' ∈ C → k = k') → (∀ x, ∀ c ∈ C, Q (x + c) = Q x) →
    ∀ F : V → ℂ, Integrable F μ → ∀ (a : Γ → ℂ) (l : Γ → V →ₗ[ℝ] ℝ), Summable (fun x => ‖a x‖) →
    l 0 = 0 → (∀ x, x ≠ 0 → l x ≠ 0) → (∀ x, a x ≠ 0 → ∀ c ∈ C, ∃ z : ℤ, l x (j c) = z) →
    (∀ v, ∑' x, Q x * F (j x + v) =
      ∑' x, a x * Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ))) →
    ∃ r : ℝ, 0 < r ∧ (∑ k, Q (t k)) * ∫ v, F v ∂μ = r * a 0 := by
  intro V _ _ _ _ _ μ _ Γ _ j hj C hfin hspan n t Q hQsupp ht hQper F hF a l ha hl0 hl hint H
  classical
  set L : Submodule ℤ V := (C.map j).toIntSubmodule with hLdef
  have hmemL : ∀ y, y ∈ L ↔ ∃ c ∈ C, j c = y := fun y => by
    exact AddSubgroup.mem_map
  have hLset : (L : Set V) = j '' (C : Set Γ) := by
    ext y; simp only [SetLike.mem_coe, hmemL, Set.mem_image]
  have hj0 : ∀ c, j c = 0 ↔ c = 0 := fun c => ⟨fun h => hj (by rw [h, map_zero]), fun h => by
    rw [h, map_zero]⟩
  haveI : DiscreteTopology L := by
    rw [discreteTopology_iff_isOpen_singleton_zero, Metric.isOpen_singleton_iff]
    set T : Finset ℝ := insert 1 (((hfin 1).toFinset.filter (· ≠ 0)).image fun c => ‖j c‖)
    have hTne : T.Nonempty := Finset.insert_nonempty _ _
    refine ⟨T.min' hTne, ?_, ?_⟩
    · show 0 < T.min' hTne
      rw [Finset.lt_min'_iff]
      intro y hy
      rw [Finset.mem_insert, Finset.mem_image] at hy
      rcases hy with rfl | ⟨c, hc, rfl⟩
      · exact one_pos
      · rw [Finset.mem_filter] at hc
        exact norm_pos_iff.2 fun h => hc.2 ((hj0 c).1 h)
    · rintro ⟨y, hy⟩ hdist
      obtain ⟨c, hc, rfl⟩ := (hmemL y).1 hy
      have hlt : ‖j c‖ < T.min' hTne := by simpa [dist_eq_norm] using hdist
      have hle1 : T.min' hTne ≤ 1 := Finset.min'_le _ _ (Finset.mem_insert_self _ _)
      by_cases hc0 : c = 0
      · ext; simp [hc0]
      · exfalso
        have hmem : ‖j c‖ ∈ T := Finset.mem_insert_of_mem (Finset.mem_image.2
          ⟨c, Finset.mem_filter.2 ⟨(Set.Finite.mem_toFinset _).2 ⟨hc, by linarith⟩, hc0⟩, rfl⟩)
        exact absurd (Finset.min'_le _ _ hmem) (not_le.2 hlt)
  haveI : IsZLattice ℝ L := ⟨by rw [hLset]; exact hspan⟩
  haveI : VAddInvariantMeasure L V μ := ⟨fun c s _ => measure_preimage_add μ (c : V) s⟩
  set ψ : C → L := fun c => ⟨j c, (hmemL _).2 ⟨c, c.2, rfl⟩⟩ with hψ
  have hψinj : Function.Injective ψ := fun c c' h => Subtype.ext (hj (congrArg Subtype.val h))
  have hψsurj : Function.Surjective ψ := fun y => by
    obtain ⟨c, hc, hcy⟩ := (hmemL y).1 y.2
    exact ⟨⟨c, hc⟩, Subtype.ext hcy⟩
  haveI : Countable L := (Module.Free.chooseBasis ℤ L).repr.injective.countable
  haveI : Countable C := hψinj.countable
  set D := ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L) with hDdef
  have hD : IsAddFundamentalDomain L D μ := ZLattice.isAddFundamentalDomain _ μ
  have hDfin : μ D < ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top
  refine ⟨ZLattice.covolume L μ, ZLattice.covolume_pos L μ, ?_⟩
  rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ hD]
  have hR : ∫ v in D, (∑' x, a x * Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ))) ∂μ =
      ((μ.real D : ℝ) : ℂ) * a 0 := by
    have hDm : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet _
    set E : Γ → V → ℂ := fun x v => Complex.exp (2 * Real.pi * Complex.I * (l x v : ℝ)) with hE
    have hEnorm : ∀ x v, ‖E x v‖ₑ = 1 := by
      intro x v
      rw [← ofReal_norm_eq_enorm]
      simp only [hE]
      rw [show (2 * Real.pi * Complex.I * ((l x v : ℝ) : ℂ)) = ((2 * Real.pi * l x v : ℝ) : ℂ) *
        Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I, ENNReal.ofReal_one]
    have hEcont : ∀ x, Continuous (E x) := fun x => by
      simp only [hE]
      fun_prop
    set s := Function.support a with hs
    have hscount : s.Countable := ha.of_norm.countable_support
    haveI : Countable s := hscount.to_subtype
    have hsub : ∀ v, ∑' x, a x * E x v = ∑' x : s, a x * E x v := fun v =>
      (tsum_subtype_eq_of_support_subset fun x hx => by
        simp only [Function.mem_support] at hx ⊢
        intro h; exact hx (by rw [h, zero_mul])).symm
    have hchar : ∀ x, ∫ v in D, a x * E x v ∂μ =
        if x = 0 then ((μ.real D : ℝ) : ℂ) * a 0 else 0 := by
      intro x
      rw [integral_const_mul]
      split_ifs with hx
      · subst hx
        simp only [hE, hl0, LinearMap.zero_apply, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
          setIntegral_const, Complex.real_smul, mul_one]
        ring
      · by_cases hax : a x = 0
        · rw [hax, zero_mul]
        · rw [setIntegral_exp_linear_fundamentalDomain_eq_zero μ L hD hDm (l x) (hl x hx)
            (fun y hy => by
              obtain ⟨c, hc, rfl⟩ := (hmemL y).1 hy
              exact hint x hax c hc), mul_zero]
    show ∫ v in D, (∑' x, a x * E x v) ∂μ = _
    simp_rw [hsub]
    rw [integral_tsum]
    · rw [tsum_subtype_eq_of_support_subset (f := fun x => ∫ v in D, a x * E x v ∂μ)]
      · simp_rw [hchar]
        exact tsum_ite_eq 0 _
      · intro x hx
        rw [Function.mem_support, hchar] at hx
        split_ifs at hx with h0
        · subst h0
          intro h; exact hx (by rw [h, mul_zero])
        · exact absurd rfl hx
    · intro x
      exact ((hEcont x).const_mul (a x) |>.aestronglyMeasurable)
    · simp_rw [enorm_mul, hEnorm, mul_one, lintegral_const, Measure.restrict_apply_univ]
      rw [ENNReal.tsum_mul_right]
      refine ENNReal.mul_ne_top ?_ hDfin.ne
      simp_rw [enorm_eq_nnnorm]
      refine ENNReal.tsum_coe_ne_top_iff_summable.2 ?_
      rw [← NNReal.summable_coe]
      exact ha.subtype s
  have hLHS : ∫ v in D, (∑' x, Q x * F (j x + v)) ∂μ = (∑ k, Q (t k)) * ∫ v, F v ∂μ := by
    have hDm : MeasurableSet D := ZSpan.fundamentalDomain_measurableSet _
    set e : Fin n × C → Γ := fun p => t p.1 + p.2 with he
    have heinj : Function.Injective e := by
      rintro ⟨k, c⟩ ⟨k', c'⟩ h
      simp only [he] at h
      have hk : k = k' := ht k k' (by
        rw [show t k - t k' = c' - c by rw [sub_eq_sub_iff_add_eq_add, h, add_comm]]
        exact C.sub_mem c'.2 c.2)
      subst hk
      exact Prod.ext rfl (Subtype.ext (add_left_cancel h))
    have hsupp : ∀ v, Function.support (fun x => Q x * F (j x + v)) ⊆ Set.range e := by
      intro v x hx
      have hQx : Q x ≠ 0 := fun h => hx (by simp [h])
      obtain ⟨k, hk⟩ := hQsupp x hQx
      exact ⟨(k, ⟨x - t k, hk⟩), by simp [he]⟩
    set g : Fin n × C → V → ℂ := fun p v => Q (t p.1) * F (j (t p.1) + (j p.2 + v)) with hg
    have hrw : ∀ v, ∑' x, Q x * F (j x + v) = ∑' p, g p v := by
      intro v
      rw [← heinj.tsum_eq (hsupp v)]
      refine tsum_congr fun p => ?_
      simp only [he, hg, map_add, hQper _ _ p.2.2, add_assoc]
    have hunf : ∀ G : V → ℂ, Integrable G μ → ∫ v, G v ∂μ = ∑' c : C, ∫ v in D, G (j c + v) ∂μ := by
      intro G hG
      rw [hD.integral_eq_tsum' G hG,
        ← ((Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩).trans (Equiv.neg L)).tsum_eq]
      refine tsum_congr fun c => ?_
      rw [Equiv.trans_apply, Equiv.neg_apply, neg_neg]
      rfl
    have hunfl : ∀ G : V → ENNReal, ∫⁻ v, G v ∂μ = ∑' c : C, ∫⁻ v in D, G (j c + v) ∂μ := by
      intro G
      rw [hD.lintegral_eq_tsum' G,
        ← ((Equiv.ofBijective ψ ⟨hψinj, hψsurj⟩).trans (Equiv.neg L)).tsum_eq]
      refine tsum_congr fun c => ?_
      rw [Equiv.trans_apply, Equiv.neg_apply, neg_neg]
      rfl
    have hfinite : ∑' p, ∫⁻ v in D, ‖g p v‖ₑ ∂μ ≠ ⊤ := by
      simp_rw [hg, enorm_mul]
      simp_rw [lintegral_const_mul' _ _ enorm_ne_top]
      rw [ENNReal.tsum_prod (f := fun k (c : C) =>
        ‖Q (t k)‖ₑ * ∫⁻ v in D, ‖F (j (t k) + (j c + v))‖ₑ ∂μ), tsum_fintype]
      refine (ENNReal.sum_lt_top.2 fun k _ => ?_).ne
      rw [ENNReal.tsum_mul_left, ← hunfl (fun v => ‖F (j (t k) + v)‖ₑ)]
      exact ENNReal.mul_lt_top enorm_lt_top (hF.comp_add_left (j (t k))).hasFiniteIntegral
    have hmeas : ∀ p, AEStronglyMeasurable (g p) (μ.restrict D) := fun p =>
      (((hF.comp_add_left (j (t p.1))).comp_add_left (j p.2)).aestronglyMeasurable.const_mul
        _).restrict
    have hsumm : Summable (fun p => ∫ v in D, g p v ∂μ) := by
      refine Summable.of_norm_bounded (ENNReal.summable_toReal hfinite) fun p => ?_
      refine (norm_integral_le_lintegral_norm _).trans_eq ?_
      simp_rw [ofReal_norm_eq_enorm]
    simp_rw [hrw]
    rw [integral_tsum hmeas hfinite, hsumm.tsum_prod, tsum_fintype, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hg, integral_const_mul]
    rw [tsum_mul_left, ← hunf _ (hF.comp_add_left (j (t k))), integral_add_left_eq_self]
  rw [← hLHS, ← hR]
  exact setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _) fun v _ => H v

end GlobalTheory.PoincareUnfold
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformizerEqPowRamificationIdxMulUnitIntegralCl
section
open IsLocalRing

namespace GlobalTheory

theorem pi_eq_pow_ramificationIdx_mul_unit
    (S K L : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S]
    [Field K] [Algebra S K] [IsFractionRing S K] [Field L] [Algebra K L] [Algebra S L] [IsScalarTower S K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] (π : S) (e : ℕ) (D : Type) [CommRing D] [Algebra S D]
    (P : Ideal (integralClosure S L)) [P.IsMaximal] :
    Irreducible π → algebraMap S (integralClosure S L) π ∈ P →
      ∃ ϖ : Localization.AtPrime P, Irreducible ϖ ∧ ∃ u : (Localization.AtPrime P)ˣ,
        algebraMap S (Localization.AtPrime P) π = ϖ ^ P.ramificationIdx S * (u : Localization.AtPrime P) := by
  intro hπ hπP
  haveI : IsDedekindDomain (integralClosure S L) := integralClosure.isDedekindDomain S K L
  have hπ0 : π ≠ 0 := hπ.ne_zero
  have hO0 : algebraMap S (integralClosure S L) π ≠ 0 := by
    intro h
    have h2 : algebraMap (integralClosure S L) L (algebraMap S (integralClosure S L) π) = 0 := by rw [h, map_zero]
    rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply S K L] at h2
    rw [map_eq_zero_iff _ (algebraMap K L).injective,
      map_eq_zero_iff _ (IsFractionRing.injective S K)] at h2
    exact hπ0 h2
  have hPbot : P ≠ ⊥ := fun h => hO0 (by rw [h] at hπP; simpa using hπP)
  haveI hA : IsDiscreteValuationRing (Localization.AtPrime P) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (integralClosure S L) hPbot (Localization.AtPrime P)
  have hinj : Function.Injective (algebraMap (integralClosure S L) (Localization.AtPrime P)) :=
    IsLocalization.injective (Localization.AtPrime P) P.primeCompl_le_nonZeroDivisors
  have hx0 : algebraMap S (Localization.AtPrime P) π ≠ 0 := by
    rw [IsScalarTower.algebraMap_apply S (integralClosure S L) (Localization.AtPrime P)]
    exact fun h => hO0 (hinj (by rw [h, map_zero]))
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime P)
  obtain ⟨n, u, hn⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hϖ

  have hunder : P.under S = Ideal.span {π} := by
    have hmem : π ∈ P.under S := by simpa [Ideal.under] using hπP
    have hne : P.under S ≠ ⊥ := fun h => hπ0 (by rw [h] at hmem; simpa using hmem)
    have hmax : (P.under S).IsMaximal := Ideal.IsPrime.isMaximal inferInstance hne
    rw [IsLocalRing.eq_maximalIdeal hmax, hπ.maximalIdeal_eq]
  have hram : P.ramificationIdx S = n := by
    rw [Ideal.ramificationIdx_def, hunder, Ideal.map_span, Set.image_singleton, hn,
      Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
      ← hϖ.maximalIdeal_eq, IsDiscreteValuationRing.length_quotient_pow_maximalIdeal,
      ENat.toNat_natCast]
  refine ⟨ϖ, hϖ, u, ?_⟩
  rw [hram, hn, mul_comm]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversallyClosedOfClosedCoverInUniversallyClose
section
open CategoryTheory Limits AlgebraicGeometry

namespace GlobalTheory

theorem universallyClosed_of_closed_cover_in_universallyClosed :
    ∀ (S X Y P : Scheme.{0}) (f : X ⟶ S) (π : Y ⟶ X) (q : Y ⟶ P) (s : P ⟶ S) (T : Set Y),
      UniversallyClosed s → IsImmersion q → q ≫ s = π ≫ f → IsClosed T → IsClosed (q '' T) →
        π '' T = Set.univ → UniversallyClosed f := by
  intro S X Y P f π q s T hs hq hcomm hT hqT hπT
  let I := Scheme.IdealSheafData.vanishingIdeal (⟨T, hT⟩ : TopologicalSpace.Closeds Y)
  have hrange : Set.range I.subschemeι = T := by
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]; rfl
  have hcl : IsClosedImmersion (I.subschemeι ≫ q) := by
    refine .of_isPreimmersion _ ?_
    have : Set.range (I.subschemeι ≫ q) = q '' T := by
      rw [← hrange, ← Set.range_comp]; rfl
    rw [this]; exact hqT
  have : UniversallyClosed ((I.subschemeι ≫ π) ≫ f) := by
    rw [Category.assoc, ← hcomm, ← Category.assoc]
    infer_instance
  have : Surjective (I.subschemeι ≫ π) := by
    constructor
    have : Set.range (I.subschemeι ≫ π) = π '' T := by
      rw [← hrange, ← Set.range_comp]; rfl
    rw [← Set.range_eq_univ, this]; exact hπT
  exact UniversallyClosed.of_comp_surjective (I.subschemeι ≫ π) f

end GlobalTheory
end

