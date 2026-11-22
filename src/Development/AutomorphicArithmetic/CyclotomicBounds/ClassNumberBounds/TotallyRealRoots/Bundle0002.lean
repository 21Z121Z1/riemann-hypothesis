import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0001

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.EqOneOfMemPrincOne
section
namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem toZMod_eq_zero_iff (x : ℤ_[l]) : PadicInt.toZMod x = 0 ↔ ‖x‖ < 1 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits]

private theorem val_red (u : ℤ_[l]ˣ) :
    ((red l u : (ZMod l)ˣ) : ZMod l) = PadicInt.toZMod (u : ℤ_[l]) := rfl

private theorem exists_root_lift (a : ℤ_[l]) (ha : PadicInt.toZMod a ≠ 0) :
    ∃ ζ ∈ rootsOfUnity (l - 1) ℤ_[l], PadicInt.toZMod (ζ : ℤ_[l]) = PadicInt.toZMod a := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hna : ‖a‖ = 1 := by
    refine le_antisymm (PadicInt.norm_le_one a) (not_lt.1 fun h => ha ?_)
    exact (toZMod_eq_zero_iff a).2 h
  set F : Polynomial ℤ := Polynomial.X ^ (l - 1) - 1 with hF
  have hev : ∀ z : ℤ_[l], Polynomial.aeval z F = z ^ (l - 1) - 1 := by
    intro z; simp [hF]
  have hder : ‖Polynomial.aeval a (Polynomial.derivative F)‖ = 1 := by
    have : Polynomial.aeval a (Polynomial.derivative F)
        = ((l - 1 : ℕ) : ℤ_[l]) * a ^ (l - 1 - 1) := by
      rw [hF, Polynomial.derivative_sub, Polynomial.derivative_one, sub_zero,
        Polynomial.derivative_X_pow, map_mul, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
        map_natCast]
    rw [this, norm_mul, norm_pow, hna, PadicInt.norm_natCast_p_sub_one]
    simp
  have hnorm : ‖Polynomial.aeval a F‖ < ‖Polynomial.aeval a (Polynomial.derivative F)‖ ^ 2 := by
    rw [hder, one_pow, hev, ← toZMod_eq_zero_iff, map_sub, map_pow, map_one,
      ZMod.pow_card_sub_one_eq_one ha, sub_self]
  obtain ⟨z, hz, hza, -⟩ := hensels_lemma hnorm
  rw [hev, sub_eq_zero] at hz
  rw [hder, ← toZMod_eq_zero_iff, map_sub, sub_eq_zero] at hza
  have hu : IsUnit z := IsUnit.of_pow_eq_one hz (by omega)
  refine ⟨hu.unit, ?_, by simpa using hza⟩
  rw [mem_rootsOfUnity']
  simpa using hz

theorem exists_teich (u : ℤ_[l]ˣ) :
    ∃ ζ ∈ rootsOfUnity (l - 1) ℤ_[l], red l ζ = red l u := by
  obtain ⟨ζ, h1, h2⟩ := exists_root_lift (u : ℤ_[l]) (by rw [← val_red]; exact Units.ne_zero _)
  exact ⟨ζ, h1, Units.ext (by rw [val_red, val_red, h2])⟩

private theorem eq_one_of_toZMod {o : ℕ} (ho : ¬ l ∣ o) {ζ : ℤ_[l]ˣ}
    (hζ : ζ ∈ rootsOfUnity o ℤ_[l]) (h1 : PadicInt.toZMod (ζ : ℤ_[l]) = 1) : ζ = 1 := by
  rw [mem_rootsOfUnity'] at hζ
  have h := mul_geom_sum (ζ : ℤ_[l]) o
  rw [hζ, sub_self, mul_eq_zero] at h
  rcases h with h | h
  · exact Units.ext (by simpa [sub_eq_zero] using h)
  · exfalso
    have := congrArg PadicInt.toZMod h
    rw [map_sum, map_zero] at this
    simp only [map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
      mul_one] at this
    exact ho ((ZMod.natCast_eq_zero_iff o l).1 this)

theorem eq_one_of_mem_princ_one {o : ℕ} (ho : ¬ l ∣ o) {ζ : ℤ_[l]ˣ}
    (hζ : ζ ∈ rootsOfUnity o ℤ_[l]) (h1 : ζ ∈ princ l 1) : ζ = 1 := by
  refine eq_one_of_toZMod ho hζ ?_
  rw [mem_princ, pow_one, ← PadicInt.norm_lt_one_iff_dvd, ← toZMod_eq_zero_iff, map_sub, map_one,
    sub_eq_zero] at h1
  exact h1

theorem map_red_rootsOfUnity {o : ℕ} (ho : o ∣ l - 1) :
    (rootsOfUnity o ℤ_[l]).map (red l) = rootsOfUnity o (ZMod l) := by
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  ext x
  constructor
  · rintro ⟨ζ, hζ, rfl⟩
    have hζ' : ζ ^ o = 1 := (mem_rootsOfUnity o ζ).1 hζ
    rw [mem_rootsOfUnity, ← map_pow, hζ', map_one]
  · intro hx
    rw [mem_rootsOfUnity] at hx
    obtain ⟨a, ha⟩ := ZMod.ringHom_surjective (PadicInt.toZMod : ℤ_[l] →+* ZMod l) (x : ZMod l)
    obtain ⟨ζ, h1, h2⟩ := exists_root_lift a (by rw [ha]; exact Units.ne_zero _)
    have hr : red l ζ = x := Units.ext (by rw [val_red, h2, ha])
    refine ⟨ζ, ?_, hr⟩
    have hnd : ¬ l ∣ l - 1 := fun h => by
      have := Nat.le_of_dvd (by omega) h
      omega
    refine (mem_rootsOfUnity o ζ).2 (eq_one_of_toZMod hnd (Subgroup.pow_mem _ h1 o) ?_)
    rw [← val_red, map_pow, hr, hx, Units.val_one]

end KStar.TotallyRealRoots
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.GalAut
section
namespace KStar.TotallyRealRoots

theorem exists_aut_pow_roots (Ω : Type*) [Field Ω] [CharZero Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic ℚ Ω] {M : ℕ} [NeZero M] (a : (ZMod M)ˣ) :
    ∃ g : Ω ≃ₐ[ℚ] Ω, ∀ ζ : Ω, ζ ^ M = 1 → g ζ = ζ ^ (a : ZMod M).val := by
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω M
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  have : Normal ℚ Ω := IsAlgClosure.normal ℚ Ω
  have hc : IsCyclotomicExtension {M} ℚ (IntermediateField.adjoin ℚ {ζ}) :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : NumberField (IntermediateField.adjoin ℚ {ζ}) := IsCyclotomicExtension.numberField {M} ℚ _
  let σ := (IsCyclotomicExtension.Rat.galEquivZMod M (IntermediateField.adjoin ℚ {ζ})).symm a
  refine ⟨σ.liftNormal Ω, fun η hη => ?_⟩
  obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hη
  let z : IntermediateField.adjoin ℚ {ζ} := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
  have hz : z ^ M = 1 := Subtype.ext (by simpa [z] using hζ.pow_eq_one)
  have h1 := IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq M _ σ hz
  have h2 := AlgEquiv.liftNormal_commutes σ Ω z
  have h3 : σ.liftNormal Ω ζ = ζ ^ (a : ZMod M).val := by
    have : algebraMap _ Ω z = ζ := rfl
    rw [this, h1, map_pow, this] at h2
    rwa [MulEquiv.apply_symm_apply] at h2
  rw [map_pow, h3, ← pow_mul, ← pow_mul, mul_comm]

theorem aut_comp_embedding {Ω : Type*} [Field Ω] [CharZero Ω] {N : ℕ} [NeZero N] {K : Type*} [Field K]
    [NumberField K] [IsCyclotomicExtension {N} ℚ K] (φ : K →+* Ω) (g : Ω →+* Ω) (a : (ZMod N)ˣ)
    (h : ∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ ^ (a : ZMod N).val) (x : K) :
    g (φ x) = φ ((IsCyclotomicExtension.Rat.galEquivZMod N K).symm a x) := by
  set σ := (IsCyclotomicExtension.Rat.galEquivZMod N K).symm a with hσ
  have hσa : IsCyclotomicExtension.Rat.galEquivZMod N K σ = a :=
    (IsCyclotomicExtension.Rat.galEquivZMod N K).apply_symm_apply a
  have hζ := IsCyclotomicExtension.zeta_spec N ℚ K
  have key : (g.comp φ).toRatAlgHom = (φ.comp (σ : K →+* K)).toRatAlgHom := by
    apply AlgHom.ext_of_adjoin_eq_top (IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ)
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show g (φ _) = φ (σ _)
    rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq N K σ hζ.pow_eq_one, hσa, map_pow,
      h _ (by rw [← map_pow, hζ.pow_eq_one, map_one])]
  exact congrArg (fun f : K →ₐ[ℚ] Ω => f x) key

theorem exists_class_of_aut {Ω : Type*} [Field Ω] [CharZero Ω] [IsAlgClosed Ω] {N : ℕ} [NeZero N]
    (g : Ω ≃+* Ω) : ∃ a : (ZMod N)ˣ, ∀ ζ : Ω, ζ ^ N = 1 → g ζ = ζ ^ (a : ZMod N).val := by
  have hn : Nat.card (rootsOfUnity N Ω) = N := HasEnoughRootsOfUnity.natCard_rootsOfUnity Ω N
  refine ⟨modularCyclotomicCharacter Ω hn g, fun ζ hζ => ?_⟩
  have := modularCyclotomicCharacter.spec Ω hn g (t := (rootsOfUnity.mkOfPowEq ζ hζ : Ωˣ)) (rootsOfUnity.mkOfPowEq ζ hζ).2
  simpa using this

end KStar.TotallyRealRoots
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.NuBasic
section
namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem nb_red_eq_one {u : ℤ_[l]ˣ} : red l u = 1 ↔ (l : ℤ_[l]) ∣ (u : ℤ_[l]) - 1 := by
  rw [← Units.val_eq_one, show ((red l u : (ZMod l)ˣ) : ZMod l) = PadicInt.toZMod (u : ℤ_[l]) from rfl,
    ← Ideal.mem_span_singleton, ← PadicInt.maximalIdeal_eq_span_p, ← PadicInt.ker_toZMod,
    RingHom.mem_ker, map_sub, map_one, sub_eq_zero]

theorem nu_pos_iff (U : Subgroup ℤ_[l]ˣ) (tr : ℕ) : 0 < nu l U tr ↔ resOrder l U ∣ tr := by
  rw [← Order.one_le_iff_pos, ← Nat.cast_one (R := ℕ∞), le_nu_iff, resOrder,
    ← IsCyclic.exponent_eq_card, Monoid.exponent_dvd_iff_forall_pow_eq_one]
  simp only [pow_one, ← Units.val_pow_eq_pow_val, ← nb_red_eq_one, map_pow]
  constructor
  · rintro h ⟨_, u, hu, rfl⟩
    exact Subtype.ext (h u hu)
  · intro h u hu
    exact congrArg Subtype.val (h ⟨red l u, u, hu, rfl⟩)

private theorem nb_two_dvd (u : ℤ_[2]ˣ) : ((2 : ℕ) : ℤ_[2]) ∣ (u : ℤ_[2]) - 1 :=
  nb_red_eq_one.mp (Subsingleton.elim _ _)

theorem nu_two_of_odd (U : Subgroup ℤ_[2]ˣ) {tr : ℕ} (htr : Odd tr) :
    nu 2 U tr = nu 2 U 1 ∧ 1 ≤ nu 2 U tr := by
  constructor
  · refine nuStar_eq_nuStar_one PadicInt.prime_p ?_ ?_
    · rintro _ ⟨u, -, rfl⟩
      exact nb_two_dvd u
    · intro h
      rw [← PadicInt.norm_lt_one_iff_dvd, PadicInt.norm_natCast_lt_one_iff] at h
      exact (Nat.not_even_iff_odd.mpr htr) (even_iff_two_dvd.mpr h)
  · rw [← Nat.cast_one (R := ℕ∞), le_nu_iff]
    intro u _
    rw [pow_one, ← Units.val_pow_eq_pow_val]
    exact nb_two_dvd _

end KStar.TotallyRealRoots
end

-- bundled from Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.PrincTop
section
namespace KStar.TotallyRealRoots

variable {l : ℕ} [Fact l.Prime]

private theorem mem_princ_iff_norm {a : ℕ} {u : ℤ_[l]ˣ} :
    u ∈ princ l a ↔ ‖(u : ℤ_[l]) - 1‖ ≤ (l : ℝ) ^ (-a : ℤ) := by
  rw [mem_princ, PadicInt.norm_le_pow_iff_mem_span_pow, Ideal.mem_span_singleton]

private theorem exists_princ_subset {s : Set ℤ_[l]ˣ} (hs : s ∈ nhds (1 : ℤ_[l]ˣ)) :
    ∃ a, (princ l a : Set ℤ_[l]ˣ) ⊆ s := by
  have h1 : Units.val '' s ∈ nhds ((1 : ℤ_[l]ˣ) : ℤ_[l]) :=
    Units.isOpenEmbedding_val.isOpenMap.image_mem_nhds hs
  simp only [Units.val_one] at h1
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp h1
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨a, ha⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ hl)
  refine ⟨a, fun u hu => ?_⟩
  have hu' : (u : ℤ_[l]) ∈ Metric.ball (1 : ℤ_[l]) ε := by
    rw [Metric.mem_ball, dist_eq_norm]
    refine lt_of_le_of_lt (mem_princ_iff_norm.mp hu) ?_
    rwa [zpow_neg, zpow_natCast, ← inv_pow]
  obtain ⟨v, hv, hvu⟩ := hball hu'
  rwa [← Units.val_injective hvu]

theorem isOpen_princ (a : ℕ) : IsOpen (princ l a : Set ℤ_[l]ˣ) := by
  have hr : ((l : ℝ) ^ (-a : ℤ)) ≠ 0 :=
    (zpow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) _).ne'
  have hset : (princ l a : Set ℤ_[l]ˣ) =
      Units.val ⁻¹' Metric.closedBall (1 : ℤ_[l]) ((l : ℝ) ^ (-a : ℤ)) := by
    ext u
    simp only [SetLike.mem_coe, Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm]
    exact mem_princ_iff_norm
  have hopen : IsOpen (princ l a : Set ℤ_[l]ˣ) := by
    rw [hset]
    exact Units.continuous_val.isOpen_preimage _ (IsUltrametricDist.isOpen_closedBall _ hr)
  exact hopen

theorem isOpen_iff_princ_le (U : Subgroup ℤ_[l]ˣ) :
    IsOpen (U : Set ℤ_[l]ˣ) ↔ ∃ a, princ l a ≤ U := by
  constructor
  · intro h
    exact exists_princ_subset (h.mem_nhds U.one_mem)
  · rintro ⟨a, ha⟩
    exact Subgroup.isOpen_mono ha (isOpen_princ a)

theorem isOpen_iff_isClosed_finiteIndex (U : Subgroup ℤ_[l]ˣ) :
    IsOpen (U : Set ℤ_[l]ˣ) ↔ IsClosed (U : Set ℤ_[l]ˣ) ∧ U.FiniteIndex := by
  constructor
  · intro h
    refine ⟨U.isClosed_of_isOpen h, ?_⟩
    obtain ⟨a, ha⟩ := (isOpen_iff_princ_le U).mp h
    haveI : (princ l a).FiniteIndex := Subgroup.finiteIndex_ker (redPow l a)
    exact Subgroup.finiteIndex_of_le ha
  · rintro ⟨hc, hf⟩
    exact U.isOpen_of_isClosed_of_finiteIndex hc

theorem mem_of_isClosed {U : Subgroup ℤ_[l]ˣ} (hU : IsClosed (U : Set ℤ_[l]ˣ)) {x : ℤ_[l]ˣ}
    (h : ∀ b, ∃ u ∈ U, redPow l b u = redPow l b x) : x ∈ U := by
  rw [← SetLike.mem_coe, ← hU.closure_eq, mem_closure_iff_nhds]
  intro t ht
  have ht' : (fun y => x * y) ⁻¹' t ∈ nhds (1 : ℤ_[l]ˣ) := by
    apply (continuous_const.mul continuous_id).continuousAt.preimage_mem_nhds
    simpa using ht
  obtain ⟨b, hb⟩ := exists_princ_subset ht'
  obtain ⟨u, hu, hux⟩ := h b
  have hmem : x⁻¹ * u ∈ princ l b := by
    show x⁻¹ * u ∈ (redPow l b).ker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hux, inv_mul_cancel]
  refine ⟨u, ?_, hu⟩
  have := hb hmem
  simpa using this

end KStar.TotallyRealRoots
end

