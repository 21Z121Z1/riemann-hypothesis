import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DiscriminantMulIntegralMem
section
private theorem int_of_rat {K : Type} [Field K] [CharZero K] (r : ℚ)
    (h : IsIntegral ℤ (r : K)) : ∃ a : ℤ, (a : ℚ) = r := by
  have h1 : IsIntegral ℤ r := by
    have h2 : IsIntegral ℤ (algebraMap ℚ K r) := by simpa using h
    exact (isIntegral_algebraMap_iff (algebraMap ℚ K).injective).mp h2
  obtain ⟨a, ha⟩ := IsIntegrallyClosed.isIntegral_iff.mp h1
  exact ⟨a, by simpa using ha⟩

theorem UpperTheory.discriminant_mul_integral_mem :
    ∀ (K : Type) [Field K] [CharZero K] (σ : K →+* K) (w y : K) (t n : ℤ), w + σ w = (t : K) → w * σ w = (n : K) → IsIntegral ℤ y → y ∈ IntermediateField.adjoin ℚ {w} → ∃ a b : ℤ, ((t ^ 2 - 4 * n : ℤ) : K) * y = (a : K) + (b : K) * w := by
  intro K _ _ σ w y t n ht hn hy hmem
  have hsq : w * w = (t : K) * w - (n : K) := by linear_combination w * ht - hn
  have hw : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 - Polynomial.C t * Polynomial.X + Polynomial.C n, ?_, ?_⟩
    · monicity!
    · rw [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
        Polynomial.eval₂_X_pow, Polynomial.eval₂_C, Polynomial.eval₂_C, Polynomial.eval₂_X,
        eq_intCast, eq_intCast]
      linear_combination hsq
  have hwQ : IsIntegral ℚ w := hw.tower_top
  have hmem' : y ∈ Algebra.adjoin ℚ {w} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hwQ.isAlgebraic]
    exact hmem
  have hrep : ∀ z ∈ Algebra.adjoin ℚ {w}, ∃ p q : ℚ, z = (p : K) + (q : K) * w := by
    intro z hz
    induction hz using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      exact ⟨0, 1, by simp [hx]⟩
    | algebraMap r => exact ⟨r, 0, by simp⟩
    | add x z _ _ hx hz =>
      obtain ⟨p, q, rfl⟩ := hx
      obtain ⟨r, s, rfl⟩ := hz
      exact ⟨p + r, q + s, by push_cast; ring⟩
    | mul x z _ _ hx hz =>
      obtain ⟨p, q, rfl⟩ := hx
      obtain ⟨r, s, rfl⟩ := hz
      exact ⟨p * r - q * s * n, p * s + q * r + q * s * t, by
        push_cast; linear_combination (q : K) * (s : K) * hsq⟩
  obtain ⟨p, q, hpq⟩ := hrep y hmem'
  have hσ : ∀ z : K, IsIntegral ℤ z → IsIntegral ℤ (z + σ z) := fun z hz =>
    hz.add (hz.map σ.toIntAlgHom)
  have hσw : σ w = (t : K) - w := by linear_combination ht
  have hσy : σ y = (p : K) + (q : K) * ((t : K) - w) := by
    rw [hpq, map_add, map_mul, map_ratCast, map_ratCast, hσw]
  have hA : y + σ y = ((2 * p + q * t : ℚ) : K) := by
    rw [hσy, hpq]; push_cast; ring
  have hB : w * y + σ (w * y) = ((p * t + q * (t ^ 2 - 2 * n) : ℚ) : K) := by
    rw [map_mul, hσy, hσw, hpq]; push_cast; linear_combination 2 * (q : K) * hsq
  obtain ⟨A, hA'⟩ := int_of_rat _ (hA ▸ hσ y hy)
  obtain ⟨B, hB'⟩ := int_of_rat _ (hB ▸ hσ _ (hw.mul hy))
  have hAK : (A : K) = 2 * p + q * t := by exact_mod_cast congrArg (Rat.cast : ℚ → K) hA'
  have hBK : (B : K) = p * t + q * (t ^ 2 - 2 * n) := by
    exact_mod_cast congrArg (Rat.cast : ℚ → K) hB'
  refine ⟨(t ^ 2 - 2 * n) * A - t * B, 2 * B - t * A, ?_⟩
  push_cast
  rw [hAK, hBK, hpq]
  ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DivisibilityFiltration
section
theorem UpperTheory.divisibility_filtration :
    ∀ {A D : Type} [CommRing A] [AddCommGroup D] [Module A D] (l f ϖ : A) (σ R : ℕ) (E e : ℕ → ℕ)
        (r s : ℕ → A) (S : Set D) (Z : Submodule A D),
        (∀ a : A, f ∣ l * a → f ∣ a) →
        (∀ a b, E a + E b ≤ E (a + b)) → (∀ y, E y ≤ e y) → e 0 = 0 →
        (∀ y, f ∣ ϖ ^ y - r y) → (∀ y, l ^ e y * s y = l ^ σ * r y) → (∀ y, R < y → f ∣ ϖ ^ y) →
        (∀ x ∈ S, ∃ c : ℕ → D, c 0 = 0 ∧ (∀ y, c y ∈ S) ∧
          l ^ σ • x - ∑ y ∈ Finset.range (R + 1), (s y * l ^ (e y - E y)) • c y ∈ Z) →
        ∀ p ∈ Submodule.span A S, ∃ p' ∈ Submodule.span A S, l ^ (2 * σ) • p - f • p' ∈ Z := by
  intro A D _ _ _ l f ϖ σ R E e r s S Z hl hE hEe he0 hr hs hR hS
  classical
  let N : Submodule A D := Z ⊔ (Submodule.span A S).map (LinearMap.lsmul A D f)
  have hZN : ∀ z ∈ Z, z ∈ N := fun z hz => Submodule.mem_sup_left hz
  have hfN : ∀ w ∈ Submodule.span A S, f • w ∈ N := fun w hw =>
    Submodule.mem_sup_right (Submodule.mem_map.2 ⟨w, hw, rfl⟩)
  have hpow : ∀ (n : ℕ) (a : A), f ∣ l ^ n * a → f ∣ a := by
    intro n
    induction n with
    | zero => intro a h; simpa using h
    | succ n ih =>
      intro a h
      exact ih a (hl _ (by rwa [← mul_assoc, ← pow_succ']))
  obtain ⟨t, ht_def⟩ : ∃ t : ℕ → A, ∀ y, t y = s y * l ^ (e y - E y) := ⟨_, fun _ => rfl⟩
  have ht : ∀ y, l ^ E y * t y = l ^ σ * r y := by
    intro y
    rw [ht_def, ← hs y]
    calc l ^ E y * (s y * l ^ (e y - E y))
        = (l ^ E y * l ^ (e y - E y)) * s y := by ring
      _ = l ^ e y * s y := by rw [← pow_add, Nat.add_sub_cancel' (hEe y)]
  have hS' : ∀ x ∈ S, ∃ c : ℕ → D, c 0 = 0 ∧ (∀ y, c y ∈ S) ∧
      l ^ σ • x - ∑ y ∈ Finset.range (R + 1), t y • c y ∈ Z := by
    intro x hx
    obtain ⟨c, h0, h1, h2⟩ := hS x hx
    refine ⟨c, h0, h1, ?_⟩
    simpa only [ht_def] using h2
  have hbig : ∀ y, R < y → f ∣ t y := by
    intro y hy
    refine hpow (E y) _ ?_
    rw [ht]
    exact Dvd.dvd.mul_left ((dvd_sub_right (hR y hy)).1 (hr y)) _
  have hprod : ∀ y z, ∃ u, t y * t z =
      f * u + l ^ (σ + (E (y + z) - (E y + E z))) * t (y + z) := by
    intro y z
    have hd : f ∣ t y * t z - l ^ (σ + (E (y + z) - (E y + E z))) * t (y + z) := by
      refine hpow (E y + E z) _ ?_
      obtain ⟨a, ha⟩ := hr y
      obtain ⟨b, hb⟩ := hr z
      obtain ⟨c, hc⟩ := hr (y + z)
      have hy : r y = ϖ ^ y - f * a := by rw [← ha]; ring
      have hz : r z = ϖ ^ z - f * b := by rw [← hb]; ring
      have hyz : r (y + z) = ϖ ^ (y + z) - f * c := by rw [← hc]; ring
      have e1 : l ^ (E y + E z) * (t y * t z) = (l ^ σ * r y) * (l ^ σ * r z) := by
        rw [← ht y, ← ht z]; ring
      have e2 : l ^ (E y + E z) * (l ^ (σ + (E (y + z) - (E y + E z))) * t (y + z))
          = l ^ σ * (l ^ σ * r (y + z)) := by
        rw [← ht (y + z)]
        calc l ^ (E y + E z) * (l ^ (σ + (E (y + z) - (E y + E z))) * t (y + z))
            = l ^ σ * ((l ^ (E y + E z) * l ^ (E (y + z) - (E y + E z))) * t (y + z)) := by
              rw [pow_add l σ]; ring
          _ = l ^ σ * (l ^ E (y + z) * t (y + z)) := by
              rw [← pow_add, Nat.add_sub_cancel' (hE y z)]
      rw [mul_sub, e1, e2, hy, hz, hyz]
      refine ⟨l ^ σ * l ^ σ * (c - a * ϖ ^ z - b * ϖ ^ y + f * a * b), ?_⟩
      rw [pow_add ϖ y z]
      ring
    obtain ⟨u, hu⟩ := hd
    exact ⟨u, by rw [← hu]; ring⟩
  have hkey : ∀ (n y : ℕ), R + 1 ≤ y + n → ∀ w ∈ S, (l ^ σ * t y) • w ∈ N := by
    intro n
    induction n with
    | zero =>
      intro y hy w hw
      obtain ⟨u, hu⟩ := hbig y (by omega)
      have : (l ^ σ * t y) • w = f • ((l ^ σ * u) • w) := by
        rw [hu, smul_smul]; congr 1; ring
      rw [this]
      exact hfN _ (Submodule.smul_mem _ _ (Submodule.subset_span hw))
    | succ n ih =>
      intro y hy w hw
      obtain ⟨c, hc0, hcS, hcZ⟩ := hS' w hw
      have hsplit : (l ^ σ * t y) • w =
          t y • (l ^ σ • w - ∑ z ∈ Finset.range (R + 1), t z • c z)
            + ∑ z ∈ Finset.range (R + 1), (t y * t z) • c z := by
        rw [smul_sub, Finset.smul_sum, smul_smul, mul_comm (t y) (l ^ σ)]
        simp only [smul_smul, sub_add_cancel]
      rw [hsplit]
      refine N.add_mem (hZN _ (Z.smul_mem _ hcZ)) (N.sum_mem ?_)
      intro z _
      rcases Nat.eq_zero_or_pos z with rfl | hz
      · rw [hc0, smul_zero]
        exact N.zero_mem
      · obtain ⟨u, hu⟩ := hprod y z
        have hsum : (t y * t z) • c z = f • (u • c z)
            + l ^ (E (y + z) - (E y + E z)) • ((l ^ σ * t (y + z)) • c z) := by
          rw [hu, add_smul, smul_smul, smul_smul, pow_add]
          congr 2
          ring
        rw [hsum]
        exact N.add_mem (hfN _ (Submodule.smul_mem _ _ (Submodule.subset_span (hcS z))))
          (N.smul_mem _ (ih (y + z) (by omega) _ (hcS z)))
  have hgen : ∀ x ∈ S, l ^ (2 * σ) • x ∈ N := by
    intro x hx
    obtain ⟨c, _, hcS, hcZ⟩ := hS' x hx
    have hsplit : l ^ (2 * σ) • x =
        l ^ σ • (l ^ σ • x - ∑ z ∈ Finset.range (R + 1), t z • c z)
          + ∑ z ∈ Finset.range (R + 1), (l ^ σ * t z) • c z := by
      rw [smul_sub, Finset.smul_sum, two_mul, pow_add, smul_smul]
      simp only [smul_smul, sub_add_cancel]
    rw [hsplit]
    exact N.add_mem (hZN _ (Z.smul_mem _ hcZ))
      (N.sum_mem fun z _ => hkey (R + 1) z (by omega) _ (hcS z))
  have hall : Submodule.span A S ≤ N.comap (LinearMap.lsmul A D (l ^ (2 * σ))) :=
    Submodule.span_le.2 fun x hx => hgen x hx
  intro p hp
  obtain ⟨z, hz, v, hv, hzv⟩ := Submodule.mem_sup.1 (hall hp)
  obtain ⟨p', hp', rfl⟩ := Submodule.mem_map.1 hv
  refine ⟨p', hp', ?_⟩
  have : l ^ (2 * σ) • p - f • p' = z := by
    have h2 : l ^ (2 * σ) • p = z + f • p' := hzv.symm
    rw [h2, add_sub_cancel_right]
  rw [this]
  exact hz
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DualLatticeDenominator
section
theorem UpperTheory.Reformulated.B.ExistsSmulMemOfIsLattice₂.dual_lattice_denom :
    ∀ {A : Type} [inst : CommRing A]
    [IsDomain A] {F V : Type} [inst_2 : Field F] [inst_3 : Algebra A F] [IsFractionRing A F] [inst_5 : AddCommGroup V]
    [inst_6 : _root_.Module F V] [inst_7 : _root_.Module A V] [inst_8 : IsScalarTower A F V] (Y : Submodule A V),
    Submodule.IsLattice F Y → ∀ (z : V), ∃ (a : A), a ≠ (0 : A) ∧ a • z ∈ Y := by
  intro A _ _ F V _ _ _ _ _ _ _ Y hY z
  have hz : z ∈ Submodule.span F (Y : Set V) := by
    rw [hY.span_eq_top]; exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Y.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact Y.smul_mem b hax
    · rw [mul_smul]; exact Y.smul_mem a hby
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨⟨d, hd⟩, n, hn⟩ := IsLocalization.exists_integer_multiple (nonZeroDivisors A) c
    refine ⟨a * d, mul_ne_zero ha (nonZeroDivisors.ne_zero hd), ?_⟩
    have h : (a * d) • c • x = n • a • x := by
      rw [mul_smul, ← smul_assoc d c x]
      have h2 : d • c = algebraMap A F n := hn.symm
      rw [h2, algebraMap_smul, smul_comm]
    rw [h]
    exact Y.smul_mem n hax
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DualMemSpanEvalOfFiniteDimensional
section
theorem UpperTheory.Reformulated.B.Yyc2.dual_mem_span_eval_of_finiteDimensional :
    ∀ {Y : Type} (E : Submodule ℂ (Y → ℂ)) [FiniteDimensional ℂ ↥E] (φ : Module.Dual ℂ ↥E),
      φ ∈ Submodule.span ℂ (Set.range fun (y : Y) ↦ LinearMap.proj y ∘ₗ E.subtype) := by
  intro Y E _ φ
  apply FiniteDimensional.mem_span_of_iInf_ker_le_ker
  intro x hx
  have h0 : x = 0 := by
    apply Subtype.ext
    funext y
    exact (Submodule.mem_iInf _).1 hx y
  rw [h0]
  exact Submodule.zero_mem _
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DvdOfAeval
section
open Polynomial in
theorem UpperTheory.Reformulated.B.DvdOfAeval.dvd_of_aeval :
    ∀ {K : Type} [inst : Field K] {n : ℕ}
    (g : Matrix (Fin n) (Fin n) K),
    g.charpoly.Separable →
      ∀ (p : Polynomial K),
        (Polynomial.aeval g : Polynomial K → Matrix (Fin n) (Fin n) K) p = (0 : Matrix (Fin n) (Fin n) K) →
          g.charpoly ∣ p := by
  intro K _ n g hsep p hp
  by_cases hp0 : p = 0
  · simp [hp0]
  let L := AlgebraicClosure K
  let φ : Matrix (Fin n) (Fin n) K →ₐ[K] Matrix (Fin n) (Fin n) L :=
    (Algebra.ofId K L).mapMatrix
  have hchar : (φ g).charpoly = g.charpoly.map (algebraMap K L) := by
    have := Matrix.charpoly_map g (algebraMap K L)
    exact this
  have hzero : aeval (φ g) (p.map (algebraMap K L)) = 0 := by
    rw [aeval_map_algebraMap, aeval_algHom_apply, hp, map_zero]
  have hpL : p.map (algebraMap K L) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (algebraMap K L).injective).mpr hp0
  have hcL : g.charpoly.map (algebraMap K L) ≠ 0 :=
    (g.charpoly_monic.map _).ne_zero
  rw [← Polynomial.map_dvd_map' (algebraMap K L)]
  refine (IsAlgClosed.splits _).dvd_of_roots_le_roots hcL ?_
  rw [Multiset.le_iff_subset (nodup_roots hsep.map)]
  intro r hr
  have hroot : IsRoot (φ g).charpoly r := by
    rw [hchar]
    exact (mem_roots'.mp hr).2
  have hspec : r ∈ spectrum L (φ g) := Matrix.mem_spectrum_of_isRoot_charpoly hroot
  have himg := spectrum.subset_polynomial_aeval (φ g) (p.map (algebraMap K L)) ⟨r, hspec, rfl⟩
  rw [hzero] at himg
  have hev : eval r (p.map (algebraMap K L)) = 0 := by
    by_cases h : n = 0
    · subst h
      exact absurd (isUnit_of_subsingleton _) (spectrum.mem_iff.mp hspec)
    · haveI : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero h⟩⟩
      simpa using himg
  exact (mem_roots hpL).mpr hev
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DvrOfNormIntegral
section
theorem UpperTheory.dvr_of_norm_integral :
    ∀ {l : ℕ} [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) [FiniteDimensional ℚ_[l] K], (∀ x : PadicAlgCl l, ‖x‖ ≤ 1 → IsIntegral ℤ_[l] x) → IsDiscreteValuationRing (integralClosure ℤ_[l] K) := by
  intro l _ K _ h
  have hded : IsDedekindDomain (integralClosure ℤ_[l] K) :=
    IsIntegralClosure.isDedekindDomain ℤ_[l] ℚ_[l] K _
  have hfr : IsFractionRing (integralClosure ℤ_[l] K) K :=
    IsIntegralClosure.isFractionRing_of_finite_extension ℤ_[l] ℚ_[l] K _
  have key : ∀ x : K, ‖(x : PadicAlgCl l)‖ ≤ 1 →
      IsLocalization.IsInteger (integralClosure ℤ_[l] K) x := by
    intro x hx
    have hi : IsIntegral ℤ_[l] x :=
      (isIntegral_algHom_iff (K.val.restrictScalars ℤ_[l]) Subtype.val_injective).mp (h _ hx)
    exact ⟨⟨x, hi⟩, rfl⟩
  have hval : ValuationRing (integralClosure ℤ_[l] K) := by
    rw [ValuationRing.iff_isInteger_or_isInteger _ K]
    intro x
    rcases le_total ‖(x : PadicAlgCl l)‖ 1 with hx | hx
    · exact Or.inl (key x hx)
    · refine Or.inr (key _ ?_)
      rw [IntermediateField.coe_inv, norm_inv]
      exact inv_le_one_of_one_le₀ hx
  have hinjK : Function.Injective (algebraMap ℤ_[l] K) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] K, RingHom.coe_comp]
    exact (algebraMap ℚ_[l] K).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l])
  have hinj : Function.Injective (algebraMap ℤ_[l] (integralClosure ℤ_[l] K)) := by
    intro a b hab
    exact hinjK (congrArg Subtype.val hab)
  have hnf : ¬ IsField (integralClosure ℤ_[l] K) := fun hf =>
    IsDiscreteValuationRing.not_isField ℤ_[l]
      ((Algebra.IsIntegral.isField_iff_isField hinj).mpr hf)
  exact ((IsDiscreteValuationRing.TFAE (integralClosure ℤ_[l] K) hnf).out 0 1).mpr hval
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DzExistsPrime
section
theorem UpperTheory.Reformulated.B.Qk11.dz_exists_prime :
    ∀
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) (n : ℕ),
    n ≠ (0 : ℕ) →
      (↑n : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal →
        ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ (↑p : NumberField.RingOfIntegers ℚ) ∈ v.asIdeal := by
  intro v n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    exact absurd ((Ideal.eq_top_iff_one _).2 (by simpa using h)) v.isPrime.ne_top
  | prime p hp => intro _ h; exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b iha ihb =>
    intro hab h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with h | h
    · obtain ⟨p, hp, hd, hm⟩ := iha (left_ne_zero_of_mul hab) h
      exact ⟨p, hp, hd.mul_right _, hm⟩
    · obtain ⟨p, hp, hd, hm⟩ := ihb (right_ne_zero_of_mul hab) h
      exact ⟨p, hp, hd.mul_left _, hm⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DzExistsPrimeAlt
section
theorem UpperTheory.Reformulated.B.Qk5.dz_exists_prime :
    ∀ {F : Type} [inst : Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (n : ℕ),
    n ≠ (0 : ℕ) →
      (↑n : NumberField.RingOfIntegers F) ∈ v.asIdeal →
        ∃ (p : ℕ), Nat.Prime p ∧ p ∣ n ∧ (↑p : NumberField.RingOfIntegers F) ∈ v.asIdeal := by
  intro F _ _ v n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one =>
    intro _ h
    rw [Nat.cast_one] at h
    exact absurd ((Ideal.eq_top_iff_one _).2 h) v.isPrime.ne_top
  | prime p hp => intro _ h; exact ⟨p, hp, dvd_rfl, h⟩
  | mul a b iha ihb =>
    intro hab h
    rw [Nat.cast_mul] at h
    rcases v.isPrime.mem_or_mem h with ha | hb
    · obtain ⟨p, hp, hd, hm⟩ := iha (left_ne_zero_of_mul hab) ha
      exact ⟨p, hp, hd.mul_right b, hm⟩
    · obtain ⟨p, hp, hd, hm⟩ := ihb (right_ne_zero_of_mul hab) hb
      exact ⟨p, hp, hd.mul_left a, hm⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EcField
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh13.Plc :
    (F : Type) → [Field F] → Type :=
    fun (F : Type) [Field F] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh13.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh13.Emb :
    {F : Type} → [inst : Field F] → [NumberField F] → (l : ℕ) → [Fact (Nat.Prime l)] → UpperTheory.Reformulated.B.Qh13.Plc F → Type :=
    fun {F : Type} [Field F] [NumberField F] (l : ℕ) [Fact (Nat.Prime l)] (w : UpperTheory.Reformulated.B.Qh13.Plc F) ↦
      { j : IsDedekindDomain.HeightOneSpectrum.adicCompletion F w →+* UpperTheory.Reformulated.B.Qh13.Qbar l //
        Continuous (⇑j : IsDedekindDomain.HeightOneSpectrum.adicCompletion F w → UpperTheory.Reformulated.B.Qh13.Qbar l) }

theorem UpperTheory.Reformulated.B.Qh13.ec_field :
    ∀ {L : Type} [inst : Field L] [inst_1 : NumberField L] {l : ℕ} [inst_2 : Fact (Nat.Prime l)]
      {w : UpperTheory.Reformulated.B.Qh13.Plc L} (j : UpperTheory.Reformulated.B.Qh13.Emb l w),
      ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
        FiniteDimensional ℚ_[l] ↥K ∧
          ∀ (x : IsDedekindDomain.HeightOneSpectrum.adicCompletion L w),
            ((↑j : IsDedekindDomain.HeightOneSpectrum.adicCompletion L w →+* UpperTheory.Reformulated.B.Qh13.Qbar l) :
                  IsDedekindDomain.HeightOneSpectrum.adicCompletion L w → UpperTheory.Reformulated.B.Qh13.Qbar l)
                x ∈
              K := by
  intro L _ _ l _ w j
  obtain ⟨j, hj⟩ := j
  let f : L →+* PadicAlgCl l :=
    j.comp (algebraMap L (IsDedekindDomain.HeightOneSpectrum.adicCompletion L w))
  let b := Module.finBasis ℚ L
  let K : IntermediateField ℚ_[l] (PadicAlgCl l) :=
    IntermediateField.adjoin ℚ_[l] (Set.range fun i => f (b i))
  have hK : FiniteDimensional ℚ_[l] K :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  have hf : ∀ y : L, f y ∈ K := by
    intro y
    rw [← b.sum_repr y, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem K _)
      (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
  have hc : IsClosed (K : Set (PadicAlgCl l)) :=
    haveI : FiniteDimensional ℚ_[l] K.toSubalgebra.toSubmodule := hK
    K.toSubalgebra.toSubmodule.closed_of_finiteDimensional
  refine ⟨K, hK, fun x => ?_⟩
  exact (IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap L w).induction_on x
    (hc.preimage hj) hf
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EigEx
section
theorem UpperTheory.Reformulated.B.Qi37.eig_ex :
    ∀ {k : Type} [inst : Field k] {n : ℕ} (P : Matrix (Fin n) (Fin n) k)
    (a : Fin n → k),
    P.charpoly = ∏ i : Fin n, (Polynomial.X - (Polynomial.C : k → Polynomial k) (a i)) →
      ∀ (i : Fin n), ∃ (v : Fin n → k), v ≠ (0 : Fin n → k) ∧ P.mulVec v = a i • v := by
  intro k _ n P a h i
  have hroot : P.charpoly.eval (a i) = 0 := by
    rw [h, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  rw [Matrix.eval_charpoly] at hroot
  obtain ⟨v, hv, hv0⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hroot
  refine ⟨v, hv, ?_⟩
  rw [Matrix.sub_mulVec, sub_eq_zero] at hv0
  rw [← hv0]
  ext j
  simp [Matrix.mulVec_diagonal]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EigenMem
section
namespace UpperTheory.Reformulated.B.S2

theorem eigen_mem {k M ι : Type} [Field k] [AddCommGroup M] [Module k M] (T : Module.End k M) (μ : ι → k)
    (hμ : Function.Injective μ) (Y : Submodule k M) (hY : ∀ y ∈ Y, T y ∈ Y) (s : Finset ι) (x : ι → M)
    (hx : ∀ j, T (x j) = μ j • x j) (h : ∑ j ∈ s, x j ∈ Y) : ∀ j ∈ s, x j ∈ Y := by
  classical
  induction s using Finset.induction_on generalizing x with
  | empty => intro j hj; simp at hj
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at h
    have key : ∑ j ∈ s, (μ j - μ a) • x j
        = T (x a + ∑ j ∈ s, x j) - μ a • (x a + ∑ j ∈ s, x j) := by
      simp only [map_add, map_sum, hx, smul_add, Finset.smul_sum, sub_smul, Finset.sum_sub_distrib]
      abel
    have h1 : ∑ j ∈ s, (μ j - μ a) • x j ∈ Y := by
      rw [key]
      exact Y.sub_mem (hY _ h) (Y.smul_mem _ h)
    have h2 := ih (fun j => (μ j - μ a) • x j)
      (fun j => by rw [map_smul, hx, smul_comm]) h1
    have h3 : ∀ j ∈ s, x j ∈ Y := by
      intro j hj
      have hne : μ j - μ a ≠ 0 := by
        intro e
        exact ha (hμ (sub_eq_zero.mp e) ▸ hj)
      exact (Y.smul_mem_iff hne).mp (h2 j hj)
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (Y.add_mem_iff_left (Y.sum_mem h3)).mp h
    · exact h3 j hj

end UpperTheory.Reformulated.B.S2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EigenvalueSquare
section
theorem UpperTheory.Reformulated.B.EigenvalueSquare.eig_sq :
    ∀ {A : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) ℂ},
    Star.star A * A = (1 : Matrix (Fin (3 : ℕ)) (Fin (3 : ℕ)) ℂ) →
      ∀ (r : ℝ), Polynomial.eval (↑r : ℂ) A.charpoly = (0 : ℂ) → r ^ (2 : ℕ) = (1 : ℝ) := by
  intro A hA r hr
  rw [Matrix.eval_charpoly] at hr
  obtain ⟨v, hv, hz⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hr
  have hAv : A.mulVec v = (r : ℂ) • v := by
    rw [Matrix.sub_mulVec, sub_eq_zero] at hz
    rw [← hz]
    ext i
    simp [Matrix.scalar_apply, Matrix.mulVec_diagonal]
  have h1 : star (A.mulVec v) ⬝ᵥ A.mulVec v = star v ⬝ᵥ v := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
      ← Matrix.star_eq_conjTranspose, hA, Matrix.one_mulVec]
  have h2 : star v ⬝ᵥ v ≠ 0 := by
    open ComplexOrder in
    exact fun h => hv (dotProduct_star_self_eq_zero.mp h)
  rw [hAv, star_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    ← mul_assoc] at h1
  have h3 : star (r : ℂ) * (r : ℂ) = 1 := mul_right_cancel₀ h2 (by rw [h1, one_mul])
  rw [Complex.star_def, Complex.conj_ofReal] at h3
  have h4 : r * r = 1 := by exact_mod_cast h3
  rw [sq, h4]
end

