import Formalism.GaussValuationBounds.Bundle0001

-- bundled from Formalism.GaussValuationBounds.GaussValueContraction.GaussBasic
section
noncomputable section

namespace Formalism.NOK

open scoped ENNReal

open IsDiscreteValuationRing in
theorem minLeGaussValAdd : GaussAdd := by
  intro O _ _ _ x f g
  refine le_iInf fun n => ?_
  have h1 : min (gaussV x f) (gaussV x g) ≤
      min ((((addVal O (PowerSeries.coeff n f) : ℕ∞)) : ℝ≥0∞) + ENNReal.ofReal (x * n))
        ((((addVal O (PowerSeries.coeff n g) : ℕ∞)) : ℝ≥0∞) + ENNReal.ofReal (x * n)) :=
    min_le_min (iInf_le _ n) (iInf_le _ n)
  refine h1.trans ?_
  rw [min_add_add_right, map_add]
  gcongr ?_ + _
  have h2 := addVal_add (R := O) (a := PowerSeries.coeff n f) (b := PowerSeries.coeff n g)
  rcases le_total (addVal O (PowerSeries.coeff n f)) (addVal O (PowerSeries.coeff n g)) with h | h
  · rw [min_eq_left (ENat.toENNReal_le.mpr h)]
    exact ENat.toENNReal_le.mpr (by rwa [min_eq_left h] at h2)
  · rw [min_eq_right (ENat.toENNReal_le.mpr h)]
    exact ENat.toENNReal_le.mpr (by rwa [min_eq_right h] at h2)

open IsDiscreteValuationRing in
theorem gaussValC : GaussC := by
  intro O _ _ _ x _ c
  refine le_antisymm ((iInf_le _ 0).trans (by simp)) (le_iInf fun n => ?_)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [PowerSeries.coeff_C, if_neg hn.ne', addVal_zero]
    simp

open IsDiscreteValuationRing in
theorem gaussValUnit : GaussUnit := by
  intro O _ _ _ x _ u hu
  obtain ⟨w, hw⟩ := hu.map (PowerSeries.constantCoeff (R := O))
  refine le_antisymm ((iInf_le _ 0).trans ?_) (by simp)
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, ← hw, addVal_eq_zero_of_unit]
  simp

open IsDiscreteValuationRing in
theorem gaussEis_true : GaussEis := by
  intro O _ _ _ ϖ hϖ x hx E N hN hE hdeg
  have hc : ∀ n, PowerSeries.coeff n (E : PowerSeries O) = E.coeff n := fun n => Polynomial.coeff_coe _ _
  have hv1 : addVal O ϖ = 1 := addVal_uniformizer hϖ
  have hlow : ∀ n, n < N → 1 ≤ addVal O (E.coeff n) := by
    intro n hn
    have hm : E.coeff n ∈ Ideal.span {ϖ} := hE.2 (by rw [hdeg]; exact hn)
    rw [Ideal.mem_span_singleton] at hm
    rw [← hv1]
    exact addVal_le_iff_dvd.mpr hm
  have h0 : addVal O (E.coeff 0) ≤ 1 := by
    by_contra h
    push_neg at h
    have h2 : 2 ≤ addVal O (E.coeff 0) := by
      have h6 := Order.add_one_le_of_lt h
      rwa [one_add_one_eq_two] at h6
    have h3 : addVal O (ϖ ^ 2) ≤ addVal O (E.coeff 0) := by
      rw [addVal_pow, hv1]
      simpa using h2
    apply hE.3
    rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton]
    exact addVal_le_iff_dvd.mp h3
  have hN0 : addVal O (E.coeff N) = 0 := by
    have hl := hE.1
    rw [Polynomial.leadingCoeff, hdeg, Ideal.mem_span_singleton] at hl
    have h4 : addVal O (E.coeff N) < 1 := by
      rw [← hv1]
      exact lt_of_not_ge (fun h => hl (addVal_le_iff_dvd.mp h))
    exact ENat.lt_one_iff_eq_zero.mp h4
  have hmin : ENNReal.ofReal (min 1 (x * N)) = min 1 (ENNReal.ofReal (x * N)) := by
    rw [ENNReal.ofReal_mono.map_min, ENNReal.ofReal_one]
  unfold gaussV
  rw [hmin]
  refine le_antisymm (le_min ?_ ?_) (le_iInf fun n => ?_)
  · refine (iInf_le _ 0).trans ?_
    rw [hc]
    simp only [Nat.cast_zero, mul_zero, ENNReal.ofReal_zero, add_zero]
    have h5 := ENat.toENNReal_le.mpr h0
    simpa using h5
  · refine (iInf_le _ N).trans ?_
    rw [hc, hN0]
    simp
  · rw [hc]
    rcases lt_trichotomy n N with h | rfl | h
    · refine (min_le_left _ _).trans ?_
      refine le_trans ?_ le_self_add
      have h5 := ENat.toENNReal_le.mpr (hlow n h)
      simpa using h5
    · rw [hN0]
      simp
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hdeg]; exact h), addVal_zero]
      simp

end Formalism.NOK
end
end

-- bundled from Formalism.GaussValuationBounds.GaussValueContraction.GaussMul
section
noncomputable section

namespace Formalism.NOK

open scoped ENNReal
open IsDiscreteValuationRing

section GaussMulAux

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

private def gaussTerm (x : ℝ) (f : PowerSeries O) (n : ℕ) : ℝ≥0∞ :=
  ((addVal O (PowerSeries.coeff n f) : ℕ∞) : ℝ≥0∞) + ENNReal.ofReal (x * n)

private theorem gaussV_le_term (x : ℝ) (f : PowerSeries O) (n : ℕ) : gaussV x f ≤ gaussTerm x f n := by
  unfold gaussV gaussTerm
  exact iInf_le _ n

private theorem ofReal_mul_natAdd {x : ℝ} (hx : 0 ≤ x) (i j : ℕ) :
    ENNReal.ofReal (x * ((i + j : ℕ) : ℝ)) = ENNReal.ofReal (x * i) + ENNReal.ofReal (x * j) := by
  rw [Nat.cast_add, mul_add]
  exact ENNReal.ofReal_add (mul_nonneg hx (Nat.cast_nonneg _)) (mul_nonneg hx (Nat.cast_nonneg _))

private theorem gaussV_zero (x : ℝ) : gaussV x (0 : PowerSeries O) = ⊤ := by
  unfold gaussV
  refine le_antisymm le_top (le_iInf fun n => ?_)
  exact le_of_eq (by rw [map_zero, (addVal O).map_zero, ENat.toENNReal_top, top_add])

private theorem exists_coeff_ne_zero {f : PowerSeries O} (hf : f ≠ 0) : ∃ m, PowerSeries.coeff m f ≠ 0 := by
  by_contra h
  push Not at h
  exact hf (PowerSeries.ext fun n => by rw [h n, map_zero])

private theorem enat_toENNReal_ne_top_of_ne_top {a : ℕ∞} (h : a ≠ ⊤) : (a : ℝ≥0∞) ≠ ⊤ := by
  lift a to ℕ using h
  simp

private theorem gaussTerm_ne_top {x : ℝ} {f : PowerSeries O} {n : ℕ} (h : PowerSeries.coeff n f ≠ 0) :
    gaussTerm x f n ≠ ⊤ := by
  have h1 : addVal O (PowerSeries.coeff n f) ≠ ⊤ := fun h' => h (addVal_eq_top_iff.mp h')
  unfold gaussTerm
  exact ENNReal.add_ne_top.mpr ⟨enat_toENNReal_ne_top_of_ne_top h1, ENNReal.ofReal_ne_top⟩

private theorem addVal_ne_top_of_term {x : ℝ} {f : PowerSeries O} {n : ℕ} (h : gaussTerm x f n ≠ ⊤) :
    addVal O (PowerSeries.coeff n f) ≠ ⊤ := by
  intro h'
  apply h
  unfold gaussTerm
  rw [h', ENat.toENNReal_top, top_add]

private theorem gaussV_ne_top {x : ℝ} {f : PowerSeries O} (hf : f ≠ 0) : gaussV x f ≠ ⊤ := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hf
  exact ne_top_of_le_ne_top (gaussTerm_ne_top (x := x) hm) (gaussV_le_term x f m)

private theorem gaussTerm_add_gaussTerm_eq_addVal_coeff_mul {x : ℝ} (hx : 0 ≤ x) (f g : PowerSeries O) (i j : ℕ) :
    gaussTerm x f i + gaussTerm x g j =
      ((addVal O (PowerSeries.coeff i f * PowerSeries.coeff j g) : ℕ∞) : ℝ≥0∞) +
        ENNReal.ofReal (x * ((i + j : ℕ) : ℝ)) := by
  unfold gaussTerm
  rw [(addVal O).map_mul, ENat.toENNReal_add, ofReal_mul_natAdd hx]
  exact add_add_add_comm _ _ _ _

private theorem gaussV_add_le_mul {x : ℝ} (hx : 0 ≤ x) (f g : PowerSeries O) :
    gaussV x f + gaussV x g ≤ gaussV x (f * g) := by
  have hR : gaussV x (f * g) = ⨅ n : ℕ, gaussTerm x (f * g) n := rfl
  rw [hR]
  refine le_iInf fun n => ?_
  have key : ∀ p ∈ Finset.HasAntidiagonal.antidiagonal n, gaussV x f + gaussV x g ≤
      ((addVal O (PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g) : ℕ∞) : ℝ≥0∞) +
        ENNReal.ofReal (x * n) := by
    intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    calc gaussV x f + gaussV x g ≤ gaussTerm x f p.1 + gaussTerm x g p.2 :=
          add_le_add (gaussV_le_term x f p.1) (gaussV_le_term x g p.2)
      _ = _ := by rw [gaussTerm_add_gaussTerm_eq_addVal_coeff_mul hx, hp]
  obtain ⟨p0, hp0, hmin⟩ := (Finset.HasAntidiagonal.antidiagonal n).exists_min_image
      (fun p => addVal O (PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g))
      ⟨(0, n), by simp⟩
  have hle : addVal O (PowerSeries.coeff p0.1 f * PowerSeries.coeff p0.2 g) ≤
      addVal O (PowerSeries.coeff n (f * g)) := by
    rw [PowerSeries.coeff_mul]
    exact (addVal O).map_le_sum hmin
  calc gaussV x f + gaussV x g ≤ _ := key p0 hp0
    _ ≤ ((addVal O (PowerSeries.coeff n (f * g)) : ℕ∞) : ℝ≥0∞) + ENNReal.ofReal (x * n) :=
        add_le_add (ENat.toENNReal_le.mpr hle) le_rfl

private theorem gaussV_exists_eq {x : ℝ} (hx : 0 < x) {f : PowerSeries O} (hf : f ≠ 0) :
    ∃ i, gaussTerm x f i = gaussV x f := by
  obtain ⟨m, hm⟩ := exists_coeff_ne_zero hf
  have hTtop : gaussTerm x f m ≠ ⊤ := gaussTerm_ne_top hm
  obtain ⟨N', hN'⟩ := exists_nat_gt ((gaussTerm x f m).toReal / x)
  obtain ⟨N, hmN, hN'N⟩ : ∃ N, m ≤ N ∧ N' ≤ N := ⟨max m N', le_max_left _ _, le_max_right _ _⟩
  obtain ⟨i, -, hmin⟩ := (Finset.range (N + 1)).exists_min_image (gaussTerm x f)
    ⟨m, Finset.mem_range.mpr (by omega)⟩
  refine ⟨i, le_antisymm ?_ (gaussV_le_term x f i)⟩
  have hR : gaussV x f = ⨅ n : ℕ, gaussTerm x f n := rfl
  rw [hR]
  refine le_iInf fun n => ?_
  by_cases hn : n ≤ N
  · exact hmin n (Finset.mem_range.mpr (by omega))
  · push Not at hn
    have h1 : gaussTerm x f i ≤ gaussTerm x f m := hmin m (Finset.mem_range.mpr (by omega))
    have h4 : (N' : ℝ) < n := by exact_mod_cast lt_of_le_of_lt hN'N hn
    have h3 : (gaussTerm x f m).toReal < N' * x := (div_lt_iff₀ hx).mp hN'
    have h2 : gaussTerm x f m < ENNReal.ofReal (x * n) := by
      rw [ENNReal.lt_ofReal_iff_toReal_lt hTtop]
      nlinarith
    have h5 : ENNReal.ofReal (x * n) ≤ gaussTerm x f n := by
      unfold gaussTerm
      exact le_add_self
    exact (h1.trans h2.le).trans h5

private theorem addVal_add_eq_left_of_addVal_lt {a b : O} (h : addVal O a < addVal O b) :
    addVal O (a + b) = addVal O a := by
  apply le_antisymm
  · by_contra hc
    push Not at hc
    have h1 := (addVal O).map_add (a + b) (-b)
    rw [add_neg_cancel_right, (addVal O).map_neg] at h1
    exact absurd h1 (not_le.mpr (lt_min hc h))
  · have h2 := (addVal O).map_add a b
    rwa [min_eq_left h.le] at h2

private theorem gaussV_mul_le {x : ℝ} (hx : 0 < x) {f g : PowerSeries O} (hf : f ≠ 0) (hg : g ≠ 0) :
    gaussV x (f * g) ≤ gaussV x f + gaussV x g := by
  classical
  have ef := gaussV_exists_eq hx hf
  have eg := gaussV_exists_eq hx hg
  obtain ⟨i0, hi0, ltf⟩ : ∃ i0, gaussTerm x f i0 = gaussV x f ∧
      ∀ i < i0, gaussV x f < gaussTerm x f i :=
    ⟨Nat.find ef, Nat.find_spec ef, fun i hi =>
      lt_of_le_of_ne (gaussV_le_term x f i) fun h => Nat.find_min ef hi h.symm⟩
  obtain ⟨j0, hj0, ltg⟩ : ∃ j0, gaussTerm x g j0 = gaussV x g ∧
      ∀ j < j0, gaussV x g < gaussTerm x g j :=
    ⟨Nat.find eg, Nat.find_spec eg, fun j hj =>
      lt_of_le_of_ne (gaussV_le_term x g j) fun h => Nat.find_min eg hj h.symm⟩
  have haf : addVal O (PowerSeries.coeff i0 f) ≠ ⊤ :=
    addVal_ne_top_of_term (x := x) (by rw [hi0]; exact gaussV_ne_top hf)
  have hbg : addVal O (PowerSeries.coeff j0 g) ≠ ⊤ :=
    addVal_ne_top_of_term (x := x) (by rw [hj0]; exact gaussV_ne_top hg)
  have ha : PowerSeries.coeff i0 f ≠ 0 := fun h => haf (by rw [h, (addVal O).map_zero])
  have hb : PowerSeries.coeff j0 g ≠ 0 := fun h => hbg (by rw [h, (addVal O).map_zero])
  have habtop : addVal O (PowerSeries.coeff i0 f * PowerSeries.coeff j0 g) ≠ ⊤ :=
    fun h => mul_ne_zero ha hb (addVal_eq_top_iff.mp h)
  have hlt : ∀ p ∈ (Finset.HasAntidiagonal.antidiagonal (i0 + j0)).erase (i0, j0),
      addVal O (PowerSeries.coeff i0 f * PowerSeries.coeff j0 g) <
        addVal O (PowerSeries.coeff p.1 f * PowerSeries.coeff p.2 g) := by
    intro p hp
    rw [Finset.mem_erase, Finset.HasAntidiagonal.mem_antidiagonal] at hp
    obtain ⟨hne, hsum⟩ := hp
    have hstrict : gaussTerm x f i0 + gaussTerm x g j0 < gaussTerm x f p.1 + gaussTerm x g p.2 := by
      rw [hi0, hj0]
      rcases lt_trichotomy p.1 i0 with h | h | h
      · calc gaussV x f + gaussV x g < gaussTerm x f p.1 + gaussV x g :=
            (ENNReal.add_lt_add_iff_right (gaussV_ne_top hg)).mpr (ltf _ h)
          _ ≤ _ := add_le_add le_rfl (gaussV_le_term x g p.2)
      · exact absurd (Prod.ext h (by show p.2 = j0; omega)) hne
      · have h' : p.2 < j0 := by omega
        calc gaussV x f + gaussV x g < gaussV x f + gaussTerm x g p.2 :=
            (ENNReal.add_lt_add_iff_left (gaussV_ne_top hf)).mpr (ltg _ h')
          _ ≤ _ := add_le_add (gaussV_le_term x f p.1) le_rfl
    rw [gaussTerm_add_gaussTerm_eq_addVal_coeff_mul hx.le f g i0 j0, gaussTerm_add_gaussTerm_eq_addVal_coeff_mul hx.le f g p.1 p.2, hsum]
      at hstrict
    exact ENat.toENNReal_lt.mp ((ENNReal.add_lt_add_iff_right ENNReal.ofReal_ne_top).mp hstrict)
  have hcoeff : addVal O (PowerSeries.coeff (i0 + j0) (f * g)) =
      addVal O (PowerSeries.coeff i0 f * PowerSeries.coeff j0 g) := by
    rw [PowerSeries.coeff_mul, ← Finset.add_sum_erase _ _
      (show (i0, j0) ∈ Finset.HasAntidiagonal.antidiagonal (i0 + j0) by simp)]
    exact addVal_add_eq_left_of_addVal_lt ((addVal O).map_lt_sum habtop hlt)
  calc gaussV x (f * g) ≤ gaussTerm x (f * g) (i0 + j0) := gaussV_le_term x (f * g) (i0 + j0)
    _ = gaussTerm x f i0 + gaussTerm x g j0 := by
        rw [gaussTerm_add_gaussTerm_eq_addVal_coeff_mul hx.le f g i0 j0]
        unfold gaussTerm
        rw [hcoeff]
    _ = gaussV x f + gaussV x g := by rw [hi0, hj0]

end GaussMulAux

theorem gaussValMul : GaussMul := by
  intro O _ _ _ x hx f g
  by_cases hf : f = 0
  · subst hf
    rw [zero_mul, gaussV_zero, top_add]
  by_cases hg : g = 0
  · subst hg
    rw [mul_zero, gaussV_zero, add_top]
  exact le_antisymm (gaussV_mul_le hx hf hg) (gaussV_add_le_mul hx.le f g)

end Formalism.NOK
end
end

-- bundled from Formalism.GaussValuationBounds.GaussValueContraction.LemmaCVal
section
namespace Formalism.NOK

open scoped ENNReal

section
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem cval_gaussV_one (hU : GaussUnit) {x : ℝ} (hx : 0 ≤ x) :
    gaussV x (1 : PowerSeries O) = 0 := hU O x hx 1 isUnit_one

theorem cval_gaussV_pow (hM : GaussMul) (hU : GaussUnit) {x : ℝ} (hx : 0 < x)
    (f : PowerSeries O) (n : ℕ) : gaussV x (f ^ n) = n * gaussV x f := by
  induction n with
  | zero => rw [pow_zero, cval_gaussV_one hU hx.le]; simp
  | succ n ih => rw [pow_succ, hM O x hx, ih]; push_cast; ring

theorem cval_gaussV_prod (hM : GaussMul) (hU : GaussUnit) {x : ℝ} (hx : 0 < x)
    (f : ℕ → PowerSeries O) (n : ℕ) :
    gaussV x (∏ s ∈ Finset.range n, f s) = ∑ s ∈ Finset.range n, gaussV x (f s) := by
  induction n with
  | zero => rw [Finset.prod_range_zero, Finset.sum_range_zero, cval_gaussV_one hU hx.le]
  | succ n ih => rw [Finset.prod_range_succ, Finset.sum_range_succ, hM O x hx, ih]

theorem cval_gaussV_letter (hM : GaussMul) (hU : GaussUnit) (hE : GaussEis) {ϖ : O}
    (hϖ : Irreducible ϖ) {x : ℝ} (hx : 0 < x) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (E : Polynomial O)
    (u : PowerSeries O) (s : ℕ) (hEis : E.IsEisensteinAt (Ideal.span {ϖ}))
    (hdeg : E.natDegree = ℓ ^ s) (hu : IsUnit u) :
    gaussV x (u * (E : PowerSeries O)) = ENNReal.ofReal (min 1 (x * (ℓ : ℝ) ^ s)) := by
  have h1 : 1 ≤ ℓ ^ s := Nat.one_le_pow _ _ (by omega)
  rw [hM O x hx, hU O x hx.le u hu, zero_add, hE O ϖ hϖ x hx.le E (ℓ ^ s) h1 hEis hdeg,
    Nat.cast_pow]

theorem cval_gaussV_C_pow (hC : GaussC) {ϖ : O} (hϖ : Irreducible ϖ) {x : ℝ} (hx : 0 ≤ x)
    (n : ℕ) : gaussV x (PowerSeries.C (ϖ ^ n)) = (n : ℝ≥0∞) := by
  rw [hC O x hx, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]
  simp

end

section
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem cval_step (hM : GaussMul) (hA : GaussAdd) (hC : GaussC) (hU : GaussUnit)
    (hE : GaussEis) {ϖ : O} (hϖ : Irreducible ϖ) {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (E : ℕ → Polynomial O) (u : ℕ → PowerSeries O)
    (hEis : ∀ s, (E s).IsEisensteinAt (Ideal.span {ϖ})) (hdeg : ∀ s, (E s).natDegree = ℓ ^ s)
    (hu : ∀ s, IsUnit (u s)) {ell g a b₀ b₁ s₀ s₁ k : ℕ} (hs : s₀ < s₁)
    (hmem : PowerSeries.C (ϖ ^ a) *
        (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
        (u s₀ * (E s₀ : PowerSeries O)) ^ b₀ ∈
      Ideal.span {PowerSeries.C (ϖ ^ k), (u s₁ * (E s₁ : PowerSeries O)) ^ b₁})
    {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ ≤ 1)
    (hlt : (a : ℝ) + 2 * g * ell + b₀ / ℓ * τ < b₁ * τ) :
    (k : ℝ) ≤ (a : ℝ) + 2 * g * ell + b₀ / ℓ * τ := by
  have hℓ1 : 1 ≤ ℓ := by omega
  have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓpos : (0 : ℝ) < ℓ := by linarith
  have hℓne : (ℓ : ℝ) ≠ 0 := hℓpos.ne'
  have hpow1 : (0 : ℝ) < (ℓ : ℝ) ^ s₁ := pow_pos hℓpos _
  have hpow2 : (ℓ : ℝ) ^ s₀ * ℓ ≤ (ℓ : ℝ) ^ s₁ := by
    rw [← pow_succ]; exact pow_le_pow_right₀ (by linarith) (by omega)
  set x : ℝ := τ / (ℓ : ℝ) ^ s₁ with hxdef
  have hx : 0 < x := div_pos hτ0 hpow1
  have hx1 : x * (ℓ : ℝ) ^ s₁ = τ := by rw [hxdef]; field_simp
  have hx0 : x * (ℓ : ℝ) ^ s₀ ≤ τ / ℓ := by
    rw [le_div_iff₀ hℓpos]
    calc x * (ℓ : ℝ) ^ s₀ * ℓ = x * ((ℓ : ℝ) ^ s₀ * ℓ) := by ring
      _ ≤ x * (ℓ : ℝ) ^ s₁ := mul_le_mul_of_nonneg_left hpow2 hx.le
      _ = τ := hx1
  have hVF : ∀ s, gaussV x (u s * (E s : PowerSeries O)) =
      ENNReal.ofReal (min 1 (x * (ℓ : ℝ) ^ s)) := fun s =>
    cval_gaussV_letter hM hU hE hϖ hx hℓ1 (E s) (u s) s (hEis s) (hdeg s) (hu s)
  have hprod : gaussV x ((∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2)
      ≤ ((2 * g * ell : ℕ) : ℝ≥0∞) := by
    rw [cval_gaussV_pow hM hU hx, cval_gaussV_prod hM hU hx]
    have hterm : ∀ s ∈ Finset.range ell,
        gaussV x ((u s * (E s : PowerSeries O)) ^ g) ≤ (g : ℝ≥0∞) := by
      intro s _
      rw [cval_gaussV_pow hM hU hx, hVF s]
      calc (g : ℝ≥0∞) * ENNReal.ofReal (min 1 (x * (ℓ : ℝ) ^ s)) ≤ (g : ℝ≥0∞) * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [← ENNReal.ofReal_one]
            exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
        _ = g := mul_one _
    calc ((2 : ℕ) : ℝ≥0∞) * ∑ s ∈ Finset.range ell, gaussV x ((u s * (E s : PowerSeries O)) ^ g)
        ≤ ((2 : ℕ) : ℝ≥0∞) * ∑ s ∈ Finset.range ell, (g : ℝ≥0∞) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
      _ = ((2 * g * ell : ℕ) : ℝ≥0∞) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; push_cast <;> ring
  have hR0 : 0 ≤ (a : ℝ) + 2 * g * ell + b₀ / ℓ * τ :=
    add_nonneg (by positivity) (mul_nonneg (by positivity) hτ0.le)
  have hR : (a : ℝ≥0∞) + ((2 * g * ell : ℕ) : ℝ≥0∞) + (b₀ : ℝ≥0∞) * ENNReal.ofReal (τ / ℓ)
      = ENNReal.ofReal ((a : ℝ) + 2 * g * ell + b₀ / ℓ * τ) := by
    have e1 : (a : ℝ) + 2 * g * ell + b₀ / ℓ * τ
        = ((a + 2 * g * ell : ℕ) : ℝ) + (b₀ : ℝ) * (τ / ℓ) := by
      push_cast; ring
    rw [e1, ENNReal.ofReal_add (Nat.cast_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (div_nonneg hτ0.le hℓpos.le)),
      ENNReal.ofReal_natCast, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    push_cast <;> ring
  have hup : gaussV x (PowerSeries.C (ϖ ^ a) *
        (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
        (u s₀ * (E s₀ : PowerSeries O)) ^ b₀)
      ≤ ENNReal.ofReal ((a : ℝ) + 2 * g * ell + b₀ / ℓ * τ) := by
    rw [← hR, hM O x hx, hM O x hx, cval_gaussV_C_pow hC hϖ hx.le,
      cval_gaussV_pow hM hU hx (u s₀ * (E s₀ : PowerSeries O)) b₀, hVF s₀]
    exact add_le_add (add_le_add le_rfl hprod)
      (mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ((min_le_right _ _).trans hx0)) (by positivity))
  have hQ : gaussV x ((u s₁ * (E s₁ : PowerSeries O)) ^ b₁) = ENNReal.ofReal (b₁ * τ) := by
    rw [cval_gaussV_pow hM hU hx, hVF s₁, hx1, min_eq_right hτ1,
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  obtain ⟨c, e, hce⟩ := Ideal.mem_span_pair.mp hmem
  have hlow : min (k : ℝ≥0∞) (ENNReal.ofReal (b₁ * τ)) ≤ gaussV x (PowerSeries.C (ϖ ^ a) *
        (∏ s ∈ Finset.range ell, (u s * (E s : PowerSeries O)) ^ g) ^ 2 *
        (u s₀ * (E s₀ : PowerSeries O)) ^ b₀) := by
    rw [← hce]
    refine le_trans ?_ (hA O x _ _)
    rw [hM O x hx c, hM O x hx e, cval_gaussV_C_pow hC hϖ hx.le, hQ]
    exact min_le_min le_add_self le_add_self
  have hRlt : ENNReal.ofReal ((a : ℝ) + 2 * g * ell + b₀ / ℓ * τ) < ENNReal.ofReal (b₁ * τ) :=
    (ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt hR0 hlt)).mpr hlt
  rcases min_le_iff.mp (hlow.trans hup) with h | h
  · rw [← ENNReal.ofReal_natCast] at h
    exact (ENNReal.ofReal_le_ofReal_iff hR0).mp h
  · exact absurd h (not_le.mpr hRlt)

end

theorem lemmaCVal_of (hM : GaussMul) (hA : GaussAdd) (hC : GaussC) (hU : GaussUnit)
    (hE : GaussEis) : LemmaCVal := by
  intro O _ _ _ ϖ hϖ ℓ hℓ E u hEis hdeg hu ell g a b₀ b₁ s₀ s₁ k hs h2A hb hmem
  have key : ∀ τ : ℝ, 0 < τ → τ ≤ 1 → (a : ℝ) + 2 * g * ell + b₀ / ℓ * τ < b₁ * τ →
      (k : ℝ) ≤ (a : ℝ) + 2 * g * ell + b₀ / ℓ * τ := fun τ hτ0 hτ1 hlt =>
    cval_step hM hA hC hU hE hϖ hℓ E u hEis hdeg hu hs hmem
      hτ0 hτ1 hlt
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast (by omega : 0 < ℓ)
  have hc0 : 0 ≤ (b₀ : ℝ) / ℓ := by positivity
  have hcB : 2 * ((b₀ : ℝ) / ℓ) ≤ b₁ := by
    have hb' : (2 : ℝ) * b₀ ≤ ℓ * b₁ := by exact_mod_cast hb
    rw [← mul_div_assoc, div_le_iff₀ hℓpos]
    linarith
  have hA0 : 0 ≤ (a : ℝ) + 2 * g * ell := by positivity
  generalize (a : ℝ) + 2 * g * ell = A at key h2A hA0 ⊢
  generalize (b₀ : ℝ) / ℓ = c at key hc0 hcB ⊢
  generalize (b₁ : ℝ) = B at key hcB h2A ⊢
  have hD : 0 < B - c := by linarith
  have hτs : A / (B - c) < 1 := by rw [div_lt_one hD]; linarith
  have hτs0 : 0 ≤ A / (B - c) := div_nonneg hA0 hD.le
  have heq : A * B / (B - c) = A + c * (A / (B - c)) := by
    have hDne : B - c ≠ 0 := hD.ne'
    field_simp; ring
  have h1 : (k : ℝ) ≤ A * B / (B - c) := by
    rw [heq]
    apply le_of_forall_pos_le_add
    intro ε hε
    have hc1 : (0 : ℝ) < c + 1 := by linarith
    have hδ : 0 < ε / (c + 1) := div_pos hε hc1
    have hτgt : A / (B - c) < min 1 (A / (B - c) + ε / (c + 1)) := lt_min hτs (by linarith)
    have hτ0 : 0 < min 1 (A / (B - c) + ε / (c + 1)) := lt_of_le_of_lt hτs0 hτgt
    have hτ1 : min 1 (A / (B - c) + ε / (c + 1)) ≤ 1 := min_le_left _ _
    have hτle : min 1 (A / (B - c) + ε / (c + 1)) ≤ A / (B - c) + ε / (c + 1) := min_le_right _ _
    have hlt : A + c * min 1 (A / (B - c) + ε / (c + 1)) < B * min 1 (A / (B - c) + ε / (c + 1)) := by
      have := (div_lt_iff₀ hD).mp hτgt
      linarith
    have hk := key _ hτ0 hτ1 hlt
    have hcδ : c * (ε / (c + 1)) ≤ ε := by
      calc c * (ε / (c + 1)) ≤ (c + 1) * (ε / (c + 1)) :=
            mul_le_mul_of_nonneg_right (by linarith) hδ.le
        _ = ε := by field_simp
    have hm := mul_le_mul_of_nonneg_left hτle hc0
    calc (k : ℝ) ≤ A + c * min 1 (A / (B - c) + ε / (c + 1)) := hk
      _ ≤ A + c * (A / (B - c) + ε / (c + 1)) := by linarith
      _ = A + c * (A / (B - c)) + c * (ε / (c + 1)) := by ring
      _ ≤ A + c * (A / (B - c)) + ε := by linarith
  refine ⟨h1, h1.trans ?_⟩
  rw [div_le_iff₀ hD]
  nlinarith [mul_nonneg hA0 (sub_nonneg.mpr hcB)]

end Formalism.NOK
end

