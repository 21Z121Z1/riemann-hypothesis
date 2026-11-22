import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemMinimalPrimesIff
section
theorem UpperTheory.Reformulated.B.Yhd1.mem_minimalPrimes_iff.{u_1} :
    ∀ {A : Type u_1} [inst : CommRing A] [IsDomain A] [IsNoetherianRing A] {z : A},
      z ≠ (0 : A) → ∀ (W : Ideal A), W ∈ (Ideal.span {z}).minimalPrimes ↔ W.IsPrime ∧ W.height = (1 : ℕ∞) ∧ z ∈ W := by
  intro A _ _ _ z hz
  have key : ∀ P : Ideal A, P.IsPrime → z ∈ P → (1 : ℕ∞) ≤ P.height := by
    intro P hP hzP
    have hlt : (⊥ : Ideal A) < P := by
      refine bot_lt_iff_ne_bot.mpr fun h => hz ?_
      rw [h] at hzP
      exact Ideal.mem_bot.mp hzP
    have := Ideal.height_add_one_le_of_lt_of_isPrime hlt
    exact le_trans le_add_self this
  intro W
  constructor
  · intro hW
    have hP : W.IsPrime := hW.1.1
    have hzW : z ∈ W := hW.1.2 (Ideal.mem_span_singleton_self z)
    exact ⟨hP, le_antisymm
      (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hW) (key W hP hzW), hzW⟩
  · rintro ⟨hP, hh, hzW⟩
    obtain ⟨P, hPm, hPW⟩ := Ideal.exists_minimalPrimes_le
      ((Ideal.span_singleton_le_iff_mem W).mpr hzW)
    have hP' : P.IsPrime := hPm.1.1
    have hzP : z ∈ P := hPm.1.2 (Ideal.mem_span_singleton_self z)
    rcases hPW.eq_or_lt with h | h
    · exact h ▸ hPm
    · exfalso
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime h
      have h2 : (1 : ℕ∞) + 1 ≤ 1 := by
        calc (1 : ℕ∞) + 1 ≤ P.height + 1 := by gcongr; exact key P hP' hzP
          _ ≤ W.height := h1
          _ = 1 := hh
      exact absurd h2 (by decide)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemOfAdjoinTop
section
theorem UpperTheory.Reformulated.B.Qj1.mem_of_adjoin_top.{u_2} :
    ∀ {l : ℕ}
    [inst : Fact (Nat.Prime l)] {K : Type u_2} [inst_1 : Field K] [inst_2 : CharZero K] {S : Set K},
    Algebra.adjoin ℚ S = ⊤ →
      ∀ (j : K →+* PadicAlgCl l) (F : IntermediateField ℚ_[l] (PadicAlgCl l)),
        (∀ s ∈ S, (j : K → PadicAlgCl l) s ∈ F) → ∀ (x : K), (j : K → PadicAlgCl l) x ∈ F := by
  intro l _ K _ _ S hS j F hF x
  have hx : x ∈ Algebra.adjoin ℚ S := hS ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact hF y hy
  | algebraMap q =>
    rw [eq_ratCast, map_ratCast]
    exact SubfieldClass.ratCast_mem F q
  | add y z _ _ hy hz =>
    rw [map_add]
    exact add_mem hy hz
  | mul y z _ _ hy hz =>
    rw [map_mul]
    exact mul_mem hy hz
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemOfCoeff
section
namespace UpperTheory.Reformulated.B.S1

theorem mem_of_coeff {O σ ι : Type} [CommRing O] (I : Ideal (MvPowerSeries σ O)) (e : ι → σ) (s : Finset ι)
    (hs : ∀ i ∈ s, MvPowerSeries.X (e i) ∈ I) (f : MvPowerSeries σ O)
    (hf : ∀ n : σ →₀ ℕ, (∀ i ∈ s, n (e i) = 0) → MvPowerSeries.coeff n f = 0) : f ∈ I := by
  classical
  induction s using Finset.induction_on generalizing f with
  | empty =>
    have h0 : f = 0 := by
      ext n
      simpa using hf n (by simp)
    rw [h0]
    exact I.zero_mem
  | insert a s _ ih =>
    let g : MvPowerSeries σ O := fun n => if n (e a) = 0 then MvPowerSeries.coeff n f else 0
    have hg : ∀ n : σ →₀ ℕ, MvPowerSeries.coeff n g =
        if n (e a) = 0 then MvPowerSeries.coeff n f else 0 := fun _ => rfl
    have hgI : g ∈ I := by
      refine ih (fun i hi => hs i (Finset.mem_insert_of_mem hi)) g ?_
      intro n hn
      rw [hg]
      split_ifs with h
      · refine hf n ?_
        intro i hi
        rcases Finset.mem_insert.mp hi with rfl | hi
        · exact h
        · exact hn i hi
      · rfl
    have hd : (MvPowerSeries.X (e a) : MvPowerSeries σ O) ∣ f - g := by
      rw [MvPowerSeries.X_dvd_iff]
      intro n hn
      rw [map_sub, hg, if_pos hn, sub_self]
    have hfg : f - g ∈ I :=
      Ideal.mem_of_dvd I hd (hs a (Finset.mem_insert_self a s))
    simpa using I.add_mem hfg hgI

end UpperTheory.Reformulated.B.S1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemPow
section
namespace PrecompleteLimitOfPowDvd

private lemma memPow {R : Type*} [CommRing R] (π x : R) (m : ℕ) :
    x ∈ ((Ideal.span {π}) ^ m • (⊤ : Submodule R R)) ↔ π ^ m ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

private lemma tele {R : Type*} [CommRing R] (π : R) (f : ℕ → R)
    (h : ∀ n : ℕ, π ^ n ∣ f (n + 1) - f n) (m : ℕ) : ∀ k : ℕ, π ^ m ∣ f (m + k) - f m := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : π ^ m ∣ f (m + k + 1) - f (m + k) :=
      (pow_dvd_pow π (Nat.le_add_right m k)).trans (h (m + k))
    have : f (m + (k + 1)) - f m = (f (m + k + 1) - f (m + k)) + (f (m + k) - f m) := by
      rw [← add_assoc]; ring
    rw [this]; exact dvd_add h2 ih

end PrecompleteLimitOfPowDvd

theorem UpperTheory.Reformulated.B.Yra6.main.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] {π : R},
      IsPrecomplete (Ideal.span {π}) R →
        ∀ (f : ℕ → R), (∀ (n : ℕ), π ^ n ∣ f (n + (1 : ℕ)) - f n) → ∃ (L : R), ∀ (n : ℕ), π ^ n ∣ f n - L := by
  intro R _ π hP f h
  obtain ⟨L, hL⟩ := hP.prec' f (by
    intro m n hmn
    rw [SModEq.sub_mem, PrecompleteLimitOfPowDvd.memPow]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have := PrecompleteLimitOfPowDvd.tele π f h m k
    rw [← neg_sub]; exact (dvd_neg).2 this)
  refine ⟨L, fun n => ?_⟩
  have := hL n
  rw [SModEq.sub_mem, PrecompleteLimitOfPowDvd.memPow] at this
  exact this
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemRealOfSq
section
theorem UpperTheory.Reformulated.B.Qh55.mem_real_of_sq :
    ∀ {Y : Type} [inst : Field Y] {δ : Y}
    {q : ℕ}, (0 : ℕ) < q → δ ^ (2 : ℕ) = (↑q : Y) → δ ∈ NumberField.maximalRealSubfield Y := by
  intro Y _ δ q hq h
  rw [NumberField.mem_maximalRealSubfield_iff]
  intro φ
  have h1 : (φ δ) ^ 2 = (q : ℂ) := by rw [← map_pow, h, map_natCast]
  have h2 : (φ δ) ^ 2 = ((Real.sqrt q : ℝ) : ℂ) ^ 2 := by
    rw [h1, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg q), Complex.ofReal_natCast]
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2 with h3 | h3
  · rw [h3, Complex.star_def, Complex.conj_ofReal]
  · rw [h3, star_neg, Complex.star_def, Complex.conj_ofReal]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemSpanVariable
section
theorem UpperTheory.Reformulated.B.MemSpanVariable.mem_span_X :
    ∀ {O σ : Type} [inst : CommRing O] [Fintype σ]
    (f : MvPowerSeries σ O),
    (MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) f = (0 : O) → f ∈ Ideal.span (Set.range MvPowerSeries.X) := by
  intro O σ _ _ f hf
  classical
  have hc : ∀ n : σ →₀ ℕ, ∃ o : Option σ, n ≠ 0 → ∃ i, o = some i ∧ n i ≠ 0 := by
    intro n
    by_cases h : n = 0
    · exact ⟨none, fun h' => absurd h h'⟩
    · obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp h
      exact ⟨some i, fun _ => ⟨i, rfl, hi⟩⟩
  choose c hc using hc
  let g : σ → MvPowerSeries σ O := fun i m =>
    if c (m + Finsupp.single i 1) = some i then
      MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0
  have hg : ∀ i m, MvPowerSeries.coeff m (g i) =
      if c (m + Finsupp.single i 1) = some i then
        MvPowerSeries.coeff (m + Finsupp.single i 1) f else 0 := fun _ _ => rfl
  have key : ∀ (i : σ) (n : σ →₀ ℕ), MvPowerSeries.coeff n (MvPowerSeries.X i * g i) =
      if n i ≠ 0 ∧ c n = some i then MvPowerSeries.coeff n f else 0 := by
    intro i n
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
    by_cases h : n i = 0
    · have h' : ¬ Finsupp.single i 1 ≤ n := by
        rw [Finsupp.single_le_iff]; omega
      rw [if_neg h', if_neg (fun hh => hh.1 h)]
    · have h' : Finsupp.single i 1 ≤ n := by
        rw [Finsupp.single_le_iff]; omega
      rw [if_pos h', one_mul, hg, tsub_add_cancel_of_le h']
      simp [h]
  have hsum : f = ∑ i, MvPowerSeries.X i * g i := by
    ext n
    rw [map_sum]
    simp only [key]
    by_cases h : n = 0
    · subst h
      simpa using hf
    · obtain ⟨i, hi, hn⟩ := hc n h
      rw [Finset.sum_eq_single i]
      · rw [if_pos ⟨hn, hi⟩]
      · intro j _ hj
        rw [if_neg]
        rintro ⟨_, h2⟩
        exact hj (Option.some.inj (h2.symm.trans hi))
      · intro h2
        exact absurd (Finset.mem_univ i) h2
  rw [hsum]
  exact Ideal.sum_mem _ fun i _ =>
    Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemSpanX
section
theorem UpperTheory.Reformulated.B.MemSpanMonomial.mem_span_X :
    ∀ {O σ : Type} [inst : CommRing O] [inst_1 : Fintype σ]
    (f : MvPowerSeries σ O),
    (MvPowerSeries.constantCoeff : MvPowerSeries σ O → O) f = (0 : O) →
      ∃ (g : σ → MvPowerSeries σ O), f = ∑ i : σ, MvPowerSeries.X i * g i := by
  intro O σ _ _ f hf
  classical
  have hex : ∀ m : σ →₀ ℕ, m ≠ 0 → ∃ i, m i ≠ 0 := by
    intro m hm
    by_contra h
    apply hm
    ext i
    by_contra hi
    exact h ⟨i, hi⟩
  choose c hc using hex
  let p : (σ →₀ ℕ) → σ → Prop := fun m i => ∃ hm : m ≠ 0, c m hm = i
  let g : σ → MvPowerSeries σ O := fun i n =>
    if p (n + Finsupp.single i 1) i then MvPowerSeries.coeff (n + Finsupp.single i 1) f else 0
  have hg : ∀ i n, MvPowerSeries.coeff n (g i) =
      if p (n + Finsupp.single i 1) i then MvPowerSeries.coeff (n + Finsupp.single i 1) f
      else 0 := fun _ _ => rfl
  have key : ∀ i m, MvPowerSeries.coeff m (MvPowerSeries.X i * g i) =
      if p m i then MvPowerSeries.coeff m f else 0 := by
    intro i m
    rw [MvPowerSeries.X_def, MvPowerSeries.coeff_monomial_mul]
    by_cases h : Finsupp.single i 1 ≤ m
    · rw [if_pos h, one_mul, hg, tsub_add_cancel_of_le h]
    · rw [if_neg h, if_neg]
      rintro ⟨hm, hi⟩
      apply h
      rw [Finsupp.single_le_iff, ← hi]
      exact Nat.one_le_iff_ne_zero.mpr (hc m hm)
  refine ⟨g, ?_⟩
  ext m
  rw [map_sum]
  simp only [key]
  by_cases hm : m = 0
  · subst hm
    rw [MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hf]
    simp
  · rw [Finset.sum_eq_single (c m hm)]
    · rw [if_pos ⟨hm, rfl⟩]
    · intro j _ hj
      rw [if_neg]
      rintro ⟨_, h⟩
      exact hj h.symm
    · intro h
      exact absurd (Finset.mem_univ _) h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MemWOfNorm
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi32.kb :
    (p : ℕ) → [Fact (Nat.Prime p)] → Type :=
    fun (p : ℕ) [Fact (Nat.Prime p)] ↦ AlgebraicClosure (ZMod p)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi32.WW :
    (p : ℕ) → [Fact (Nat.Prime p)] → Type :=
    fun (p : ℕ) [Fact (Nat.Prime p)] ↦ WittVector p (UpperTheory.Reformulated.B.Qi32.kb p)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi32.K0 :
    (p : ℕ) → [Fact (Nat.Prime p)] → Type :=
    fun (p : ℕ) [Fact (Nat.Prime p)] ↦ FractionRing (UpperTheory.Reformulated.B.Qi32.WW p)

theorem UpperTheory.Reformulated.B.Qi32.mem_W_of_norm :
    ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] (i0 : UpperTheory.Reformulated.B.Qi32.K0 p →+* ℂ_[p]),
      (∀ (x : UpperTheory.Reformulated.B.Qi32.WW p),
          ‖(i0 : UpperTheory.Reformulated.B.Qi32.K0 p → ℂ_[p])
                ((Algebra.algebraMap (UpperTheory.Reformulated.B.Qi32.WW p) (UpperTheory.Reformulated.B.Qi32.K0 p) :
                    UpperTheory.Reformulated.B.Qi32.WW p → UpperTheory.Reformulated.B.Qi32.K0 p)
                  x)‖ ≤
            (1 : ℝ)) →
        ∀ (x : UpperTheory.Reformulated.B.Qi32.K0 p),
          ‖(i0 : UpperTheory.Reformulated.B.Qi32.K0 p → ℂ_[p]) x‖ ≤ (1 : ℝ) →
            ∃ (w : UpperTheory.Reformulated.B.Qi32.WW p),
              (Algebra.algebraMap (UpperTheory.Reformulated.B.Qi32.WW p) (UpperTheory.Reformulated.B.Qi32.K0 p) :
                    UpperTheory.Reformulated.B.Qi32.WW p → UpperTheory.Reformulated.B.Qi32.K0 p)
                  w =
                x := by
  intro p inst i0 hW x hx
  have hp : ‖(p : ℂ_[p])‖ < 1 := by
    have h : (p : ℂ_[p]) = algebraMap ℚ_[p] ℂ_[p] (p : ℚ_[p]) := (map_natCast _ p).symm
    rw [h, norm_algebraMap']
    exact Padic.norm_p_lt_one
  rcases ValuationRing.isInteger_or_isInteger (UpperTheory.Reformulated.B.Qi32.WW p) x with h | ⟨w, hw⟩
  · exact h
  rcases eq_or_ne x 0 with rfl | hx0
  · exact ⟨0, map_zero _⟩
  by_cases hu : IsUnit w
  · obtain ⟨u, rfl⟩ := hu
    refine ⟨((u⁻¹ : (UpperTheory.Reformulated.B.Qi32.WW p)ˣ) : UpperTheory.Reformulated.B.Qi32.WW p), ?_⟩
    rw [map_units_inv, hw, inv_inv]
  · exfalso
    have hirr : Irreducible (p : UpperTheory.Reformulated.B.Qi32.WW p) := WittVector.irreducible p
    have hmem : w ∈ IsLocalRing.maximalIdeal (UpperTheory.Reformulated.B.Qi32.WW p) := hu
    rw [hirr.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨v, rfl⟩ := hmem
    have h1 : ‖i0 x‖ * ‖i0 x⁻¹‖ = 1 := by
      rw [← norm_mul, ← map_mul, mul_inv_cancel₀ hx0, map_one, norm_one]
    have h2 : ‖i0 x⁻¹‖ < 1 := by
      rw [← hw, map_mul, map_mul, map_natCast, map_natCast, norm_mul]
      exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) (hW v)) hp
    have h3 : ‖i0 x‖ * ‖i0 x⁻¹‖ ≤ ‖i0 x⁻¹‖ := mul_le_of_le_one_left (norm_nonneg _) hx
    linarith
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MinimalPrimesMap
section
private lemma UpperTheory.Reformulated.B.MinimalPrimesMap.map_lt_map {A : Type} [CommRing A] {P I J : Ideal A}
    (hI : P ≤ I) (h : I < J) :
    I.map (Ideal.Quotient.mk P) < J.map (Ideal.Quotient.mk P) := by
  refine (Ideal.map_mono h.le).lt_of_not_ge fun e => h.not_ge ?_
  have e' := Ideal.comap_mono (f := Ideal.Quotient.mk P) e
  rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker, sup_eq_left.mpr hI,
    sup_eq_left.mpr (hI.trans h.le)] at e'
  exact e'

theorem UpperTheory.Reformulated.B.MinimalPrimesMap.eq_or_eq_of_mem_minimalPrimes :
    ∀ {A : Type} [inst : CommRing A] [IsNoetherianRing A]
    {P Q W : Ideal A} [hP : P.IsPrime] [hQ : Q.IsPrime] {s : A},
    W ∈ (P ⊔ Ideal.span {s}).minimalPrimes → P ≤ Q → Q ≤ W → Q = P ∨ Q = W := by
  intro A _ _ P Q W hP hQ s hW hPQ hQW
  by_contra hne
  rw [not_or] at hne
  have hW' : W.IsPrime := hW.1.1
  have hprime : ∀ I : Ideal A, I.IsPrime → P ≤ I → (I.map (Ideal.Quotient.mk P)).IsPrime :=
    fun I hI hle => Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker])
  have i1 := hprime P hP le_rfl
  have i2 := hprime Q hQ hPQ
  have i3 := hprime W hW' (hPQ.trans hQW)
  have h1 := Ideal.height_add_one_le_of_lt_of_isPrime
    (UpperTheory.Reformulated.B.MinimalPrimesMap.map_lt_map le_rfl (lt_of_le_of_ne hPQ (Ne.symm hne.1)))
  have h2 := Ideal.height_add_one_le_of_lt_of_isPrime
    (UpperTheory.Reformulated.B.MinimalPrimesMap.map_lt_map hPQ (lt_of_le_of_ne hQW hne.2))
  have h3 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have h4 : (1 : ℕ∞) ≤ (Q.map (Ideal.Quotient.mk P)).height := le_add_self.trans h1
  have h5 : (1 : ℕ∞) + 1 ≤ 1 := (add_le_add h4 le_rfl).trans (h2.trans h3)
  exact absurd h5 (by decide)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MinorDeterminants
section
theorem UpperTheory.Reformulated.B.MinorDeterminants.aux1 :
    ∀ {N : ℕ} (J : Finset (Fin N)), J.card = J.card := by
  intro N J
  rfl

noncomputable def UpperTheory.Reformulated.B.MinorDeterminants.minorIJ :
    {R : Type} → [CommRing R] → {N : ℕ} → Matrix (Fin N) (Fin N) R → Finset (Fin N) → Finset (Fin N) → R :=
    fun {R : Type} [CommRing R] {N : ℕ} (h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) ↦
      if e : I.card = J.card then
        (h.submatrix (⇑(I.orderEmbOfFin e) : Fin J.card → Fin N)
            (⇑(J.orderEmbOfFin (UpperTheory.Reformulated.B.MinorDeterminants.aux1 J)) : Fin J.card → Fin N)).det
      else (0 : R)

theorem UpperTheory.Reformulated.B.MinorDeterminants.main :
    ∀ {N : ℕ} (C : Matrix (Fin N) (Fin N) ℂ) (S : Finset (Fin N)) (f : Fin S.card → Fin N),
      Function.Injective f →
        UpperTheory.Reformulated.B.MinorDeterminants.minorIJ C (Finset.image f Finset.univ) S = (0 : ℂ) →
          (C.submatrix f (⇑(S.orderEmbOfFin rfl) : Fin S.card → Fin N)).det = (0 : ℂ) := by
  intro N C S f hf h0
  have e : (Finset.image f Finset.univ).card = S.card := by
    rw [Finset.card_image_of_injective _ hf]; simp
  unfold UpperTheory.Reformulated.B.MinorDeterminants.minorIJ at h0
  rw [dif_pos e] at h0
  set I := Finset.image f Finset.univ with hI
  have mem : ∀ i, f i ∈ I := fun i => by simp [hI]
  let σf : Fin S.card → Fin S.card := fun i => (I.orderIsoOfFin e).symm ⟨f i, mem i⟩
  have hσ : Function.Injective σf := by
    intro a b hab
    apply hf
    have := congrArg (fun x => ((I.orderIsoOfFin e x : I) : Fin N)) hab
    simpa [σf] using this
  let σ : Equiv.Perm (Fin S.card) := Equiv.ofBijective σf hσ.bijective_of_finite
  have hfg : f = (⇑(I.orderEmbOfFin e)) ∘ σ := by
    funext i
    simp only [Function.comp, σ, Equiv.ofBijective_apply, σf]
    rw [← Finset.coe_orderIsoOfFin_apply]
    simp
  have key : C.submatrix f (⇑(S.orderEmbOfFin rfl)) =
      (C.submatrix (⇑(I.orderEmbOfFin e)) (⇑(S.orderEmbOfFin (UpperTheory.Reformulated.B.MinorDeterminants.aux1 S)))).submatrix σ id := by
    rw [hfg, Matrix.submatrix_submatrix]
    rfl
  rw [key, Matrix.det_permute, h0, mul_zero]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MirabolicColumnBlock
section
namespace UpperTheory.Reformulated.B.MirabolicColumnBlock

theorem conj_diagonal {K : Type} [Field K] {n : ℕ} (d : Fin n → K) (hd : Function.Injective d)
    (M : Matrix (Fin n) (Fin n) K) (hM : M.charpoly = ∏ a, (Polynomial.X - Polynomial.C (d a))) :
    ∃ h : GL (Fin n) K, ((h⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M * h = Matrix.diagonal d := by
  have hev : ∀ a, ∃ v : Fin n → K, Module.End.HasEigenvector (Matrix.toLin' M) (d a) v := by
    intro a
    apply Module.End.HasEigenvalue.exists_hasEigenvector
    rw [Module.End.hasEigenvalue_iff_isRoot_charpoly, Matrix.charpoly_toLin', hM,
      Polynomial.IsRoot.def, Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ a) (by simp)
  choose v hv using hev
  have hli : LinearIndependent K v :=
    Module.End.eigenvectors_linearIndependent' (Matrix.toLin' M) d hd v hv
  have hu : IsUnit (Matrix.of v).transpose := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    exact hli
  have hmul : M * (Matrix.of v).transpose = (Matrix.of v).transpose * Matrix.diagonal d := by
    ext i a
    have h := congrFun (hv a).apply_eq_smul i
    rw [Matrix.toLin'_apply] at h
    rw [Matrix.mul_diagonal, mul_comm]
    simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  obtain ⟨u, hu⟩ := hu
  refine ⟨u, ?_⟩
  rw [Matrix.mul_assoc, hu, hmul, ← hu, ← Matrix.mul_assoc]
  simp

end UpperTheory.Reformulated.B.MirabolicColumnBlock
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MirabolicRowCongruence
section
theorem UpperTheory.mirabolic_row_congruence :
    ∀ {R : Type} [CommRing R] (I J : Ideal R) (g : GL (Fin 2) R), I ≤ J →
        Matrix.vecMul ![0, 1] ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk I) g : GL (Fin 2) (R ⧸ I)) : Matrix (Fin 2) (Fin 2) (R ⧸ I)) = ![0, 1] →
        Matrix.vecMul ![0, 1] ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk J) g : GL (Fin 2) (R ⧸ J)) : Matrix (Fin 2) (Fin 2) (R ⧸ J)) = ![0, 1] := by
  intro R _ I J g hIJ h
  have key : ∀ (K : Ideal R) (j : Fin 2),
      Matrix.vecMul ![0, 1] ((Matrix.GeneralLinearGroup.map (Ideal.Quotient.mk K) g :
        GL (Fin 2) (R ⧸ K)) : Matrix (Fin 2) (Fin 2) (R ⧸ K)) j
        = Ideal.Quotient.mk K ((g : Matrix (Fin 2) (Fin 2) R) 1 j) := by
    intro K j
    simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.GeneralLinearGroup.map]
  funext j
  have hj := congrArg (Ideal.Quotient.factor hIJ) ((key I j).symm.trans (congrFun h j))
  rw [Ideal.Quotient.factor_mk] at hj
  rw [key J j, hj]
  fin_cases j <;> simp
end

