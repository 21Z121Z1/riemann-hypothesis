import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.QuotientSpanRange
section
open IsLocalRing Matrix

namespace GlobalTheory.RegularQuotient

open IsLocalRing Matrix in

theorem _root_.GlobalTheory.RegularQuotient.quot_regular (Λ : Type) [CommRing Λ]
    [IsRegularLocalRing Λ] {ι κ : Type} [Fintype ι]
    [Fintype κ] (t : ι → Λ) (z : κ → Λ)
    (hs : Ideal.span (Set.range t ∪ Set.range z) = maximalIdeal Λ)
    (hd : ringKrullDim Λ = ((Fintype.card ι + Fintype.card κ : ℕ) : ℕ)) :
    ∃ _ : IsRegularLocalRing (Λ ⧸ Ideal.span (Set.range z)),
      Ideal.map (Ideal.Quotient.mk (Ideal.span (Set.range z))) (maximalIdeal Λ) =
        maximalIdeal (Λ ⧸ Ideal.span (Set.range z)) ∧
      Ideal.span (Set.range fun i => Ideal.Quotient.mk (Ideal.span (Set.range z)) (t i)) =
        maximalIdeal (Λ ⧸ Ideal.span (Set.range z)) ∧
      ringKrullDim (Λ ⧸ Ideal.span (Set.range z)) = (Fintype.card ι : ℕ) := by
  set I := Ideal.span (Set.range z) with hIdef
  have hIm : I ≤ maximalIdeal Λ := by
    rw [Ideal.span_le, ← hs]
    exact (Set.subset_union_right).trans Ideal.subset_span
  have hItop : I ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal Λ).ne_top hIm
  haveI : Nontrivial (Λ ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  haveI : IsLocalRing (Λ ⧸ I) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  have hmap : Ideal.map (Ideal.Quotient.mk I) (maximalIdeal Λ) = maximalIdeal (Λ ⧸ I) := by
    have hc : Ideal.comap (Ideal.Quotient.mk I) (maximalIdeal (Λ ⧸ I)) = maximalIdeal Λ :=
      IsLocalRing.eq_maximalIdeal
        (Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective)
    rw [← hc, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective]
  have hspan : Ideal.span (Set.range fun i => Ideal.Quotient.mk I (t i)) =
      maximalIdeal (Λ ⧸ I) := by
    rw [← hmap, ← hs, Ideal.span_union, Ideal.map_sup, Ideal.map_quotient_self, sup_bot_eq,
      Ideal.map_span, ← Set.range_comp]
    rfl
  have hgen : ((maximalIdeal (Λ ⧸ I)).spanFinrank : WithBot ℕ∞) ≤ (Fintype.card ι : ℕ) := by
    rw [← hspan]
    have h := Submodule.spanFinrank_span_le_ncard_of_finite (R := Λ ⧸ I)
      (Set.finite_range fun i => Ideal.Quotient.mk I (t i))
    have h' : (Set.range fun i => Ideal.Quotient.mk I (t i)).ncard ≤ Fintype.card ι := by
      rw [← Set.image_univ]; exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
    exact_mod_cast h.trans h'
  have hle : ringKrullDim (Λ ⧸ I) ≤ (Fintype.card ι : ℕ) :=
    (ringKrullDim_le_spanFinrank_maximalIdeal _).trans hgen
  have hI : (I.spanFinrank : WithBot ℕ∞) ≤ (Fintype.card κ : ℕ) := by
    have h := Submodule.spanFinrank_span_le_ncard_of_finite (R := Λ) (Set.finite_range z)
    have h' : (Set.range z).ncard ≤ Fintype.card κ := by
      rw [← Set.image_univ]; exact (Set.ncard_image_le Set.finite_univ).trans (by simp)
    exact_mod_cast h.trans h'
  have hge := ringKrullDim_le_ringKrullDim_quotient_add_spanFinrank I
    (by rw [ringJacobson_eq_maximalIdeal]; exact hIm)
  rw [hd] at hge
  have h1 : ((Fintype.card ι + Fintype.card κ : ℕ) : WithBot ℕ∞) ≤
      ringKrullDim (Λ ⧸ I) + (Fintype.card κ : ℕ) :=
    hge.trans (add_le_add le_rfl hI)
  have hdim : ringKrullDim (Λ ⧸ I) = (Fintype.card ι : ℕ) := by
    generalize ringKrullDim (Λ ⧸ I) = e at h1 hle ⊢
    induction e using WithBot.recBotCoe with
    | bot => simp at h1
    | coe e =>
      induction e using ENat.recTopCoe with
      | top => exact absurd hle (by exact_mod_cast (not_le.mpr (ENat.coe_lt_top _)))
      | coe n =>
        norm_cast at h1 hle ⊢
        omega
  exact ⟨IsRegularLocalRing.of_spanFinrank_maximalIdeal_le _ (hgen.trans hdim.ge), hmap, hspan,
    hdim⟩

open IsLocalRing Matrix in

theorem _root_.GlobalTheory.RegularQuotient.exists_extend (Λ : Type) [CommRing Λ]
    [IsRegularLocalRing Λ] {ι : Type} [Fintype ι]
    (τ : ι → maximalIdeal Λ)
    (hτ : LinearIndependent (ResidueField Λ) (fun i => (maximalIdeal Λ).toCotangent (τ i))) :
    ∃ (J : Type) (_ : Fintype J) (t : J → Λ),
      Ideal.span (Set.range t ∪ Set.range fun i => (τ i : Λ)) = maximalIdeal Λ ∧
      ringKrullDim Λ = ((Fintype.card J + Fintype.card ι : ℕ) : ℕ) := by
  set N : Submodule (ResidueField Λ) (CotangentSpace Λ) :=
    Submodule.span (ResidueField Λ) (Set.range fun i => (maximalIdeal Λ).toCotangent (τ i))
    with hN
  let b := Module.finBasis (ResidueField Λ) (CotangentSpace Λ ⧸ N)
  have hsurj : Function.Surjective
      fun y : maximalIdeal Λ => N.mkQ ((maximalIdeal Λ).toCotangent y) :=
    (Submodule.mkQ_surjective N).comp (maximalIdeal Λ).toCotangent_surjective
  choose s hs using fun j => hsurj (b j)
  refine ⟨Fin (Module.finrank (ResidueField Λ) (CotangentSpace Λ ⧸ N)), inferInstance,
    fun j => (s j : Λ), ?_, ?_⟩
  · have htop : Submodule.span (ResidueField Λ)
        ((maximalIdeal Λ).toCotangent '' (Set.range s ∪ Set.range τ)) = ⊤ := by
      set P := Submodule.span (ResidueField Λ)
        ((maximalIdeal Λ).toCotangent '' (Set.range s ∪ Set.range τ))
      have hNP : N ≤ P := by
        rw [hN, Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨τ i, Or.inr ⟨i, rfl⟩, rfl⟩
      have hmap : Submodule.map N.mkQ P = ⊤ := by
        rw [eq_top_iff, ← b.span_eq, Submodule.span_le]
        rintro _ ⟨j, rfl⟩
        exact ⟨_, Submodule.subset_span ⟨s j, Or.inl ⟨j, rfl⟩, rfl⟩, hs j⟩
      rw [Submodule.map_mkQ_eq_top, sup_eq_right.mpr hNP] at hmap
      exact hmap
    rw [IsLocalRing.CotangentSpace.span_image_eq_top_iff] at htop
    have key := congrArg (Submodule.map (maximalIdeal Λ).subtype) htop
    rw [← Submodule.span_image, Submodule.map_subtype_top, Set.image_union,
      ← Set.range_comp, ← Set.range_comp] at key
    exact key
  · rw [← (IsRegularLocalRing.iff_finrank_cotangentSpace Λ).mp inferInstance, Fintype.card_fin,
      ← finrank_span_eq_card hτ, ← hN, Submodule.finrank_quotient_add_finrank]

open IsLocalRing Matrix in
private theorem linearIndependent_toCotangent_of_sum_mem_maximalIdeal_sq (A : Type) [CommRing A]
    [IsRegularLocalRing A] (k : ℕ) (x : Fin k → A) (hx : ∀ i, x i ∈ maximalIdeal A)
    (hind : ∀ a : Fin k → A, ∑ i, a i * x i ∈ maximalIdeal A ^ 2 → ∀ i, a i ∈ maximalIdeal A) :
    LinearIndependent (ResidueField A)
      (fun i => (maximalIdeal A).toCotangent (⟨x i, hx i⟩ : maximalIdeal A)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  choose a ha using fun j => IsLocalRing.residue_surjective (g j)
  have hmem : (∑ j, a j * x j) ∈ maximalIdeal A :=
    Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hx j)
  have hsum : (∑ j, a j * x j) ∈ maximalIdeal A ^ 2 := by
    rw [← Ideal.toCotangent_eq_zero (maximalIdeal A) ⟨_, hmem⟩]
    have he : (⟨∑ j, a j * x j, hmem⟩ : maximalIdeal A) =
        ∑ j, a j • (⟨x j, hx j⟩ : maximalIdeal A) := by
      ext; simp [Submodule.coe_sum, smul_eq_mul]
    rw [he, map_sum, ← hg]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, ← ha j, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
  rw [← ha i, IsLocalRing.residue_eq_zero_iff]
  exact hind a hsum i

open IsLocalRing Matrix in

theorem _root_.GlobalTheory.RegularQuotient.quotient_span_range : ∀ (A : Type) [CommRing A] [IsRegularLocalRing A] (d k : ℕ)
    (x : Fin k → A),
    ringKrullDim A = ((d + k : ℕ) : WithBot ℕ∞) → (∀ i, x i ∈ maximalIdeal A) →
    (∀ a : Fin k → A, ∑ i, a i * x i ∈ maximalIdeal A ^ 2 → ∀ i, a i ∈ maximalIdeal A) →
    IsRegularLocalRing (A ⧸ Ideal.span (Set.range x)) ∧
      ringKrullDim (A ⧸ Ideal.span (Set.range x)) = (d : WithBot ℕ∞) := by
  intro A _ _ d k x hd hx hind
  obtain ⟨J, _, t, hspan, hdim⟩ := _root_.GlobalTheory.RegularQuotient.exists_extend A
    (fun i => (⟨x i, hx i⟩ : maximalIdeal A))
    (linearIndependent_toCotangent_of_sum_mem_maximalIdeal_sq A k x hx hind)
  have hJ : Fintype.card J = d := by
    rw [hd, Fintype.card_fin] at hdim
    have h : d + k = Fintype.card J + k := by exact_mod_cast hdim
    omega
  have hspan' : Ideal.span (Set.range t ∪ Set.range x) = maximalIdeal A := hspan
  have hdim' : ringKrullDim A = ((Fintype.card J + Fintype.card (Fin k) : ℕ) : ℕ) := by
    rw [hd, Fintype.card_fin, hJ]
  obtain ⟨hreg, -, -, hq⟩ := _root_.GlobalTheory.RegularQuotient.quot_regular A t x hspan' hdim'
  exact ⟨hreg, by rw [hq, hJ]⟩

end GlobalTheory.RegularQuotient
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumCosetRepsNeZeroIffCommensurable
section
namespace GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable

theorem finsum_quot_eq {V K : Type} [AddCommGroup V] [Field K] (f : V → K) (M N : AddSubgroup V)
    (S : Finset V) (hMN : M ≤ N) (hidx : M.relIndex N ≠ 0)
    (hf : ∀ v, ∀ u ∈ N, f (v + u) = f v)
    (hinj : ∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s')
    (hcov : ∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) :
    ∑ᶠ c : V ⧸ M, f c.out = (M.relIndex N : K) * ∑ s ∈ S, f s := by
  classical
  haveI : Finite (N ⧸ M.addSubgroupOf N) := Nat.finite_of_card_ne_zero hidx
  letI : Fintype (N ⧸ M.addSubgroupOf N) := Fintype.ofFinite _
  let φ : V × (N ⧸ M.addSubgroupOf N) → V ⧸ M :=
    fun p => QuotientAddGroup.mk (p.1 + ((p.2.out : N) : V))
  have hout : ∀ v : V, f (QuotientAddGroup.mk v : V ⧸ M).out = f v := by
    intro v
    have h : -v + (QuotientAddGroup.mk v : V ⧸ M).out ∈ M := by
      rw [← QuotientAddGroup.eq]; simp
    have := hf v _ (hMN h)
    simpa using this
  rw [finsum_eq_sum_of_support_subset (s := (S ×ˢ Finset.univ).image φ)]
  · rw [Finset.sum_image]
    · rw [Finset.sum_product]
      have : ∀ s ∈ S, ∑ q : N ⧸ M.addSubgroupOf N, f (φ (s, q)).out = (M.relIndex N : K) * f s := by
        intro s _
        have : ∀ q : N ⧸ M.addSubgroupOf N, f (φ (s, q)).out = f s := by
          intro q
          simp only [φ]
          rw [hout, hf _ _ (q.out).2]
        simp only [this, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        rw [← Nat.card_eq_fintype_card]
        rfl
      rw [Finset.sum_congr rfl this, Finset.mul_sum]
    · rintro ⟨s, q⟩ hp ⟨s', q'⟩ hp' h
      simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe] at hp hp'
      simp only [φ, QuotientAddGroup.eq] at h
      have hs : s = s' := by
        apply hinj s hp.1 s' hp'.1
        have h1 := N.add_mem (N.sub_mem (q'.out).2 (q.out).2) (N.neg_mem (hMN h))
        convert h1 using 1
        abel
      subst hs
      have hq : q = q' := by
        rw [← Quotient.out_eq q, ← Quotient.out_eq q']
        apply QuotientAddGroup.eq.2
        rw [AddSubgroup.mem_addSubgroupOf]
        convert h using 1
        push_cast
        abel
      rw [hq]
  · intro c hc
    obtain ⟨s, hs, hn⟩ := hcov c.out hc
    simp only [Finset.coe_image, Set.mem_image]
    refine ⟨(s, QuotientAddGroup.mk ⟨c.out - s, hn⟩), by simp [hs], ?_⟩
    have h : -(QuotientAddGroup.mk (⟨c.out - s, hn⟩ : N) : N ⧸ M.addSubgroupOf N).out
        + (⟨c.out - s, hn⟩ : N) ∈ M.addSubgroupOf N := by
      rw [← QuotientAddGroup.eq]; simp
    rw [AddSubgroup.mem_addSubgroupOf] at h
    conv_rhs => rw [← Quotient.out_eq c]
    apply QuotientAddGroup.eq.2
    convert h using 1
    push_cast
    abel

theorem sum_reps_ne_zero_iff : ∀ (V K : Type) [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (N N' : AddSubgroup V) (S S' : Finset V), N'.relIndex N ≠ 0 → N.relIndex N' ≠ 0 → (∀ v, ∀ u ∈ N, f (v + u) = f v) → (∀ v, ∀ u ∈ N', f (v + u) = f v) → (∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) → (∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ N' → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ N') → (∑ s ∈ S, f s ≠ 0 ↔ ∑ s ∈ S', f s ≠ 0) := by
  intro V K _ _ _ f N N' S S' h1 h2 hf hf' hi hc hi' hc'
  have e1 : (N ⊓ N').relIndex N ≠ 0 := by rwa [AddSubgroup.inf_relIndex_left]
  have e2 : (N ⊓ N').relIndex N' ≠ 0 := by rwa [AddSubgroup.inf_relIndex_right]
  have a := finsum_quot_eq f (N ⊓ N') N S inf_le_left e1 hf hi hc
  have b := finsum_quot_eq f (N ⊓ N') N' S' inf_le_right e2 hf' hi' hc'
  have c1 : (((N ⊓ N').relIndex N : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 e1
  have c2 : (((N ⊓ N').relIndex N' : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 e2
  rw [← mul_ne_zero_iff_left c1, ← a, b, mul_ne_zero_iff_left c2]

end GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumIntervalIntegralLeOfSpaced
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory

namespace GlobalTheory

theorem gallagher_interval (f f' h : ℝ → ℝ) (hf : ∀ t, HasDerivAt f (f' t) t)
    (hf' : Continuous f') (hh : Continuous h) (hb : ∀ t, |f' t| ≤ h t) (x δ : ℝ) (hδ : 0 < δ) :
    f x ≤ ∫ t in x..(x + δ), (f t / δ + h t) := by
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun t => (hf t).continuousAt
  have hF : ∀ t, HasDerivAt (fun t => (t - x - δ) / δ * f t) (f t / δ + (t - x - δ) / δ * f' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (t - x - δ) / δ) (1 / δ) t :=
      (((hasDerivAt_id t).sub_const x).sub_const δ).div_const δ
    exact (h1.fun_mul (hf t)).congr_deriv (by ring)
  have hc : Continuous fun t => f t / δ + (t - x - δ) / δ * f' t := by fun_prop
  have h2 := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x) (b := x + δ)
    (fun t _ => hF t) (hc.intervalIntegrable _ _)
  have h3 : (x + δ - x - δ) / δ * f (x + δ) - (x - x - δ) / δ * f x = f x := by
    field_simp
    ring
  rw [h3] at h2
  rw [← h2]
  apply intervalIntegral.integral_mono_on (by linarith) (hc.intervalIntegrable _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _)
  intro t ht
  have h4 : |(t - x - δ) / δ| ≤ 1 := by
    rw [abs_div, abs_of_pos hδ, div_le_one hδ, abs_le]
    constructor <;> linarith [ht.1, ht.2]
  have h5 : (t - x - δ) / δ * f' t ≤ h t := by
    calc _ ≤ |(t - x - δ) / δ * f' t| := le_abs_self _
      _ = |(t - x - δ) / δ| * |f' t| := abs_mul _ _
      _ ≤ 1 * h t := mul_le_mul h4 (hb t) (abs_nonneg _) zero_le_one
      _ = h t := one_mul _
  linarith

theorem integral_exp_two_pi_sub (n m : ℕ) (y : ℝ) :
    ∫ t in y..(y + 1), Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * t) = if n = m then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · have hc : (2 * Real.pi * I * ((n : ℂ) - m)) ≠ 0 := by
      have : (n : ℂ) - m ≠ 0 := sub_ne_zero.2 (by exact_mod_cast h)
      have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [this, hpi, I_ne_zero]
    rw [integral_exp_mul_complex hc]
    have : Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * ((y + 1 : ℝ) : ℂ))
        = Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * (y : ℂ)) := by
      have h1 := Complex.exp_int_mul_two_pi_mul_I ((n : ℤ) - m)
      rw [show 2 * Real.pi * I * ((n : ℂ) - m) * ((y + 1 : ℝ) : ℂ)
        = 2 * Real.pi * I * ((n : ℂ) - m) * (y : ℂ) + (((n : ℤ) - m : ℤ) : ℂ) * (2 * Real.pi * I) by
          push_cast; ring, Complex.exp_add, h1, mul_one]
    rw [this]; simp

theorem norm_expSum_shift (s : Finset ℕ) (b : ℕ → ℂ) (c t : ℝ) :
    ‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t)‖
      = ‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t)‖ := by
  have : ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t)
      = Complex.exp (((-(2 * Real.pi * c * t) : ℝ) : ℂ) * I) *
        ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mul_left_comm, ← Complex.exp_add]
    congr 2
    push_cast; ring
  rw [this, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]

theorem integral_norm_sq_expSum (s : Finset ℕ) (b : ℕ → ℂ) (y : ℝ) :
    ∫ t in y..(y + 1), ‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t)‖ ^ 2
      = ∑ n ∈ s, ‖b n‖ ^ 2 := by
  have key : ∀ t : ℝ, ((‖∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * t)‖ ^ 2 : ℝ) : ℂ)
      = ∑ n ∈ s, ∑ m ∈ s, b n * (starRingEnd ℂ) (b m) *
        Complex.exp (2 * Real.pi * I * ((n : ℂ) - m) * t) := by
    intro t
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, ← Complex.exp_conj]
    simp only [map_mul, conj_ofReal, conj_I, map_natCast, map_ofNat]
    rw [mul_mul_mul_comm, ← Complex.exp_add]
    congr 2
    ring
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [key]
  rw [intervalIntegral.integral_finset_sum (fun n _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  push_cast
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [intervalIntegral.integral_finset_sum (fun n _ => Continuous.intervalIntegrable (by fun_prop) _ _)]
  simp_rw [intervalIntegral.integral_const_mul, integral_exp_two_pi_sub]
  simp [hn, Complex.mul_conj']

theorem sum_intervalIntegral_le_of_spaced (g : ℝ → ℝ) (hg : Continuous g) (h0 : ∀ t, 0 ≤ g t)
    (S : Finset ℝ) (p : ℝ → ℝ) (δ y : ℝ) (hδ : 0 < δ)
    (h1 : ∀ x ∈ S, y ≤ p x) (h2 : ∀ x ∈ S, p x + δ ≤ y + 1)
    (h3 : ∀ x ∈ S, ∀ z ∈ S, x ≠ z → δ ≤ |p x - p z|) :
    ∑ x ∈ S, ∫ t in (p x)..(p x + δ), g t ≤ ∫ t in y..(y + 1), g t := by
  have hi : ∀ u v : ℝ, IntegrableOn g (Set.Ioc u v) := fun u v =>
    (hg.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  rw [intervalIntegral.integral_of_le (by linarith : y ≤ y + 1)]
  rw [Finset.sum_congr rfl fun x _ =>
    intervalIntegral.integral_of_le (by linarith : p x ≤ p x + δ)]
  rw [← integral_biUnion_finset S (s := fun x => Set.Ioc (p x) (p x + δ))
    (fun _ _ => measurableSet_Ioc) ?_ (fun x _ => hi _ _)]
  · apply setIntegral_mono_set (hi _ _) (Filter.Eventually.of_forall h0)
    apply HasSubset.Subset.eventuallyLE
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨x, hx, ht⟩ := ht
    exact ⟨lt_of_le_of_lt (h1 x hx) ht.1, ht.2.trans (h2 x hx)⟩
  · intro x hx z hz hxz
    have := h3 x hx z hz hxz
    rw [Function.onFun, Set.disjoint_left]
    intro t ht ht'
    have : |p x - p z| < δ := by
      rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
    linarith

theorem expSum_sub_int (s : Finset ℕ) (b : ℕ → ℂ) (x : ℝ) (k : ℤ) :
    ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * ((x - k : ℝ) : ℂ))
      = ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * n * x) := by
  refine Finset.sum_congr rfl fun n _ => ?_
  have h1 := Complex.exp_int_mul_two_pi_mul_I (-(n * k))
  rw [show 2 * Real.pi * I * (n : ℂ) * ((x - k : ℝ) : ℂ)
    = 2 * Real.pi * I * n * x + ((-(n * k) : ℤ) : ℂ) * (2 * Real.pi * I) by
      push_cast; ring, Complex.exp_add, h1, mul_one]

theorem additive_large_sieve : ∀ (M N : ℕ) (a : ℕ → ℂ) (S : Finset ℝ) (δ : ℝ), 0 < δ → δ ≤ 1 → (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ∀ k : ℤ, δ ≤ |x - y - k|) → ∑ x ∈ S, ‖∑ n ∈ Finset.Ioc M (M + N), a n * Complex.exp (2 * Real.pi * I * n * x)‖ ^ 2 ≤ (1 / δ + 2 * Real.pi * N) * ∑ n ∈ Finset.Ioc M (M + N), ‖a n‖ ^ 2 := by
  intro M N a S δ hδ hδ1 hS
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  rcases S.eq_empty_or_nonempty with rfl | ⟨y, hy⟩
  · simp only [Finset.sum_empty]; positivity
  set s := Finset.Ioc M (M + N) with hs
  set c : ℝ := M + N / 2 with hc
  set L : ℝ := Real.pi * N with hL
  have hL0 : 0 < L := by positivity
  set b : ℕ → ℂ := fun n => a n * (2 * Real.pi * I * ((n : ℂ) - c)) with hb
  set T : ℝ → ℂ := fun t => ∑ n ∈ s, a n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t) with hT
  set T' : ℝ → ℂ := fun t => ∑ n ∈ s, b n * Complex.exp (2 * Real.pi * I * ((n : ℂ) - c) * t) with hT'
  have hd : ∀ t, HasDerivAt T (T' t) t := by
    intro t
    apply HasDerivAt.fun_sum
    intro n _
    have h1 : HasDerivAt (fun t : ℝ => 2 * Real.pi * I * ((n : ℂ) - c) * (t : ℂ))
        (2 * Real.pi * I * ((n : ℂ) - c)) t := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (2 * Real.pi * I * ((n : ℂ) - c))
    exact ((h1.cexp).const_mul (a n)).congr_deriv (by simp only [hb]; ring)
  have hTc : Continuous T := by simp only [hT]; fun_prop
  have hTc' : Continuous T' := by simp only [hT']; fun_prop
  have hG : ∀ x, ‖T x‖ ^ 2 ≤ ∫ t in x..(x + δ), (‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L)) := by
    intro x
    refine gallagher_interval (fun t => ‖T t‖ ^ 2) (fun t => 2 * inner ℝ (T t) (T' t))
      (fun t => L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L) (fun t => (hd t).norm_sq) (by fun_prop) (by fun_prop) ?_ x δ hδ
    intro t
    have h1 := abs_real_inner_le_norm (T t) (T' t)
    rw [abs_mul, abs_two]
    have h2 : L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L - 2 * (‖T t‖ * ‖T' t‖)
        = (L * ‖T t‖ - ‖T' t‖) ^ 2 / L := by field_simp; ring
    have h3 : 0 ≤ (L * ‖T t‖ - ‖T' t‖) ^ 2 / L := by positivity
    linarith
  set p : ℝ → ℝ := fun x => x - (⌊x - y⌋ : ℤ) with hp
  have hsum := sum_intervalIntegral_le_of_spaced
    (fun t => ‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L)) (by fun_prop) (fun t => by positivity)
    S p δ y hδ (fun x _ => by simp only [hp]; linarith [Int.floor_le (x - y)]) ?_ ?_
  · have e1 : ∫ t in y..(y + 1), ‖T t‖ ^ 2 = ∑ n ∈ s, ‖a n‖ ^ 2 := by
      simp only [hT, norm_expSum_shift]; exact integral_norm_sq_expSum s a y
    have e2 : ∫ t in y..(y + 1), ‖T' t‖ ^ 2 = ∑ n ∈ s, ‖b n‖ ^ 2 := by
      simp only [hT', norm_expSum_shift]; exact integral_norm_sq_expSum s b y
    have e3 : ∑ n ∈ s, ‖b n‖ ^ 2 ≤ L ^ 2 * ∑ n ∈ s, ‖a n‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun n hn => ?_
      rw [hs, Finset.mem_Ioc] at hn
      have hn1 : (M : ℝ) < n := by exact_mod_cast hn.1
      have hn2 : (n : ℝ) ≤ M + N := by exact_mod_cast hn.2
      have h4 : ‖(n : ℂ) - c‖ ≤ N / 2 := by
        rw [show (n : ℂ) - c = ((n - c : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_eq_abs, abs_le]
        constructor <;> linarith
      have h5 : ‖b n‖ ≤ L * ‖a n‖ := by
        simp only [hb, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos Real.pi_pos, Complex.norm_ofNat]
        calc ‖a n‖ * (2 * Real.pi * 1 * ‖(n : ℂ) - c‖) ≤ ‖a n‖ * (2 * Real.pi * 1 * (N / 2)) := by
              gcongr
          _ = L * ‖a n‖ := by rw [hL]; ring
      rw [← mul_pow]
      gcongr
    have e4 : ∫ t in y..(y + 1), (‖T t‖ ^ 2 / δ + (L * ‖T t‖ ^ 2 + ‖T' t‖ ^ 2 / L))
        = (∑ n ∈ s, ‖a n‖ ^ 2) / δ + (L * ∑ n ∈ s, ‖a n‖ ^ 2 + (∑ n ∈ s, ‖b n‖ ^ 2) / L) := by
      rw [intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _),
        intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
        (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_div,
        intervalIntegral.integral_div, intervalIntegral.integral_const_mul, e1, e2]
    have e5 : (∑ n ∈ s, ‖b n‖ ^ 2) / L ≤ L * ∑ n ∈ s, ‖a n‖ ^ 2 := by
      rw [div_le_iff₀ hL0]; nlinarith
    calc _ = ∑ x ∈ S, ‖T (p x)‖ ^ 2 := by
          refine Finset.sum_congr rfl fun x _ => ?_
          simp only [hT, hp]
          rw [norm_expSum_shift, expSum_sub_int]
      _ ≤ _ := Finset.sum_le_sum fun x _ => hG (p x)
      _ ≤ _ := hsum
      _ = _ := e4
      _ ≤ (∑ n ∈ s, ‖a n‖ ^ 2) / δ + (L * ∑ n ∈ s, ‖a n‖ ^ 2 + L * ∑ n ∈ s, ‖a n‖ ^ 2) := by
          linarith
      _ = _ := by rw [hL]; ring
  · intro x hx
    simp only [hp]
    by_cases hxy : x = y
    · subst hxy; simp [hδ1]
    · have h1 := hS x hx y hy hxy (⌊x - y⌋ + 1)
      have h2 := Int.lt_floor_add_one (x - y)
      push_cast at h1
      rw [abs_of_neg (by linarith)] at h1
      linarith
  · intro x hx z hz hxz
    have h1 := hS x hx z hz hxz (⌊x - y⌋ - ⌊z - y⌋)
    simp only [hp]
    convert h1 using 2
    push_cast; ring

end GlobalTheory
end

