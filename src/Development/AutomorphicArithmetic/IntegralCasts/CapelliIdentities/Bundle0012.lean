import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DcAevalIntertwineAlt
section
theorem UpperTheory.Reformulated.B.Qk13.dc_aeval_intertwine.{u_1, u_2} :
    ∀ {Y : Type u_1} {Z : Type u_2} [inst : AddCommGroup Y] [inst_1 : _root_.Module ℂ Y] [inst_2 : AddCommGroup Z]
    [inst_3 : _root_.Module ℂ Z] (ψ : Y →ₗ[ℂ] Z) (A : Module.End ℂ Y) (B : Module.End ℂ Z),
    (∀ (y : Y), (ψ : Y → Z) ((A : Y → Y) y) = (B : Z → Z) ((ψ : Y → Z) y)) →
      ∀ (p : Polynomial ℂ) (y : Y),
        (ψ : Y → Z) (((Polynomial.aeval A : Polynomial ℂ → Module.End ℂ Y) p : Y → Y) y) =
          ((Polynomial.aeval B : Polynomial ℂ → Module.End ℂ Z) p : Z → Z) ((ψ : Y → Z) y) := by
  intro Y Z _ _ _ _ ψ A B h p
  have hpow : ∀ (n : ℕ) (y : Y), ψ ((A ^ n) y) = (B ^ n) (ψ y) := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih, h]
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    intro y
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hp, hq]
  | monomial n a =>
    intro y
    rw [Polynomial.aeval_monomial, Polynomial.aeval_monomial, Module.End.mul_apply,
      Module.End.mul_apply, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
      map_smul, hpow]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DcCons
section
noncomputable def UpperTheory.Reformulated.B.Qj27.dc :
    {Y : Type} → {m : ℕ} → ((Fin (m + (1 : ℕ)) → Y) → ℝ) → (Fin (m + (2 : ℕ)) → Y) → ℝ :=
    fun {Y : Type} {m : ℕ} (F : (Fin (m + (1 : ℕ)) → Y) → ℝ) (y : Fin (m + (2 : ℕ)) → Y) ↦
      ∑ i : Fin (m + (2 : ℕ)), (-1 : ℝ) ^ (↑i : ℕ) * F fun (j : Fin (m + (1 : ℕ))) ↦ y (i.succAbove j)

theorem UpperTheory.Reformulated.B.Qj27.dc_cons :
    ∀ {Y : Type} {m : ℕ} (F : (Fin (m + (2 : ℕ)) → Y) → ℝ) (a : Y) (w : Fin (m + (2 : ℕ)) → Y),
      UpperTheory.Reformulated.B.Qj27.dc F (Fin.cons a w) =
        F w - UpperTheory.Reformulated.B.Qj27.dc (fun (w' : Fin (m + (1 : ℕ)) → Y) ↦ F (Fin.cons a w')) w := by
  intro Y m F a w
  have h : ∀ i : Fin (m + 2),
      (fun j : Fin (m + 2) ↦ (Fin.cons a w : Fin (m + 3) → Y) (i.succ.succAbove j)) =
        (Fin.cons a (fun j : Fin (m + 1) ↦ w (i.succAbove j)) : Fin (m + 2) → Y) := by
    intro i
    funext j
    refine Fin.cases ?_ (fun k ↦ ?_) j
    · simp
    · simp
  unfold UpperTheory.Reformulated.B.Qj27.dc
  rw [Fin.sum_univ_succ, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [h i, Fin.val_succ, pow_succ]
    ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DeRhamEllipticIdentity
section
theorem UpperTheory.Reformulated.B.InvariantSumOfTranslates.main :
    ∀ {K S : Type} [inst : Group K] [inst_1 : TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
      [inst_4 : AddCommGroup S] [inst_5 : _root_.Module ℂ S] (ω : K →* Module.End ℂ S) (f₀ : S),
      (∃ U ∈ nhds (1 : K), ∀ k ∈ U, ((ω : K → Module.End ℂ S) k : S → S) f₀ = f₀) →
        ∃ (m : ℕ) (k : Fin (m + (1 : ℕ)) → K),
          ∀ (g : K),
            ((ω : K → Module.End ℂ S) g : S → S) (∑ i : Fin (m + (1 : ℕ)), ((ω : K → Module.End ℂ S) (k i) : S → S) f₀) =
              ∑ i : Fin (m + (1 : ℕ)), ((ω : K → Module.End ℂ S) (k i) : S → S) f₀ := by
  intro K S _ _ _ _ _ _ ω f₀ h
  obtain ⟨U, hU, hfix⟩ := h
  have hmul : ∀ (a b : K) (v : S), ω (a * b) v = ω a (ω b v) := by
    intro a b v
    rw [map_mul, Module.End.mul_apply]

  let H : Subgroup K :=
    { carrier := {k | ω k f₀ = f₀}
      one_mem' := by simp
      mul_mem' := by
        intro a b ha hb
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [hmul, hb, ha]
      inv_mem' := by
        intro a ha
        simp only [Set.mem_setOf_eq] at ha ⊢
        have h1 : ω a⁻¹ (ω a f₀) = f₀ := by
          rw [← hmul]; simp
        rwa [ha] at h1 }
  have hmem : ∀ k, k ∈ H ↔ ω k f₀ = f₀ := fun k => Iff.rfl
  have hopen : IsOpen (H : Set K) :=
    H.isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset hU (fun k hk => hfix k hk))
  haveI : Finite (K ⧸ H) := Subgroup.quotient_finite_of_isOpen H hopen
  haveI : Fintype (K ⧸ H) := Fintype.ofFinite _

  let F : K ⧸ H → S := fun q => ω q.out f₀
  have hF : ∀ (g : K) (q : K ⧸ H), ω g (F q) = F (g • q) := by
    intro g q
    have hq : ((g * q.out : K) : K ⧸ H) = g • q := by
      conv_rhs => rw [← QuotientGroup.out_eq' q]
      rfl
    have hq' : (((g • q).out : K) : K ⧸ H) = ((g * q.out : K) : K ⧸ H) := by
      rw [hq, QuotientGroup.out_eq']
    have hh : ((g • q).out)⁻¹ * (g * q.out) ∈ H := QuotientGroup.eq.mp hq'
    have h2 : g * q.out = (g • q).out * (((g • q).out)⁻¹ * (g * q.out)) := by group
    change ω g (ω q.out f₀) = ω (g • q).out f₀
    rw [← hmul, h2, hmul, (hmem _).mp hh]
  obtain ⟨m, hm⟩ : ∃ m, Fintype.card (K ⧸ H) = m + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let e : Fin (m + 1) ≃ K ⧸ H := (Fintype.equivFinOfCardEq hm).symm
  refine ⟨m, fun i => (e i).out, fun g => ?_⟩
  have hsum : ∑ i : Fin (m + 1), ω (e i).out f₀ = ∑ q, F q := Equiv.sum_comp e F
  rw [hsum, map_sum]
  simp_rw [hF]
  exact Equiv.sum_comp (MulAction.toPerm g) F
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DegLESum
section
noncomputable def UpperTheory.Reformulated.B.Qf21.degLE :
    {κ R : Type} → [inst : CommRing R] → Finset κ → ℕ → MvPolynomial κ R → Prop :=
    fun {κ R : Type} [CommRing R] (W : Finset κ) (n : ℕ) (F : MvPolynomial κ R) ↦
      ∀ (β : κ →₀ ℕ), MvPolynomial.coeff β F ≠ (0 : R) → ∑ k ∈ W, (β : κ → ℕ) k ≤ n

theorem UpperTheory.Reformulated.B.Qf21.degLE_sum.{u_1} :
    ∀ {κ R : Type} [inst : CommRing R] {α : Type u_1} {W : Finset κ} {n : ℕ} (s : Finset α) (F : α → MvPolynomial κ R),
      (∀ a ∈ s, UpperTheory.Reformulated.B.Qf21.degLE W n (F a)) → UpperTheory.Reformulated.B.Qf21.degLE W n (∑ a ∈ s, F a) := by
  intro κ R _ α W n s F h β hβ
  rw [MvPolynomial.coeff_sum] at hβ
  obtain ⟨a, ha, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hβ
  exact h a ha β hne
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DegreeOneStatement
section
namespace DegreeOneCoeffSubstitution
open MvPowerSeries Finsupp

private lemma deg_one {σ : Type} [DecidableEq σ] (d : σ →₀ ℕ) (h : d.degree = 1) :
    ∃ s, d = Finsupp.single s 1 := by
  have hd : d ≠ 0 := by rintro rfl; simp at h
  obtain ⟨s, hs⟩ := Finsupp.support_nonempty_iff.mpr hd
  refine ⟨s, ?_⟩
  have hsum : d s + ∑ i ∈ d.support.erase s, d i = 1 := by
    rw [Finset.add_sum_erase _ _ hs, ← degree_apply, h]
  have hs0 : d s ≠ 0 := Finsupp.mem_support_iff.mp hs
  have hds : d s = 1 := by omega
  have hrest : ∑ i ∈ d.support.erase s, d i = 0 := by omega
  rw [Finset.sum_eq_zero_iff] at hrest
  ext i
  by_cases his : i = s
  · subst his; simp [hds]
  · rw [Finsupp.single_apply, if_neg (Ne.symm his)]
    by_cases hi : i ∈ d.support
    · exact hrest i (Finset.mem_erase.mpr ⟨his, hi⟩)
    · exact Finsupp.notMem_support_iff.mp hi

end DegreeOneCoeffSubstitution

open MvPowerSeries Finsupp in
theorem UpperTheory.Reformulated.B.LinearTermOfSubstitution.main :
    ∀ {S : Type}
    [inst : CommRing S] {σ τ : Type} [inst_1 : Fintype σ] [DecidableEq σ] [DecidableEq τ] (a : σ → MvPowerSeries τ S),
    (∀ (s : σ), (MvPowerSeries.constantCoeff : MvPowerSeries τ S → S) (a s) = (0 : S)) →
      ∀ (f : MvPowerSeries σ S) (t : τ),
        (MvPowerSeries.coeff fun₀ | t => (1 : ℕ) : MvPowerSeries τ S → S) (MvPowerSeries.subst a f) =
          ∑ s : σ,
            (MvPowerSeries.coeff fun₀ | s => (1 : ℕ) : MvPowerSeries σ S → S) f *
              (MvPowerSeries.coeff fun₀ | t => (1 : ℕ) : MvPowerSeries τ S → S) (a s) := by
  intro S _ σ τ _ _ _ a ha f t
  have hS : HasSubst a := hasSubst_of_constantCoeff_zero ha
  rw [coeff_subst hS]
  have key : ∀ d : σ →₀ ℕ, d ∉ Finset.univ.image (fun s => Finsupp.single s 1) →
      coeff (Finsupp.single t 1) (d.prod fun s e => a s ^ e) = 0 := by
    intro d hd
    by_cases h0 : d = 0
    · subst h0
      simp [coeff_one]
    have h1 : d.degree ≠ 1 := by
      intro h
      obtain ⟨s, rfl⟩ := DegreeOneCoeffSubstitution.deg_one d h
      exact hd (by simp)
    have h2 : 2 ≤ d.degree := by
      have : d.degree ≠ 0 := fun h => h0 ((degree_eq_zero_iff d).mp h)
      omega
    unfold Finsupp.prod
    apply coeff_of_lt_order
    rw [Finsupp.degree_single]
    refine lt_of_lt_of_le ?_ (le_order_prod _ _)
    calc ((1 : ℕ) : ℕ∞) < 2 := by norm_num
      _ ≤ ((d.degree : ℕ) : ℕ∞) := by exact_mod_cast h2
      _ = ∑ i ∈ d.support, ((d i : ℕ) : ℕ∞) := by rw [degree_apply]; push_cast; rfl
      _ ≤ ∑ i ∈ d.support, (a i ^ d i).order :=
          Finset.sum_le_sum fun i _ => le_order_pow_of_constantCoeff_eq_zero _ (ha i)
  rw [finsum_eq_sum_of_support_subset _ (s := Finset.univ.image (fun s => Finsupp.single s 1)) ?_]
  · rw [Finset.sum_image (fun x _ y _ h => Finsupp.single_left_injective one_ne_zero h)]
    apply Finset.sum_congr rfl
    intro s _
    simp [Finsupp.prod_single_index, smul_eq_mul]
  · intro d hd
    by_contra h
    apply hd
    simp only
    rw [key d (by simpa using h), smul_zero]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DenLE
section
noncomputable def UpperTheory.Reformulated.B.Yhb9.DenLE :
    {V H : Type} →
      [inst : MeasurableSpace V] →
        [inst_1 : MeasurableSpace H] → MeasureTheory.Measure V → MeasureTheory.Measure H → (V → H) → Set V → ENNReal → Prop :=
    fun {V H : Type} [MeasurableSpace V] [MeasurableSpace H] (μ : MeasureTheory.Measure V) (ν : MeasureTheory.Measure H)
        (q : V → H) (S : Set V) (C : ENNReal) ↦
      ∀ (Y : Set H), MeasurableSet Y → (μ : Set V → ENNReal) (S ∩ q ⁻¹' Y) ≤ C * (ν : Set H → ENNReal) Y

theorem UpperTheory.Reformulated.B.Yhb9.main :
    ∀ {V H : Type} [inst : MeasurableSpace V] [inst_1 : MeasurableSpace H] {μ : MeasureTheory.Measure V}
      {ν : MeasureTheory.Measure H} {q : V → H} {T : V → V} {τ : H → H},
      MeasurableEmbedding T →
        Measurable τ →
          (∀ (X : V), q (T X) = τ (q X)) →
            ∀ {a c : NNReal},
              a ≠ (0 : NNReal) →
                MeasureTheory.Measure.map T μ = a • μ →
                  MeasureTheory.Measure.map τ ν = c • ν →
                    ∀ {S : Set V} {C : ENNReal},
                      UpperTheory.Reformulated.B.Yhb9.DenLE μ ν q S C → UpperTheory.Reformulated.B.Yhb9.DenLE μ ν q (T '' S) ((↑(a⁻¹ * c) : ENNReal) * C) := by
  intro V H _ _ μ ν q T τ hT hτ hq a c ha hTμ hτν S C hS Y hY
  have h1 : T ⁻¹' (T '' S ∩ q ⁻¹' Y) = S ∩ q ⁻¹' (τ ⁻¹' Y) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_inter_iff, hT.injective.mem_set_image, hq]
  have h2 : (a : ENNReal) * μ (T '' S ∩ q ⁻¹' Y) = μ (S ∩ q ⁻¹' (τ ⁻¹' Y)) := by
    have := congrArg (fun m => m (T '' S ∩ q ⁻¹' Y)) hTμ
    rw [hT.map_apply, h1, MeasureTheory.Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at this
    exact this.symm
  have h3 : ν (τ ⁻¹' Y) = (c : ENNReal) * ν Y := by
    have := congrArg (fun m => m Y) hτν
    rw [MeasureTheory.Measure.map_apply hτ hY, MeasureTheory.Measure.smul_apply,
      ENNReal.smul_def, smul_eq_mul] at this
    exact this
  have h4 := hS (τ ⁻¹' Y) (hτ hY)
  rw [h3, ← h2] at h4
  have ha' : (a : ENNReal) ≠ 0 := by exact_mod_cast ha
  calc μ (T '' S ∩ q ⁻¹' Y) = (a : ENNReal)⁻¹ * ((a : ENNReal) * μ (T '' S ∩ q ⁻¹' Y)) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel ha' ENNReal.coe_ne_top, one_mul]
    _ ≤ (a : ENNReal)⁻¹ * (C * ((c : ENNReal) * ν Y)) := by gcongr
    _ = _ := by rw [ENNReal.coe_mul, ENNReal.coe_inv ha]; ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DenominatorOfSpan
section
theorem UpperTheory.Reformulated.B.SpanDenominator.den_of_span :
    ∀ {K : Type} [inst : Field K] [inst_1 : NumberField K] {i : ℕ} (P : Ideal (NumberField.RingOfIntegers K))
      [inst_2 : P.IsPrime] (M : Submodule (NumberField.RingOfIntegers K) (Fin i → K)),
      ∀
        x ∈
          Submodule.span ↥(Localization.subalgebra.ofField K P.primeCompl (Ideal.primeCompl_le_nonZeroDivisors P))
            (↑M : Set (Fin i → K)),
        ∃ s ∈ P.primeCompl, s • x ∈ M := by
  intro K _ _ i P _ M x hx
  obtain ⟨t, ht⟩ := multiple_mem_span_of_mem_localization_span P.primeCompl
    ↥(Localization.subalgebra.ofField K P.primeCompl (Ideal.primeCompl_le_nonZeroDivisors P))
    (↑M : Set (Fin i → K)) x hx
  rw [Submodule.span_eq] at ht
  exact ⟨t.1, t.2, ht⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DerivZeroOut
section
namespace YiaHelp

private lemma deriv_zero_out (x : ℝ) (hx : x ∉ Set.Icc (0 : ℝ) (1 : ℝ)) :
    deriv Real.smoothTransition x = 0 := by
  rcases lt_or_ge x 0 with h | h
  · have : Real.smoothTransition =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds h] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [this.deriv_eq]; simp
  · have h1 : 1 < x := by
      by_contra hc
      exact hx ⟨h, not_lt.mp hc⟩
    have : Real.smoothTransition =ᶠ[nhds x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds h1] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [this.deriv_eq]; simp

end YiaHelp

theorem UpperTheory.Reformulated.B.Yia2.main :
    ∃ (K : ℝ),
      (0 : ℝ) ≤ K ∧
        (∀ (x : ℝ), |deriv Real.smoothTransition x| ≤ K) ∧
          ∀ x ∉ Set.Icc (0 : ℝ) (1 : ℝ), deriv Real.smoothTransition x = (0 : ℝ) := by
  have hc : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_, YiaHelp.deriv_zero_out⟩
  intro x
  by_cases hx : x ∈ Set.Icc (0 : ℝ) (1 : ℝ)
  · have := hC x hx
    rw [Real.norm_eq_abs] at this
    exact le_trans this (le_max_left _ _)
  · rw [YiaHelp.deriv_zero_out x hx]; simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DerivationMemPowOfMemPowSucc
section
theorem UpperTheory.Reformulated.B.Qn11.derivation_mem_pow_of_mem_pow_succ :
    ∀ {R : Type} [inst : CommRing R]
    (I : Ideal R) (D : Derivation ℤ R R) {n : ℕ} {r : R}, r ∈ I ^ (n + (1 : ℕ)) → (D : R → R) r ∈ I ^ n := by
  intro R _ I D n
  induction n with
  | zero =>
    intro r _
    simp
  | succ n ih =>
    intro r hr
    rw [pow_succ] at hr
    refine Submodule.mul_induction_on hr ?_ ?_
    · intro a ha b hb
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      refine Ideal.add_mem _ (Ideal.mul_mem_right _ _ ha) ?_
      rw [pow_succ, mul_comm b]
      exact Ideal.mul_mem_mul (ih ha) hb
    · intro x y hx hy
      rw [map_add]
      exact Ideal.add_mem _ hx hy
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DerivativeLocallyConstant
section
theorem UpperTheory.Reformulated.B.DerivativeLocallyConstant.dz_locConst :
    ∀ {Γ A : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [inst_3 : Group A] (ψ : Γ →* A), IsOpen (↑ψ.ker : Set Γ) → IsLocallyConstant (⇑ψ : Γ → A) := by
  intro Γ A _ _ _ _ ψ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (ψ.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change x⁻¹ * x ∈ ψ.ker
    simp
  · intro y hy
    have hy' : ψ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
    rw [map_mul, map_inv, inv_mul_eq_one] at hy'
    exact hy'.symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DetEmbUnitriA
section
theorem UpperTheory.Reformulated.B.Qe13.aux1 :
    ∀ (R : Type) [inst : CommRing R] (n : ℕ),
      Matrix.fromBlocks (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin (1 : ℕ)) R)
          (0 : Matrix (Fin (1 : ℕ)) (Fin n) R) (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) =
        (1 : Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R) := by
  intro R _ n
  exact Matrix.fromBlocks_one

theorem UpperTheory.Reformulated.B.Qe13.aux2 :
    ∀ (R : Type) [inst : CommRing R] (n : ℕ) (A B : Matrix (Fin n) (Fin n) R),
      Matrix.fromBlocks (A * B) (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
          (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) =
        Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
            (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) *
          Matrix.fromBlocks B (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
            (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R) := by
  intro R _ n A B
  rw [Matrix.fromBlocks_multiply]
  simp

noncomputable def UpperTheory.Reformulated.B.Qe13.blkHom :
    (R : Type) →
      [inst : CommRing R] → (n : ℕ) → Matrix (Fin n) (Fin n) R →* Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R :=
    fun (R : Type) [CommRing R] (n : ℕ) ↦
      {
        toFun := fun (A : Matrix (Fin n) (Fin n) R) ↦
          Matrix.fromBlocks A (0 : Matrix (Fin n) (Fin (1 : ℕ)) R) (0 : Matrix (Fin (1 : ℕ)) (Fin n) R)
            (1 : Matrix (Fin (1 : ℕ)) (Fin (1 : ℕ)) R),
        map_one' := UpperTheory.Reformulated.B.Qe13.aux1 R n, map_mul' := UpperTheory.Reformulated.B.Qe13.aux2 R n :
        Matrix (Fin n) (Fin n) R →* Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R }

noncomputable def UpperTheory.Reformulated.B.Qe13.embGL :
    (R : Type) → [inst : CommRing R] → (n N : ℕ) → n + (1 : ℕ) = N → GL (Fin n) R →* GL (Fin N) R :=
    fun (R : Type) [CommRing R] (n N : ℕ) (h : n + (1 : ℕ) = N) ↦
      Units.map
        ((↑(↑(Matrix.reindexAlgEquiv R R (finSumFinEquiv.trans (finCongr h))) :
                    Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R →ₐ[R] Matrix (Fin N) (Fin N) R).toRingHom :
              Matrix (Fin n ⊕ Fin (1 : ℕ)) (Fin n ⊕ Fin (1 : ℕ)) R →* Matrix (Fin N) (Fin N) R).comp
          (UpperTheory.Reformulated.B.Qe13.blkHom R n))

theorem UpperTheory.Reformulated.B.Qe13.det_emb_unitri_A :
    ∀ {n : ℕ} (g : GL (Fin n) ℂ),
      (∀ (i j : Fin n), j < i → (↑g : Matrix (Fin n) (Fin n) ℂ) i j = (0 : ℂ)) →
        (∀ (i : Fin n), (↑g : Matrix (Fin n) (Fin n) ℂ) i i = (1 : ℂ)) →
          (Matrix.GeneralLinearGroup.det : GL (Fin (n + (1 : ℕ))) ℂ → ℂˣ)
              ((UpperTheory.Reformulated.B.Qe13.embGL ℂ n (n + (1 : ℕ)) rfl : GL (Fin n) ℂ → GL (Fin (n + (1 : ℕ))) ℂ) g) =
            (1 : ℂˣ) := by
  intro n g hlow hdiag
  have htri : (↑g : Matrix (Fin n) (Fin n) ℂ).BlockTriangular id := fun i j hij => hlow i j hij
  have hg : (↑g : Matrix (Fin n) (Fin n) ℂ).det = 1 := by
    rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => hdiag i
  apply Units.ext
  change Matrix.det (Matrix.reindex (finSumFinEquiv.trans (finCongr rfl)) (finSumFinEquiv.trans (finCongr rfl))
    (Matrix.fromBlocks (↑g : Matrix (Fin n) (Fin n) ℂ) (0 : Matrix (Fin n) (Fin 1) ℂ)
      (0 : Matrix (Fin 1) (Fin n) ℂ) (1 : Matrix (Fin 1) (Fin 1) ℂ))) = 1
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁, hg, Matrix.det_one, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.DetMulExpand
section
theorem UpperTheory.Reformulated.B.DetMulExpand.det_mul_expand :
    ∀ {F : Type} [inst : CommRing F] {k r : ℕ} (A : Matrix (Fin k) (Fin r) F) (B : Matrix (Fin r) (Fin k) F),
      (A * B).det = ∑ f : Fin k → Fin r, (∏ a : Fin k, A a (f a)) * (B.submatrix f id).det := by
  intro F _ k r A B
  have h1 : (A * B) = (fun a => ∑ j, (A a j • B j : Fin k → F)) := by
    ext a c
    simp [Matrix.mul_apply, Finset.sum_apply]
  have h2 : (A * B).det
      = (Matrix.detRowAlternating (R := F) (n := Fin k)).toMultilinearMap
          (fun a => ∑ j, (A a j • B j : Fin k → F)) := by
    rw [← h1]
    rfl
  rw [h2, MultilinearMap.map_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [MultilinearMap.map_smul_univ]
  rfl
end

