import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LintegralSwapNorm
section
open MeasureTheory in
theorem UpperTheory.Reformulated.B.Qf2.lintegral_swap_norm :
    ∀ {X T : Type} [inst : Group X]
    [inst_1 : TopologicalSpace X] [IsTopologicalGroup X] [LocallyCompactSpace X] [T2Space X] [SecondCountableTopology X]
    [inst_6 : MeasurableSpace X] [BorelSpace X] [inst_8 : Group T] [inst_9 : TopologicalSpace T] [IsTopologicalGroup T]
    [LocallyCompactSpace T] [T2Space T] [SecondCountableTopology T] [inst_14 : MeasurableSpace T] [BorelSpace T]
    (μ : MeasureTheory.Measure X) [μ.IsHaarMeasure] (ν : MeasureTheory.Measure T) [ν.IsHaarMeasure] [ν.IsInvInvariant]
    (i : T →* X),
    Continuous (⇑i : T → X) →
      ∀ {a b Ψ : X → ENNReal},
        Measurable a →
          Measurable b →
            Measurable Ψ →
              (∀ (t : T) (x : X), Ψ ((i : T → X) t * x) = Ψ x) →
                (∀ (x : X), ∫⁻ (t : T), a ((i : T → X) t * x) ∂ν = (1 : ENNReal)) →
                  (∀ (x : X), ∫⁻ (t : T), b ((i : T → X) t * x) ∂ν = (1 : ENNReal)) →
                    ∫⁻ (x : X), Ψ x * a x ∂μ = ∫⁻ (x : X), Ψ x * b x ∂μ := by
  intro X T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ μ _ ν _ _ i hi a b Ψ ha hb hΨ hinv hA hB
  have him : Measurable (i : T → X) := hi.measurable
  have m1 : Measurable (fun p : X × T => i p.2 * p.1) :=
    (him.comp measurable_snd).mul measurable_fst
  have m2 : Measurable (fun p : X × T => i p.2⁻¹ * p.1) :=
    (him.comp measurable_snd.inv).mul measurable_fst
  have f1 : Measurable (Function.uncurry fun (x : X) (t : T) => Ψ x * a x * b (i t * x)) :=
    ((hΨ.comp measurable_fst).mul (ha.comp measurable_fst)).mul (hb.comp m1)
  have f2 : Measurable (Function.uncurry fun (x : X) (t : T) => Ψ x * b x * a (i t⁻¹ * x)) :=
    ((hΨ.comp measurable_fst).mul (hb.comp measurable_fst)).mul (ha.comp m2)
  have e1 : ∀ x : X, ∫⁻ t, Ψ x * a x * b (i t * x) ∂ν = Ψ x * a x := by
    intro x
    have hm : Measurable (fun t : T => b (i t * x)) := hb.comp (him.mul_const x)
    rw [lintegral_const_mul _ hm, hB x, mul_one]
  have e2 : ∀ x : X, ∫⁻ t, Ψ x * b x * a (i t⁻¹ * x) ∂ν = Ψ x * b x := by
    intro x
    have hm : Measurable (fun t : T => a (i t⁻¹ * x)) :=
      ha.comp ((him.comp measurable_inv).mul_const x)
    rw [lintegral_const_mul _ hm, lintegral_inv_eq_self (fun t : T => a (i t * x)), hA x, mul_one]
  have e3 : ∀ t : T, ∫⁻ x, Ψ x * a x * b (i t * x) ∂μ = ∫⁻ x, Ψ x * b x * a (i t⁻¹ * x) ∂μ := by
    intro t
    rw [← lintegral_mul_left_eq_self (fun x => Ψ x * b x * a (i t⁻¹ * x)) (i t)]
    refine lintegral_congr fun x => ?_
    simp only [hinv, map_inv, inv_mul_cancel_left]
    ring
  calc ∫⁻ x, Ψ x * a x ∂μ = ∫⁻ x, ∫⁻ t, Ψ x * a x * b (i t * x) ∂ν ∂μ :=
        lintegral_congr fun x => (e1 x).symm
    _ = ∫⁻ t, ∫⁻ x, Ψ x * a x * b (i t * x) ∂μ ∂ν := lintegral_lintegral_swap f1.aemeasurable
    _ = ∫⁻ t, ∫⁻ x, Ψ x * b x * a (i t⁻¹ * x) ∂μ ∂ν := lintegral_congr e3
    _ = ∫⁻ x, ∫⁻ t, Ψ x * b x * a (i t⁻¹ * x) ∂ν ∂μ :=
        (lintegral_lintegral_swap f2.aemeasurable).symm
    _ = ∫⁻ x, Ψ x * b x ∂μ := lintegral_congr e2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocLenEqZero
section
theorem UpperTheory.Reformulated.B.Yzb1.aux1.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) {x y : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → x + y ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L x y ⟨s, hs, hx⟩ ⟨t, ht, hy⟩
  refine ⟨s * t, S.mul_mem hs ht, ?_⟩
  have e : (s * t) • (x + y) = t • (s • x) + s • (t • y) := by
    rw [smul_add, mul_smul, smul_comm s t x, mul_smul]
  rw [e]
  exact L.add_mem (L.smul_mem t hx) (L.smul_mem s hy)

theorem UpperTheory.Reformulated.B.Yzb1.aux2.{u_1, u_2} :
    ∀ {R : Type u_1} [inst : CommRing R] {W : Type u_2} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W), ∃ s ∈ S, s • (0 : W) ∈ L := by
  intro R _ W _ _ S L
  exact ⟨1, S.one_mem, by rw [smul_zero]; exact L.zero_mem⟩

theorem UpperTheory.Reformulated.B.Yzb1.aux3.{u_1, u_2} :
    ∀ {R : Type u_2} [inst : CommRing R] {W : Type u_1} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
      (S : Submonoid R) (L : Submodule R W) (r : R) {x : W},
      x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} → r • x ∈ {x : W | ∃ s ∈ S, s • x ∈ L} := by
  rintro R _ W _ _ S L r x ⟨s, hs, hx⟩
  refine ⟨s, hs, ?_⟩
  rw [smul_comm]
  exact L.smul_mem r hx

noncomputable def UpperTheory.Reformulated.B.Yzb1.locS.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module R W] → Submonoid R → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [inst : CommRing R] {W : Type u_4} [inst_1 : AddCommGroup W] [inst_2 : _root_.Module R W]
        (S : Submonoid R) (L : Submodule R W) ↦
      { carrier := {x : W | ∃ s ∈ S, s • x ∈ L}, add_mem' := @UpperTheory.Reformulated.B.Yzb1.aux1 R inst W inst_1 inst_2 S L,
        zero_mem' := UpperTheory.Reformulated.B.Yzb1.aux2 S L, smul_mem' := UpperTheory.Reformulated.B.Yzb1.aux3 S L : Submodule R W }

noncomputable def UpperTheory.Reformulated.B.Yzb1.localization₂.{u_1, u_4} :
    {R : Type u_1} →
      [inst : CommRing R] →
        {W : Type u_4} →
          [inst_1 : AddCommGroup W] →
            [inst_2 : _root_.Module R W] → (p : Ideal R) → [p.IsPrime] → Submodule R W → Submodule R W :=
    fun {R : Type u_1} [CommRing R] {W : Type u_4} [AddCommGroup W] [_root_.Module R W] (p : Ideal R) [p.IsPrime]
        (L : Submodule R W) ↦
      UpperTheory.Reformulated.B.Yzb1.locS p.primeCompl L

noncomputable def UpperTheory.Reformulated.B.Yzb1.locLen.{u_1, u_3} :
    {R : Type u_1} →
      {V : Type u_3} →
        [inst : CommRing R] →
          [inst_1 : AddCommGroup V] →
            [inst_2 : _root_.Module R V] → (p : Ideal R) → [p.IsPrime] → Submodule R V → Submodule R V → ℕ :=
    fun {R : Type u_1} {V : Type u_3} [CommRing R] [AddCommGroup V] [_root_.Module R V] (p : Ideal R) [p.IsPrime]
        (A B : Submodule R V) ↦
      (Module.length R
          (↥(UpperTheory.Reformulated.B.Yzb1.localization₂ p A) ⧸
            Submodule.comap (UpperTheory.Reformulated.B.Yzb1.localization₂ p A).subtype (UpperTheory.Reformulated.B.Yzb1.localization₂ p B))).toNat

noncomputable def UpperTheory.Reformulated.B.Yzb1.lidx.{u_1, u_3} :
    {R : Type u_1} →
      {V : Type u_3} →
        [inst : CommRing R] →
          [inst_1 : AddCommGroup V] →
            [inst_2 : _root_.Module R V] → (p : Ideal R) → [p.IsPrime] → Submodule R V → Submodule R V → ℤ :=
    fun {R : Type u_1} {V : Type u_3} [CommRing R] [AddCommGroup V] [_root_.Module R V] (p : Ideal R) [p.IsPrime]
        (A B : Submodule R V) ↦
      (↑(UpperTheory.Reformulated.B.Yzb1.locLen p A (A ⊓ B)) : ℤ) - (↑(UpperTheory.Reformulated.B.Yzb1.locLen p B (A ⊓ B)) : ℤ)

private lemma UpperTheory.Reformulated.B.Yzb1.locLen_eq_zero {R V : Type*} [CommRing R] [AddCommGroup V]
    [_root_.Module R V] (p : Ideal R) [p.IsPrime] (A C : Submodule R V)
    (h : UpperTheory.Reformulated.B.Yzb1.localization₂ p A ≤ UpperTheory.Reformulated.B.Yzb1.localization₂ p C) :
    UpperTheory.Reformulated.B.Yzb1.locLen p A C = 0 := by
  have hs : Subsingleton (↥(UpperTheory.Reformulated.B.Yzb1.localization₂ p A) ⧸
      Submodule.comap (UpperTheory.Reformulated.B.Yzb1.localization₂ p A).subtype (UpperTheory.Reformulated.B.Yzb1.localization₂ p C)) := by
    rw [Submodule.Quotient.subsingleton_iff, Submodule.comap_subtype_eq_top]
    exact h
  have hl := (Module.length_eq_zero_iff (R := R)).mpr hs
  show (Module.length R _).toNat = 0
  rw [hl]
  rfl

private lemma UpperTheory.Reformulated.B.Yzb1.localization_le_localization_inf {R V : Type*} [CommRing R] [AddCommGroup V]
    [_root_.Module R V] (p : Ideal R) [p.IsPrime] (A B : Submodule R V) (s : R) (hs : s ∉ p)
    (h : ∀ x ∈ A, s • x ∈ B) :
    UpperTheory.Reformulated.B.Yzb1.localization₂ p A ≤ UpperTheory.Reformulated.B.Yzb1.localization₂ p (A ⊓ B) := by
  rintro x ⟨t, ht, hx⟩
  refine ⟨s * t, p.primeCompl.mul_mem hs ht, ?_⟩
  rw [mul_smul]
  exact ⟨A.smul_mem s hx, h _ hx⟩

theorem UpperTheory.Reformulated.B.Yzb1.lidx_finite :
    ∀ {K V : Type} [inst : Field K] [NumberField K] [inst_2 : AddCommGroup V]
      [inst_3 : _root_.Module (NumberField.RingOfIntegers K) V] (A B : Submodule (NumberField.RingOfIntegers K) V)
      (s : NumberField.RingOfIntegers K),
      s ≠ (0 : NumberField.RingOfIntegers K) →
        (∀ x ∈ A, s • x ∈ B) →
          (∀ x ∈ B, s • x ∈ A) →
            {w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K) |
                UpperTheory.Reformulated.B.Yzb1.lidx w.asIdeal A B ≠ (0 : ℤ)}.Finite := by
  intro K V _ _ _ _ A B s hs hAB hBA
  have hI : Ideal.span {s} ≠ (0 : Ideal (NumberField.RingOfIntegers K)) := by
    simpa using hs
  refine (Ideal.finite_factors hI).subset ?_
  intro w hw
  by_contra hc
  have hsw : s ∉ w.asIdeal := fun hm => hc (Ideal.dvd_span_singleton.mpr hm)
  apply hw
  have h1 := UpperTheory.Reformulated.B.Yzb1.locLen_eq_zero w.asIdeal A (A ⊓ B)
    (UpperTheory.Reformulated.B.Yzb1.localization_le_localization_inf w.asIdeal A B s hsw hAB)
  have h2 := UpperTheory.Reformulated.B.Yzb1.locLen_eq_zero w.asIdeal B (A ⊓ B)
    (by rw [inf_comm]; exact UpperTheory.Reformulated.B.Yzb1.localization_le_localization_inf w.asIdeal B A s hsw hBA)
  show ((UpperTheory.Reformulated.B.Yzb1.locLen w.asIdeal A (A ⊓ B) : ℕ) : ℤ) -
    ((UpperTheory.Reformulated.B.Yzb1.locLen w.asIdeal B (A ⊓ B) : ℕ) : ℤ) = 0
  rw [h1, h2]
  simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocalHeightDeterminant
section
noncomputable def UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight.{u_1} :
    {E : Type u_1} → [inst : NormedField E] → {n : ℕ} → GL (Fin n) E → ℝ :=
    fun {E : Type u_1} [NormedField E] {n : ℕ} (g : GL (Fin n) E) ↦
      Max.max (1 : ℝ)
        (↑(Finset.univ.sup fun (p : Fin n × Fin n) ↦
              Max.max ‖(↑g : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊ ‖(↑g⁻¹ : Matrix (Fin n) (Fin n) E) p.1 p.2‖₊) :
          ℝ)

theorem UpperTheory.Reformulated.B.LocalHeightDeterminant.norm_det_le_pow.{u_1} :
    ∀ {R : Type u_1} [inst : NormedField R] [IsUltrametricDist R] {n : ℕ} (g : GL (Fin n) R),
      ‖(↑g : Matrix (Fin n) (Fin n) R).det‖ ≤ UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g ^ n := by
  intro R _ _ n g
  have h1 : (1 : ℝ) ≤ UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g := le_max_left _ _
  have h0 : (0 : ℝ) ≤ UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g := zero_le_one.trans h1
  have hent : ∀ i j, ‖(↑g : Matrix (Fin n) (Fin n) R) i j‖ ≤ UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g := by
    intro i j
    refine le_trans ?_ (le_max_right _ _)
    rw [← coe_nnnorm, NNReal.coe_le_coe]
    exact (le_max_left _ _).trans (Finset.le_sup (f := fun (p : Fin n × Fin n) ↦
      Max.max ‖(↑g : Matrix (Fin n) (Fin n) R) p.1 p.2‖₊
        ‖(↑g⁻¹ : Matrix (Fin n) (Fin n) R) p.1 p.2‖₊) (Finset.mem_univ (i, j)))
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg h0 n) ?_
  intro σ _
  have hs : ‖Equiv.Perm.sign σ • ∏ i, (↑g : Matrix (Fin n) (Fin n) R) (σ i) i‖
      = ‖∏ i, (↑g : Matrix (Fin n) (Fin n) R) (σ i) i‖ := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]
  rw [hs, norm_prod]
  calc ∏ i, ‖(↑g : Matrix (Fin n) (Fin n) R) (σ i) i‖
      ≤ ∏ _i : Fin n, UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g :=
        Finset.prod_le_prod (fun _ _ ↦ norm_nonneg _) (fun i _ ↦ hent _ _)
    _ = UpperTheory.Reformulated.B.LocalHeightDeterminant.locHeight g ^ n := by simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocalQuotientHomExt
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR :
    ℕ → Type :=
    fun (q : ℕ) ↦ LaurentPolynomial (Localization.Away (↑q : ℤ))

theorem UpperTheory.Reformulated.B.LocalQuotientHomExt.hom_ext :
    ∀ (q : ℕ) {R : Type} [inst : CommRing R] {f g : UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR q →+* R},
      (f : UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR q → R) (LaurentPolynomial.T (1 : ℤ)) =
          (g : UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR q → R) (LaurentPolynomial.T (1 : ℤ)) →
        f = g := by
  intro q R _ f g h
  have hC : f.comp LaurentPolynomial.C = g.comp LaurentPolynomial.C := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (q : ℤ))
    exact RingHom.ext_int _ _
  have hCa : ∀ a, f (LaurentPolynomial.C a) = g (LaurentPolynomial.C a) :=
    fun a => RingHom.congr_fun hC a
  have hmul : ∀ m n : ℤ, (LaurentPolynomial.T m : UpperTheory.Reformulated.B.LocalQuotientHomExt.LqR q) * LaurentPolynomial.T n
      = LaurentPolynomial.T (m + n) := fun m n => (LaurentPolynomial.T_add m n).symm
  have h1 : f (LaurentPolynomial.T 1) * f (LaurentPolynomial.T (-1)) = 1 := by
    rw [← map_mul, hmul]; simp
  have h2 : g (LaurentPolynomial.T 1) * g (LaurentPolynomial.T (-1)) = 1 := by
    rw [← map_mul, hmul]; simp
  have hinv : f (LaurentPolynomial.T (-1)) = g (LaurentPolynomial.T (-1)) := by
    calc f (LaurentPolynomial.T (-1))
        = f (LaurentPolynomial.T (-1)) * (g (LaurentPolynomial.T 1) * g (LaurentPolynomial.T (-1))) := by
          rw [h2, mul_one]
      _ = (f (LaurentPolynomial.T 1) * f (LaurentPolynomial.T (-1))) * g (LaurentPolynomial.T (-1)) := by
          rw [← h]; ring
      _ = g (LaurentPolynomial.T (-1)) := by rw [h1, one_mul]
  have hT : ∀ n : ℤ, f (LaurentPolynomial.T n) = g (LaurentPolynomial.T n) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ i ih => rw [← hmul, map_mul, map_mul, ih, h]
    | pred i ih => rw [sub_eq_add_neg, ← hmul, map_mul, map_mul, ih, hinv]
  apply RingHom.ext
  intro p
  induction p using LaurentPolynomial.induction_on' with
  | add p r hp hr => rw [map_add, map_add, hp, hr]
  | C_mul_T n a =>
    rw [map_mul, map_mul, hCa, hT]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantFunctions
section
theorem UpperTheory.Reformulated.B.LocallyConstantFunctions.locConst :
    ∀ {Γ A : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [inst_3 : Group A] (ψ : Γ →* A), IsOpen (↑ψ.ker : Set Γ) → IsLocallyConstant (⇑ψ : Γ → A) := by
  intro Γ A _ _ _ _ ψ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (↑ψ.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp [MonoidHom.mem_ker]
  · intro y hy
    have hk : ψ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
    rw [map_mul, map_inv, inv_mul_eq_one] at hk
    exact hk.symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantMaps
section
theorem UpperTheory.Reformulated.B.LocallyConstantMaps.locConst :
    ∀ {Γ A : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [inst_3 : Group A] (ψ : Γ →* A), IsOpen (↑ψ.ker : Set Γ) → IsLocallyConstant (⇑ψ : Γ → A) := by
  intro Γ A _ _ _ _ ψ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (↑ψ.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp [MonoidHom.mem_ker]
  · intro y hy
    have hy' : ψ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
    rw [map_mul, map_inv, inv_mul_eq_one] at hy'
    exact hy'.symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfKernel
section
theorem UpperTheory.Reformulated.B.LocallyConstantOfKernel.lc_of_ker :
    ∀ {Γ C : Type} [inst : Group Γ]
    [inst_1 : TopologicalSpace Γ] [IsTopologicalGroup Γ] [inst_3 : Group C] (η : Γ →* C),
    IsOpen (↑η.ker : Set Γ) → IsLocallyConstant (⇑η : Γ → C) := by
  intro Γ C _ _ _ _ η h
  refine (IsLocallyConstant.iff_exists_open _).2 fun x => ?_
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (η.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change x⁻¹ * x ∈ η.ker
    simp [MonoidHom.mem_ker]
  · intro y hy
    have hy' : η (x⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv] at hy'
    exact (inv_mul_eq_one.mp hy').symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfOpen
section
theorem UpperTheory.Reformulated.B.LocallyConstantOfOpen.ho_locConst :
    ∀ {Γ A : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [inst_3 : Group A] (ψ : Γ →* A), IsOpen (↑ψ.ker : Set Γ) → IsLocallyConstant (⇑ψ : Γ → A) := by
  intro Γ A _ _ _ _ ψ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (ψ.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · change x⁻¹ * x ∈ ψ.ker
    simp [MonoidHom.mem_ker]
  · intro y hy
    have hy' : ψ (x⁻¹ * y) = 1 := hy
    rw [map_mul, map_inv, inv_mul_eq_one] at hy'
    exact hy'.symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfOpenSet
section
theorem UpperTheory.Reformulated.B.LocallyConstantOfOpenSet.lc_of_open :
    ∀ {G H : Type} [inst : Group G] [inst_1 : TopologicalSpace G]
    [IsTopologicalGroup G] [inst_3 : Group H] (f : G →* H), IsOpen (↑f.ker : Set G) → IsLocallyConstant (⇑f : G → H) := by
  intro G H _ _ _ _ f hk
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hc : Continuous fun y : G => x⁻¹ * y := continuous_const.mul continuous_id
  have ho : IsOpen ((fun y : G => x⁻¹ * y) ⁻¹' (f.ker : Set G)) := hk.preimage hc
  have hx : x ∈ (fun y : G => x⁻¹ * y) ⁻¹' (f.ker : Set G) := by
    simp [Set.mem_preimage, MonoidHom.mem_ker]
  filter_upwards [ho.mem_nhds hx] with y hy
  have h1 : f (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
  rw [map_mul, map_inv, inv_mul_eq_one] at h1
  exact h1.symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOpenPreimage
section
theorem UpperTheory.Reformulated.B.LocallyConstantOpenPreimage.lc_of_open :
    ∀ {Γ A : Type} [inst : Group Γ] [inst_1 : TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [inst_3 : Group A] (ψ : Γ →* A), IsOpen (↑ψ.ker : Set Γ) → IsLocallyConstant (⇑ψ : Γ → A) := by
  intro Γ A _ _ _ _ ψ h
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  refine ⟨(fun y => x⁻¹ * y) ⁻¹' (ψ.ker : Set Γ),
    h.preimage (continuous_const.mul continuous_id), ?_, ?_⟩
  · simp [MonoidHom.mem_ker]
  · intro y hy
    have hk : ψ (x⁻¹ * y) = 1 := MonoidHom.mem_ker.mp hy
    rw [map_mul, map_inv] at hk
    exact (inv_mul_eq_one.mp hk).symm
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapCastMono
section
noncomputable def UpperTheory.Reformulated.B.Qh31.vR :
    {K : Type} → [inst : Field K] → AddValuation K (WithTop ℚ) → K → WithTop ℝ :=
    fun {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) (x : K) ↦
      WithTop.map (fun (n : ℚ) ↦ (↑n : ℝ)) ((v : K → WithTop ℚ) x)

noncomputable def UpperTheory.Reformulated.B.Qh31.vge :
    {K : Type} → [inst : Field K] → AddValuation K (WithTop ℚ) → ℝ → K → Prop :=
    fun {K : Type} [Field K] (v : AddValuation K (WithTop ℚ)) (a : ℝ) (x : K) ↦ (↑a : WithTop ℝ) ≤ UpperTheory.Reformulated.B.Qh31.vR v x

private theorem UpperTheory.Reformulated.B.Qh31.map_cast_mono :
    Monotone (WithTop.map (fun (n : ℚ) ↦ (↑n : ℝ))) :=
  Monotone.withTop_map (fun _ _ h ↦ Rat.cast_le.mpr h)

theorem UpperTheory.Reformulated.B.Qh31.vge_sum :
    ∀ {K : Type} [inst : Field K] (v : AddValuation K (WithTop ℚ)) {ι : Type} {a : ℝ} (s : Finset ι) (f : ι → K),
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qh31.vge v a (f i)) → UpperTheory.Reformulated.B.Qh31.vge v a (∑ i ∈ s, f i) := by
  intro K _ v ι a s f h
  refine Finset.sum_induction f (UpperTheory.Reformulated.B.Qh31.vge v a) ?_ ?_ h
  · intro x y hx hy
    unfold UpperTheory.Reformulated.B.Qh31.vge UpperTheory.Reformulated.B.Qh31.vR at *
    rcases min_le_iff.mp (v.map_add x y) with hxy | hxy
    · exact hx.trans (UpperTheory.Reformulated.B.Qh31.map_cast_mono hxy)
    · exact hy.trans (UpperTheory.Reformulated.B.Qh31.map_cast_mono hxy)
  · unfold UpperTheory.Reformulated.B.Qh31.vge UpperTheory.Reformulated.B.Qh31.vR
    rw [v.map_zero, WithTop.map_top]
    exact le_top
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapInvolutionEq
section
open MeasureTheory in
private theorem UpperTheory.Reformulated.B.Qh1.map_involution_eq {G : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (φ : G ≃ₜ* G) (hφ : ∀ x, φ (φ x) = x) :
    μ.map φ = μ := by
  have h1 : φ.trans φ = ContinuousMulEquiv.refl G := by
    ext x
    exact hφ x
  have h2 : mulEquivHaarChar φ * mulEquivHaarChar φ = 1 := by
    rw [← mulEquivHaarChar_trans, h1, mulEquivHaarChar_refl]
  have h3 : mulEquivHaarChar φ = 1 := by
    have h : (mulEquivHaarChar φ) ^ 2 = 1 := by rw [sq, h2]
    exact (pow_eq_one_iff_of_nonneg zero_le two_ne_zero).1 h
  have h4 := mulEquivHaarChar_smul_map μ φ
  rwa [h3, one_smul] at h4

theorem UpperTheory.Reformulated.B.Qh1.twist_general.{u_1} :
    ∀ {G : Type u_1} [inst : Group G]
    [inst_1 : TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G]
    [inst_5 : MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsHaarMeasure] (Γ : Subgroup G)
    [Countable ↥Γ] {F : Set G},
    MeasureTheory.IsFundamentalDomain (↥Γ) F μ →
      ∀ (θ : G →* G),
        Continuous (⇑θ : G → G) →
          (∀ (x : G), (θ : G → G) ((θ : G → G) x) = x) →
            (∀ γ ∈ Γ, (θ : G → G) γ ∈ Γ) →
              ∀ (f : G → ℂ),
                (∀ (γ : ↥Γ) (x : G), f ((↑γ : G) * x) = f x) →
                  MeasureTheory.Integrable f (μ.restrict F) →
                    MeasureTheory.Integrable (fun (x : G) ↦ f ((θ : G → G) x)) (μ.restrict F) ∧
                      ∫ (x : G) in F, f ((θ : G → G) x) ∂μ = ∫ (x : G) in F, f x ∂μ := by
  intro G _ _ _ _ _ _ _ μ _ Γ _ F hF θ hθc hθθ hθΓ f hf hfi
  let φ : G ≃ₜ* G :=
    { toFun := θ
      invFun := θ
      left_inv := hθθ
      right_inv := hθθ
      map_mul' := map_mul θ
      continuous_toFun := hθc
      continuous_invFun := hθc }
  have hmp : MeasureTheory.MeasurePreserving θ μ μ :=
    ⟨hθc.measurable, UpperTheory.Reformulated.B.Qh1.map_involution_eq μ φ hθθ⟩
  have hemb : MeasurableEmbedding (θ : G → G) := φ.toHomeomorph.measurableEmbedding
  let e : Γ → Γ := fun γ => ⟨θ γ, hθΓ γ γ.2⟩
  have he : Function.Involutive e := fun γ => Subtype.ext (hθθ γ)
  have hF' : MeasureTheory.IsFundamentalDomain Γ (θ ⁻¹' F) μ := by
    refine hF.preimage_of_equiv hmp.quasiMeasurePreserving he.bijective ?_
    intro γ x
    change θ (θ γ * x) = γ * θ x
    rw [map_mul, hθθ]
  have hg : ∀ (γ : Γ) (x : G), f (θ (γ • x)) = f (θ x) := by
    intro γ x
    change f (θ (γ * x)) = f (θ x)
    rw [map_mul]
    exact hf (e γ) (θ x)
  refine ⟨?_, ?_⟩
  · have h1 : MeasureTheory.IntegrableOn (fun x => f (θ x)) (θ ⁻¹' F) μ :=
      (hmp.integrableOn_comp_preimage hemb).2 hfi
    exact (hF.integrableOn_iff hF' (f := fun x => f (θ x)) hg).2 h1
  · rw [hF.setIntegral_eq hF' (f := fun x => f (θ x)) hg]
    exact hmp.setIntegral_preimage_emb hemb f F
end

