import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MainFin
section
namespace UpperTheory.Reformulated.B.Ra5

open Polynomial

private theorem ext_inj {R S K : Type} [CommRing R] [CommRing S] [IsDomain S]
    [Field K] [IsAlgClosed K] (f : R →+* S) (hf : Function.Injective f) (hfi : f.IsIntegral)
    (g : R →+* K) (hg : Function.Injective g) :
    ∃ l : S →+* K, l.comp f = g := by
  haveI : IsDomain R := hf.isDomain f
  letI : Algebra R S := f.toAlgebra
  letI : Algebra R K := g.toAlgebra
  haveI : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).mpr hf
  haveI : FaithfulSMul R K := (faithfulSMul_iff_algebraMap_injective _ _).mpr hg
  haveI : Algebra.IsIntegral R S := ⟨hfi⟩
  let l := IsAlgClosed.lift (R := R) (S := S) (M := K)
  exact ⟨(l : S →+* K), RingHom.ext fun x => l.commutes x⟩

private theorem ext_integral {R S K : Type} [CommRing R] [CommRing S] [IsDomain S]
    [Field K] [IsAlgClosed K] (f : R →+* S) (hinj : Function.Injective f) (hfi : f.IsIntegral)
    (y : R →+* K) :
    ∃ ξ : S →+* K, ξ.comp f = y := by
  letI : Algebra R S := f.toAlgebra
  haveI : Algebra.IsIntegral R S := ⟨hfi⟩
  haveI hp : (RingHom.ker y).IsPrime := RingHom.ker_isPrime y
  obtain ⟨Q, -, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := S)
    (RingHom.ker y) (⊥ : Ideal S) (by
      intro x hx
      have h0 : algebraMap R S x = 0 := by simpa using hx
      have hx0 : x = 0 := hinj (h0.trans (map_zero f).symm)
      simp [hx0])
  have hQc' : Q.comap f = RingHom.ker y := hQc
  let q : (R ⧸ Q.comap f) →+* (S ⧸ Q) := Ideal.quotientMap Q f le_rfl
  have hq : Function.Injective q := Ideal.quotientMap_injective
  have hqi : q.IsIntegral := RingHom.IsIntegral.quotient f hfi
  let g : (R ⧸ Q.comap f) →+* K := Ideal.Quotient.lift _ y (fun a ha => by
    have : a ∈ RingHom.ker y := hQc' ▸ ha
    exact this)
  have hg : Function.Injective g := by
    rw [injective_iff_map_eq_zero]
    intro a
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
    intro h
    have hx : x ∈ RingHom.ker y := h
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (hQc' ▸ hx)
  obtain ⟨l, hl⟩ := ext_inj q hq hqi g hg
  refine ⟨l.comp (Ideal.Quotient.mk Q), RingHom.ext fun x => ?_⟩
  have h := RingHom.congr_fun hl (Ideal.Quotient.mk _ x)
  exact h

private theorem gen_alg {A B K : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra B A] [Field K] [IsAlgClosed K]
    (hinj : Function.Injective (algebraMap B A)) (t : A) (ht : Algebra.adjoin B {t} = ⊤)
    (f : B[X]) (hf : f ≠ 0) (hft : aeval t f = 0) (y : B →+* K) (hy : y f.leadingCoeff ≠ 0) :
    ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y := by
  have hc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf
  let M : Submonoid B := Submonoid.powers f.leadingCoeff
  have hM : M ≤ nonZeroDivisors B := powers_le_nonZeroDivisors_of_noZeroDivisors hc
  let M' : Submonoid A := M.map (algebraMap B A)
  have hM' : M' ≤ nonZeroDivisors A := by
    rintro _ ⟨m, hm, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      (fun h => nonZeroDivisors.ne_zero (hM hm) (hinj (by simpa using h)))
  haveI : IsDomain (Localization M') := IsLocalization.isDomain_localization hM'
  let φ : Localization M →+* Localization M' :=
    IsLocalization.map (Localization M') (algebraMap B A) M.le_comap_map
  have hφ : ∀ r : B, φ (algebraMap B (Localization M) r) =
      algebraMap A (Localization M') (algebraMap B A r) := fun r => IsLocalization.map_eq _ r
  have h1 : ∀ s : A, φ.IsIntegralElem (algebraMap A (Localization M') s) := by
    intro s
    have hs : s ∈ Algebra.adjoin B {t} := ht ▸ Algebra.mem_top
    induction hs using Algebra.adjoin_induction with
    | mem x hx =>
      rw [Set.mem_singleton_iff] at hx
      subst hx
      exact RingHom.isIntegralElem_localization_at_leadingCoeff (algebraMap B A) x f hft M
        (Submonoid.mem_powers _)
    | algebraMap r =>
      rw [← hφ]
      exact RingHom.isIntegralElem_map φ
    | add x y _ _ hx hy =>
      rw [map_add]
      exact RingHom.IsIntegralElem.add φ hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact RingHom.IsIntegralElem.mul φ hx hy
  have hint : φ.IsIntegral := by
    intro x
    obtain ⟨⟨s, ⟨_, m, hm, rfl⟩⟩, hx⟩ := IsLocalization.surj M' x
    obtain ⟨v, hv⟩ := isUnit_iff_exists_inv.mp
      (IsLocalization.map_units (Localization M) (⟨m, hm⟩ : M))
    have hv' : algebraMap A (Localization M') (algebraMap B A m) * φ v = 1 := by
      rw [← hφ, ← map_mul]
      have : algebraMap B (Localization M) m * v = 1 := hv
      rw [this, map_one]
    have hxe : x = algebraMap A (Localization M') s * φ v := by
      rw [← hx, mul_assoc]
      simp only [] at hv' ⊢
      rw [hv', mul_one]
    rw [hxe]
    exact RingHom.IsIntegralElem.mul φ (h1 s) (RingHom.isIntegralElem_map φ)
  have hφi : Function.Injective φ :=
    IsLocalization.map_injective_of_injective M (Localization M) (Localization M') hinj
  let y' : Localization M →+* K := IsLocalization.lift (M := M) (g := y) (by
    rintro ⟨_, n, rfl⟩
    simpa using (isUnit_iff_ne_zero.mpr hy).pow n)
  obtain ⟨ξ, hξ⟩ := ext_integral φ hφi hint y'
  refine ⟨ξ.comp (algebraMap A (Localization M')), RingHom.ext fun r => ?_⟩
  have h := RingHom.congr_fun hξ (algebraMap B (Localization M) r)
  simp only [RingHom.comp_apply, hφ] at h ⊢
  rw [h]
  exact IsLocalization.lift_eq _ r

private theorem one_gen {A B : Type} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [Algebra B A] (hinj : Function.Injective (algebraMap B A)) (t : A)
    (ht : Algebra.adjoin B {t} = ⊤) (a : A) (ha : a ≠ 0) :
    ∃ b : B, b ≠ 0 ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] (y : B →+* K), y b ≠ 0 →
      ∃ ξ : A →+* K, ξ.comp (algebraMap B A) = y ∧ ξ a ≠ 0 := by
  haveI : FaithfulSMul B A := (faithfulSMul_iff_algebraMap_injective B A).mpr hinj
  by_cases hta : IsAlgebraic B t
  · have haa : IsAlgebraic B a :=
      Algebra.isAlgebraic_adjoin_singleton_iff.mpr hta a (ht ▸ Algebra.mem_top)
    obtain ⟨f, hf, hft⟩ := hta
    obtain ⟨r, hr, d, hd⟩ := haa.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero ha)
    refine ⟨f.leadingCoeff * r, mul_ne_zero (leadingCoeff_ne_zero.mpr hf) hr,
      fun K _ _ y hy => ?_⟩
    rw [map_mul] at hy
    obtain ⟨ξ, hξ⟩ := gen_alg hinj t ht f hf hft y (left_ne_zero_of_mul hy)
    refine ⟨ξ, hξ, fun h0 => right_ne_zero_of_mul hy ?_⟩
    have h1 := congrArg ξ hd
    rw [map_mul, h0, zero_mul] at h1
    rw [← hξ]
    exact h1
  · have hsurj : Function.Surjective (aeval t : B[X] →ₐ[B] A) := by
      intro x
      have hx : x ∈ Algebra.adjoin B {t} := ht ▸ Algebra.mem_top
      rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
      exact hx
    have hbij : Function.Bijective (aeval t : B[X] →ₐ[B] A) :=
      ⟨transcendental_iff_injective.mp hta, hsurj⟩
    obtain ⟨p, rfl⟩ := hsurj a
    have hp : p ≠ 0 := fun h => ha (by simp [h])
    refine ⟨p.leadingCoeff, leadingCoeff_ne_zero.mpr hp, fun K _ _ y hy => ?_⟩
    have hpm : p.map y ≠ 0 := by
      intro h
      apply hy
      have := congrArg (fun q => q.coeff p.natDegree) h
      simpa [coeff_map] using this
    obtain ⟨r, hr⟩ : ∃ r, (p.map y).eval r ≠ 0 := by
      by_contra! h
      exact hpm (Polynomial.funext (by simpa using h))
    let e := AlgEquiv.ofBijective (aeval t : B[X] →ₐ[B] A) hbij
    refine ⟨(eval₂RingHom y r).comp (e.symm : A →+* B[X]), RingHom.ext fun x => ?_, ?_⟩
    · have : e.symm (algebraMap B A x) = C x := by
        rw [AlgEquiv.symm_apply_eq]
        simp [e]
      simp [this]
    · have : e.symm (aeval t p) = p := e.symm_apply_apply p
      simpa [this, eval_map] using hr

end UpperTheory.Reformulated.B.Ra5

theorem UpperTheory.Reformulated.B.Ra5.main_fin :
    ∀ (A : Type) [inst : CommRing A] [IsDomain A]
    (s : Finset A) (B : Type) [inst_2 : CommRing B] [IsDomain B] [inst_4 : Algebra B A],
    Algebra.adjoin B (↑s : Set A) = ⊤ →
      Function.Injective (⇑(Algebra.algebraMap B A) : B → A) →
        ∀ (a : A),
          a ≠ (0 : A) →
            ∃ (b : B),
              b ≠ (0 : B) ∧
                ∀ (K : Type) [inst_5 : Field K] [IsAlgClosed K] (y : B →+* K),
                  (y : B → K) b ≠ (0 : K) →
                    ∃ (ξ : A →+* K), ξ.comp (Algebra.algebraMap B A) = y ∧ (ξ : A → K) a ≠ (0 : K) := by
  intro A _ _ s
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro B _ _ _ htop hinj a ha
    have hinj' : Function.Injective (algebraMap B A) := hinj
    have hsurj : Function.Surjective (algebraMap B A) := by
      intro x
      have hx : x ∈ (⊥ : Subalgebra B A) := by
        rw [← Algebra.adjoin_empty B A, ← Finset.coe_empty, htop]
        exact Algebra.mem_top
      exact Algebra.mem_bot.mp hx
    obtain ⟨b, rfl⟩ := hsurj a
    let e := RingEquiv.ofBijective (algebraMap B A) ⟨hinj', hsurj⟩
    have hb : b ≠ 0 := fun h => ha (by simp [h])
    refine ⟨b, hb, fun K _ _ y hy => ⟨y.comp (e.symm : A →+* B), ?_, ?_⟩⟩
    · refine RingHom.ext fun x => ?_
      have : e.symm (algebraMap B A x) = x := e.symm_apply_apply x
      exact congrArg y this
    · have : e.symm (algebraMap B A b) = b := e.symm_apply_apply b
      simpa [this] using hy
  | insert t s' hts ih =>
    intro B _ _ _ htop hinj a ha
    have hinj' : Function.Injective (algebraMap B A) := hinj
    rw [Finset.coe_insert, Set.insert_eq, Algebra.adjoin_union_eq_adjoin_adjoin] at htop
    have h1 : Algebra.adjoin (Algebra.adjoin B ({t} : Set A)) (s' : Set A) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have hx : x ∈ Subalgebra.restrictScalars B
          (Algebra.adjoin (Algebra.adjoin B ({t} : Set A)) (s' : Set A)) := htop ▸ Algebra.mem_top
      exact hx
    obtain ⟨b₁, hb₁, h⟩ := ih (Algebra.adjoin B ({t} : Set A)) h1 Subtype.val_injective a ha
    let t₁ : Algebra.adjoin B ({t} : Set A) := ⟨t, Algebra.subset_adjoin rfl⟩
    have ht₁ : Algebra.adjoin B {t₁} = ⊤ := by
      apply Subalgebra.map_injective (f := (Algebra.adjoin B ({t} : Set A)).val)
        Subtype.val_injective
      rw [AlgHom.map_adjoin, Algebra.map_top, Subalgebra.range_val, Set.image_singleton]
      rfl
    have hinj₁ : Function.Injective (algebraMap B (Algebra.adjoin B ({t} : Set A))) := by
      intro x x' hxx
      exact hinj' (congrArg Subtype.val hxx)
    obtain ⟨b, hb, h2⟩ := one_gen hinj₁ t₁ ht₁ b₁ hb₁
    refine ⟨b, hb, fun K _ _ y hy => ?_⟩
    obtain ⟨ξ₁, h3, h4⟩ := h2 K y hy
    obtain ⟨ξ, h5, h6⟩ := h K ξ₁ h4
    refine ⟨ξ, RingHom.ext fun x => ?_, h6⟩
    have h7 := RingHom.congr_fun h5 (algebraMap B _ x)
    have h8 := RingHom.congr_fun h3 x
    exact h7.trans h8
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapInvolutionEqSelf
section
theorem UpperTheory.map_involution_eq_self :
    ∀ (X : Type) [MeasurableSpace X] (μ : MeasureTheory.Measure X) [MeasureTheory.SigmaFinite μ] (ι : X → X) (c : NNReal), Measurable ι → (∀ᵐ x ∂μ, ι (ι x) = x) → μ.map ι = c • μ → μ.map ι = μ := by
  intro X _ μ _ ι c hι hinv hc
  by_cases h0 : μ = 0
  · subst h0
    simp
  have h1 : (μ.map ι).map ι = μ := by
    rw [MeasureTheory.Measure.map_map hι hι]
    have h : (ι ∘ ι) =ᵐ[μ] id := hinv
    rw [MeasureTheory.Measure.map_congr h, MeasureTheory.Measure.map_id]
  have h2 : (c * c) • μ = μ := by
    calc (c * c) • μ = c • (c • μ) := mul_smul c c μ
      _ = c • μ.map ι := by rw [hc]
      _ = (c • μ).map ι := (MeasureTheory.Measure.map_smul c μ ι).symm
      _ = (μ.map ι).map ι := by rw [hc]
      _ = μ := h1
  obtain ⟨s, -, -, hs0, hs1⟩ :=
    MeasureTheory.Measure.exists_subset_measure_lt_top (μ := μ) (s := Set.univ) (r := 0)
      MeasurableSet.univ (MeasureTheory.Measure.measure_univ_pos.mpr h0)
  have h3 : ((c * c : NNReal) : ENNReal) * μ s = 1 * μ s := by
    have h := congrArg (fun ν : MeasureTheory.Measure X => ν s) h2
    simpa [ENNReal.smul_def] using h
  have h4 : ((c * c : NNReal) : ENNReal) = 1 :=
    (ENNReal.mul_left_inj hs0.ne' hs1.ne).mp h3
  have h5 : c * c = 1 := by exact_mod_cast h4
  have h6 : c = 1 := by
    have h : (c : ℝ) * c = 1 := by exact_mod_cast h5
    have hc0 : (0 : ℝ) ≤ c := c.2
    have h' : (c : ℝ) = 1 := by nlinarith
    exact_mod_cast h'
  rw [hc, h6, one_smul]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapLeftMulVolumeEq
section
private def UpperTheory.matrixSpaceLinearEquiv (n : ℕ) : (Fin n → Fin n → ℂ) ≃ₗ[ℂ] (Fin n → Fin n → ℂ) where
  toFun x := fun i j => x j i
  invFun x := fun i j => x j i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def UpperTheory.matrixLeftMulLinearMap (n : ℕ) (a : Fin n → Fin n → ℂ) :
    (Fin n → Fin n → ℂ) →ₗ[ℂ] (Fin n → Fin n → ℂ) :=
  (UpperTheory.matrixSpaceLinearEquiv n).toLinearMap ∘ₗ
    (LinearMap.pi fun j : Fin n => (Matrix.toLin' (Matrix.of a)).comp (LinearMap.proj j)) ∘ₗ
    (UpperTheory.matrixSpaceLinearEquiv n).symm.toLinearMap

private theorem UpperTheory.det_leftMulLinearMap (n : ℕ) (a : Fin n → Fin n → ℂ) :
    LinearMap.det (UpperTheory.matrixLeftMulLinearMap n a) = (Matrix.of a).det ^ n := by
  unfold UpperTheory.matrixLeftMulLinearMap
  rw [LinearMap.det_conj, LinearMap.det_pi]
  simp

theorem UpperTheory.map_left_mul_volume_eq :
    ∀ (n : ℕ) (a : Fin n → Fin n → ℂ), ‖(Matrix.of a).det‖ = 1 →
        MeasureTheory.Measure.map (fun x : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of a * Matrix.of x))
          (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Fin n → ℂ)) = MeasureTheory.volume := by
  intro n a ha
  have hf : (fun x : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of a * Matrix.of x))
      = ⇑((UpperTheory.matrixLeftMulLinearMap n a).restrictScalars ℝ) := by
    funext x i j
    rfl
  have hd : LinearMap.det ((UpperTheory.matrixLeftMulLinearMap n a).restrictScalars ℝ) = 1 := by
    rw [LinearMap.det_restrictScalars, UpperTheory.det_leftMulLinearMap, Algebra.norm_complex_apply, map_pow,
      Complex.normSq_eq_norm_sq, ha]
    simp
  haveI h1 : (MeasureTheory.volume : MeasureTheory.Measure (Fin n → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  haveI h2 : (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Fin n → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  rw [hf, MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar _
    (by rw [hd]; exact one_ne_zero), hd]
  simp
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.MapMulVolumeOfSubgroup
section
open MeasureTheory Set

private noncomputable def mulE {n : ℕ} (a x : Fin n → Fin n → ℂ) : Fin n → Fin n → ℂ :=
  Matrix.of.symm (Matrix.of a * Matrix.of x)

private lemma mulE_apply {n : ℕ} (a x : Fin n → Fin n → ℂ) (i j : Fin n) :
    mulE a x i j = ∑ k, a i k * x k j := by
  simp [mulE, Matrix.mul_apply]

private lemma continuous_mulE {n : ℕ} :
    Continuous (fun p : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) => mulE p.1 p.2) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [mulE_apply]
  fun_prop

private lemma measurable_mulE {n : ℕ} (a : Fin n → Fin n → ℂ) : Measurable (mulE a) :=
  (continuous_mulE.comp (Continuous.prodMk_right a)).measurable

private lemma norm_mulE_le {n : ℕ} (a x : Fin n → Fin n → ℂ) :
    ‖mulE a x‖ ≤ n * (‖a‖ * ‖x‖) := by
  have h0 : (0 : ℝ) ≤ n * (‖a‖ * ‖x‖) := by positivity
  refine (pi_norm_le_iff_of_nonneg h0).2 fun i => (pi_norm_le_iff_of_nonneg h0).2 fun j => ?_
  rw [mulE_apply]
  calc ‖∑ k, a i k * x k j‖ ≤ ∑ k, ‖a i k * x k j‖ := norm_sum_le _ _
    _ ≤ ∑ _k : Fin n, ‖a‖ * ‖x‖ := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul]
        exact mul_le_mul ((norm_le_pi_norm (a i) k).trans (norm_le_pi_norm a i))
          ((norm_le_pi_norm (x k) j).trans (norm_le_pi_norm x k)) (norm_nonneg _) (norm_nonneg _)
    _ = n * (‖a‖ * ‖x‖) := by simp

private lemma continuous_detE {n : ℕ} :
    Continuous (fun v : Fin n → Fin n → ℂ => (Matrix.of v).det) :=
  Continuous.matrix_det (A := fun v : Fin n → Fin n → ℂ => Matrix.of v) continuous_id

private lemma continuous_adjE {n : ℕ} :
    Continuous (fun v : Fin n → Fin n → ℂ =>
      (Matrix.of.symm (Matrix.of v).adjugate : Fin n → Fin n → ℂ)) :=
  Continuous.matrix_adjugate (A := fun v : Fin n → Fin n → ℂ => Matrix.of v) continuous_id

private lemma haarE (n : ℕ) :
    (volume : Measure (Fin n → Fin n → ℂ)).IsAddHaarMeasure := by
  haveI : (volume : Measure (Fin n → ℂ)).IsAddHaarMeasure :=
    Measure.pi.isAddHaarMeasure fun _ : Fin n => (volume : Measure ℂ)
  exact Measure.pi.isAddHaarMeasure fun _ : Fin n => (volume : Measure (Fin n → ℂ))

private lemma exists_pair (n : ℕ) :
    ∃ V K : Set (Fin n → Fin n → ℂ), IsCompact V ∧ IsCompact K ∧ 0 < volume V ∧
      ∀ y, ∀ v ∈ V, ∀ w ∈ V, mulE y v = w → y ∈ K := by
  haveI := haarE n
  have hU : IsOpen {v : Fin n → Fin n → ℂ | (Matrix.of v).det ≠ 0} :=
    isOpen_ne_fun continuous_detE continuous_const
  have h1 : (Matrix.of.symm (1 : Matrix (Fin n) (Fin n) ℂ)) ∈
      {v : Fin n → Fin n → ℂ | (Matrix.of v).det ≠ 0} := by simp
  obtain ⟨V, hV, hi, hsub⟩ := exists_compact_subset hU h1
  refine ⟨V, (fun p : (Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ) =>
    ((Matrix.of p.2).det)⁻¹ • mulE p.1 (Matrix.of.symm (Matrix.of p.2).adjugate)) '' (V ×ˢ V),
    hV, ?_, Measure.measure_pos_of_nonempty_interior _ ⟨_, hi⟩, ?_⟩
  · refine (hV.prod hV).image_of_continuousOn ?_
    refine ContinuousOn.fun_smul ?_ ?_
    · exact (continuous_detE.comp continuous_snd).continuousOn.inv₀ fun p hp => hsub hp.2
    · exact (continuous_mulE.comp
        (continuous_fst.prodMk (continuous_adjE.comp continuous_snd))).continuousOn
  · rintro y v hv w hw rfl
    refine ⟨(mulE y v, v), ⟨hw, hv⟩, ?_⟩
    have hd : (Matrix.of v).det ≠ 0 := hsub hv
    have : mulE (mulE y v) (Matrix.of.symm (Matrix.of v).adjugate) = (Matrix.of v).det • y := by
      simp only [mulE, Equiv.apply_symm_apply, Matrix.mul_assoc, Matrix.mul_adjugate,
        Matrix.mul_smul, Matrix.mul_one]
      rfl
    simp only [this, smul_smul, inv_mul_cancel₀ hd, one_smul]

private lemma mulE_cancel {n : ℕ} {a y v w : Fin n → Fin n → ℂ} (ha : (Matrix.of a).det ≠ 0)
    (h : mulE (mulE a y) v = mulE a w) : mulE y v = w := by
  have hu : IsUnit (Matrix.of a) := (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit ha)
  have h' : Matrix.of a * (Matrix.of y * Matrix.of v) = Matrix.of a * Matrix.of w := by
    rw [← Matrix.mul_assoc]
    exact h
  exact hu.mul_left_cancel h'

private lemma key {n : ℕ} {G : Set (Fin n → Fin n → ℂ)} {μ : Measure (Fin n → Fin n → ℂ)}
    [SFinite μ] (hG : μ Gᶜ = 0) (hdet : ∀ a ∈ G, (Matrix.of a).det ≠ 0)
    (hvol : ∀ a ∈ G, Measure.map (mulE a) volume = volume)
    (hinv : ∀ a ∈ G, Measure.map (mulE a) μ = μ)
    {V K B D : Set (Fin n → Fin n → ℂ)} (hV : IsCompact V) (hB : IsCompact B)
    (hD : MeasurableSet D)
    (hK : ∀ y, ∀ v ∈ V, ∀ w ∈ V, mulE y v = w → y ∈ K)
    (hBD : ∀ g ∈ B, ∀ v ∈ V, mulE g v ∈ D) :
    volume V * μ B ≤ μ K * volume D := by
  set S : Set ((Fin n → Fin n → ℂ) × (Fin n → Fin n → ℂ)) :=
    (fun p => (p.1, mulE p.1 p.2)) '' (B ×ˢ V) with hS
  have hSm : MeasurableSet S :=
    ((hB.prod hV).image (continuous_fst.prodMk continuous_mulE)).measurableSet
  have hae : ∀ᵐ g ∂μ, g ∈ G := hG
  have h1 : volume V * μ B ≤ (μ.prod volume) S := by
    rw [Measure.prod_apply hSm, ← lintegral_indicator_const hB.measurableSet]
    refine lintegral_mono_ae (hae.mono fun g hg => ?_)
    by_cases hgB : g ∈ B
    · rw [indicator_of_mem hgB]
      have hm : MeasurableSet (Prod.mk g ⁻¹' S) := measurable_prodMk_left hSm
      calc volume V ≤ volume (mulE g ⁻¹' (Prod.mk g ⁻¹' S)) :=
            measure_mono fun v hv => ⟨(g, v), ⟨hgB, hv⟩, rfl⟩
        _ = volume (Prod.mk g ⁻¹' S) := by
            rw [← Measure.map_apply (measurable_mulE g) hm, hvol g hg]
    · rw [indicator_of_notMem hgB]
      exact zero_le
  have h2 : (μ.prod volume) S ≤ μ K * volume D := by
    rw [Measure.prod_apply_symm hSm, ← lintegral_indicator_const hD]
    refine lintegral_mono fun x => ?_
    have hm : MeasurableSet ((fun g => (g, x)) ⁻¹' S) := measurable_prodMk_right hSm
    by_cases hne : (((fun g => (g, x)) ⁻¹' S) ∩ G).Nonempty
    · obtain ⟨a, ⟨⟨a', w⟩, ⟨haB, hw⟩, he⟩, haG⟩ := hne
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      show μ _ ≤ _
      rw [indicator_of_mem (hBD _ haB _ hw), ← hinv _ haG,
        Measure.map_apply (measurable_mulE _) hm, hinv _ haG]
      refine measure_mono ?_
      rintro y ⟨⟨g, v⟩, ⟨-, hv⟩, he'⟩
      obtain ⟨rfl, h'⟩ := Prod.mk.inj he'
      exact hK y v hv w hw (mulE_cancel (hdet _ haG) h')
    · have : μ ((fun g => (g, x)) ⁻¹' S) = 0 :=
        measure_mono_null (fun g hg hgG => hne ⟨g, hg, hgG⟩) hG
      show μ _ ≤ _
      rw [this]
      exact zero_le
  exact h1.trans h2

theorem UpperTheory.map_mul_volume_of_subgroup :
    ∀ (n : ℕ) (G : Set (Fin n → Fin n → ℂ)) (μ : MeasureTheory.Measure (Fin n → Fin n → ℂ)),
        μ Gᶜ = 0 →
        (∀ a ∈ G, ‖(Matrix.of a).det‖ = 1) →
        (∀ a ∈ G, MeasureTheory.Measure.map (fun x : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of a * Matrix.of x))
          (MeasureTheory.volume : MeasureTheory.Measure (Fin n → Fin n → ℂ)) = MeasureTheory.volume) →
        (∀ a ∈ G, MeasureTheory.Measure.map (fun x : Fin n → Fin n → ℂ => Matrix.of.symm (Matrix.of a * Matrix.of x)) μ = μ) →
        (∀ K : Set (Fin n → Fin n → ℂ), IsCompact K → μ K < ⊤) →
        ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R →
          μ {g | Real.sqrt (∑ i, ∑ j, Complex.normSq (g i j)) ≤ R} ≤ ENNReal.ofReal (C * R ^ (2 * n ^ 2)) := by
  intro n G μ hG hdet hvol hinv hfin
  haveI : IsFiniteMeasureOnCompacts μ := ⟨fun K hK => hfin K hK⟩
  haveI := haarE n
  obtain ⟨V, K, hV, hK, hpos, hVK⟩ := exists_pair n
  obtain ⟨M, hM0, hM⟩ := hV.isBounded.exists_pos_norm_le
  have hdim : Module.finrank ℝ (Fin n → Fin n → ℂ) = 2 * n ^ 2 := by
    simp [Module.finrank_pi_fintype]
    ring
  set c : ENNReal := μ K * volume (Metric.ball (0 : Fin n → Fin n → ℂ) 1) / volume V with hc
  have hcf : c ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.mul_ne_top (hfin K hK).ne measure_ball_lt_top.ne) hpos.ne'
  refine ⟨c.toReal * (n * M) ^ (2 * n ^ 2), fun R hR => ?_⟩
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hk := key (μ := μ) hG (fun a ha h => by simpa [h] using hdet a ha) hvol hinv hV
    (isCompact_closedBall (0 : Fin n → Fin n → ℂ) R)
    (D := Metric.closedBall 0 (n * M * R)) measurableSet_closedBall hVK (fun g hg v hv => by
      rw [mem_closedBall_zero_iff] at hg ⊢
      refine (norm_mulE_le g v).trans ?_
      have := hM v hv
      calc (n : ℝ) * (‖g‖ * ‖v‖) ≤ n * (R * M) := by gcongr
        _ = n * M * R := by ring)
  rw [Measure.addHaar_closedBall volume _ (by positivity), hdim] at hk
  have hsub : {g : Fin n → Fin n → ℂ | Real.sqrt (∑ i, ∑ j, Complex.normSq (g i j)) ≤ R} ⊆
      Metric.closedBall 0 R := by
    intro g hg
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg hR0).2 fun i => (pi_norm_le_iff_of_nonneg hR0).2 fun j => ?_
    refine le_trans (Real.le_sqrt_of_sq_le ?_) hg
    rw [← Complex.normSq_eq_norm_sq]
    calc Complex.normSq (g i j) ≤ ∑ j, Complex.normSq (g i j) :=
          Finset.single_le_sum (f := fun j => Complex.normSq (g i j))
            (fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i, ∑ j, Complex.normSq (g i j) :=
          Finset.single_le_sum (f := fun i => ∑ j, Complex.normSq (g i j))
            (fun _ _ => Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _) (Finset.mem_univ i)
  refine (measure_mono hsub).trans ?_
  have hVf : volume V ≠ ⊤ := hV.measure_lt_top.ne
  calc μ (Metric.closedBall 0 R) ≤ (μ K * (ENNReal.ofReal ((n * M * R) ^ (2 * n ^ 2)) *
        volume (Metric.ball (0 : Fin n → Fin n → ℂ) 1))) / volume V := by
        rw [ENNReal.le_div_iff_mul_le (Or.inl hpos.ne') (Or.inl hVf), mul_comm]
        exact hk
    _ = c * ENNReal.ofReal ((n * M * R) ^ (2 * n ^ 2)) := by
        rw [hc, div_eq_mul_inv, div_eq_mul_inv]
        ring
    _ = ENNReal.ofReal (c.toReal * (n * M) ^ (2 * n ^ 2) * R ^ (2 * n ^ 2)) := by
        rw [mul_assoc c.toReal, ← mul_pow, ENNReal.ofReal_mul ENNReal.toReal_nonneg,
          ENNReal.ofReal_toReal hcf]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SmoothOf
section
noncomputable def UpperTheory.Reformulated.B.SmoothnessCriteria.IsSmooth :
    {k G V : Type} →
      [inst : Field k] →
        [inst_1 : Group G] →
          [inst_2 : AddCommGroup V] → [inst_3 : _root_.Module k V] → [TopologicalSpace G] → Representation k G V → Prop :=
    fun {k G V : Type} [Field k] [Group G] [AddCommGroup V] [_root_.Module k V] [TopologicalSpace G]
        (ρ : Representation k G V) ↦
      ∀ (v : V), IsOpen {g : G | ((ρ : G → V →ₗ[k] V) g : V → V) v = v}
end

