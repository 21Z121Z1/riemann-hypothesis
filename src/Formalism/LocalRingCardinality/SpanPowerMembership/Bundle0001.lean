import Mathlib

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.BasisOfBasisF
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open scoped TensorProduct nonZeroDivisors

section Kap

variable (A B : Type) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Algebra A B]
  [Algebra.IsIntegral A B]

theorem isFrac_tensor (hinj : Function.Injective (algebraMap A B)) :
    IsFractionRing B (B ⊗[A] FractionRing A) := by
  have h0 : IsLocalization (Algebra.algebraMapSubmonoid B A⁰) (B ⊗[A] FractionRing A) := inferInstance
  refine IsLocalization.of_le (Algebra.algebraMapSubmonoid B A⁰) B⁰ ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero ha))
  · intro r hr
    have hr0 : r ≠ 0 := nonZeroDivisors.ne_zero hr
    have hne := Ideal.comap_ne_bot_of_integral_mem (R := A) (I := Ideal.span {r}) hr0
      (Ideal.mem_span_singleton_self r) (Algebra.IsIntegral.isIntegral r)
    obtain ⟨d, hd, hd0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton.mp (Ideal.mem_comap.mp hd)
    have hu : IsUnit (algebraMap B (B ⊗[A] FractionRing A) (algebraMap A B d)) :=
      IsLocalization.map_units (M := Algebra.algebraMapSubmonoid B A⁰) _
        ⟨_, ⟨d, mem_nonZeroDivisors_of_ne_zero hd0, rfl⟩⟩
    rw [hs, map_mul] at hu
    exact isUnit_of_mul_isUnit_left hu

def kap (hinj : Function.Injective (algebraMap A B)) : (B ⊗[A] FractionRing A) ≃ₐ[B] FractionRing B :=
  haveI := isFrac_tensor A B hinj
  IsLocalization.algEquiv B⁰ _ _

variable (ι : Type) [Fintype ι] [DecidableEq ι]

def vecE (hinj : Function.Injective (algebraMap A B)) :
    (ι → FractionRing B) ≃ₗ[B] B ⊗[A] (ι → FractionRing A) :=
  (LinearEquiv.piCongrRight fun _ : ι => (kap A B hinj).symm.toLinearEquiv) ≪≫ₗ
    (TensorProduct.piRight A B B (fun _ : ι => FractionRing A)).symm

theorem vecE_single (hinj : Function.Injective (algebraMap A B)) (a : ι) :
    vecE A B ι hinj (Pi.single a 1) = (1 : B) ⊗ₜ[A] (Pi.single a 1 : ι → FractionRing A) := by
  unfold vecE
  rw [LinearEquiv.trans_apply, LinearEquiv.symm_apply_eq]
  funext j
  rw [TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul]
  show (kap A B hinj).symm ((Pi.single a 1 : ι → FractionRing B) j) = _
  by_cases h : j = a
  · subst h
    rw [Pi.single_eq_same, map_one]
    show (1 : B ⊗[A] FractionRing A) = 1 ⊗ₜ[A] (Pi.single j 1 : ι → FractionRing A) j
    rw [Pi.single_eq_same]
    rfl
  · rw [Pi.single_eq_of_ne h, map_zero]
    show (0 : B ⊗[A] FractionRing A) = 1 ⊗ₜ[A] (Pi.single a 1 : ι → FractionRing A) j
    rw [Pi.single_eq_of_ne h, TensorProduct.tmul_zero]

theorem single_li (hB : Function.Injective (algebraMap B (FractionRing B))) :
    LinearIndependent B (fun a : ι => (Pi.single a 1 : ι → FractionRing B)) := by
  have h := (Pi.basisFun (FractionRing B) ι).linearIndependent
  have h2 := h.restrict_scalars (R := B) (by
    intro x y hxy
    simpa [Algebra.smul_def] using hB (by simpa [Algebra.smul_def] using hxy))
  have e : (fun a : ι => (Pi.single a 1 : ι → FractionRing B)) = ⇑(Pi.basisFun (FractionRing B) ι) :=
    funext fun a => (Pi.basisFun_apply _ _ a).symm
  rw [e]; exact h2

end Kap

theorem basis_of_basisF {K F W M ι κ : Type} [Field K] [Field F] [AddCommGroup W] [Module K W] [AddCommGroup M]
    [Module F M] [Fintype ι] [Fintype κ] (σ : K →+* F) (e : W →ₛₗ[σ] M)
    (b : Module.Basis ι K W)
    (hb : LinearIndependent F (fun i => e (b i)) ∧ Submodule.span F (Set.range fun i => e (b i)) = ⊤)
    (b' : Module.Basis κ K W) :
    LinearIndependent F (fun i => e (b' i)) ∧ Submodule.span F (Set.range fun i => e (b' i)) = ⊤ := by
  have hexp' : ∀ x : W, e x = ∑ i, σ (b'.repr x i) • e (b' i) := fun x => by
    conv_lhs => rw [← b'.sum_repr x]
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => LinearMap.map_smulₛₗ e _ _
  have hspan : Submodule.span F (Set.range fun i => e (b' i)) = ⊤ := by
    rw [eq_top_iff, ← hb.2, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    show e (b i) ∈ _
    rw [hexp' (b i)]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  refine ⟨?_, hspan⟩
  have hcard : Fintype.card κ = Fintype.card ι := by
    rw [← Module.finrank_eq_card_basis b', ← Module.finrank_eq_card_basis b]
  let B : Module.Basis ι F M := Module.Basis.mk hb.1 hb.2.ge
  have hfin : Module.finrank F M = Fintype.card κ := by
    rw [Module.finrank_eq_card_basis B, hcard]
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hspan.ge hfin.symm

end Formalism.BasicNotions.Examples₂.NZ
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.GatRing
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.GatR

open QuadraticAlgebra IsLocalRing

variable {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] {ϖ : W}

theorem om_sq : (ω : QuadraticAlgebra W ϖ 0) ^ 2 = algebraMap W _ ϖ := by
  rw [sq, algebraMap_eq]; ext <;> simp

theorem om_pow (n : ℕ) : (ω : QuadraticAlgebra W ϖ 0) ^ (2 * n) = algebraMap W _ (ϖ ^ n) := by
  rw [pow_mul, om_sq, map_pow]

theorem isUnit_of_re (hϖ : Irreducible ϖ) (z : QuadraticAlgebra W ϖ 0) (h : IsUnit z.re) : IsUnit z := by
  rw [isUnit_iff_norm_isUnit, norm_def]
  by_contra hn
  have h1 : ϖ * z.im * z.im ∈ nonunits W := fun hu =>
    hϖ.not_isUnit (isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left hu))
  have h2 := nonunits_add (show _ ∈ nonunits W from hn) h1
  have e : z.re * z.re + 0 * z.re * z.im - ϖ * z.im * z.im + ϖ * z.im * z.im = z.re * z.re := by ring
  rw [e] at h2
  exact h2 (h.mul h)

theorem om_not_isUnit (hϖ : Irreducible ϖ) : ¬ IsUnit (ω : QuadraticAlgebra W ϖ 0) := by
  rw [isUnit_iff_norm_isUnit, norm_def]
  simp only [omega_re, omega_im]
  intro h
  have e : (0 : W) * 0 + 0 * 0 * 1 - ϖ * 1 * 1 = -ϖ := by ring
  rw [e, IsUnit.neg_iff] at h
  exact hϖ.not_isUnit h

theorem fact (hϖ : Irreducible ϖ) (z : QuadraticAlgebra W ϖ 0) (hz : z ≠ 0) :
    ∃ (n : ℕ) (u : QuadraticAlgebra W ϖ 0), IsUnit u ∧ z = ω ^ n * u := by
  have caseB : ∀ (j : ℕ) (v : Wˣ) (a' : W), z.im = v * ϖ ^ j → z.re = ϖ ^ (j + 1) * a' →
      ∃ (n : ℕ) (u : QuadraticAlgebra W ϖ 0), IsUnit u ∧ z = ω ^ n * u := fun j v a' h1 h2 => by
    refine ⟨2 * j + 1, ⟨v, a'⟩, isUnit_of_re hϖ _ v.isUnit, ?_⟩
    rw [pow_succ, om_pow, algebraMap_eq]
    ext
    · simp only [re_mul, im_mul, omega_re, omega_im, h2]; ring
    · simp only [re_mul, im_mul, omega_re, omega_im, h1]; ring
  by_cases ha : z.re = 0
  · have hb : z.im ≠ 0 := fun hb => hz (by ext <;> simp [ha, hb])
    obtain ⟨j, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
    exact caseB j v 0 hv (by rw [ha, mul_zero])
  · obtain ⟨i, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha hϖ
    by_cases hd : ϖ ^ i ∣ z.im
    · obtain ⟨b', hb'⟩ := hd
      refine ⟨2 * i, ⟨u, b'⟩, isUnit_of_re hϖ _ u.isUnit, ?_⟩
      rw [om_pow, algebraMap_eq]
      ext
      · simp [hu]; ring
      · simp [hb']
    · have hb : z.im ≠ 0 := fun hb => hd (by rw [hb]; exact dvd_zero _)
      obtain ⟨j, v, hv⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb hϖ
      have hji : j < i := by
        by_contra hc
        exact hd (hv ▸ Dvd.dvd.mul_left (pow_dvd_pow ϖ (not_lt.mp hc)) _)
      obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_lt hji
      exact caseB j v (u * ϖ ^ c) hv (by rw [hu]; ring)

theorem om_pow_ne_zero (hϖ : Irreducible ϖ) (n : ℕ) : (ω : QuadraticAlgebra W ϖ 0) ^ n ≠ 0 := by
  intro h
  have h2 : (ω : QuadraticAlgebra W ϖ 0) ^ (2 * n) = 0 := by rw [two_mul, pow_add, h, mul_zero]
  rw [om_pow, map_eq_zero_iff _ algebraMap_injective] at h2
  exact pow_ne_zero n hϖ.ne_zero h2

theorem isDomain (hϖ : Irreducible ϖ) : IsDomain (QuadraticAlgebra W ϖ 0) := by
  have : NoZeroDivisors (QuadraticAlgebra W ϖ 0) := ⟨fun {x y} hxy => by
    by_contra hc
    rw [not_or] at hc
    obtain ⟨n, u, hu, rfl⟩ := fact hϖ x hc.1
    obtain ⟨m, v, hv, rfl⟩ := fact hϖ y hc.2
    have e : ω ^ n * u * (ω ^ m * v) = ω ^ (n + m) * (u * v) := by ring
    rw [e] at hxy
    exact om_pow_ne_zero hϖ (n + m) ((hu.mul hv).mul_left_eq_zero.mp hxy)⟩
  exact NoZeroDivisors.to_isDomain _

theorem om_irreducible (hϖ : Irreducible ϖ) : Irreducible (ω : QuadraticAlgebra W ϖ 0) := by
  have := isDomain hϖ
  refine ⟨om_not_isUnit hϖ, fun x y hxy => ?_⟩
  have h0 : (ω : QuadraticAlgebra W ϖ 0) ≠ 0 := by simpa using om_pow_ne_zero hϖ 1
  have hx : x ≠ 0 := fun h => h0 (by rw [hxy, h, zero_mul])
  have hy : y ≠ 0 := fun h => h0 (by rw [hxy, h, mul_zero])
  obtain ⟨n, u, hu, rfl⟩ := fact hϖ x hx
  obtain ⟨m, v, hv, rfl⟩ := fact hϖ y hy
  rcases n with _ | n
  · left; simpa using hu
  rcases m with _ | m
  · right; simpa using hv
  exfalso
  have e : (ω : QuadraticAlgebra W ϖ 0) * 1 = ω * (ω * (ω ^ (n + m) * (u * v))) := by
    rw [mul_one]; conv_lhs => rw [hxy]
    ring
  exact om_not_isUnit hϖ (IsUnit.of_mul_eq_one _ (mul_left_cancel₀ h0 e).symm)

theorem isDVR (hϖ : Irreducible ϖ) :
    haveI := isDomain hϖ; IsDiscreteValuationRing (QuadraticAlgebra W ϖ 0) := by
  have := isDomain hϖ
  refine IsDiscreteValuationRing.ofHasUnitMulPowIrreducibleFactorization
    ⟨ω, om_irreducible hϖ, fun {x} hx => ?_⟩
  obtain ⟨n, u, hu, rfl⟩ := fact hϖ x hx
  exact ⟨n, hu.unit, rfl⟩

theorem mem_span_om_pow (m : ℕ) (z : QuadraticAlgebra W ϖ 0) :
    z ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ (2 * m)} ↔ ϖ ^ m ∣ z.re ∧ ϖ ^ m ∣ z.im := by
  rw [Ideal.mem_span_singleton, om_pow, algebraMap_eq]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨⟨t.re, by simp⟩, ⟨t.im, by simp⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    exact ⟨⟨a, b⟩, by ext <;> simp [ha, hb]⟩

theorem isAdicComplete (hϖ : Irreducible ϖ) (hC : IsAdicComplete (Ideal.span {ϖ}) W) :
    haveI := isDomain hϖ; haveI := isDVR hϖ
    IsAdicComplete (maximalIdeal (QuadraticAlgebra W ϖ 0)) (QuadraticAlgebra W ϖ 0) := by
  have := isDomain hϖ
  have := isDVR hϖ
  have keyO : ∀ (n : ℕ) (x y : QuadraticAlgebra W ϖ 0),
      x ≡ y [SMOD (maximalIdeal (QuadraticAlgebra W ϖ 0) ^ n • ⊤ : Submodule _ (QuadraticAlgebra W ϖ 0))] ↔
        x - y ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ n} := fun n x y => by
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, (om_irreducible hϖ).maximalIdeal_eq,
      Ideal.span_singleton_pow]
  have keyW : ∀ (n : ℕ) (x y : W),
      x ≡ y [SMOD (Ideal.span {ϖ} ^ n • ⊤ : Submodule W W)] ↔ ϖ ^ n ∣ x - y := fun n x y => by
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  have hle : ∀ {m n : ℕ}, m ≤ n → Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ n} ≤ Ideal.span {ω ^ m} :=
    fun h => (Ideal.span_singleton_le_span_singleton).mpr (pow_dvd_pow _ h)
  refine { toIsHausdorff := inferInstance, prec' := fun f hf => ?_ }
  have hf' : ∀ {m n : ℕ}, m ≤ n → f (2 * m) - f (2 * n) ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ (2 * m)} :=
    fun h => (keyO _ _ _).mp (hf (Nat.mul_le_mul_left 2 h))
  obtain ⟨a, ha⟩ := hC.toIsPrecomplete.prec' (fun m => (f (2 * m)).re)
    (fun {m n} h => (keyW _ _ _).mpr (by simpa using ((mem_span_om_pow m _).mp (hf' h)).1))
  obtain ⟨b, hb⟩ := hC.toIsPrecomplete.prec' (fun m => (f (2 * m)).im)
    (fun {m n} h => (keyW _ _ _).mpr (by simpa using ((mem_span_om_pow m _).mp (hf' h)).2))
  refine ⟨⟨a, b⟩, fun n => (keyO _ _ _).mpr ?_⟩
  have h1 : f n - f (2 * n) ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ n} :=
    (keyO _ _ _).mp (hf (by omega))
  have h2 : f (2 * n) - ⟨a, b⟩ ∈ Ideal.span {(ω : QuadraticAlgebra W ϖ 0) ^ n} :=
    hle (by omega : n ≤ 2 * n) ((mem_span_om_pow n _).mpr
      ⟨by simpa using (keyW _ _ _).mp (ha n), by simpa using (keyW _ _ _).mp (hb n)⟩)
  have e : f n - ⟨a, b⟩ = (f n - f (2 * n)) + (f (2 * n) - ⟨a, b⟩) := by ring
  rw [e]
  exact add_mem h1 h2

end Formalism.BasicNotions.Examples₂.GatR
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.HasStrictFDerivAtExpZero
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.CD

open Filter Topology Metric NormedSpace Asymptotics

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem hasStrictFDerivAt_exp_zero_alt : HasStrictFDerivAt (exp : 𝔸 → 𝔸)
    ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := by
  have h := hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)
  exact h

variable (𝔸) in

def logA : 𝔸 → 𝔸 := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).localInverse _ _ _

theorem logA_exp : ∀ᶠ X in 𝓝 (0 : 𝔸), logA 𝔸 (exp X) = X := hasStrictFDerivAt_exp_zero_alt.eventually_left_inverse

theorem exp_logA : ∀ᶠ h in 𝓝 (1 : 𝔸), exp (logA 𝔸 h) = h := by
  have h := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).eventually_right_inverse
  rw [exp_zero] at h
  exact h

theorem logA_one : logA 𝔸 (1 : 𝔸) = 0 := by
  have h := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).localInverse_apply_image
  rw [exp_zero] at h
  exact h

theorem hasStrict_logA : HasStrictFDerivAt (logA 𝔸) (ContinuousLinearMap.id ℝ 𝔸) (1 : 𝔸) := by
  have h := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).to_localInverse
  rw [exp_zero] at h
  exact h

theorem exp_cont : Continuous (exp : 𝔸 → 𝔸) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  exact NormedSpace.exp_continuous

theorem exp_neg_mul (X : 𝔸) : exp (-X) * exp X = 1 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_add_of_commute (Commute.neg_left (Commute.refl X)), neg_add_cancel, exp_zero]

theorem exp_mul_neg (X : 𝔸) : exp X * exp (-X) = 1 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_add_of_commute (Commute.neg_right (Commute.refl X)), add_neg_cancel, exp_zero]

def F1 (p : 𝔸 × 𝔸) : 𝔸 := logA 𝔸 (exp (-p.1) * exp (p.1 + p.2))

def F2 (p : 𝔸 × 𝔸) : 𝔸 := logA 𝔸 (exp p.1 * exp p.2)

theorem hasStrict_exp_comp (L : 𝔸 × 𝔸 →L[ℝ] 𝔸) :
    HasStrictFDerivAt (fun p : 𝔸 × 𝔸 => exp (L p)) L (0 : 𝔸 × 𝔸) := by
  have h0 : HasStrictFDerivAt (exp : 𝔸 → 𝔸)
      ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) (L 0) := by
    rw [map_zero]
    exact hasStrictFDerivAt_exp_zero_alt
  have h := h0.comp (0 : 𝔸 × 𝔸) L.hasStrictFDerivAt
  simpa using h

theorem hasStrict_mul (L M : 𝔸 × 𝔸 →L[ℝ] 𝔸) :
    HasStrictFDerivAt (fun p : 𝔸 × 𝔸 => logA 𝔸 (exp (L p) * exp (M p))) (L + M) (0 : 𝔸 × 𝔸) := by
  have hprod := (hasStrict_exp_comp L).mul' (hasStrict_exp_comp M)
  simp only [map_zero, exp_zero, one_smul, MulOpposite.op_one] at hprod
  have hlog : HasStrictFDerivAt (logA 𝔸) (ContinuousLinearMap.id ℝ 𝔸)
      (((fun p : 𝔸 × 𝔸 => exp (L p)) * fun p : 𝔸 × 𝔸 => exp (M p)) 0) := by
    simp only [Pi.mul_apply, map_zero, exp_zero, mul_one]
    exact hasStrict_logA
  have h := hlog.comp (0 : 𝔸 × 𝔸) hprod
  rw [ContinuousLinearMap.id_comp, add_comm] at h
  exact h

theorem hasStrictFDerivAt_translateLog : HasStrictFDerivAt (F1 (𝔸 := 𝔸)) (ContinuousLinearMap.snd ℝ 𝔸 𝔸) 0 := by
  have h := hasStrict_mul (𝔸 := 𝔸) (-ContinuousLinearMap.fst ℝ 𝔸 𝔸)
    (ContinuousLinearMap.fst ℝ 𝔸 𝔸 + ContinuousLinearMap.snd ℝ 𝔸 𝔸)
  rw [neg_add_cancel_left] at h
  have hf : F1 (𝔸 := 𝔸) = fun p => logA 𝔸 (exp ((-ContinuousLinearMap.fst ℝ 𝔸 𝔸) p) *
      exp ((ContinuousLinearMap.fst ℝ 𝔸 𝔸 + ContinuousLinearMap.snd ℝ 𝔸 𝔸) p)) := by
    funext p
    simp [F1]
  rw [hf]
  exact h

theorem hasStrictFDerivAt_productLog : HasStrictFDerivAt (F2 (𝔸 := 𝔸))
    (ContinuousLinearMap.fst ℝ 𝔸 𝔸 + ContinuousLinearMap.snd ℝ 𝔸 𝔸) 0 := hasStrict_mul (ContinuousLinearMap.fst ℝ 𝔸 𝔸) (ContinuousLinearMap.snd ℝ 𝔸 𝔸)

theorem eventually_pair {P : 𝔸 × 𝔸 → Prop} (h : ∀ᶠ p in 𝓝 (0 : 𝔸 × 𝔸), P p) :
    ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ → P (X, Y) := by
  obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun X Y hX hY => hP ?_⟩
  rw [dist_zero_right, Prod.norm_def]
  exact max_lt hX hY

theorem strict_est {F : 𝔸 × 𝔸 → 𝔸} {F' : 𝔸 × 𝔸 →L[ℝ] 𝔸} (hF : HasStrictFDerivAt F F' 0)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ →
      ‖F (X, Y) - F (X, 0) - F' (0, Y)‖ ≤ ε * ‖Y‖ := by
  have h := hF.isLittleO.def hε
  obtain ⟨δ, hδ, hq⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun X Y hX hY => ?_⟩
  have hd : dist ((X, Y), (X, (0 : 𝔸))) ((0 : 𝔸 × 𝔸), (0 : 𝔸 × 𝔸)) < δ := by
    rw [dist_eq_norm]
    have e : ((X, Y), (X, (0 : 𝔸))) - ((0 : 𝔸 × 𝔸), (0 : 𝔸 × 𝔸)) = ((X, Y), (X, 0)) := by simp
    rw [e, Prod.norm_def, Prod.norm_def, Prod.norm_def]
    simp only [norm_zero]
    exact max_lt (max_lt hX hY) (max_lt hX hδ)
  have h1 := hq hd
  beta_reduce at h1
  have e2 : ((X, Y) - (X, 0) : 𝔸 × 𝔸) = (0, Y) := by simp
  rw [e2, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] at h1
  exact h1

theorem distortion {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ →
    (exp (F1 (X, Y)) = exp (-X) * exp (X + Y) ∧ ‖F1 (X, Y) - Y‖ ≤ ε * ‖Y‖) ∧
    (exp (F2 (X, Y)) = exp X * exp Y ∧ ‖F2 (X, Y) - X - Y‖ ≤ ε * ‖Y‖) := by
  have hc1 : Continuous (fun p : 𝔸 × 𝔸 => exp (-p.1) * exp (p.1 + p.2)) :=
    (exp_cont.comp continuous_fst.neg).mul (exp_cont.comp (continuous_fst.add continuous_snd))
  have hc2 : Continuous (fun p : 𝔸 × 𝔸 => exp p.1 * exp p.2) :=
    (exp_cont.comp continuous_fst).mul (exp_cont.comp continuous_snd)
  have e1 : ∀ᶠ p in 𝓝 (0 : 𝔸 × 𝔸),
      exp (logA 𝔸 (exp (-p.1) * exp (p.1 + p.2))) = exp (-p.1) * exp (p.1 + p.2) := by
    have ht := hc1.tendsto 0
    simp only [Prod.fst_zero, Prod.snd_zero, neg_zero, add_zero, exp_zero, mul_one] at ht
    exact ht.eventually exp_logA
  have e2 : ∀ᶠ p in 𝓝 (0 : 𝔸 × 𝔸), exp (logA 𝔸 (exp p.1 * exp p.2)) = exp p.1 * exp p.2 := by
    have ht := hc2.tendsto 0
    simp only [Prod.fst_zero, Prod.snd_zero, exp_zero, mul_one] at ht
    exact ht.eventually exp_logA
  have e3 : ∀ᶠ p in 𝓝 (0 : 𝔸 × 𝔸), logA 𝔸 (exp p.1) = p.1 := by
    have ht := (continuous_fst (X := 𝔸) (Y := 𝔸)).tendsto 0
    simp only [Prod.fst_zero] at ht
    exact ht.eventually logA_exp
  obtain ⟨δ1, hδ1, h1⟩ := eventually_pair (e1.and (e2.and e3))
  obtain ⟨δ2, hδ2, h2⟩ := strict_est (hasStrictFDerivAt_translateLog (𝔸 := 𝔸)) hε
  obtain ⟨δ3, hδ3, h3⟩ := strict_est (hasStrictFDerivAt_productLog (𝔸 := 𝔸)) hε
  refine ⟨min δ1 (min δ2 δ3), lt_min hδ1 (lt_min hδ2 hδ3), fun X Y hX hY => ?_⟩
  have hX1 : ‖X‖ < δ1 := lt_of_lt_of_le hX (min_le_left _ _)
  have hY1 : ‖Y‖ < δ1 := lt_of_lt_of_le hY (min_le_left _ _)
  have hX2 : ‖X‖ < δ2 := lt_of_lt_of_le hX ((min_le_right _ _).trans (min_le_left _ _))
  have hY2 : ‖Y‖ < δ2 := lt_of_lt_of_le hY ((min_le_right _ _).trans (min_le_left _ _))
  have hX3 : ‖X‖ < δ3 := lt_of_lt_of_le hX ((min_le_right _ _).trans (min_le_right _ _))
  have hY3 : ‖Y‖ < δ3 := lt_of_lt_of_le hY ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨k1, k2, k3⟩ := h1 X Y hX1 hY1
  refine ⟨⟨k1, ?_⟩, ⟨k2, ?_⟩⟩
  · have h := h2 X Y hX2 hY2
    have hz : F1 (X, (0 : 𝔸)) = 0 := by
      simp only [F1, add_zero, exp_neg_mul, logA_one]
    rw [hz, sub_zero] at h
    simpa using h
  · have h := h3 X Y hX3 hY3
    have hz : F2 (X, (0 : 𝔸)) = X := by
      simp only [F2, exp_zero, mul_one]
      exact k3
    rw [hz] at h
    simpa using h

end Formalism.BasicNotions.Examples₂.CD
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.NZColB
section
namespace Formalism.BasicNotions.Examples₂.NZ

open IsDedekindDomain

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {V : Type*} [AddCommGroup V] [Module R V]

def glue (A : HeightOneSpectrum R → Submodule R V) : Submodule R V := ⨅ w, A w

theorem not_le_of_prod {S : Finset (HeightOneSpectrum R)} (m : HeightOneSpectrum R → ℕ) (w : HeightOneSpectrum R)
    (hw : w ∉ S) : ¬ (∏ v ∈ S, v.asIdeal ^ m v) ≤ w.asIdeal := by
  intro h
  obtain ⟨v, hv, hle⟩ := (w.isPrime.prod_le).mp h
  have h2 : v.asIdeal ≤ w.asIdeal := w.isPrime.le_of_pow_le hle
  have h3 : v.asIdeal = w.asIdeal := (v.isMaximal).eq_of_le w.isPrime.ne_top h2
  exact hw (HeightOneSpectrum.ext h3 ▸ hv)

theorem glue_loc (A : HeightOneSpectrum R → Submodule R V)
    (hsat : ∀ w (s : R), s ∉ w.asIdeal → ∀ x, s • x ∈ A w → x ∈ A w)
    (hfin : ∀ x : V, {w | x ∉ A w}.Finite)
    (habs : ∀ w (x : V), ∃ m : ℕ, ∀ a ∈ w.asIdeal ^ m, a • x ∈ A w)
    (w : HeightOneSpectrum R) (x : V) :
    (∃ s : R, s ∉ w.asIdeal ∧ s • x ∈ glue A) ↔ x ∈ A w := by
  constructor
  · rintro ⟨s, hs, hx⟩
    exact hsat w s hs x ((Submodule.mem_iInf _).mp hx w)
  · intro hx
    classical
    choose m hm using fun v => habs v x
    have hw : w ∉ (hfin x).toFinset := by simpa using hx
    obtain ⟨s, hsI, hsw⟩ := SetLike.not_le_iff_exists.mp (not_le_of_prod m w hw)
    refine ⟨s, hsw, (Submodule.mem_iInf _).mpr fun v => ?_⟩
    by_cases hv : x ∈ A v
    · exact (A v).smul_mem s hv
    · exact hm v s (Ideal.prod_le_inf.trans (Finset.inf_le ((hfin x).mem_toFinset.mpr hv)) hsI)

end Formalism.BasicNotions.Examples₂.NZ
end

