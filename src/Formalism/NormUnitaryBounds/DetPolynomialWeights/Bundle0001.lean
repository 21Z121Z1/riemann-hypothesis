import Formalism.NormUnitaryBounds.Statement

-- bundled from Formalism.NormUnitaryBounds.DetPolynomialWeights.CoefficientBoundHolds
section
open Module

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

lemma addVal_prod {ι : Type*} (s : Finset ι) (c : ι → R) :
    IsDiscreteValuationRing.addVal R (∏ i ∈ s, c i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal R (c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, AddValuation.map_mul, ih]

lemma length_quot_zero : Module.length R (R ⧸ Ideal.span ({0} : Set R)) = ⊤ := by
  have := Ring.ord_eq_addVal (R := R) 0
  simpa [Ring.ord] using this

lemma key {ρ : ℕ} (P : Submodule R (Fin ρ → R)) (n : ℕ)
    (hP : Module.length R ((Fin ρ → R) ⧸ P) ≤ n) (ϖ : R) (hϖ : Irreducible ϖ) :
    ∃ G : Matrix (Fin ρ) (Fin ρ) R, (∀ i, G i ∈ P) ∧ G.det ∣ ϖ ^ n := by
  classical
  obtain ⟨n', snf⟩ := P.smithNormalForm (Pi.basisFun R (Fin ρ))
  have hsurj : Function.Surjective snf.f := by
    by_contra h
    obtain ⟨k, hk⟩ : ∃ k, k ∉ Set.range snf.f := by
      simp only [Function.Surjective, not_forall] at h
      obtain ⟨k, hk⟩ := h
      exact ⟨k, by simpa using hk⟩
    let L : (Fin ρ → R) →ₗ[R] R ⧸ Ideal.span ({0} : Set R) :=
      (Ideal.span ({0} : Set R)).mkQ ∘ₗ snf.bM.coord k
    have hle : P ≤ LinearMap.ker L := fun x hx => by
      have := snf.le_ker_coord_of_notMem_range hk hx
      rw [LinearMap.mem_ker] at this ⊢
      simp [L, this]
    have hLs : Function.Surjective (P.liftQ L hle) := by
      intro y
      obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      exact ⟨Submodule.Quotient.mk (r • snf.bM k), by
        simp [L]; rw [Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]⟩
    have h1 := Module.length_le_of_surjective (P.liftQ L hle) hLs
    rw [length_quot_zero] at h1
    exact absurd (h1.trans hP) (by simp)
  let σ : Fin n' ≃ Fin ρ := Equiv.ofBijective snf.f ⟨snf.f.injective, hsurj⟩
  have hσ : ∀ k, snf.f (σ.symm k) = k := fun k => σ.apply_symm_apply k
  let c : Fin ρ → R := fun k => snf.a (σ.symm k)
  let G : Matrix (Fin ρ) (Fin ρ) R := fun k => (snf.bN (σ.symm k) : Fin ρ → R)
  have hGrow : ∀ k, G k = c k • snf.bM k := fun k => by
    simp only [G, c, snf.snf, hσ]
  refine ⟨G, fun k => (snf.bN (σ.symm k)).2, ?_⟩

  have hdetG : G.det = (∏ k, c k) * (Matrix.of fun k j => snf.bM k j).det := by
    rw [← Matrix.det_mul_column]
    congr 1
    ext k j
    simp [hGrow]
  have hunit : IsUnit (Matrix.of fun k j => snf.bM k j).det := by
    have := (Pi.basisFun R (Fin ρ)).isUnit_det snf.bM
    rw [Basis.det_apply] at this
    have heq : (Matrix.of fun k j => snf.bM k j) = ((Pi.basisFun R (Fin ρ)).toMatrix snf.bM).transpose := by
      ext k j; simp [Basis.toMatrix_apply]
    rw [heq, Matrix.det_transpose]; exact this

  let L : (Fin ρ → R) →ₗ[R] (Π k : Fin ρ, R ⧸ Ideal.span ({c k} : Set R)) :=
    LinearMap.pi fun k => (Ideal.span ({c k} : Set R)).mkQ ∘ₗ snf.bM.coord k
  have hle : P ≤ LinearMap.ker L := fun x hx => by
    rw [LinearMap.mem_ker]
    funext k
    simp only [L, LinearMap.pi_apply, LinearMap.comp_apply, Submodule.mkQ_apply, Pi.zero_apply,
      Submodule.Quotient.mk_eq_zero, Basis.coord_apply]
    have := snf.repr_apply_embedding_eq_repr_smul ⟨x, hx⟩ (i := σ.symm k)
    rw [hσ] at this
    simp only at this
    rw [this, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span rfl)
  have hLs : Function.Surjective (P.liftQ L hle) := by
    intro y
    choose r hr using fun k => Submodule.Quotient.mk_surjective _ (y k)
    refine ⟨Submodule.Quotient.mk (snf.bM.equivFun.symm r), ?_⟩
    funext k
    have hrep : snf.bM.repr (snf.bM.equivFun.symm r) k = r k := by
      rw [← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    simp only [L, Submodule.liftQ_apply, LinearMap.pi_apply, LinearMap.comp_apply,
      Basis.coord_apply, hrep, Submodule.mkQ_apply, hr]
  have h1 := Module.length_le_of_surjective (P.liftQ L hle) hLs
  rw [Module.length_pi_of_fintype] at h1
  have h2 : IsDiscreteValuationRing.addVal R (∏ k, c k) ≤ IsDiscreteValuationRing.addVal R (ϖ ^ n) := by
    rw [addVal_prod, IsDiscreteValuationRing.addVal_pow, IsDiscreteValuationRing.addVal_uniformizer hϖ]
    simp only [nsmul_eq_mul, mul_one]
    refine le_trans (le_of_eq ?_) (h1.trans hP)
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Ring.ord_eq_addVal]; rfl
  rw [IsDiscreteValuationRing.addVal_le_iff_dvd] at h2
  rw [hdetG]
  exact (IsUnit.mul_right_dvd hunit).mpr h2

end Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas

namespace Formalism.NormUnitaryCountingLemmas

open Formalism.NormUnitaryCountingLemmas.CoefficientBoundLemmas in
theorem coefficient_bound_holds : CB := by
  intro R _ _ _ ϖ hϖ S _ _ _ N n hlen I Φ e hΦ ρ φ J
  classical
  let ψ : (Fin ρ → R) →ₗ[R] S := Fintype.linearCombination R φ
  let P : Submodule R (Fin ρ → R) := N.comap ψ
  have hP : Module.length R ((Fin ρ → R) ⧸ P) ≤ n := by
    refine le_trans (Module.length_le_of_injective (P.mapQ N ψ le_rfl) ?_) hlen
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ]
    simp [P]
  obtain ⟨G, hG, c, hc⟩ := key P n hP ϖ hϖ
  let A : Matrix (Fin ρ) (Fin ρ) (FractionRing R) := Matrix.of fun a b => Φ (φ a) (J b)
  have hentry : ∀ i b, ∃ r : R, algebraMap R (FractionRing R) ϖ ^ e *
      ((G.map (algebraMap R (FractionRing R))) * A) i b = algebraMap R (FractionRing R) r := by
    intro i b
    have : ((G.map (algebraMap R (FractionRing R))) * A) i b = Φ (ψ (G i)) (J b) := by
      simp [Matrix.mul_apply, A, ψ, Fintype.linearCombination_apply, map_sum, map_smul,
        Algebra.smul_def]
    rw [this]
    exact hΦ _ (hG i) (J b)
  choose r hr using hentry
  have hϖK : algebraMap R (FractionRing R) ϖ ≠ 0 := by
    rw [ne_eq, map_eq_zero_iff _ (IsFractionRing.injective R (FractionRing R))]
    exact hϖ.ne_zero
  have hdet : algebraMap R (FractionRing R) ϖ ^ ((ρ : ℤ) * e) *
      ((G.map (algebraMap R (FractionRing R))) * A).det =
        algebraMap R (FractionRing R) (Matrix.of r).det := by
    rw [RingHom.map_det]
    have : (algebraMap R (FractionRing R)).mapMatrix (Matrix.of r) =
        (algebraMap R (FractionRing R) ϖ ^ e) • ((G.map (algebraMap R (FractionRing R))) * A) := by
      ext i b
      simp [← hr i b]
    rw [this, Matrix.det_smul, Fintype.card_fin, ← zpow_natCast, ← zpow_mul, mul_comm e]
  refine ⟨c * (Matrix.of r).det, ?_⟩
  rw [zpow_add₀ hϖK, zpow_natCast, ← map_pow, hc, map_mul, map_mul, ← hdet, Matrix.det_mul,
    RingHom.map_det]
  simp only [RingHom.mapMatrix_apply]
  ring

end Formalism.NormUnitaryCountingLemmas
end
end

-- bundled from Formalism.NormUnitaryBounds.DetPolynomialWeights.IntegralExpInt
section
open MeasureTheory Complex

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures

lemma integral_exp_int (k : ℤ) :
    ∫ θ in Set.Ioc (0:ℝ) (2 * Real.pi), Complex.exp ((k : ℂ) * I * (θ : ℂ)) =
      if k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  rw [← intervalIntegral.integral_of_le (by positivity)]
  split_ifs with hk
  · subst hk; simp
  · have hc : (k : ℂ) * I ≠ 0 := mul_ne_zero (by exact_mod_cast hk) I_ne_zero
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp ((k : ℂ) * I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I k]; congr 1; push_cast; ring
    rw [h1]; simp

abbrev mu1 : Measure ℝ := volume.restrict (Set.Ioc (0:ℝ) (2 * Real.pi))

abbrev muT (G : ℕ) : Measure (Fin G → ℝ) := Measure.pi (fun _ : Fin G => mu1)

lemma muT_real_univ (G : ℕ) : (muT G).real Set.univ = (2 * Real.pi) ^ G := by
  rw [Measure.real, Measure.pi_univ, ENNReal.toReal_prod]
  simp [Real.volume_Ioc, Real.pi_pos.le]

theorem cauchy_torus (G : ℕ) (Θ : (Fin G → ℂ) → ℂ) (c : (Fin G → ℕ) → ℂ)
    (hΘ : ∀ z : Fin G → ℂ, HasSum (fun e : Fin G → ℕ => c e * ∏ i, z i ^ e i) (Θ z))
    (r : Fin G → ℝ) (B : ℝ)
    (hB : ∀ θ : Fin G → ℝ, ‖Θ (fun i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * I))‖ ≤ B)
    (e : Fin G → ℕ) : ‖c e‖ * ∏ i, |r i| ^ e i ≤ B := by
  set zθ : (Fin G → ℝ) → Fin G → ℂ := fun θ i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * I) with hzθ
  set w : (Fin G → ℝ) → ℂ := fun θ => ∏ i, Complex.exp (-(e i : ℂ) * I * (θ i : ℂ)) with hw
  set F : (Fin G → ℕ) → (Fin G → ℝ) → ℂ :=
    fun e' θ => c e' * (∏ i, zθ θ i ^ e' i) * w θ with hF
  set a : (Fin G → ℕ) → ℂ := fun e' => c e' * ∏ i, ((r i : ℂ)) ^ e' i with ha
  set k : (Fin G → ℕ) → Fin G → ℤ := fun e' i => (e' i : ℤ) - (e i : ℤ) with hk
  have key : ∀ e' θ, F e' θ = a e' * ∏ i, Complex.exp (((k e' i : ℤ) : ℂ) * I * (θ i : ℂ)) := by
    intro e' θ
    simp only [hF, ha, hw, hzθ, hk]
    rw [mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [mul_pow, ← Complex.exp_nat_mul, mul_assoc, ← Complex.exp_add]
    congr 2
    push_cast; ring
  have hnormexp : ∀ (m : ℤ) (t : ℝ), ‖Complex.exp ((m : ℂ) * I * (t : ℂ))‖ = 1 := by
    intro m t
    rw [Complex.norm_exp]; simp
  have hnormF : ∀ e' θ, ‖F e' θ‖ = ‖a e'‖ := by
    intro e' θ
    rw [key, norm_mul, norm_prod]
    simp [hnormexp]
  have hcont : ∀ e', Continuous (F e') := by
    intro e'
    have : F e' = fun θ => a e' * ∏ i, Complex.exp (((k e' i : ℤ) : ℂ) * I * (θ i : ℂ)) :=
      funext (key e')
    rw [this]
    fun_prop
  have hint : ∀ e', Integrable (F e') (muT G) := by
    intro e'
    exact Integrable.of_bound (hcont e').aestronglyMeasurable ‖a e'‖
      (Filter.Eventually.of_forall fun θ => (hnormF e' θ).le)
  have hsumr : Summable a := (hΘ (fun i => (r i : ℂ))).summable
  have hsum : Summable fun e' => ∫ θ, ‖F e' θ‖ ∂(muT G) := by
    simp_rw [hnormF, integral_const, smul_eq_mul]
    exact (summable_norm_iff.mpr hsumr).mul_left _
  have htsum : ∀ θ, ∑' e', F e' θ = Θ (zθ θ) * w θ := fun θ => ((hΘ (zθ θ)).mul_right (w θ)).tsum_eq
  have hI : ∀ e', ∫ θ, F e' θ ∂(muT G) =
      a e' * ∏ i, (if k e' i = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0) := by
    intro e'
    simp_rw [key]
    rw [integral_const_mul]
    congr 1
    rw [integral_fintype_prod_eq_prod (μ := fun _ : Fin G => mu1)
      (fun i (t : ℝ) => Complex.exp (((k e' i : ℤ) : ℂ) * I * (t : ℂ)))]
    apply Finset.prod_congr rfl
    intro i _
    exact integral_exp_int (k e' i)
  have hmain : ∫ θ, Θ (zθ θ) * w θ ∂(muT G) = a e * ((2 * Real.pi : ℝ) : ℂ) ^ G := by
    simp_rw [← htsum]
    rw [← integral_tsum_of_summable_integral_norm hint hsum]
    rw [tsum_eq_single e]
    · rw [hI]; congr 1
      simp [hk]
    · intro e' he'
      rw [hI]
      obtain ⟨i, hi⟩ : ∃ i, e' i ≠ e i := by
        by_contra h; push Not at h; exact he' (funext h)
      have : k e' i ≠ 0 := by simp only [hk]; omega
      rw [Finset.prod_eq_zero (Finset.mem_univ i) (if_neg this), mul_zero]
  have hbound : ‖∫ θ, Θ (zθ θ) * w θ ∂(muT G)‖ ≤ B * (muT G).real Set.univ := by
    apply norm_integral_le_of_norm_le_const
    refine Filter.Eventually.of_forall fun θ => ?_
    rw [norm_mul, hw, norm_prod]
    have : ∀ i ∈ Finset.univ, ‖Complex.exp (-(e i : ℂ) * I * (θ i : ℂ))‖ = 1 := by
      intro i _; rw [Complex.norm_exp]; simp
    rw [Finset.prod_congr rfl this, Finset.prod_const_one, mul_one]
    exact hB θ
  rw [hmain, muT_real_univ, norm_mul, norm_pow] at hbound
  have h2pi : (0:ℝ) < (2 * Real.pi) ^ G := by positivity
  have hn2 : ‖((2 * Real.pi : ℝ) : ℂ)‖ = 2 * Real.pi := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hn2] at hbound
  have ha' : ‖a e‖ = ‖c e‖ * ∏ i, |r i| ^ e i := by
    simp only [ha, norm_mul, norm_prod, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rw [← ha']
  exact le_of_mul_le_mul_right hbound h2pi

end Formalism.NormUnitaryCountingLemmas.ExponentialIntegralMeasures
end
end

-- bundled from Formalism.NormUnitaryBounds.DetPolynomialWeights.NatDegreeAevalLe
section
open MvPolynomial

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas.H1OnPoints

variable {R : Type*} [CommRing R]

lemma blockSum {N n : ℕ} {ν : Fin N → ℕ} (d : Fin N × Fin n →₀ ℕ)
    (hd : Finsupp.weight (blockWt N n) d = ν) (j : Fin N) : ∑ k, d (j, k) = ν j := by
  have h := congrFun hd j
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h
  simp only [Finset.sum_apply, Pi.smul_apply, blockWt, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero, Fintype.sum_prod_type] at h
  simpa [Finset.sum_ite_eq, Finset.sum_comm] using h

lemma aeval_scale {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} {ν : Fin N → ℕ}
    (F : MvPolynomial (Fin N × Fin n) R)
    (hF : IsWeightedHomogeneous (blockWt N n) F ν) (lam : Fin N → S) (y : Fin N × Fin n → S) :
    aeval (fun p => lam p.1 * y p) F = (∏ j, lam j ^ ν j) * aeval y F := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  simp only [map_sum, Finset.mul_sum, aeval_monomial]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hw : Finsupp.weight (blockWt N n) d = ν := hF (mem_support_iff.mp hd)
  have hprod : (d.prod fun p k => lam p.1 ^ k) = ∏ j, lam j ^ ν j := by
    rw [Finsupp.prod_fintype _ _ (by simp), Fintype.prod_prod_type]
    refine Finset.prod_congr rfl fun j _ => ?_
    show ∏ k, lam j ^ d (j, k) = _
    rw [Finset.prod_pow_eq_pow_sum, blockSum d hw j]
  have : (d.prod fun p k => (lam p.1 * y p) ^ k) =
      (d.prod fun p k => lam p.1 ^ k) * d.prod fun p k => y p ^ k := by
    rw [← Finsupp.prod_mul]
    simp [mul_pow]
  rw [this, hprod]
  ring

lemma shear_eval {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} (i j : Fin N)
    (y : Fin N × Fin n → S) (s : S) (G : MvPolynomial (Fin N × Fin n) R) :
    Polynomial.eval₂ (aeval y).toRingHom s (shear R i j G) =
      aeval (fun p => y p + if p.1 = j then s * y (i, p.2) else 0) G := by
  induction G using MvPolynomial.induction_on with
  | C a =>
    simp [shear, Polynomial.algebraMap_apply]
  | add p q hp hq => simp only [map_add, Polynomial.eval₂_add, hp, hq]
  | mul_X p q hp =>
    simp only [map_mul, Polynomial.eval₂_mul, hp]
    congr 1
    simp only [shear, aeval_X]
    split_ifs <;> simp <;> ring

lemma shear_eq {N n : ℕ} {ν : Fin N → ℕ} {F : MvPolynomial (Fin N × Fin n) R} (hF : F ∈ H R ν)
    (i j : Fin N) (hij : i < j) : shear R i j F = Polynomial.C F := by
  have h := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp
    ((Submodule.mem_iInf _).mp (Submodule.mem_inf.mp hF).2 i) j) hij
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
  exact h

lemma shear_inv {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} {ν : Fin N → ℕ}
    {F : MvPolynomial (Fin N × Fin n) R} (hF : F ∈ H R ν) (i j : Fin N) (hij : i < j)
    (y : Fin N × Fin n → S) (s : S) :
    aeval (fun p => y p + if p.1 = j then s * y (i, p.2) else 0) F = aeval y F := by
  rw [← shear_eval, shear_eq hF i j hij, Polynomial.eval₂_C]
  rfl

lemma shear_multi {S : Type*} [CommRing S] [Algebra R S] {N n : ℕ} {ν : Fin (N + 1) → ℕ}
    {F : MvPolynomial (Fin (N + 1) × Fin n) R} (hF : F ∈ H R ν)
    (y : Fin (N + 1) × Fin n → S) (s : Fin (N + 1) → S) (T : Finset (Fin (N + 1)))
    (hT : (0 : Fin (N + 1)) ∉ T) :
    aeval (fun p => y p + if p.1 ∈ T then s p.1 * y (0, p.2) else 0) F = aeval y F := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T haT ih =>
    have ha0 : a ≠ 0 := fun h => hT (h ▸ Finset.mem_insert_self _ _)
    have h0T : (0 : Fin (N + 1)) ∉ T := fun h => hT (Finset.mem_insert_of_mem h)
    have key : (fun p : Fin (N + 1) × Fin n =>
        y p + if p.1 ∈ insert a T then s p.1 * y (0, p.2) else 0) =
        fun p => (fun q : Fin (N + 1) × Fin n => y q + if q.1 ∈ T then s q.1 * y (0, q.2) else 0) p
          + if p.1 = a then s a * (fun q : Fin (N + 1) × Fin n =>
              y q + if q.1 ∈ T then s q.1 * y (0, q.2) else 0) (0, p.2) else 0 := by
      funext p
      by_cases hpa : p.1 = a
      · have : p.1 ∉ T := hpa ▸ haT
        simp [hpa, h0T, haT]
      · simp [hpa, Finset.mem_insert]
    rw [key, shear_inv hF 0 a (Fin.pos_iff_ne_zero.mpr ha0), ih h0T]

lemma natDegree_aeval_le {B : Type*} [CommRing B] [Algebra R B] {N n : ℕ} {ν : Fin (N + 1) → ℕ}
    (F : MvPolynomial (Fin (N + 1) × Fin n) R) (hF : IsWeightedHomogeneous (blockWt (N + 1) n) F ν)
    (y : Fin (N + 1) × Fin n → Polynomial B)
    (hy : ∀ p, (y p).natDegree ≤ if p.1 = 0 then 1 else 0) : (aeval y F).natDegree ≤ ν 0 := by
  rw [F.as_sum, map_sum]
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun d hd => ?_
  have hw : Finsupp.weight (blockWt (N + 1) n) d = ν := hF (mem_support_iff.mp hd)
  rw [aeval_monomial, Polynomial.algebraMap_apply]
  refine (Polynomial.natDegree_C_mul_le _ _).trans ?_
  rw [Finsupp.prod_fintype _ _ (by simp)]
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  calc ∑ p, (y p ^ d p).natDegree ≤ ∑ p : Fin (N + 1) × Fin n, d p * (if p.1 = 0 then 1 else 0) :=
        Finset.sum_le_sum fun p _ => Polynomial.natDegree_pow_le.trans (Nat.mul_le_mul_left _ (hy p))
    _ = ν 0 := by
        rw [← blockSum d hw 0, Fintype.sum_prod_type]
        simp

end Formalism.NormUnitaryCountingLemmas.H1OnPoints
end
end

-- bundled from Formalism.NormUnitaryBounds.DetPolynomialWeights.NormUnitary
section
open MvPolynomial Finset

noncomputable section

namespace Formalism.NormUnitaryCountingLemmas.NU

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def cnt {d : ℕ} (t : Fin d → σ) : σ →₀ ℕ := ∑ m, Finsupp.single (t m) 1

def fct (e : σ →₀ ℕ) : ℕ := ∏ i, (e i).factorial

def P {d : ℕ} (S : (Fin d → σ) → ℂ) : MvPolynomial σ ℂ := ∑ t, monomial (cnt t) (S t)

lemma coeff_P {d : ℕ} (S : (Fin d → σ) → ℂ) (e : σ →₀ ℕ) :
    coeff e (P S) = ∑ t, if cnt t = e then S t else 0 := by
  simp only [P, coeff_sum, coeff_monomial]

lemma prod_X_eq {R : Type*} [CommSemiring R] {d : ℕ} (t : Fin d → σ) :
    (∏ m, (X (t m) : MvPolynomial σ R)) = monomial (cnt t) 1 := by
  rw [cnt, monomial_sum_one]; rfl

lemma pow_sum_X (d : ℕ) :
    (∑ i, (X i : MvPolynomial σ ℕ)) ^ d = ∑ t : Fin d → σ, monomial (cnt t) 1 := by
  have : (∑ i, (X i : MvPolynomial σ ℕ)) ^ d = ∏ _m : Fin d, ∑ i, (X i : MvPolynomial σ ℕ) := by
    simp [Finset.prod_const]
  rw [this, Finset.prod_univ_sum, Fintype.piFinset_univ]
  simp_rw [prod_X_eq]

lemma card_fib {d : ℕ} (e : σ →₀ ℕ) (he : ∑ i, e i = d) :
    (univ.filter fun t : Fin d → σ => cnt t = e).card * fct e = d.factorial := by
  have h := congrArg (coeff e) (pow_sum_X (σ := σ) d)
  rw [Finset.sum_pow_eq_sum_piAntidiag] at h
  have hk : ∀ k : σ → ℕ, (∏ i, (X i : MvPolynomial σ ℕ) ^ k i) =
      monomial (Finsupp.equivFunOnFinite.symm k) 1 := by
    intro k
    rw [Finsupp.equivFunOnFinite_symm_eq_sum, monomial_sum_one]
    simp [X_pow_eq_monomial]
  simp only [hk, coeff_sum, coeff_monomial] at h
  have hc : ∀ k : σ → ℕ, coeff e ((Nat.multinomial univ k : MvPolynomial σ ℕ) *
      monomial (Finsupp.equivFunOnFinite.symm k) 1) =
      if k = ⇑e then Nat.multinomial univ k else 0 := by
    intro k
    rw [← map_natCast (C : ℕ →+* MvPolynomial σ ℕ), C_mul_monomial, mul_one, coeff_monomial]
    by_cases hke : k = ⇑e
    · subst hke; simp
    · rw [if_neg hke, if_neg]
      intro h'; apply hke; rw [← h']; simp
  simp only [hc, Finset.sum_ite_eq', Finset.sum_boole] at h
  rw [if_pos (by simp [he])] at h
  rw [Nat.cast_id] at h
  rw [← h, mul_comm, fct, ← he]
  exact Nat.multinomial_spec _ _

def T (d : ℕ) (F : MvPolynomial σ ℂ) (t : Fin d → σ) : ℂ :=
  coeff (cnt t) F * (fct (cnt t) : ℂ) / (d.factorial : ℂ)

lemma rep {d : ℕ} (F : MvPolynomial σ ℂ) (hF : ∀ e ∈ F.support, ∑ i, e i = d) :
    P (T d F) = F := by
  ext e
  rw [coeff_P]
  have hsum : (∑ t : Fin d → σ, if cnt t = e then T d F t else 0)
      = ((univ.filter fun t : Fin d → σ => cnt t = e).card : ℂ) *
        (coeff e F * fct e / d.factorial) := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_congr rfl (g := fun _ => coeff e F * fct e / d.factorial)]
    · simp
    · intro t ht
      simp only [T, (Finset.mem_filter.1 ht).2]
  rw [hsum]
  by_cases he : ∑ i, e i = d
  · have hc := card_fib e he
    have hc' : ((univ.filter fun t : Fin d → σ => cnt t = e).card : ℂ) * (fct e : ℂ) =
        d.factorial := by exact_mod_cast hc
    have hd : (d.factorial : ℂ) ≠ 0 := by exact_mod_cast d.factorial_ne_zero
    calc ((univ.filter fun t : Fin d → σ => cnt t = e).card : ℂ) *
          (coeff e F * fct e / d.factorial)
        = coeff e F * (((univ.filter fun t : Fin d → σ => cnt t = e).card : ℂ) * (fct e : ℂ))
          / d.factorial := by ring
      _ = coeff e F := by rw [hc', mul_div_assoc, div_self hd, mul_one]
  · have hz : coeff e F = 0 := by
      by_contra h
      exact he (hF e (mem_support_iff.2 h))
    simp [hz]

def ip (F G : MvPolynomial σ ℂ) : ℂ :=
  ∑ e ∈ F.support, coeff e F * star (coeff e G) * (fct e : ℂ)

def sub (V : Matrix σ σ ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun i => ∑ l, C (V i l) * X l

def act {d : ℕ} (V : Matrix σ σ ℂ) (S : (Fin d → σ) → ℂ) (t : Fin d → σ) : ℂ :=
  ∑ s, S s * ∏ m, V (s m) (t m)

lemma sub_sub (V : Matrix σ σ ℂ) (hV : V * star V = 1) (F : MvPolynomial σ ℂ) :
    sub (star V) (sub V F) = F := by
  have key : (sub (star V)).comp (sub V) = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, sub, aeval_X, map_sum, map_mul, aeval_C, algebraMap_eq,
      AlgHom.id_apply]
    simp_rw [Finset.mul_sum, ← mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ← map_sum]
    have h2 : ∀ k, ∑ l, V i l * star V l k = (1 : Matrix σ σ ℂ) i k := fun k => by
      rw [← hV, Matrix.mul_apply]
    simp_rw [h2, Matrix.one_apply]
    simp
  simpa using AlgHom.congr_fun key F

def FR (F : MvPolynomial σ ℂ) : ℝ := ∑ e ∈ F.support, ‖coeff e F‖ ^ 2 * (fct e : ℝ)

lemma ip_self (F : MvPolynomial σ ℂ) : ip F F = (FR F : ℂ) := by
  simp only [ip, FR, Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_natCast]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast; ring

def blk {N n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin N × Fin n) (Fin N × Fin n) ℂ :=
  fun p q => if p.1 = q.1 then U p.2 q.2 else 0

end Formalism.NormUnitaryCountingLemmas.NU

namespace Formalism.NormUnitaryCountingLemmas

end Formalism.NormUnitaryCountingLemmas
end
end

