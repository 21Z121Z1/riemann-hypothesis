import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0087
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0001
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0024
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0081
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0004
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0063
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.AbelianUnramIn
section
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize

namespace GlobalTheory.FieldSize.WeberUnram

set_option autoImplicit false in
open NumberField IsDedekindDomain in

theorem _root_.GlobalTheory.FieldSize.WeberUnram.of_algHom {K M R : Type} [Field K] [NumberField K]
    [Field M] [Algebra K M] [Field R] [NumberField R]
    [Algebra K R] [IsAbelianGalois K R] (f : M →ₐ[K] R) :
    ∃ (_ : NumberField M) (_ : IsAbelianGalois K M),
      ∀ 𝔭 : HeightOneSpectrum (𝓞 K), _root_.GlobalTheory.NT.UnramIn R 𝔭 →
        _root_.GlobalTheory.NT.UnramIn M 𝔭 := by
  have hab : IsAbelianGalois K M := IsAbelianGalois.of_algHom f
  letI : Algebra M R := f.toRingHom.toAlgebra
  haveI : IsScalarTower K M R := IsScalarTower.of_algebraMap_eq (fun x => (f.commutes x).symm)
  haveI : CharZero M := charZero_of_injective_algebraMap (algebraMap K M).injective
  haveI : FiniteDimensional K M := FiniteDimensional.left K M R
  haveI : FiniteDimensional ℚ M := Module.Finite.trans K M
  haveI nf : NumberField M := ⟨⟩
  exact ⟨nf, hab, fun 𝔭 h => _root_.GlobalTheory.RayMaximal.unramIn_of_tower (L := M) (M := R) h⟩

end GlobalTheory.FieldSize.WeberUnram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.CurveOverOfRayField
section
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.RayExistCurve

section Quadratic

variable {K : Type} [Field K] [NumberField K] {d : ℕ}

theorem norm_int_eq (h2 : Module.finrank ℚ K = 2) (hD : discr K = -d) (φ : K →+* ℂ) (a : 𝓞 K) :
    ((Algebra.norm ℤ a : ℤ) : ℝ) = ‖φ a‖ ^ 2 := by
  rw [← GlobalTheory.QuadraticZeta.norm_eq_sq h2 hD φ, ← Algebra.coe_norm_int, Rat.cast_intCast]

theorem sq_ne_prime (h2 : Module.finrank ℚ K = 2) (hD : discr K = -d) (φ : K →+* ℂ) {p : ℕ} (hp : p.Prime)
    (a : 𝓞 K) : a * a ≠ p := by
  intro h
  have h1 : φ a * φ a = p := by
    rw [← map_mul]
    have := congrArg (fun x : 𝓞 K => φ x) h
    simpa using this
  have hre := congrArg Complex.re h1
  have him := congrArg Complex.im h1
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im] at hre him
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hi : (φ a).im = 0 := by
    by_contra hi
    have : (φ a).re = 0 := mul_right_cancel₀ hi (by linarith)
    rw [this] at hre
    nlinarith [mul_self_nonneg (φ a).im]
  have h3 := norm_int_eq h2 hD φ (a + 1)
  rw [Complex.sq_norm, Complex.normSq_apply] at h3
  simp only [map_add, map_one, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im, hi] at h3
  generalize Algebra.norm ℤ (a + 1) = m at h3
  rw [hi] at hre
  have h4 : Irrational (φ a).re := by
    have h5 := hp.irrational_sqrt
    rw [← hre, mul_zero, sub_zero, Real.sqrt_mul_self_eq_abs] at h5
    rcases abs_choice (φ a).re with h | h <;> rw [h] at h5
    · exact h5
    · exact h5.of_neg
  refine h4 ⟨((m : ℚ) - p - 1) / 2, ?_⟩
  push_cast
  linarith

theorem span_isPrime (h2 : Module.finrank ℚ K = 2) (hD : discr K = -d) (φ : K →+* ℂ) {p : ℕ} (hp : p.Prime)
    {a : 𝓞 K} (ha : ‖φ a‖ ^ 2 = p) : (Ideal.span {a}).IsPrime := by
  refine Ideal.isPrime_of_irreducible_absNorm ?_
  have : Algebra.norm ℤ a = p := by
    have := (norm_int_eq h2 hD φ a).trans ha
    exact_mod_cast this
  rw [Ideal.absNorm_span_singleton, this, Int.natAbs_natCast]
  exact hp

theorem eq_of_span_eq (h2 : Module.finrank ℚ K = 2) (hD : discr K = -d) (φ : K →+* ℂ) {n : ℕ} (hn : 3 ≤ n)
    {c c' : 𝓞 K} (h0 : (1 + n * c : 𝓞 K) ≠ 0) (hnorm : ‖φ (1 + n * c' : 𝓞 K)‖ = ‖φ (1 + n * c : 𝓞 K)‖)
    (h : Ideal.span {1 + n * c} = Ideal.span {(1 + n * c' : 𝓞 K)}) : (1 + n * c : 𝓞 K) = 1 + n * c' := by
  obtain ⟨u, hu⟩ : (1 + n * c : 𝓞 K) ∣ 1 + n * c' := by
    rw [← Ideal.mem_span_singleton, h]
    exact Ideal.mem_span_singleton_self _
  have hu1 : ‖φ u‖ = 1 := by
    rw [hu] at hnorm
    simp only [map_mul, norm_mul] at hnorm
    refine (mul_eq_left₀ ?_).1 hnorm
    rw [norm_ne_zero_iff, map_ne_zero]
    exact fun h => h0 (RingOfIntegers.coe_injective (by rw [h, map_zero]))
  have ht : u - 1 = n * (c' - c * u) := by linear_combination -hu
  generalize c' - c * u = t at ht
  have h3 : (n : ℝ) * ‖φ t‖ ≤ 2 := by
    have e : (n : ℂ) * φ t = φ u - 1 := by
      have := congrArg (fun x : 𝓞 K => φ x) ht
      simpa using this.symm
    have := norm_sub_le (φ u) 1
    rw [← e, norm_mul, Complex.norm_natCast, hu1, norm_one] at this
    linarith
  have h4 := norm_int_eq h2 hD φ t
  have hn' : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h5 : ‖φ t‖ < 1 := by nlinarith [norm_nonneg (φ t)]
  have h6 : Algebra.norm ℤ t = 0 := by
    have a1 : ((Algebra.norm ℤ t : ℤ) : ℝ) < 1 := by nlinarith [norm_nonneg (φ t)]
    have a2 : (0 : ℝ) ≤ (Algebra.norm ℤ t : ℤ) := by rw [h4]; positivity
    have a3 : Algebra.norm ℤ t < 1 := by exact_mod_cast a1
    have a4 : 0 ≤ Algebra.norm ℤ t := by exact_mod_cast a2
    omega
  rw [Algebra.norm_eq_zero_iff] at h6
  rw [h6, mul_zero, sub_eq_zero] at ht
  rw [hu, ht, mul_one]

theorem ncard_eq_finrank [IsTotallyComplex K] (h2 : Module.finrank ℚ K = 2) (hD : discr K = -d) (φ : K →+* ℂ)
    {n : ℕ} (hn : 3 ≤ n) (R : Type) [Field R] [NumberField R] [Algebra K R] [IsAbelianGalois K R]
    (hR : IsRay R (Ideal.span {(n : 𝓞 K)})) {p : ℕ} (hp : p.Prime) {c c' : 𝓞 K}
    (hnorm : ‖φ (1 + n * c' : 𝓞 K)‖ = ‖φ (1 + n * c : 𝓞 K)‖) (hmul : (1 + n * c) * (1 + n * c') = (p : 𝓞 K)) :
    {v : HeightOneSpectrum (𝓞 R) | ((p : ℕ) : 𝓞 R) ∈ v.asIdeal}.ncard = Module.finrank ℚ R := by
  have hp0 : (p : 𝓞 K) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hsq : ‖φ (1 + n * c : 𝓞 K)‖ ^ 2 = p := by
    have := congrArg (fun x : 𝓞 K => ‖φ x‖) hmul
    simp only [map_mul, norm_mul, map_natCast, Complex.norm_natCast] at this
    rw [sq]
    nth_rewrite 2 [← hnorm]
    exact this
  have key : ∀ b : 𝓞 K, ‖φ (1 + n * b : 𝓞 K)‖ ^ 2 = p → (Ideal.span {(1 + n * b : 𝓞 K)}).IsMaximal ∧
      {Q : HeightOneSpectrum (𝓞 R) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 R)) = Ideal.span {1 + n * b}}.ncard =
        Module.finrank K R := by
    intro b hb
    have hP := span_isPrime h2 hD φ hp hb
    have hne : Ideal.span {(1 + n * b : 𝓞 K)} ≠ ⊥ := by
      rw [Ne, Ideal.span_singleton_eq_bot]
      intro h
      rw [h] at hb
      exact hp.ne_zero (by simpa using hb.symm)
    refine ⟨hP.isMaximal hne, (RaySplit.ncard_eq_finrank_iff K R n (by omega) hR ⟨_, hP, hne⟩ fun h => ?_).2
      ⟨_, rfl, Ideal.mem_span_singleton.2 ⟨b, by ring⟩⟩⟩
    refine hP.ne_top ((Ideal.eq_top_iff_one _).2 ?_)
    have := Ideal.sub_mem _ (Ideal.mem_span_singleton_self (1 + n * b : 𝓞 K)) (Ideal.mul_mem_right b _ h)
    simpa using this
  obtain ⟨hm, hc⟩ := key c hsq
  obtain ⟨hm', hc'⟩ := key c' (by rw [hnorm, hsq])
  have hpos : Module.finrank K R ≠ 0 := Module.finrank_pos.ne'
  have hmem : ∀ (Q : HeightOneSpectrum (𝓞 R)) (a : 𝓞 K), (Ideal.span {a}).IsMaximal →
      (a ∈ Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 R)) ↔ Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 R)) = Ideal.span {a}) := by
    intro Q a ha
    have := Q.isPrime
    refine ⟨fun h => (ha.eq_of_le (Ideal.IsPrime.ne_top inferInstance) ((Ideal.span_singleton_le_iff_mem _).2 h)).symm,
      fun h => h ▸ Ideal.mem_span_singleton_self a⟩
  have hset : {v : HeightOneSpectrum (𝓞 R) | ((p : ℕ) : 𝓞 R) ∈ v.asIdeal} =
      {Q : HeightOneSpectrum (𝓞 R) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 R)) = Ideal.span {1 + n * c}} ∪
      {Q : HeightOneSpectrum (𝓞 R) | Q.asIdeal.comap (algebraMap (𝓞 K) (𝓞 R)) = Ideal.span {1 + n * c'}} := by
    ext Q
    have := Q.isPrime
    simp only [Set.mem_union, Set.mem_setOf_eq]
    rw [← hmem Q _ hm, ← hmem Q _ hm', ← Ideal.IsPrime.mul_mem_iff_mem_or_mem inferInstance, hmul, Ideal.mem_comap,
      map_natCast]
  rw [hset, Set.ncard_union_eq ?_ (Set.finite_of_ncard_ne_zero (hc ▸ hpos)) (Set.finite_of_ncard_ne_zero (hc' ▸ hpos)),
    hc, hc', ← Module.finrank_mul_finrank ℚ K R, h2, two_mul]
  rw [Set.disjoint_left]
  intro Q h1 h1'
  have := eq_of_span_eq h2 hD φ hn (left_ne_zero_of_mul (hmul ▸ hp0)) hnorm (h1.symm.trans h1')
  rw [← this] at hmul
  exact sq_ne_prime h2 hD φ hp _ hmul

end Quadratic

theorem ncard_congr {M R : Type} [Field M] [Field R] [NumberField M] [NumberField R] (e : M ≃+* R) (p : ℕ) :
    {v : HeightOneSpectrum (𝓞 M) | ((p : ℕ) : 𝓞 M) ∈ v.asIdeal}.ncard =
      {v : HeightOneSpectrum (𝓞 R) | ((p : ℕ) : 𝓞 R) ∈ v.asIdeal}.ncard := by
  refine Set.ncard_congr' (Equiv.subtypeEquiv
    (HeightOneSpectrum.equivOfRingEquiv (RingOfIntegers.mapRingEquiv e)) fun Q => ?_)
  simp [HeightOneSpectrum.equivOfRingEquiv, HeightOneSpectrum.comap, Ideal.mem_comap]

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField in

theorem _root_.GlobalTheory.FieldSize.RayExistCurve.finrank_adjoin {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) :
    FiniteDimensional ℚ ℚ⟮r⟯ ∧ Module.finrank ℚ ℚ⟮r⟯ = 2 := by
  have hroot : aeval r (X ^ 2 + C (d : ℚ)) = 0 := by simp [hr]
  have hmon : (X ^ 2 + C (d : ℚ)).Monic := monic_X_pow_add_C _ (by norm_num)
  have hint : IsIntegral ℚ r := ⟨_, hmon, by simpa [aeval_def] using hroot⟩
  have hdeg : (X ^ 2 + C (d : ℚ)).natDegree = 2 := natDegree_X_pow_add_C
  have hirr : Irreducible (X ^ 2 + C (d : ℚ)) := by
    apply irreducible_of_degree_le_three_of_not_isRoot
    · rw [hdeg]; decide
    · intro x hx
      have hx' : x ^ 2 + (d : ℚ) = 0 := by simpa using hx
      have hd' : (0 : ℚ) < d := by exact_mod_cast hd
      nlinarith [sq_nonneg x]
  have hmin : minpoly ℚ r = X ^ 2 + C (d : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hmon).symm
  refine ⟨IntermediateField.adjoin.finiteDimensional hint, ?_⟩
  rw [IntermediateField.adjoin.finrank hint, hmin, hdeg]

theorem conj_eq_neg {d : ℕ} (hd : 0 < d) {r : ℂ} (hr : r ^ 2 = -(d : ℂ)) : starRingEnd ℂ r = -r := by
  have h1 := congrArg Complex.re hr
  have h2 := congrArg Complex.im hr
  simp [sq] at h1 h2
  have h3 : (0 : ℝ) < d := by exact_mod_cast hd
  have h4 : r.re = 0 := by
    by_contra h
    have : r.im = 0 := mul_left_cancel₀ h (by linarith)
    rw [this] at h1
    nlinarith [mul_self_nonneg r.re]
  apply Complex.ext <;> simp [h4]

end GlobalTheory.FieldSize.RayExistCurve
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsRayIntermediateField
section
set_option autoImplicit false

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory.Mem GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.SmallField

theorem exists_isRay_intermediateField (hR : GlobalTheory.NT.RayField) (K : IntermediateField ℚ ℂ) [NumberField K]
    (𝔮 : Ideal (𝓞 K)) (h𝔮 : 𝔮 ≠ ⊥) :
    ∃ (R : IntermediateField K ℂ) (_ : NumberField R) (_ : IsAbelianGalois K R), IsRay R 𝔮 := by
  obtain ⟨M, _, _, _, hM⟩ := GlobalTheory.Mem.Fld.rayField_iff.1 hR K 𝔮 h𝔮
  have := hM.1
  let f : M →ₐ[K] ℂ := IsAlgClosed.lift
  let e : M ≃ₐ[K] f.fieldRange := AlgEquiv.ofInjectiveField f
  have : FiniteDimensional K f.fieldRange := e.toLinearEquiv.finiteDimensional
  have : NumberField f.fieldRange := NumberField.of_module_finite K f.fieldRange
  have h := hM.of_algEquiv e
  exact ⟨f.fieldRange, inferInstance, h.1, h.2⟩

theorem exists_weber_of_rayField (hR : GlobalTheory.NT.RayField) (K : IntermediateField ℚ ℂ) [NumberField K] [IsTotallyComplex K]
    (h2 : Module.finrank ℚ K = 2) (hd : discr K < -4) (n : ℕ) (hodd : Odd n) (h3 : 3 ≤ n) :
    ∃ W : IntermediateField ℚ ℂ, Sz W (7 + 3 / 2 * Real.log |(discr K : ℝ)| + 3 * Real.log n)
        (7 + 3 / 2 * Real.log |(discr K : ℝ)| + 3 * Real.log n) ∧
      ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → weberSet L n ⊆ W := by
  have hd1 : (1 : ℝ) ≤ |(discr K : ℝ)| := by
    have : ((discr K : ℤ) : ℝ) < -4 := by exact_mod_cast hd
    rw [abs_of_neg (by linarith)]; linarith
  have hd0 := Real.log_nonneg hd1
  have hn0 : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hn : 0 < n := by omega
  have hq : Ideal.span {(n : 𝓞 K)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn.ne'
  obtain ⟨R, i1, i2, hRay⟩ := exists_isRay_intermediateField hR K _ hq
  have h := log_sizes_of_isRay_natCast K R h2 n hn hRay
  have hs : Sz (R.restrictScalars ℚ) _ _ := ⟨i1.to_finiteDimensional, h⟩
  refine ⟨R.restrictScalars ℚ, sz_mono hs ?_ ?_, fun L hL => GlobalTheory.T.weber_set_subset_ray_field K h2 hd L hL n hodd h3 R hRay⟩
  · rw [Real.log_mul (by norm_num) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 8 by norm_num)
    linarith
  · rw [Real.log_mul (by norm_num) (by linarith)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 4 by norm_num)
    linarith

theorem odd_level (P : Pre) {p : ℕ} (hp : p ∈ P.host.levelPrimes) :
    Odd (P.host.g 0 * P.host.g 1 * p) ∧ 3 ≤ P.host.g 0 * P.host.g 1 * p := by
  have ho : ∀ q ∈ P.host.levelPrimes, Odd q := fun q hq => by
    have := P.level_mod_four q hq
    rw [Nat.odd_iff]; omega
  refine ⟨((ho _ (P.host.g_level 0)).mul (ho _ (P.host.g_level 1))).mul (ho p hp), ?_⟩
  have h2 := (P.level_prime p hp).two_le
  have h4 := P.level_mod_four p hp
  have h0 : 0 < P.host.g 0 * P.host.g 1 := Nat.mul_pos (P.host.g_prime 0).pos (P.host.g_prime 1).pos
  calc 3 ≤ p := by omega
    _ ≤ _ := Nat.le_mul_of_pos_left p h0

end GlobalTheory.FieldSize.SmallField

namespace GlobalTheory.FieldSize

open SmallField GlobalTheory.Mem.BaseExt

theorem exists_rich_small_of_rayField : GlobalTheory.NT.RayField → ∀ P : Pre, ∃ F : IntermediateField ℚ ℂ, FiniteDimensional ℚ F ∧
    Rich P F ∧ ∀ L : ℝ, HostSz P.host L → Sz F (poR P.R L) (poR P.R L) := by
  intro hW P
  have hcm : IsCMField P.host.E := P.host.isCMField_hostE
  have hgal : IsGalois ℚ P.host.E := P.host.hostE_isGalois
  obtain ⟨K, _, _, hK2, -, hKd, hKE, hlat, hdeg⟩ := GlobalTheory.T.exists_imag_quadratic_host P.R P.host
  have hg0 := (P.host.g_prime 0).pos
  have hg1 := (P.host.g_prime 1).pos
  have hp := (P.level_prime _ P.host.pde_level.1).pos
  have hp' := (P.level_prime _ P.host.pde_level.2).pos
  have hE := sz_fieldRange_embedding P.host.E P.host.φ₀
  set lE : ℝ := Real.log |((discr P.host.E : ℤ) : ℝ)| / Module.finrank ℚ P.host.E with hlE
  set lh : ℝ := Real.log (classNumber P.host.E) with hlh
  have hlE0 : 0 ≤ lE := by
    refine div_nonneg (Real.log_nonneg ?_) (Nat.cast_nonneg _)
    exact_mod_cast Int.one_le_abs (discr_ne_zero P.host.E)
  have hdeg0 : 0 ≤ Real.log (Module.finrank ℚ P.host.E) := Real.log_natCast_nonneg _
  have hdK : Real.log |(discr K : ℝ)| ≤ 2 * lE := by
    obtain ⟨_, -, h⟩ := GlobalTheory.T.field_size_monotone.2 _ _ _ _ hKE hE
    have h' : Real.log |(discr K : ℝ)| / Module.finrank ℚ K ≤ lE := h
    rw [hK2] at h'
    push_cast at h'
    linarith
  have hE' := sz_mono hE (le_add_of_nonneg_right hlE0) (le_add_of_nonneg_left hdeg0)
  obtain ⟨W, hWs, hWc⟩ := exists_weber_of_rayField hW K hK2 hKd (P.host.g 0 * P.host.g 1 * P.host.pde)
    (odd_level P P.host.pde_level.1).1 (odd_level P P.host.pde_level.1).2
  obtain ⟨W', hWs', hWc'⟩ := exists_weber_of_rayField hW K hK2 hKd (P.host.g 0 * P.host.g 1 * P.host.pde')
    (odd_level P P.host.pde_level.2).1 (odd_level P P.host.pde_level.2).2
  have h0 := GlobalTheory.T.field_size_sup_add _ _ _ _ _ _ (GlobalTheory.T.field_size_sup_add _ _ _ _ _ _ hE' hWs) hWs'
  obtain ⟨F₁, l1, s1, r1⟩ := exists_roots [P.restRowsFiniteGroupCard, P.host.g 0 * (P.host.g 0 - 1), P.host.g 1 * (P.host.g 1 - 1),
    3 ^ 4, 5 ^ 4, P.host.pde, P.host.pde',
      classNumber P.host.E, xiOrd P.host (P.host.g 0 * P.host.g 1 * P.host.pde),
      xiOrd P.host (P.host.g 0 * P.host.g 1 * P.host.pde')] _ _ h0
  have hφ : ∀ x, P.host.φ₀ x ∈ F₁ := fun x =>
    l1 ((le_sup_left : _ ≤ _ ⊔ W') ((le_sup_left : _ ≤ _ ⊔ W) ⟨x, rfl⟩))
  obtain ⟨F₂, l2, s2, c2⟩ := GlobalTheory.T.exists_field_ideals_principal P.host.E P.host.φ₀ F₁ _ _ s1 hφ
  have hτ : ∀ (τ : P.host.E →+* ℂ) x, τ x ∈ F₂ := fun τ x => by
    obtain ⟨g, rfl⟩ := (factEmb P.R P.host).1.2 τ
    exact l2 (hφ (P.host.sigmaOf g x))
  obtain ⟨F, l3, s3, c3⟩ := exists_chain (fun j K => ∀ 𝔞 : Ideal (𝓞 P.host.E), 𝔞 ≠ ⊥ → ∃ β : K, β ≠ 0 ∧
      Submodule.span (𝓞 K) {β} = ∏ τ : P.host.E →+* ℂ, Submodule.span (𝓞 K)
        {x : K | ∃ a ∈ 𝔞, (x : ℂ) = τ (a : P.host.E)} ^ typeExp P.host (P.R.sigW j).1 (P.R.sigW j).2 τ ∧
      ∀ σ : K →+* ℂ, ‖σ β‖ ^ 2 = (Ideal.absNorm 𝔞 : ℝ) ^ ((P.R.sigW j).1 + (P.R.sigW j).2)) lh F₂ _ s2
    (fun j G b hG hs => by
      obtain ⟨G', g1, g2, g3⟩ := GlobalTheory.T.exists_capitulation_field_size P.host.E _ _ (typeExp_add P.host (P.R.sigW j).1 (P.R.sigW j).2) G b b hs
        fun τ x => hG (hτ τ x)
      exact ⟨G', g1, g2, fun K hK h => g3 K h⟩) P.R.m
  have hfd := finiteDimensional_of_sz s3
  have l : F₁ ≤ F := l2.trans l3
  refine ⟨F, hfd, ⟨fun x => l (hφ x), fun N hN => l (r1 N hN), c2 F l3, ?_, ?_⟩, ?_⟩
  · intro j j1 j2 𝔞 h𝔞
    obtain ⟨β, hβ, hsp, hn⟩ := c3 F hfd le_rfl j j1 j2 𝔞 h𝔞
    refine ⟨β, hβ, ?_, hn⟩
    rw [hsp, prod_typeExp]
    refine Finset.prod_congr rfl fun g _ => ?_
    simp only [conjugate_emb_apply]
    rfl
  · intro L hL p hpm z hz
    have hL' : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z := fun z => (hL z).trans (hlat z)
    refine l (l1 ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hpm
    rcases hpm with rfl | rfl
    · exact (le_sup_left : _ ≤ _ ⊔ W') ((le_sup_right : W ≤ _ ⊔ W) (hWc L hL' hz))
    · exact (le_sup_right : W' ≤ _ ⊔ W') (hWc' L hL' hz)
  · intro L hL
    obtain ⟨hG, hxi, hf8, hm⟩ := GlobalTheory.T.host_xi_order_bounds P L hL
    have hx := (hxi P.host.pde (by simp)).2
    have hx' := (hxi P.host.pde' (by simp)).2
    have hcl := GlobalTheory.log_classNumber_le_log_abs_discr_div P.host.E P.R.f hdeg
    have hlE' : lE = Real.log |((discr P.host.E : ℤ) : ℝ)| / (2 * P.R.f) := by rw [hlE, hdeg]; push_cast; rfl
    rw [← hlE'] at hcl
    have hrd := hL.rd
    rw [← hlE'] at hrd
    have hL4 := hL.len
    have hnum := GlobalTheory.sum_sizes_le_ring_polynomial P.R.f P.R.r P.R.m L lE lh (Real.log P.restRowsFiniteGroupCard) (by exact_mod_cast hf8)
      (by exact_mod_cast hL.rank) (by exact_mod_cast hm) (Nat.cast_nonneg _) hL4 hrd hlE0 hL.deg hcl hG
    have hlh0 : 0 ≤ lh := Real.log_natCast_nonneg _
    have a0 := hL.g 0
    have a1 := hL.g 1
    obtain ⟨a2, a3⟩ := hL.p
    have b0 := log_mul_pred_le (P.host.g 0)
    have b1 := log_mul_pred_le (P.host.g 1)
    have hn : ∀ p : ℕ, 0 < p → Real.log ((P.host.g 0 * P.host.g 1 * p : ℕ) : ℝ) =
        Real.log (P.host.g 0) + Real.log (P.host.g 1) + Real.log p := fun p h => by
      push_cast
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
    have n1 := hn _ hp
    have n2 := hn _ hp'
    have d1 : Real.log (Module.finrank ℚ P.host.E) ≤ 1 + L := by
      rw [hdeg]; push_cast
      rw [Real.log_mul (by norm_num) (by positivity)]
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      have := hL.deg
      linarith
    have e3 : Real.log ((3 ^ 4 : ℕ) : ℝ) ≤ 8 := by
      push_cast
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num)
      rw [show (81 : ℝ) = 3 ^ 4 by norm_num, Real.log_pow]; push_cast; linarith
    have e5 : Real.log ((5 ^ 4 : ℕ) : ℝ) ≤ 16 := by
      push_cast
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 5 by norm_num)
      rw [show (625 : ℝ) = 5 ^ 4 by norm_num, Real.log_pow]; push_cast; linarith
    refine sz_mono s3 ?_ ?_ <;>
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, poR]
      rw [← hlh] at hx hx' ⊢
      rw [n1, n2]
      generalize Real.log ((3 ^ 4 : ℕ) : ℝ) = x3 at e3 ⊢
      generalize Real.log ((5 ^ 4 : ℕ) : ℝ) = x5 at e5 ⊢
      linarith only [hx, hx', hnum, hlh0, a0, a1, a2, a3, b0, b1, d1, e3, e5, hdK, hrd, hL4]

end GlobalTheory.FieldSize
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasAllKTypesOfClosureDiscreteSeriesCoefficientsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasAllKTypes_of_closure_discreteSeriesCoefficients : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsDS ε lam σ → ∀ f : Matrix (Fin n) (Fin n) ℂ → ℂ, ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (v : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v j)) ∧
        ∀ y ∈ C, y ∈ UJset ε → ‖f y - ∑ j, ℓ j (σ y (v j))‖ < δ) →
    GlobalTheory.TypeSum.HasTypeAll (GlobalTheory.TypeSum.lieOf (Formalism.REAL.Jm ε)) (Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε)) σ f := by
  first | exact @GlobalTheory.ClosureSeries.hasTypeAll_of_closure | exact GlobalTheory.ClosureSeries.hasTypeAll_of_closure | (intros; apply GlobalTheory.ClosureSeries.hasTypeAll_of_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetOfContainsRayFiStatement
section
open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weberInvariantTorsionValues_subset_of_containsRayField : ∀ (K L : IntermediateField ℚ ℂ) [NumberField K] [NumberField L] [IsTotallyComplex K] (h : K ≤ L), Module.finrank ℚ K = 2 → discr K < -4 → ∀ P : PeriodPair, (∀ z, z ∈ P.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, 3 ≤ n → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (IntermediateField.inclusion h).toRingHom n → weberSet P n ⊆ L := by
  first | exact @GlobalTheory.FieldSize.WeberIn.weberSet_subset | exact GlobalTheory.FieldSize.WeberIn.weberSet_subset | (intros; apply GlobalTheory.FieldSize.WeberIn.weberSet_subset <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetRayClassFieldStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weberInvariantTorsionValues_subset_rayClassField : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, 3 ≤ n → ∀ (R : IntermediateField K ℂ) [NumberField R] [IsAbelianGalois K R], IsRay R (Ideal.span {(n : 𝓞 K)}) → weberSet L n ⊆ R := by
  first | exact @GlobalTheory.FieldSize.InRayAny.weberSet_subset | exact GlobalTheory.FieldSize.InRayAny.weberSet_subset | (intros; apply GlobalTheory.FieldSize.InRayAny.weberSet_subset <;> assumption)
end

