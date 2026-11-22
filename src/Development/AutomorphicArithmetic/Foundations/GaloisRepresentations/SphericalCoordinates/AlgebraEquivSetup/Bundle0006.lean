import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PKqEx
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pKqEx :
    TraceType → KqEx := by
  intro _ E _ _ _ A
  obtain ⟨w, hw⟩ : ∃ w : E, w = (A.ω : E) := ⟨_, rfl⟩
  have h1 : w + IsCMField.complexConj E w = (A.tr : E) := by
    have h := congrArg (fun z : 𝓞 E => (z : E)) A.tr_eq
    simpa [A.bar_eq, hw] using h
  have h2 : w * IsCMField.complexConj E w = (A.nm : E) := by
    have h := congrArg (fun z : 𝓞 E => (z : E)) A.nm_eq
    simpa [A.bar_eq, hw] using h
  have hq : w ^ 2 - (A.tr : E) * w + (A.nm : E) = 0 := by
    linear_combination w * h1 - h2
  have him : ∀ τ : E →+* ℂ, (τ w).im ≠ 0 := by
    intro τ h0
    have hz : (τ w) ^ 2 - (A.tr : ℂ) * τ w + (A.nm : ℂ) = 0 := by
      have h := congrArg τ hq
      simpa using h
    have hr : τ w = (((τ w).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h0])
    obtain ⟨r, hr'⟩ : ∃ r : ℝ, τ w = (r : ℂ) := ⟨_, hr⟩
    rw [hr'] at hz
    have hz' : r ^ 2 - (A.tr : ℝ) * r + (A.nm : ℝ) = 0 := by exact_mod_cast hz
    have hd : ((A.tr : ℝ)) ^ 2 - 4 * (A.nm : ℝ) < 0 := by exact_mod_cast A.disc_neg
    nlinarith [sq_nonneg (2 * r - (A.tr : ℝ))]
  have hint : IsIntegral ℚ w := Algebra.IsIntegral.isIntegral w
  have hdeg : (minpoly ℚ w).natDegree = 2 := by
    have hpd : (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ).natDegree = 2 := by
      compute_degree!
    have hp0 : (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ) ≠ 0 := by
      intro h
      rw [h] at hpd
      simp at hpd
    have hroot : Polynomial.aeval w (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ) = 0 := by
      simpa using hq
    have hle := Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ w hroot) hp0
    have hpos := minpoly.natDegree_pos hint
    have hne : (minpoly ℚ w).natDegree ≠ 1 := by
      intro h
      obtain ⟨q, hq'⟩ := minpoly.natDegree_eq_one_iff.1 h
      apply him A.τ₀
      rw [← hq']
      simp
    omega
  have hfr : Module.finrank ℚ (IntermediateField.adjoin ℚ {w}) = 2 := by
    rw [IntermediateField.adjoin.finrank hint, hdeg]
  have hmem : w ∈ IntermediateField.adjoin ℚ {w} := IntermediateField.mem_adjoin_simple_self ℚ w
  refine ⟨(IntermediateField.adjoin ℚ {w}).toSubfield, hw ▸ hmem, ⟨?_, fun τ => ⟨w, hmem, him τ⟩⟩, ?_⟩
  · exact hfr
  · intro x hx
    rw [← hw]
    let pb := IntermediateField.adjoin.powerBasis hint
    obtain ⟨f, hf, hfx⟩ := pb.exists_eq_aeval ⟨x, hx⟩
    have hdim : pb.dim = 2 := by
      rw [IntermediateField.adjoin.powerBasis_dim, hdeg]
    have hf1 : f.natDegree ≤ 1 := by omega
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hf1] at hfx
    refine ⟨f.coeff 0, f.coeff 1, ?_⟩
    have h := congrArg (fun z : IntermediateField.adjoin ℚ {w} => (z : E)) hfx
    simp [pb] at h
    rw [h]
    simp [add_comm]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPerfCof
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pPerfCof :
    PerfCof := by
  intro E _ _ _ A
  classical
  have hδ : A.δ ≠ 0 := by
    intro h
    have h2 := A.δ_sign A.τ₀ rfl
    rw [h, map_zero, Complex.zero_im] at h2
    exact lt_irrefl _ h2
  let Ψ : E →ₗ[ℚ] Module.Dual ℚ E :=
    ((LinearMap.mul ℚ E).compr₂ (Algebra.trace ℚ E)) ∘ₗ LinearMap.mulLeft ℚ A.δ
  have hΨ : ∀ x z, Ψ x z = Algebra.trace ℚ E (A.δ * x * z) := fun x z => rfl
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    by_contra hx0
    have h1 := LinearMap.congr_fun hx (A.δ * x)⁻¹
    rw [hΨ, mul_inv_cancel₀ (mul_ne_zero hδ hx0), LinearMap.zero_apply,
      show (1 : E) = algebraMap ℚ E 1 from (map_one _).symm, Algebra.trace_algebraMap] at h1
    have hpos : 0 < Module.finrank ℚ E := Module.finrank_pos
    simp at h1
    omega
  have hsurj : Function.Surjective Ψ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank Subspace.dual_finrank_eq.symm).mp hinj
  let bQ := NumberField.integralBasis E
  let b := NumberField.RingOfIntegers.basis E
  choose ξ hξ using fun i => hsurj (bQ.coord i)
  obtain ⟨y, hy0, hyint⟩ := exists_integral_multiples ℤ ℚ (Finset.univ.image ξ)
  have hint : ∀ i, ∃ w : 𝓞 E, algebraMap (𝓞 E) E w = y • ξ i := fun i =>
    (IsIntegralClosure.isIntegral_iff (A := 𝓞 E)).mp
      (hyint _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))
  choose w hw using hint
  let η : _ → 𝓞 E := fun i => (y : 𝓞 E) * w i
  have hηc : ∀ i, algebraMap (𝓞 E) E (η i) = (y : E) * ((y : E) * ξ i) := by
    intro i
    change algebraMap (𝓞 E) E ((y : 𝓞 E) * w i) = _
    rw [map_mul, map_intCast, hw i, zsmul_eq_mul]
  have hDz : ((y.natAbs * y.natAbs : ℕ) : ℤ) = y * y := Int.natAbs_mul_self
  have hDpos : 0 < y.natAbs * y.natAbs :=
    Nat.mul_pos (Int.natAbs_pos.mpr hy0) (Int.natAbs_pos.mpr hy0)
  have key : ∀ i z, A.trd (η i * z) = ((y.natAbs * y.natAbs : ℕ) : ℤ) * b.coord i z := by
    intro i
    have hlin : A.trd ∘ₗ LinearMap.mulLeft ℤ (η i) = ((y.natAbs * y.natAbs : ℕ) : ℤ) • b.coord i := by
      refine b.ext fun j => ?_
      apply Int.cast_injective (α := ℚ)
      have hb : bQ j = algebraMap (𝓞 E) E (b j) := NumberField.integralBasis_apply E j
      have hc : (((η i * b j : 𝓞 E)) : E) = (y : E) * ((y : E) * ξ i) * bQ j := by
        change algebraMap (𝓞 E) E (η i * b j) = _
        rw [map_mul, hηc, hb]
      rw [LinearMap.comp_apply, LinearMap.mulLeft_apply, A.trd_spec, hc, LinearMap.smul_apply,
        smul_eq_mul, hDz,
        show A.δ * ((y : E) * ((y : E) * ξ i) * bQ j) = ((y * y : ℤ) : ℚ) • (A.δ * ξ i * bQ j) by
          rw [Algebra.smul_def, map_intCast]
          push_cast
          ring,
        map_smul, smul_eq_mul, ← hΨ, hξ]
      rw [Module.Basis.coord_apply, Module.Basis.coord_apply, Module.Basis.repr_self,
        Module.Basis.repr_self]
      rcases eq_or_ne j i with h | h
      · subst h
        simp
      · simp [Finsupp.single_apply, h]
    intro z
    exact LinearMap.congr_fun hlin z
  have hdual : ∀ f : 𝓞 E →ₗ[ℤ] ℤ, ∃ x : 𝓞 E, ∀ z,
      A.trd (x * z) = ((y.natAbs * y.natAbs : ℕ) : ℤ) * f z := by
    intro f
    refine ⟨∑ i, f (b i) • η i, fun z => ?_⟩
    conv_rhs => rw [← b.sum_dual_apply_smul_coord f]
    rw [Finset.sum_mul, map_sum, LinearMap.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_mul_assoc, map_smul, key, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul]
    ring
  have hc0 : A.c ≠ 0 := by
    intro h
    exact A.c_ne (by rw [h]; rfl)
  have hN0 : 0 < Ideal.absNorm (Ideal.span {A.c}) := by
    refine Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hc0
  obtain ⟨c', hc'⟩ := Ideal.mem_span_singleton.mp (Ideal.absNorm_mem (Ideal.span {A.c}))
  refine ⟨y.natAbs * y.natAbs * Ideal.absNorm (Ideal.span {A.c}), Nat.mul_pos hDpos hN0,
    fun q hq => ⟨_, hq, fun f => ?_, ⟨c' * ((y.natAbs * y.natAbs : ℕ) : 𝓞 E), ?_⟩⟩⟩
  · obtain ⟨x, hx⟩ := hdual ((Ideal.absNorm (Ideal.span {A.c}) : ℤ) • f)
    refine ⟨x, fun z => ?_⟩
    rw [hx, LinearMap.smul_apply, smul_eq_mul]
    push_cast
    ring
  · rw [← mul_assoc, ← hc']
    push_cast
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPerfOf
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

private theorem exists_trace_rep (E : Type) [Field E] [NumberField E] (f : 𝓞 E →ₗ[ℤ] ℤ) :
    ∃ z : E, ∀ y : 𝓞 E, Algebra.trace ℚ E (z * (y : E)) = ((f y : ℤ) : ℚ) := by
  let g : E →ₗ[ℚ] ℚ := (integralBasis E).constr ℚ (fun i => ((f (RingOfIntegers.basis E i) : ℤ) : ℚ))
  have hg : ∀ y : 𝓞 E, g (y : E) = ((f y : ℤ) : ℚ) := by
    have hext : ((g.restrictScalars ℤ).comp ((Algebra.linearMap (𝓞 E) E).restrictScalars ℤ)) =
        (Algebra.linearMap ℤ ℚ).comp f := by
      refine (RingOfIntegers.basis E).ext fun i => ?_
      simp [g, ← integralBasis_apply]
    intro y
    simpa using LinearMap.congr_fun hext y
  have hnd : (Algebra.traceForm ℚ E).Nondegenerate := traceForm_nondegenerate ℚ E
  refine ⟨(LinearMap.BilinForm.toDual (Algebra.traceForm ℚ E) hnd).symm g, fun y => ?_⟩
  rw [← Algebra.traceForm_apply, ← LinearMap.BilinForm.toDual_def hnd, LinearEquiv.apply_symm_apply]
  exact hg y

theorem UpperTheory.Gal.W2.Seed.pPerfOf :
    PerfOf := by
  intro E _ _ _ A M hgen hc q hq
  obtain ⟨_, e1, he1, hz⟩ := hgen
  obtain ⟨e2, he2, c', hc'⟩ := hc
  refine ⟨e1 * e2, Nat.Coprime.mul (he1.coprime_dvd_right hq) (he2.coprime_dvd_right hq), ?_, ⟨c' * e1, ?_⟩⟩
  · intro f
    obtain ⟨z, hzf⟩ := exists_trace_rep E f
    have hzc : InCodiff z := fun y => ⟨f y, hzf y⟩
    obtain ⟨x, hx⟩ := hz z hzc
    refine ⟨(e2 : 𝓞 E) * x, fun y => ?_⟩
    have h := A.trd_spec ((e2 : 𝓞 E) * x * y)
    have hmul : A.δ * ((((e2 : 𝓞 E) * x * y : 𝓞 E)) : E) = ((e1 * e2 : ℕ) : ℚ) • (z * (y : E)) := by
      rw [Algebra.smul_def, map_natCast]
      push_cast
      linear_combination (-((e2 : E) * (y : E))) * hx
    have hq' : ((A.trd ((e2 : 𝓞 E) * x * y) : ℤ) : ℚ) = (((e1 * e2 : ℕ) : ℤ) : ℚ) * ((f y : ℤ) : ℚ) := by
      rw [h, hmul, map_smul, hzf, smul_eq_mul]
      push_cast; ring
    exact_mod_cast hq'
  · rw [← mul_assoc, hc']
    push_cast
    ring
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PPosGen
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pPosGen :
    CodiffUnit → PosGen := by
  intro hCU E _ _ _ M hM t htc hg
  obtain ⟨hin, e, he, hz⟩ := id hg

  have h1 : InCodiff (1 : E) := by
    intro x
    have hx : IsIntegral ℤ (Algebra.trace ℚ E (x : E)) := Algebra.isIntegral_trace x.2
    obtain ⟨m, hm⟩ := IsIntegrallyClosed.isIntegral_iff.mp hx
    exact ⟨m, by rw [one_mul, ← hm]; simp⟩

  obtain ⟨N, hN⟩ := exists_nat_gt (∑ τ : E →+* ℂ, |(τ t).re|)
  have hbound : ∀ τ : E →+* ℂ, |(τ t).re| < N := fun τ =>
    lt_of_le_of_lt (Finset.single_le_sum (f := fun τ : E →+* ℂ => |(τ t).re|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ τ)) hN
  have hin' : InCodiff (t + (M : E) * (N : E)) := by
    intro x
    obtain ⟨a, ha⟩ := hin x
    obtain ⟨b, hb⟩ := h1 x
    refine ⟨a + M * N * b, ?_⟩
    have hs : (t + (M : E) * (N : E)) * (x : E) = t * x + ((M : ℚ) * (N : ℚ)) • (1 * (x : E)) := by
      rw [Algebra.smul_def]; simp; ring
    rw [hs, map_add, map_smul, ha, hb]
    simp
  obtain ⟨x, hx⟩ := hz 1 h1
  have hgen : GenCodiff M (t + (M : E) * (N : E)) := by
    refine hCU E M hM t _ hg hin' ?_
    intro P hP hMP
    have heP : (e : 𝓞 E) ∉ P := by
      intro h
      have hc : ((e.gcdA M : ℤ) : 𝓞 E) * (e : 𝓞 E) + ((e.gcdB M : ℤ) : 𝓞 E) * (M : 𝓞 E) = 1 := by
        have := Nat.gcd_eq_gcd_ab e M
        rw [he.gcd_eq_one] at this
        have h2 : ((e : ℤ) * e.gcdA M + (M : ℤ) * e.gcdB M) = 1 := by
          rw [← this]; simp
        have h3 := congrArg (Int.cast : ℤ → 𝓞 E) h2
        push_cast at h3
        rw [← h3]; ring
      apply hP.ne_top
      rw [Ideal.eq_top_iff_one, ← hc]
      exact P.add_mem (P.mul_mem_left _ h) (P.mul_mem_left _ hMP)
    refine ⟨(e : 𝓞 E), (e : 𝓞 E) + (M : 𝓞 E) * ((N : 𝓞 E) * x), heP, ?_, ?_⟩
    · intro h
      exact heP ((P.add_mem_iff_left (P.mul_mem_right _ hMP)).mp h)
    · have hx' : (e : E) = t * x := by simpa using hx
      push_cast
      linear_combination ((M : E) * (N : E)) * hx'
  refine ⟨t + (M : E) * (N : E), ?_, hgen, ?_⟩
  · simp [htc]
  · intro τ
    have hb := abs_lt.mp (hbound τ)
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hre : (τ (t + (M : E) * (N : E))).re = (τ t).re + (M : ℝ) * (N : ℝ) := by
      simp
    rw [hre]
    nlinarith [hb.1]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PQuadEx
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

namespace UpperTheory.Gal.W2.Seed.QuadraticExtensions

private lemma sq_in_Zq (q : ℕ) [Fact q.Prime] (d g d0 : ℕ) (hg : 0 < g) (hd : g ^ 2 * d0 = d)
    (h : IsSquare (-(d : ℚ_[q]))) : ∃ z : ℤ_[q], z ^ 2 = -(d0 : ℤ_[q]) := by
  obtain ⟨y, hy⟩ := h
  have hg0 : (g : ℚ_[q]) ≠ 0 := by exact_mod_cast hg.ne'
  have hd' : (d : ℚ_[q]) = (g : ℚ_[q]) ^ 2 * d0 := by rw [← hd]; push_cast; ring
  rw [hd'] at hy
  have hx : (y / g) ^ 2 = -(d0 : ℚ_[q]) := by
    rw [div_pow, div_eq_iff (pow_ne_zero 2 hg0)]
    linear_combination -hy
  have hxn : ‖y / (g : ℚ_[q])‖ ≤ 1 := by
    have h1 : ‖y / (g : ℚ_[q])‖ ^ 2 ≤ 1 := by
      rw [← norm_pow, hx, norm_neg]
      have : ‖((d0 : ℤ_[q]) : ℚ_[q])‖ ≤ 1 := PadicInt.norm_le_one _
      simpa using this
    by_contra hc
    push_neg at hc
    nlinarith
  let z : ℤ_[q] := ⟨y / g, hxn⟩
  have hzc : (z : ℚ_[q]) = y / g := rfl
  refine ⟨z, ?_⟩
  have hc : ((z ^ 2 : ℤ_[q]) : ℚ_[q]) = ((-(d0 : ℤ_[q]) : ℤ_[q]) : ℚ_[q]) := by
    push_cast
    rw [hzc]
    exact hx
  first
    | exact PadicInt.ext hc
    | exact Subtype.ext hc
    | exact PadicInt.coe_injective hc

private lemma not_dvd (q : ℕ) [hq : Fact q.Prime] (d0 : ℕ) (hsq : Squarefree d0) (z : ℤ_[q])
    (hz : z ^ 2 = -(d0 : ℤ_[q])) : ¬ q ∣ d0 := by
  intro hdvd
  have hnorm : ‖z‖ ^ 2 = ‖((d0 : ℤ) : ℤ_[q])‖ := by
    rw [← norm_pow, hz, norm_neg, Int.cast_natCast]
  have hd1 : ‖((d0 : ℤ) : ℤ_[q])‖ < 1 :=
    (PadicInt.norm_int_lt_one_iff_dvd _).mpr (by exact_mod_cast hdvd)
  have hz1 : ‖z‖ < 1 := by
    by_contra hc
    push_neg at hc
    nlinarith [norm_nonneg z]
  obtain ⟨w, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd z).mp hz1
  have hle : ‖((d0 : ℤ) : ℤ_[q])‖ ≤ (q : ℝ) ^ (-(2 : ℕ) : ℤ) := by
    rw [← hnorm, norm_mul, PadicInt.norm_p, mul_pow]
    have hw := PadicInt.norm_le_one w
    have he : (q : ℝ) ^ (-(2 : ℕ) : ℤ) = ((q : ℝ)⁻¹) ^ 2 := by
      rw [_root_.zpow_neg, zpow_natCast, inv_pow]
    rw [he]
    exact mul_le_of_le_one_right (by positivity) (pow_le_one₀ (norm_nonneg w) hw)
  have h2 := PadicInt.norm_int_le_pow_iff_dvd.mp hle
  have h3 : q ^ 2 ∣ d0 := by exact_mod_cast h2
  rw [sq] at h3
  exact (Nat.Prime.one_lt hq.out).ne' (Nat.isUnit_iff.mp (hsq q h3))

private lemma root_mod (q : ℕ) [Fact q.Prime] (d0 : ℕ) (z : ℤ_[q])
    (hz : z ^ 2 = -(d0 : ℤ_[q])) : ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 + d0 := by
  refine ⟨((PadicInt.toZMod z).val : ℤ), ?_⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).1
  have h := congrArg (PadicInt.toZMod (p := q)) hz
  simp only [map_pow, map_neg, map_natCast] at h
  push_cast
  rw [ZMod.natCast_zmod_val, h]
  ring

private lemma two_case [Fact (Nat.Prime 2)] (d0 : ℕ) (hodd : ¬ 2 ∣ d0) (z : ℤ_[2])
    (hz : z ^ 2 = -(d0 : ℤ_[2])) : d0 % 8 = 7 := by
  have h := congrArg (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) hz
  rw [map_pow, map_neg, map_natCast] at h
  generalize (PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod (2 ^ 3)) z = a at h
  revert a
  show ∀ a : ZMod 8, a ^ 2 = -((d0 : ZMod 8)) → d0 % 8 = 7
  rw [← ZMod.natCast_mod d0 8]
  have hlt := Nat.mod_lt d0 (by norm_num : 8 > 0)
  have hodd : d0 % 2 = 1 := by omega
  interval_cases h8 : d0 % 8
  all_goals first | omega | decide

private lemma not_dvd_four (q : ℕ) (hq : q.Prime) (h2 : q ≠ 2) : ¬ (q : ℤ) ∣ 4 := by
  intro h
  have h' : q ∣ 2 ^ 2 := by exact_mod_cast h
  exact h2 ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp (hq.dvd_of_dvd_pow h'))

private lemma root_odd (q : ℕ) (hq : q.Prime) (h2 : q ≠ 2) (d0 m : ℕ) (hm : d0 + 1 = 4 * m) (r0 : ℤ)
    (hr : (q : ℤ) ∣ r0 ^ 2 + d0) : ∃ r : ℤ, (q : ℤ) ∣ r ^ 2 - 1 * r + m := by
  obtain ⟨k, hk⟩ : ∃ k : ℕ, q + 1 = 2 * k := by
    rcases hq.eq_two_or_odd' with h | ⟨j, hj⟩
    · exact absurd h h2
    · exact ⟨j + 1, by omega⟩
  refine ⟨(r0 + 1) * k, ?_⟩
  have hpz : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
  have h4 : (q : ℤ) ∣ 4 * (((r0 + 1) * k) ^ 2 - 1 * ((r0 + 1) * k) + m) := by
    obtain ⟨c, hc⟩ := hr
    have hk' : (2 * k : ℤ) = q + 1 := by exact_mod_cast hk.symm
    have hm' : (4 * m : ℤ) = d0 + 1 := by exact_mod_cast hm.symm
    refine ⟨c + (r0 + 1) * (2 * r0 + (r0 + 1) * q), ?_⟩
    linear_combination ((r0 + 1) ^ 2 * (2 * (k : ℤ) + q + 1) - 2 * (r0 + 1)) * hk' + hm' + hc
  rcases hpz.dvd_or_dvd h4 with h | h
  · exact absurd h (not_dvd_four q hq h2)
  · exact h

end UpperTheory.Gal.W2.Seed.QuadraticExtensions

open UpperTheory.Gal.W2.Seed.QuadraticExtensions in
theorem UpperTheory.Gal.W2.Seed.pQuadEx :
    QuadEx := by
  intro d hd
  obtain ⟨d0, g, hgd, hsq⟩ := Nat.sq_mul_squarefree d
  have hg : 0 < g := by
    rcases Nat.eq_zero_or_pos g with h | h
    · subst h; simp at hgd; omega
    · exact h
  have hd0 : 0 < d0 := by
    rcases Nat.eq_zero_or_pos d0 with h | h
    · subst h; simp at hgd; omega
    · exact h
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  have hdq : (d : ℚ) = (g : ℚ) ^ 2 * d0 := by rw [← hgd]; push_cast; ring
  by_cases h43 : d0 % 4 = 3
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, d0 + 1 = 4 * m := ⟨(d0 + 1) / 4, by omega⟩
    have hdisc : (1 : ℤ) ^ 2 - 4 * (m : ℤ) = -(d0 : ℤ) := by
      have : ((d0 : ℤ) + 1) = 4 * (m : ℤ) := by exact_mod_cast hm
      linarith
    refine ⟨1, m, 1 / (g : ℚ), ?_, ?_, ?_⟩
    · rw [hdisc]; omega
    · rw [hdisc, hdq]; push_cast; field_simp
    · intro q _ hsqr
      obtain ⟨z, hz⟩ := sq_in_Zq q d g d0 hg hgd hsqr
      have hnd := not_dvd q d0 hsq z hz
      refine ⟨?_, ?_⟩
      · rw [hdisc, dvd_neg]
        intro h
        exact hnd (by exact_mod_cast h)
      · by_cases hq2 : q = 2
        · subst hq2
          have h7 := two_case d0 hnd z hz
          refine ⟨0, ?_⟩
          have : (m : ℤ) % 2 = 0 := by omega
          push_cast
          omega
        · obtain ⟨r0, hr0⟩ := root_mod q d0 z hz
          exact root_odd q (Fact.out) hq2 d0 m hm r0 hr0
  · refine ⟨0, d0, 2 / (g : ℚ), ?_, ?_, ?_⟩
    · omega
    · rw [hdq]; push_cast; field_simp; ring
    · intro q _ hsqr
      obtain ⟨z, hz⟩ := sq_in_Zq q d g d0 hg hgd hsqr
      have hnd := not_dvd q d0 hsq z hz
      refine ⟨?_, ?_⟩
      · by_cases hq2 : q = 2
        · subst hq2
          have h7 := two_case d0 hnd z hz
          omega
        · have hq : q.Prime := Fact.out
          have hpz : Prime (q : ℤ) := Nat.prime_iff_prime_int.mp hq
          intro h
          have h' : (q : ℤ) ∣ 4 * (d0 : ℤ) := by
            have : (0 : ℤ) ^ 2 - 4 * (d0 : ℤ) = -(4 * (d0 : ℤ)) := by ring
            rw [this, dvd_neg] at h
            exact h
          rcases hpz.dvd_or_dvd h' with h4 | h4
          · exact not_dvd_four q hq hq2 h4
          · exact hnd (by exact_mod_cast h4)
      · obtain ⟨r0, hr0⟩ := root_mod q d0 z hz
        exact ⟨r0, by simpa using hr0⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.PRepEx
section
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

theorem UpperTheory.Gal.W2.Seed.pRepEx :
    RepEx := by
  intro E _ _ n
  classical
  let b := NumberField.RingOfIntegers.basis E
  let bZ := Pi.basis (fun _ : Fin n => b)
  let bQ := Pi.basis (fun _ : Fin n => NumberField.integralBasis E)
  let b1 := Algebra.TensorProduct.basis ℚ bZ
  refine ⟨b1.equiv bQ (Equiv.refl _), ?_⟩
  let f1 : (Fin n → 𝓞 E) →ₗ[ℤ] (Fin n → E) :=
    ((b1.equiv bQ (Equiv.refl _)).toLinearMap.restrictScalars ℤ) ∘ₗ
      TensorProduct.mk ℤ ℚ (Fin n → 𝓞 E) 1
  let f2 : (Fin n → 𝓞 E) →ₗ[ℤ] (Fin n → E) :=
    LinearMap.pi (fun i => (algebraMap (𝓞 E) E).toIntAlgHom.toLinearMap ∘ₗ LinearMap.proj i)
  have hf : f1 = f2 := by
    refine bZ.ext fun k => ?_
    have hk : f1 (bZ k) = b1.equiv bQ (Equiv.refl _) (b1 k) := by
      rw [Algebra.TensorProduct.basis_apply]
      rfl
    rw [hk, Module.Basis.equiv_apply]
    obtain ⟨i, j⟩ := k
    funext l
    simp [bQ, bZ, f2, Pi.basis_apply, Pi.single_apply, NumberField.integralBasis_apply]
    split_ifs <;> simp
    rfl
  intro v i
  exact congr_fun (LinearMap.congr_fun hf v) i
end

