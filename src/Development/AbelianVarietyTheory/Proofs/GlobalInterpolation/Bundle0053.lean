import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0052
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GoodTopBot
import Development.AbelianVarietyTheory.PublishedTheorems.GlobalTheta.WeylDualWeylLatticesAgreeOfLowestAlcove
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0041
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0039
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsExtensionRepIndexTwoOfTraceInvariant
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0047
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.EqOneOrEqOfKer
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationMemOfIsGLSchemeSubmodule
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BrunTitchmarshExistsConst
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

theorem exists_dvd_mul_add_of_prime (l q r : ℕ) (hl : l.Prime) (hq : ¬ l ∣ q) : ∃ c : ℕ, l ∣ q * c + r := by
  haveI := Fact.mk hl
  have hq' : (q : ZMod l) ≠ 0 := fun h => hq ((ZMod.natCast_eq_zero_iff q l).1 h)
  refine ⟨(-(r : ZMod l) * (q : ZMod l)⁻¹).val, (ZMod.natCast_eq_zero_iff _ l).1 ?_⟩
  push_cast
  rw [ZMod.natCast_zmod_val]
  field_simp
  ring

theorem card_large_primes_class_le (q a Q M N : ℕ) (P : Finset ℕ) (hq : 1 ≤ q) (hQ : 1 ≤ Q)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≡ a [MOD q] ∧ Q < p ∧ q * M ≤ p ∧ p < q * (M + N)) :
    (P.card : ℝ) * ((q.totient : ℝ) / q * Real.log Q) ≤ (Q : ℝ) ^ 2 + 2 * Real.pi * N := by
  have hdec : ∀ p ∈ P, p = q * (p / q) + a % q := fun p hp => by
    have h : p % q = a % q := (hP p hp).2.1
    rw [← h, Nat.div_add_mod]
  have hinj : Set.InjOn (fun p => p / q + 1) (P : Set ℕ) := by
    intro p hp p' hp' h
    have h' : p / q = p' / q := by simpa using h
    rw [hdec p hp, hdec p' hp', h']
  have key := GlobalTheory.T.arithmeticLargeSieve_one_residue_class_per_prime M N Q q (P.image fun p => p / q + 1) hQ hq ?_ ?_
  · rwa [Finset.card_image_of_injOn hinj] at key
  · intro n hn
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hn
    obtain ⟨-, -, -, h1, h2⟩ := hP p hp
    have h3 : M ≤ p / q := (Nat.le_div_iff_mul_le hq).2 (by rwa [mul_comm])
    have h4 : p / q < M + N := (Nat.div_lt_iff_lt_mul hq).2 (by rwa [mul_comm])
    exact Finset.mem_Ioc.2 ⟨by omega, by omega⟩
  · intro l hl hlQ hlq
    obtain ⟨c, hc⟩ := exists_dvd_mul_add_of_prime l q (a % q) hl hlq
    refine ⟨c + 1, fun n hn h => ?_⟩
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hn
    have h1 : p / q ≡ c [MOD l] := Nat.ModEq.add_right_cancel' 1 h
    have h2 : q * (p / q) + a % q ≡ q * c + a % q [MOD l] := (h1.mul_left q).add_right _
    rw [← hdec p hp] at h2
    have h3 : l ∣ p := (Nat.modEq_zero_iff_dvd).1 (h2.trans ((Nat.modEq_zero_iff_dvd).2 hc))
    have h4 := (Nat.prime_dvd_prime_iff_eq hl (hP p hp).1).1 h3
    have := (hP p hp).2.2.1
    omega

theorem brun_titchmarsh_const : ∃ C : ℝ, 0 < C ∧ ∀ (q a : ℕ) (x y : ℝ), 1 ≤ q → Nat.Coprime a q → 0 ≤ x → 2 * (q : ℝ) ≤ y → (((primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q])).card : ℝ) ≤ C * y / (q.totient * Real.log (y / q)) := by
  refine ⟨48, by norm_num, fun q a x y hq _ hx hy => ?_⟩
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  obtain ⟨z, hz⟩ : ∃ z : ℝ, z = y / q := ⟨_, rfl⟩
  have hyz : y = q * z := by rw [hz]; field_simp
  have hz2 : 2 ≤ z := by rw [hz, le_div_iff₀ hq0]; exact hy
  rw [← hz]
  have hfl : 2 ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast hz2)
  have hflz : (⌊z⌋₊ : ℝ) ≤ z := Nat.floor_le (by linarith)
  have hzfl : z < ⌊z⌋₊ + 1 := Nat.lt_floor_add_one z
  obtain ⟨s, hs⟩ : ∃ s, s = Nat.sqrt ⌊z⌋₊ := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by rw [hs, Nat.le_sqrt]; omega
  have hs2 : s * s ≤ ⌊z⌋₊ := hs ▸ Nat.sqrt_le _
  have hs3 : ⌊z⌋₊ < (s + 1) * (s + 1) := hs ▸ Nat.lt_succ_sqrt _
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = s + 1 := ⟨_, rfl⟩
  have hQ2 : (2 : ℝ) ≤ Q := by exact_mod_cast (by omega : 2 ≤ Q)
  have hQz : (Q : ℝ) ^ 2 ≤ 4 * z := by
    have : Q ^ 2 ≤ 4 * ⌊z⌋₊ := by rw [hQ]; nlinarith
    have : (Q : ℝ) ^ 2 ≤ 4 * ⌊z⌋₊ := by exact_mod_cast this
    linarith
  have hzQ : z ≤ (Q : ℝ) ^ 2 := by
    have : ⌊z⌋₊ + 1 ≤ Q ^ 2 := by rw [hQ]; nlinarith
    have : (⌊z⌋₊ : ℝ) + 1 ≤ (Q : ℝ) ^ 2 := by exact_mod_cast this
    linarith
  have hlz : 0 < Real.log z := Real.log_pos (by linarith)
  have hlog : Real.log z ≤ 2 * Real.log Q := by
    have := Real.log_le_log (by linarith) hzQ
    rw [Real.log_pow] at this
    exact_mod_cast this
  have hlQ : Real.log Q ≤ Q := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < Q)
    linarith
  have hφ0 : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.2 hq
  have hφq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  set P := (primesIoc x (x + y)).filter (fun p => p ≡ a [MOD q]) with hP
  have hbig := card_large_primes_class_le q a Q (⌊x⌋₊ / q) (⌊z⌋₊ + 2) (P.filter fun p => Q < p) hq (by omega) (by
    intro p hp
    simp only [hP, primesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := hp
    refine ⟨h3, h4, h5, (Nat.mul_div_le _ _).trans h1.le, ?_⟩
    have h6 : (p : ℝ) ≤ x + y := (Nat.le_floor_iff (by nlinarith)).1 h2
    have h7 : x < ⌊x⌋₊ + 1 := Nat.lt_floor_add_one x
    have h8 : ⌊x⌋₊ + 1 ≤ q * (⌊x⌋₊ / q + 1) := Nat.lt_mul_div_succ _ hq
    have h9 : (⌊x⌋₊ : ℝ) + 1 ≤ q * (((⌊x⌋₊ / q : ℕ) : ℝ) + 1) := by exact_mod_cast h8
    have h10 : (p : ℝ) < q * (((⌊x⌋₊ / q : ℕ) : ℝ) + (⌊z⌋₊ + 2)) := by nlinarith
    exact_mod_cast h10)
  have hsmall : (P.filter fun p => ¬ Q < p).card ≤ Q := by
    calc _ ≤ (Finset.Icc 1 Q).card := Finset.card_le_card fun p hp => by
            simp only [hP, primesIoc, Finset.mem_filter, Finset.mem_Ioc] at hp
            exact Finset.mem_Icc.2 ⟨hp.1.1.2.one_le, by omega⟩
      _ = Q := by simp
  have hsum := Finset.card_filter_add_card_filter_not (s := P) (fun p => Q < p)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = ((P.filter fun p => Q < p).card : ℝ) := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hB ▸ Nat.cast_nonneg _
  have hcard : (P.card : ℝ) ≤ B + Q := by
    rw [hB]; exact_mod_cast (by omega)
  rw [← hB] at hbig
  push_cast at hbig
  have hpi := Real.pi_lt_four
  have hpi0 := Real.pi_pos
  have h1 : B * ((q.totient : ℝ) / q * Real.log Q) ≤ 20 * z := by nlinarith
  have h2 : B * (q.totient * Real.log Q) ≤ 20 * y := by
    have := mul_le_mul_of_nonneg_left h1 hq0.le
    rw [hyz]
    calc _ = q * (B * ((q.totient : ℝ) / q * Real.log Q)) := by field_simp
      _ ≤ _ := by linarith
  have h3 : B * (q.totient * Real.log z) ≤ 40 * y := by
    have := mul_le_mul_of_nonneg_left hlog (mul_nonneg hB0 hφ0.le)
    nlinarith
  have h4 : (Q : ℝ) * Real.log z ≤ 8 * z := by nlinarith
  have h5 : (Q : ℝ) * (q.totient * Real.log z) ≤ 8 * y := by
    have : (q.totient : ℝ) * (Q * Real.log z) ≤ q * (8 * z) :=
      mul_le_mul hφq h4 (by positivity) hq0.le
    rw [hyz]; nlinarith
  rw [le_div_iff₀ (by positivity)]
  have := mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℝ) ≤ q.totient * Real.log z)
  nlinarith

end GlobalTheory.Lin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqWeightsOfTraceEPowerHighestWeightValueEqStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_weights_of_traceEPowerHighestWeightValue_eq : ∀ (p : ℕ), p.Prime → ∀ (k : Type) [Field k] [CharP k p] (N : ℕ) (ν μ : Fin N → ℕ), Antitone ν → Antitone μ → (∀ h : 0 < N, ν ⟨N - 1, by omega⟩ = 0 ∧ μ ⟨0, h⟩ ≤ ν ⟨0, h⟩ ∧ ν ⟨0, h⟩ + (N - 1) ≤ p) → (∀ j, hcVal k (fun i => (μ i : k)) j = hcVal k (fun i => (ν i : k)) j) → μ = ν := by
  first | exact @GlobalTheory.Alc.eq_of_hcVal_eq | exact GlobalTheory.Alc.eq_of_hcVal_eq | (intros; apply GlobalTheory.Alc.eq_of_hcVal_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsDominantHighestVectorOfLtStableStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dominant_highest_vector_of_lt_stable : ∀ (k : Type) [Field k] (N : ℕ) (M M' : Submodule k (MvPolynomial (Fin N × Fin N) k)), Good M → Good M' → M < M' → (∃ c : ℕ, ∀ f ∈ M', ∀ m ∈ f.support, ∑ a, rowDeg m a ≤ c) → ∃ (μ : Fin N → ℕ) (v : MvPolynomial (Fin N × Fin N) k), Antitone μ ∧ v ∈ M' ∧ v ∉ M ∧ IsWeightedHomogeneous (rowW N N) v μ ∧ ∀ a b, a < b → rowE k N N a b v ∈ M := by
  first | exact @GlobalTheory.Alc.exists_dominant_highest_vector_of_lt | exact GlobalTheory.Alc.exists_dominant_highest_vector_of_lt | (intros; apply GlobalTheory.Alc.exists_dominant_highest_vector_of_lt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsSide
section

end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PowDvdOfMulNatCastEqOfNotMemPrime
section
open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory

theorem pow_dvd_of_mul_natCast_eq_of_notMem_prime {R : Type} [CommRing R] [IsDomain R] [CharZero R] (I : Ideal R)
    (hI : I.IsPrime) {q : ℕ} (hq : q.Prime) (hqI : (q : R) ∈ I) {s : R} (hs : s ∉ I) :
    ∀ (d i : ℕ) (r : R), s * (i : R) = (q : R) ^ d * r → q ^ d ∣ i := by
  intro d
  induction d with
  | zero => intro i r _; simp
  | succ d ih =>
    intro i r h
    have hiI : (i : R) ∈ I := by
      have : s * (i : R) ∈ I := by
        rw [h, pow_succ', mul_assoc]
        exact I.mul_mem_right _ hqI
      exact (hI.mem_or_mem this).resolve_left hs
    have hdvd : q ∣ i := by
      by_contra hn
      have hc : IsCoprime (q : R) (i : R) := by
        have := (Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hq).2 hn)).map (Int.castRingHom R)
        simpa using this
      obtain ⟨a, b, hab⟩ := hc
      exact hI.one_notMem (hab ▸ I.add_mem (I.mul_mem_left a hqI) (I.mul_mem_left b hiI))
    obtain ⟨j, rfl⟩ := hdvd
    have hq0 : (q : R) ≠ 0 := by exact_mod_cast hq.ne_zero
    have h' : s * (j : R) = (q : R) ^ d * r := by
      apply mul_left_cancel₀ hq0
      push_cast at h
      linear_combination h
    rw [pow_succ']
    exact Nat.mul_dvd_mul_left q (ih j r h')

theorem sum_valsQ_eq_of_support_intAt : ∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)), (qOf P).Prime → ∀ (K : Type) [Field K] (f : E → K) (A₀ : ℕ), (∀ a, f a ≠ 0 → IntAt P ((qOf P : E) ^ A₀ * a)) → ∀ A B : ℕ, A₀ ≤ A → ∑ a ∈ LocE.valsQ E (qOf P) A B, f a = ∑ a ∈ LocE.valsQ E (qOf P) A₀ B, f a := by
  intro E _ _ P hq K _ f A₀ hf A B hA
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hA
  have hqP : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem _
  generalize qOf P = q at *
  have hq0 : (q : E) ≠ 0 := by exact_mod_cast hq.ne_zero
  have hpos : 0 < q ^ d := pow_pos hq.pos d
  symm
  apply Finset.sum_subset
  · intro a ha
    simp only [LocE.valsQ, Finset.mem_image, Finset.mem_range] at ha ⊢
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨q ^ d * i, ?_, ?_⟩
    · have : q ^ (A₀ + d + B) = q ^ d * q ^ (A₀ + B) := by ring
      rw [this]
      exact Nat.mul_lt_mul_of_pos_left hi hpos
    · push_cast
      field_simp
      ring
  · intro a ha hna
    by_contra hfa
    apply hna
    simp only [LocE.valsQ, Finset.mem_image, Finset.mem_range] at ha ⊢
    obtain ⟨i, hi, rfl⟩ := ha
    obtain ⟨r, s, hs, hrs⟩ := hf _ hfa
    have h1 : s * (i : 𝓞 E) = (q : 𝓞 E) ^ d * r := by
      apply FaithfulSMul.algebraMap_injective (𝓞 E) E
      simp only [map_mul, map_pow, map_natCast]
      rw [← hrs]
      field_simp
      ring
    obtain ⟨j, rfl⟩ := pow_dvd_of_mul_natCast_eq_of_notMem_prime P.asIdeal P.isPrime hq hqP hs d i r h1
    refine ⟨j, ?_, ?_⟩
    · have : q ^ (A₀ + d + B) = q ^ d * q ^ (A₀ + B) := by ring
      rw [this] at hi
      exact Nat.lt_of_mul_lt_mul_left hi
    · push_cast
      field_simp
      ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RowPolarizationMemOfIsGLSchemeSubmoduleStatement
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowPolarization_mem_of_isGLSchemeSubmodule : ∀ (k : Type) [Field k] (N : ℕ) (lam : DomWeight N) (M : Submodule k (MvPolynomial (Fin N × Fin N) k)), GlobalTheory.Published.IsGLSubmodule k N lam M → ∀ a b : Fin N, a ≠ b → ∀ f ∈ M, rowE k N N a b f ∈ M := by
  first | exact @GlobalTheory.Alc.rowE_mem_of_isGLSubmodule | exact GlobalTheory.Alc.rowE_mem_of_isGLSubmodule | (intros; apply GlobalTheory.Alc.rowE_mem_of_isGLSubmodule <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SumValsQOfInvariant
section
open NumberField IsDedekindDomain Formalism.L2.Col

namespace GlobalTheory

theorem sum_range_mul_of_periodic {K : Type} [Field K] (g : ℕ → K) (N : ℕ)
    (hg : ∀ i, g (N + i) = g i) (k : ℕ) :
    ∑ i ∈ Finset.range (N * k), g i = (k : K) * ∑ i ∈ Finset.range N, g i := by
  first
  | exact @_root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic
  | exact _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic
  | (apply _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic <;> assumption)
  | (intros; apply _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PeriodicSumShift.sum_range_mul_of_periodic ..)

theorem sum_valsQ_of_invariant (E : Type) [Field E] [NumberField E]
    (P : HeightOneSpectrum (𝓞 E)) (K : Type) [Field K] (f : E → K) (B₀ : ℕ)
    (hf : ∀ a u, IntAt P u → f (a + (qOf P : E) ^ B₀ * u) = f a) (A B : ℕ) (hB : B₀ ≤ B) :
    ∑ a ∈ LocE.valsQ E (qOf P) A B, f a
      = (qOf P : K) ^ (B - B₀) * ∑ a ∈ LocE.valsQ E (qOf P) A B₀, f a := by
  classical
  have hq : (qOf P : E) ≠ 0 := by
    have : qOf P ≠ 0 := by
      unfold qOf
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact P.ne_bot
    exact_mod_cast this
  have key : ∀ C : ℕ, ∑ a ∈ LocE.valsQ E (qOf P) A C, f a
      = ∑ i ∈ Finset.range (qOf P ^ (A + C)), f ((i : E) / (qOf P : E) ^ A) := by
    intro C
    unfold LocE.valsQ
    rw [Finset.sum_image]
    intro i _ j _ hij
    have := (div_left_inj' (pow_ne_zero A hq)).1 hij
    exact_mod_cast this
  rw [key, key]
  have e : qOf P ^ (A + B) = qOf P ^ (A + B₀) * qOf P ^ (B - B₀) := by
    rw [← pow_add]; congr 1; omega
  rw [e, sum_range_mul_of_periodic (fun i : ℕ => f ((i : E) / (qOf P : E) ^ A))]
  · push_cast; rfl
  · intro i
    have h1 : IntAt P (1 : E) := by simpa using IntAt.coe P 1
    have := hf ((i : E) / (qOf P : E) ^ A) 1 h1
    rw [← this]
    congr 1
    push_cast
    field_simp
    ring

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TraceGlMatrixUnitPowHighestWeightMod
section
open MvPolynomial Formalism.GradedWeylDivisibility Formalism.BasicNotions GlobalTheory.Alc

noncomputable section

namespace GlobalTheory.Alc

def hwRowSum (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) (i : Fin N) : R :=
  ∑ l, (hcMat R μ ^ k) i l

theorem hwRowSum_zero (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (i : Fin N) :
    hwRowSum R μ 0 i = 1 := by
  simp [hwRowSum, Matrix.one_apply]

theorem hwRowSum_succ_eq_mul (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) (i : Fin N) :
    hwRowSum R μ (k + 1) i = ∑ m, hcMat R μ i m * hwRowSum R μ k m := by
  simp only [hwRowSum, pow_succ', Matrix.mul_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem hwRowSum_succ (R : Type) [CommRing R] {N : ℕ} (μ : Fin N → R) (k : ℕ) (i : Fin N) :
    hwRowSum R μ (k + 1) i =
      ∑ l, (if l < i then 0 else if l = i then μ i * hwRowSum R μ k i
        else hwRowSum R μ k i - hwRowSum R μ k l) := by
  rw [hwRowSum_succ_eq_mul]
  set r := hwRowSum R μ k with hr
  have h1 : ∀ l, hcMat R μ i l * r l =
      (if l = i then μ i * r i else 0) + (if l = i then ((N - 1 - i.val : ℕ) : R) * r i else 0)
        - (if i < l then r l else 0) := by
    intro l
    by_cases hl : l = i
    · subst hl
      simp [hcMat, shift, add_mul]
    · by_cases hil : i < l
      · simp [hcMat, hl, hil]
      · simp [hcMat, hl, hil]
  have h2 : ∀ l, (if l < i then 0 else if l = i then μ i * r i else r i - r l) =
      (if l = i then μ i * r i else 0) + (if i < l then r i else 0)
        - (if i < l then r l else 0) := by
    intro l
    rcases lt_trichotomy l i with h | h | h
    · simp [h, h.ne, h.not_gt]
    · subst h
      simp
    · simp [h, h.ne', h.not_gt]
  simp only [h1, h2, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  congr 2
  have h3 : ∑ l : Fin N, (if i < l then r i else 0) = ((N - 1 - i.val : ℕ) : R) * r i := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    congr 2
    have : Finset.univ.filter (fun l : Fin N => i < l) = Finset.Ioi i := by
      ext l
      simp
    rw [this, Fin.card_Ioi]
  rw [h3]
  simp

theorem pow_entry_stable {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {N : ℕ}
    (E : Matrix (Fin N) (Fin N) (Module.End R V)) (M : Submodule R V)
    (hM : ∀ a b, ∀ f ∈ M, E a b f ∈ M) (k : ℕ) :
    ∀ a b, ∀ f ∈ M, (E ^ k) a b f ∈ M := by
  induction k with
  | zero =>
    intro a b f hf
    by_cases h : a = b
    · subst h
      simpa [Matrix.one_apply] using hf
    · simp [Matrix.one_apply, h]
  | succ k ih =>
    intro a b f hf
    rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply]
    exact Submodule.sum_mem _ fun l _ => hM a l _ (ih l b f hf)

theorem hw_pow_entries {R V : Type} [CommRing R] [AddCommGroup V] [Module R V] {N : ℕ}
    (E : Matrix (Fin N) (Fin N) (Module.End R V)) (hE : GlRel E) (M : Submodule R V)
    (hM : ∀ a b, ∀ f ∈ M, E a b f ∈ M) (μ : Fin N → R) (v : V)
    (hup : ∀ a b, a < b → E a b v ∈ M) (hd : ∀ a, E a a v - μ a • v ∈ M) (k : ℕ) :
    (∀ i j, i < j → (E ^ k) i j v ∈ M) ∧ (∀ i, (E ^ k) i i v - hwRowSum R μ k i • v ∈ M) := by
  induction k with
  | zero =>
    constructor
    · intro i j hij
      simp [Matrix.one_apply, hij.ne]
    · intro i
      simp [hwRowSum_zero, Matrix.one_apply]
  | succ k ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hcomm := (GlobalTheory.T.glMatrixUnit_pow_commutator_and_trace_central (Module.End R V) N E hE k).1
    have hst := pow_entry_stable E M hM k
    have key : ∀ i j l, i < l →
        E i l ((E ^ k) l j v) - ((E ^ k) i j v - (if j = i then (E ^ k) l l v else 0)) ∈ M := by
      intro i j l hil
      have h := LinearMap.congr_fun (hcomm i l l j) v
      have h' : E i l ((E ^ k) l j v) - (E ^ k) l j (E i l v) =
          (E ^ k) i j v - (if j = i then (E ^ k) l l v else 0) := by
        by_cases hji : j = i
        · simpa [hji, Module.End.mul_apply] using h
        · simpa [hji, Module.End.mul_apply] using h
      have h2 : (E ^ k) l j (E i l v) ∈ M := hst l j _ (hup i l hil)
      rw [← h']
      simpa using h2
    constructor
    · intro i j hij
      rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply]
      refine Submodule.sum_mem _ fun l _ => ?_
      rw [Module.End.mul_apply]
      rcases lt_trichotomy l j with h | h | h
      · exact hM i l _ (ih1 l j h)
      · subst h
        have h1 := hM i l _ (ih2 l)
        rw [map_sub, map_smul] at h1
        have h2 := M.smul_mem (hwRowSum R μ k l) (hup i l hij)
        simpa using M.add_mem h1 h2
      · have h1 := key i j l (hij.trans h)
        rw [if_neg hij.ne'] at h1
        simpa using M.add_mem h1 (ih1 i j hij)
    · intro i
      rw [pow_succ', Matrix.mul_apply, LinearMap.sum_apply, hwRowSum_succ, Finset.sum_smul,
        ← Finset.sum_sub_distrib]
      refine Submodule.sum_mem _ fun l _ => ?_
      rw [Module.End.mul_apply]
      rcases lt_trichotomy l i with h | h | h
      · simpa [h] using hM i l _ (ih1 l i h)
      · subst h
        have h1 := hM l l _ (ih2 l)
        rw [map_sub, map_smul] at h1
        have h2 := M.smul_mem (hwRowSum R μ k l) (hd l)
        have h3 := M.add_mem h1 h2
        have e : E l l ((E ^ k) l l v) - hwRowSum R μ k l • E l l v +
            hwRowSum R μ k l • (E l l v - μ l • v) =
            E l l ((E ^ k) l l v) - (μ l * hwRowSum R μ k l) • v := by
          rw [smul_sub, smul_smul, mul_comm (hwRowSum R μ k l)]
          abel
        rw [e] at h3
        simpa using h3
      · have h1 := key i i l h
        rw [if_pos rfl] at h1
        have h3 := M.sub_mem (M.add_mem h1 (ih2 i)) (ih2 l)
        have e : E i l ((E ^ k) l i v) - ((E ^ k) i i v - (E ^ k) l l v) +
            ((E ^ k) i i v - hwRowSum R μ k i • v) - ((E ^ k) l l v - hwRowSum R μ k l • v) =
            E i l ((E ^ k) l i v) - (hwRowSum R μ k i - hwRowSum R μ k l) • v := by
          rw [sub_smul]
          abel
        rw [e] at h3
        simpa [h.not_gt, h.ne'] using h3

theorem trace_pow_hw : ∀ (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] (N : ℕ)
    (E : Matrix (Fin N) (Fin N) (Module.End R V)), GlRel E → ∀ (M : Submodule R V),
    (∀ a b, ∀ f ∈ M, E a b f ∈ M) → ∀ (μ : Fin N → R) (v : V), (∀ a b, a < b → E a b v ∈ M) →
    (∀ a, E a a v - μ a • v ∈ M) → ∀ k : ℕ, (E ^ k).trace v - hcVal R μ k • v ∈ M := by
  intro R V _ _ _ N E hE M hM μ v hup hd k
  have h := (hw_pow_entries E hE M hM μ v hup hd k).2
  have e : (E ^ k).trace v - hcVal R μ k • v = ∑ i, ((E ^ k) i i v - hwRowSum R μ k i • v) := by
    simp only [Matrix.trace, Matrix.diag, LinearMap.sum_apply, hcVal, Finset.sum_sub_distrib,
      Finset.sum_smul, hwRowSum]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => h i

end GlobalTheory.Alc
end
end

