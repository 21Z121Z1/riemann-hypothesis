import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0449
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0450
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0439
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.PeriodValuationTheory
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.WeightedSumBounds.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0274
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ValuationCoeEqNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0393

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsQuaternionNormOneReEq
section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology

namespace GlobalTheory.QSA.IntRep

open NumberField IsDedekindDomain in
open scoped Quaternion Topology in
private lemma coe_adicCompletionIntegers_inv {F : Type} [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) {x y : v.adicCompletionIntegers F} (h : x * y = 1) :
    (y : v.adicCompletion F) = (x : v.adicCompletion F)⁻¹ := by
  refine (eq_inv_of_mul_eq_one_right ?_)
  exact_mod_cast h

open IsDedekindDomain NumberField IsLocalRing in
open Polynomial in
private lemma exists_root_monic_quadratic_henselian {R : Type*} [CommRing R] [IsLocalRing R]
    [HenselianRing R (IsLocalRing.maximalIdeal R)] (p q a₀ : R)
    (h : a₀ ^ 2 + p * a₀ + q ∈ IsLocalRing.maximalIdeal R) (hu : IsUnit (2 * a₀ + p)) :
    ∃ a : R, a ^ 2 + p * a + q = 0 ∧ a - a₀ ∈ IsLocalRing.maximalIdeal R := by
  obtain ⟨a, ha, haa⟩ := HenselianRing.is_henselian (X ^ 2 + (C p * X + C q))
    (monic_X_pow_add degree_linear_lt) a₀
    (by simpa only [eval_add, eval_pow, eval_X, eval_mul, eval_C, add_assoc] using h)
    (by
      have : eval a₀ (derivative (X ^ 2 + (C p * X + C q))) = 2 * a₀ + p := by
        simp [derivative_X_pow]; ring
      rw [this]; exact hu.map _)
  exact ⟨a, by simpa only [IsRoot, eval_add, eval_pow, eval_X, eval_mul, eval_C, add_assoc] using ha,
    haa⟩

open IsDedekindDomain NumberField IsLocalRing in
open Polynomial in
private lemma exists_binary_form_eq_unit {O : Type*} [CommRing O] [IsLocalRing O]
    [HenselianRing O (maximalIdeal O)] [Finite (ResidueField O)] (t n u : O)
    (hD : IsUnit (t ^ 2 - 4 * n)) (hu : IsUnit u) :
    ∃ r s : O, r ^ 2 + t * r * s + n * s ^ 2 = u := by
  have hu' := (residue_ne_zero_iff_isUnit u).2 hu
  by_cases h2 : IsUnit (2 : O)
  · have h2k : (2 : ResidueField O) ≠ 0 := by
      have := (residue_ne_zero_iff_isUnit (2 : O)).2 h2
      rwa [map_ofNat] at this
    set i : O := ↑h2.unit⁻¹ with hi_def
    have hi : 2 * i = 1 := h2.mul_val_inv
    set e : O := (t ^ 2 - 4 * n) * i ^ 2 with he_def
    have he : IsUnit e := hD.mul ((h2.unit⁻¹).isUnit.pow 2)
    have hek := (residue_ne_zero_iff_isUnit e).2 he
    haveI := Fintype.ofFinite (ResidueField O)
    have hchar : ringChar (ResidueField O) ≠ 2 := by
      intro h
      haveI := ringChar.eq_iff.mp h
      exact h2k (by simpa using CharP.cast_eq_zero (ResidueField O) 2)
    obtain ⟨α, σ, hασ⟩ := FiniteField.exists_root_sum_quadratic
      (f := X ^ 2 - C (residue O u)) (g := C (-(residue O e)) * X ^ 2)
      (degree_X_pow_sub_C (by norm_num) _) (degree_C_mul_X_pow 2 (neg_ne_zero.2 hek))
      (FiniteField.odd_card_of_char_ne_two hchar)
    obtain ⟨x₀, rfl⟩ := residue_surjective α
    obtain ⟨s₀, rfl⟩ := residue_surjective σ
    simp only [eval_sub, eval_pow, eval_X, eval_C, eval_mul] at hασ
    have hm : x₀ ^ 2 - e * s₀ ^ 2 - u ∈ maximalIdeal O := by
      rw [← residue_eq_zero_iff]
      simp only [map_sub, map_mul, map_pow]
      linear_combination hασ
    have key : ∃ X s : O, X ^ 2 - e * s ^ 2 = u := by
      by_cases hx : IsUnit x₀
      · obtain ⟨X, hX, -⟩ := exists_root_monic_quadratic_henselian 0 (-(e * s₀ ^ 2 + u)) x₀
          (by convert hm using 1; ring) (by simpa using h2.mul hx)
        exact ⟨X, s₀, by linear_combination hX⟩
      · have hs : IsUnit s₀ := by
          by_contra hs
          rw [← residue_ne_zero_iff_isUnit, not_not] at hx hs
          apply hu'
          rw [hx, hs] at hασ
          linear_combination -hασ
        set E : O := ↑he.unit⁻¹ with hE_def
        have hE : e * E = 1 := he.mul_val_inv
        obtain ⟨s, hs', -⟩ := exists_root_monic_quadratic_henselian 0 (-(x₀ ^ 2 - u) * E) s₀
          (by
            have : s₀ ^ 2 + 0 * s₀ + -(x₀ ^ 2 - u) * E = -E * (x₀ ^ 2 - e * s₀ ^ 2 - u) := by
              linear_combination (-s₀ ^ 2) * hE
            rw [this]; exact Ideal.mul_mem_left _ _ hm)
          (by simpa using h2.mul hs)
        exact ⟨x₀, s, by linear_combination (-e) * hs' - (x₀ ^ 2 - u) * hE⟩
    obtain ⟨X, s, hXs⟩ := key
    exact ⟨X - t * s * i, s, by
      linear_combination hXs + (t ^ 2 * s ^ 2 * i - n * s ^ 2 * (1 + 2 * i) - t * X * s) * hi⟩
  · have h2k : (2 : ResidueField O) = 0 := by
      by_contra h
      exact h2 ((residue_ne_zero_iff_isUnit _).1 (by rwa [map_ofNat]))
    have h4 : (4 : ResidueField O) = 0 := by
      rw [show (4 : ResidueField O) = 2 * 2 by norm_num, h2k, zero_mul]
    have ht : IsUnit t := by
      rw [← residue_ne_zero_iff_isUnit] at hD ⊢
      intro h
      apply hD
      rw [map_sub, map_mul, map_pow, h, map_ofNat, h4]
      ring
    have hchar : ringChar (ResidueField O) = 2 :=
      CharP.ringChar_of_prime_eq_zero Nat.prime_two (by simpa using h2k)
    obtain ⟨ρ, hρ⟩ := FiniteField.isSquare_of_char_two hchar (residue O u)
    obtain ⟨r₀, rfl⟩ := residue_surjective ρ
    have hr₀ : IsUnit r₀ := by
      rw [← residue_ne_zero_iff_isUnit]
      rintro h
      rw [h, mul_zero] at hρ
      exact hu' hρ
    set c : O := r₀ ^ 2 - u with hc_def
    have hc : c ∈ maximalIdeal O := by
      rw [← residue_eq_zero_iff, hc_def, map_sub, map_pow, hρ]
      ring
    have hb : IsUnit (t * r₀) := ht.mul hr₀
    set β : O := ↑hb.unit⁻¹ with hβ_def
    have hβ : t * r₀ * β = 1 := hb.mul_val_inv
    obtain ⟨w, hw, hw1⟩ := exists_root_monic_quadratic_henselian (-1) (n * β ^ 2 * c) 1
      (by
        have : (1 : O) ^ 2 + -1 * 1 + n * β ^ 2 * c = (n * β ^ 2) * c := by ring
        rw [this]; exact Ideal.mul_mem_left _ _ hc)
      (by norm_num)
    have hwu : IsUnit w := by
      rw [← residue_ne_zero_iff_isUnit]
      have := (residue_eq_zero_iff _).2 hw1
      rw [map_sub, map_one, sub_eq_zero] at this
      rw [this]; exact one_ne_zero
    set ω : O := ↑hwu.unit⁻¹ with hω_def
    have hω : w * ω = 1 := hwu.mul_val_inv
    exact ⟨r₀, -c * β * ω, by
      linear_combination (-c * ω) * hβ + (c * ω ^ 2) * hw + (-c * (w * ω + 1) + c * ω) * hω⟩

open NumberField IsDedekindDomain in
open scoped Quaternion Topology in

theorem _root_.GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 →
    ∀ᶠ v in (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 F))), ∀ t ∈ v.adicCompletionIntegers F,
      ∃ u : ℍ[v.adicCompletion F, algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) b],
        _root_.GlobalTheory.QSA.nrm u = 1 ∧ u.re = t ∧ u.imI ∈ v.adicCompletionIntegers F ∧ u.imJ ∈ v.adicCompletionIntegers F ∧
          u.imK ∈ v.adicCompletionIntegers F := by
  intro F _ _ a b ha hb
  obtain ⟨α, d, hd, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) a
  obtain ⟨β, e, he, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 F) b
  have hα : α ≠ 0 := by rintro rfl; simp at ha
  have hβ : β ≠ 0 := by rintro rfl; simp at hb
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have he0 : e ≠ 0 := nonZeroDivisors.ne_zero he
  have hx0 : α * d * β * e * 2 ≠ 0 := by
    have : (2 : 𝓞 F) ≠ 0 := two_ne_zero
    positivity
  refine Filter.eventually_cofinite.2 ((Ideal.finite_factors (I := Ideal.span {α * d * β * e * 2})
    (by simpa using hx0)).subset fun v hv => ?_)
  rw [Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  by_contra hx
  apply hv
  haveI := _root_.GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers v
  haveI := _root_.GlobalTheory.SelfDualGenus.finite_residueField_adicCompletionIntegers v
  have hunit := (_root_.GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff v _).2 hx
  simp only [map_mul, IsUnit.mul_iff] at hunit
  obtain ⟨⟨⟨⟨hA, hD⟩, hB⟩, hE⟩, h2⟩ := hunit
  rw [map_ofNat] at h2
  set a' : v.adicCompletionIntegers F :=
    algebraMap (𝓞 F) (v.adicCompletionIntegers F) α * ↑hD.unit⁻¹ with ha'_def
  set b' : v.adicCompletionIntegers F :=
    algebraMap (𝓞 F) (v.adicCompletionIntegers F) β * ↑hE.unit⁻¹ with hb'_def
  have ha'K : (a' : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F α / algebraMap (𝓞 F) F d) := by
    rw [map_div₀, ha'_def, MulMemClass.coe_mul,
      coe_adicCompletionIntegers_inv v hD.mul_val_inv]
    rfl
  have hb'K : (b' : v.adicCompletion F) =
      algebraMap F (v.adicCompletion F) (algebraMap (𝓞 F) F β / algebraMap (𝓞 F) F e) := by
    rw [map_div₀, hb'_def, MulMemClass.coe_mul,
      coe_adicCompletionIntegers_inv v hE.mul_val_inv]
    rfl
  have ha'u : IsUnit a' := hA.mul (hD.unit⁻¹).isUnit
  have hb'u : IsUnit b' := hB.mul (hE.unit⁻¹).isUnit
  set ai : v.adicCompletionIntegers F := ↑ha'u.unit⁻¹ with hai_def
  have hai : a' * ai = 1 := ha'u.mul_val_inv
  intro t ht
  set T : v.adicCompletionIntegers F := ⟨t, ht⟩ with hT
  obtain ⟨z, hz⟩ : ∃ z : v.adicCompletionIntegers F, IsUnit (T ^ 2 - 1 + a' * b' * z ^ 2) := by
    by_cases hc : IsUnit (T ^ 2 - 1)
    · exact ⟨0, by simpa using hc⟩
    · refine ⟨1, ?_⟩
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, not_not] at hc
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_add, hc, zero_add, one_pow, mul_one]
      exact (IsLocalRing.residue_ne_zero_iff_isUnit _).2 (ha'u.mul hb'u)
  obtain ⟨r, s, hrs⟩ := exists_binary_form_eq_unit 0 (b' * ai) ((T ^ 2 - 1 + a' * b' * z ^ 2) * ai)
    (by
      rw [show (0 : v.adicCompletionIntegers F) ^ 2 - 4 * (b' * ai) = -(2 * 2 * (b' * ai)) by ring]
      exact ((h2.mul h2).mul (hb'u.mul (ha'u.unit⁻¹).isUnit)).neg)
    (hz.mul (ha'u.unit⁻¹).isUnit)
  have hO : T ^ 2 - a' * r ^ 2 - b' * s ^ 2 + a' * b' * z ^ 2 = 1 := by
    linear_combination (-a') * hrs + (b' * s ^ 2 - (T ^ 2 - 1) - a' * b' * z ^ 2) * hai
  refine ⟨⟨t, r, s, z⟩, ?_, rfl, r.2, s.2, z.2⟩
  unfold _root_.GlobalTheory.QSA.nrm
  rw [← ha'K, ← hb'K]
  have := congrArg (fun x : v.adicCompletionIntegers F => (x : v.adicCompletion F)) hO
  push_cast at this
  exact this

end GlobalTheory.QSA.IntRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAdeleSqSubMulSqStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteAdele_sq_sub_mul_sq_eq_of_local : ∀ (K : Type) [Field K] [NumberField K] (δ a : K), δ ≠ 0 → a ≠ 0 → (∀ v : HeightOneSpectrum (𝓞 K), ∃ x y : v.adicCompletion K, x ^ 2 - algebraMap K (v.adicCompletion K) δ * y ^ 2 = algebraMap K (v.adicCompletion K) a) → ∃ x y : FiniteAdeleRing (𝓞 K) K, x ^ 2 - algebraMap K (FiniteAdeleRing (𝓞 K) K) δ * y ^ 2 = algebraMap K (FiniteAdeleRing (𝓞 K) K) a := by
  first | (exact @GlobalTheory.AdelicQuadSol.exists_finiteAdele_sq_sub_mul_sq) | (exact GlobalTheory.AdelicQuadSol.exists_finiteAdele_sq_sub_mul_sq) | (intros; apply GlobalTheory.AdelicQuadSol.exists_finiteAdele_sq_sub_mul_sq  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFormOfCompatibleFractionsStatement
section
open MvPolynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneous_form_of_compatible_fractions : ∀ (A : Type) [CommRing A] [IsNoetherianRing A] (n : ℕ) (J : Ideal (MvPolynomial (Fin (n + 1)) A)), (∀ F ∈ J, ∀ d, homogeneousComponent d F ∈ J) → ∃ d₀ : ℕ, ∀ d, d₀ ≤ d → ∀ (N : ℕ) (F : Fin (n + 1) → MvPolynomial (Fin (n + 1)) A), (∀ i, (F i).IsHomogeneous (d + N)) → (∀ i j, ∃ L : ℕ, ((X i : MvPolynomial (Fin (n + 1)) A) * X j) ^ L * (X j ^ N * F i - X i ^ N * F j) ∈ J) → ∃ G : MvPolynomial (Fin (n + 1)) A, G.IsHomogeneous d ∧ ∀ i, ∃ L : ℕ, (X i : MvPolynomial (Fin (n + 1)) A) ^ L * (F i - X i ^ N * G) ∈ J := by
  first | exact @GlobalTheory.exists_form_of_compatible_fractions | exact GlobalTheory.exists_form_of_compatible_fractions | (intros; apply GlobalTheory.exists_form_of_compatible_fractions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueFunctionsAffineOpenFromPairsStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR Opposite KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_functions_affineOpen_from_pairs : ∀ {R' : Type} [CommRing R'] {X X' : Scheme.{0}} (φ : X' ⟶ X) (s' : X' ⟶ Sp R') (W : X'.affineOpens) (k : ∀ p : Pair φ, p.1.1 ≤ W → (OAff s').obj (op p.1.1)), (∀ (p q : Pair φ) (hp : p.1.1 ≤ W) (hq : q.1.1 ≤ W) (hqp : q ≤ p), mp (OAff s') (homOfLE (Pair.le_fst hqp)).op (k p hp) = k q hq) → ∃ G : (OAff s').obj (op W), ∀ (p : Pair φ) (hp : p.1.1 ≤ W), mp (OAff s') (homOfLE hp).op G = k p hp := by
  first | exact @GlobalTheory.CechDR.pair_glue | exact GlobalTheory.CechDR.pair_glue | (intros; apply GlobalTheory.CechDR.pair_glue <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlueFunctionsSpecFromPairsStatement
section
open CategoryTheory AlgebraicGeometry Opposite ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CechDR.AffLoc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_glue_functions_spec_from_pairs : ∀ {X : Scheme.{0}} (B : Type) [CommRing B] (x : Sp B ⟶ X) (h : ∀ p : Pair x, Γ(Sp B, p.1.1.1)), (∀ p q : Pair x, ∀ hpq : p ≤ q, ((Sp B).presheaf.map (homOfLE (Pair.le_fst hpq)).op).hom (h q) = h p) → ∃ G : B, ∀ p : Pair x, (secMap (𝟙 (Sp B)) p.1.1.1).hom G = h p := by
  first | exact @GlobalTheory.CechDR.AffLoc.exists_glue_pair | exact GlobalTheory.CechDR.AffLoc.exists_glue_pair | (intros; apply GlobalTheory.CechDR.AffLoc.exists_glue_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralInvariantDerivationLogStatement
section
open MvPowerSeries ReciprocityTheory.PGsh ReciprocityTheory.ChartRestriction.G.Sh GlobalTheory.FGDepth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_invariant_derivation_log : ∀ (C : Type) [Field C] [CharZero C] (v : AddValuation C (WithTop ℝ)) (d : ℕ) (G : LogFGL v d), ∃ D : Fin d → Fin d → MvPowerSeries (Fin d) C, (∀ k l, MvIsInt v (D k l)) ∧ ∀ (f : MvPowerSeries (Fin d) C) (k : Fin d) (α : Fin d →₀ ℕ), ((α k : C) + 1) * coeff (α + Finsupp.single k 1) (subst (expOf G) f) = coeff α (subst (expOf G) (∑ l, D k l * (show MvPowerSeries (Fin d) C from fun β => ((β l : C) + 1) * coeff (β + Finsupp.single l 1) f))) := by
  first | exact @GlobalTheory.LogJacobian.exists_integral_invariant_derivation | exact GlobalTheory.LogJacobian.exists_integral_invariant_derivation | (intros; apply GlobalTheory.LogJacobian.exists_integral_invariant_derivation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsomComp
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.EmbConj

open GlobalTheory.PadicComplexHost

noncomputable def stdInt (p : ℕ) [Fact p.Prime] : ℤ_[p] →+* 𝓞_ℂ_[p] :=
  ((algebraMap (PadicAlgCl p) ℂ_[p]).comp (algebraMap ℤ_[p] (PadicAlgCl p))).codRestrict
    (𝓞_ℂ_[p]).toSubring (fun x => by
      change _ ∈ 𝓞_ℂ_[p]
      rw [mem_iff_norm, RingHom.comp_apply, ← PadicComplex.coe_eq, PadicComplex.norm_extends,
        IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p), norm_algebraMap']
      exact x.norm_le_one)

theorem coe_stdInt (p : ℕ) [Fact p.Prime] (a : ℤ_[p]) :
    ((stdInt p a : 𝓞_ℂ_[p]) : ℂ_[p]) =
      algebraMap (PadicAlgCl p) ℂ_[p] (algebraMap ℤ_[p] (PadicAlgCl p) a) :=
  rfl

variable {p : ℕ} [Fact p.Prime]

theorem apply_algebraMap {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] (t : Λ →+* 𝓞_ℂ_[p])
    (a : ℤ_[p]) : ((t (algebraMap ℤ_[p] Λ a) : 𝓞_ℂ_[p]) : ℂ_[p]) =
      algebraMap (PadicAlgCl p) ℂ_[p] (algebraMap ℤ_[p] (PadicAlgCl p) a) := by
  haveI := isHausdorff p
  have h := GlobalTheory.padicInt_ringHom_ext p 𝓞_ℂ_[p] (t.comp (algebraMap ℤ_[p] Λ)) (stdInt p)
  rw [← coe_stdInt, ← h, RingHom.comp_apply]

theorem isAlgebraic_coe {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ]
    (t : Λ →+* 𝓞_ℂ_[p]) (x : Λ) : IsAlgebraic ℚ_[p] ((t x : 𝓞_ℂ_[p]) : ℂ_[p]) := by
  obtain ⟨f, hf, hfx⟩ := Algebra.IsIntegral.isIntegral (R := ℤ_[p]) x
  let g : Λ →+* ℂ_[p] := (𝓞_ℂ_[p]).subtype.comp t
  have hstd : g.comp (algebraMap ℤ_[p] Λ) =
      (algebraMap ℚ_[p] ℂ_[p]).comp (algebraMap ℤ_[p] ℚ_[p]) := by
    ext a
    refine (apply_algebraMap t a).trans ?_
    rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p),
      IsScalarTower.algebraMap_apply ℚ_[p] (PadicAlgCl p) ℂ_[p]]
  refine ⟨f.map (algebraMap ℤ_[p] ℚ_[p]), (hf.map _).ne_zero, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, ← hstd]
  change Polynomial.eval₂ (g.comp (algebraMap ℤ_[p] Λ)) (g x) f = 0
  rw [← Polynomial.hom_eval₂, hfx, map_zero]

theorem exists_lift {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ]
    (t : Λ →+* 𝓞_ℂ_[p]) : ∃ φ : Λ →+* PadicAlgCl p,
      (∀ x, algebraMap (PadicAlgCl p) ℂ_[p] (φ x) = ((t x : 𝓞_ℂ_[p]) : ℂ_[p])) ∧
      φ.comp (algebraMap ℤ_[p] Λ) = algebraMap ℤ_[p] (PadicAlgCl p) := by
  have hex : ∀ x : Λ, ∃ y : PadicAlgCl p,
      algebraMap (PadicAlgCl p) ℂ_[p] y = ((t x : 𝓞_ℂ_[p]) : ℂ_[p]) := fun x => by
    have h1 : IsIntegral (PadicAlgCl p) ((t x : 𝓞_ℂ_[p]) : ℂ_[p]) :=
      ((isAlgebraic_coe t x).tower_top (PadicAlgCl p)).isIntegral
    exact minpoly.mem_range_of_degree_eq_one _ _
      (IsAlgClosed.degree_eq_one_of_irreducible _ (minpoly.irreducible h1))
  choose f hf using hex
  have hinj : Function.Injective (algebraMap (PadicAlgCl p) ℂ_[p]) :=
    (algebraMap (PadicAlgCl p) ℂ_[p]).injective
  refine ⟨{ toFun := f, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hf, ?_⟩
  · apply hinj; rw [hf]; simp
  · intro x y; apply hinj; rw [map_mul, hf, hf, hf]; simp
  · apply hinj; rw [hf]; simp
  · intro x y; apply hinj; rw [map_add, hf, hf, hf]; simp
  · ext a
    apply hinj
    exact (hf _).trans (apply_algebraMap t a)

theorem injective_of_comp {Λ : Type} [CommRing Λ] [IsDomain Λ] [Algebra ℤ_[p] Λ]
    [Module.Finite ℤ_[p] Λ] (φ : Λ →+* PadicAlgCl p)
    (h : φ.comp (algebraMap ℤ_[p] Λ) = algebraMap ℤ_[p] (PadicAlgCl p)) :
    Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[p])
  rw [RingHom.comap_ker, h, ← RingHom.injective_iff_ker_eq_bot,
    IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PadicAlgCl p), RingHom.coe_comp]
  exact (algebraMap ℚ_[p] (PadicAlgCl p)).injective.comp (IsFractionRing.injective ℤ_[p] ℚ_[p])

theorem exists_algEquiv {Λ : Type} [CommRing Λ] [IsDomain Λ] [Algebra ℤ_[p] Λ]
    [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (φ₀ φ₁ : Λ →+* PadicAlgCl p)
    (h₀ : φ₀.comp (algebraMap ℤ_[p] Λ) = algebraMap ℤ_[p] (PadicAlgCl p))
    (h₁ : φ₁.comp (algebraMap ℤ_[p] Λ) = algebraMap ℤ_[p] (PadicAlgCl p)) :
    ∃ σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p, ∀ x, σ (φ₀ x) = φ₁ x := by
  have tf : ∀ φ : Λ →+* PadicAlgCl p, Function.Injective φ →
      letI := φ.toAlgebra
      Module.IsTorsionFree Λ (PadicAlgCl p) := fun φ hφ => by
    letI := φ.toAlgebra
    haveI : FaithfulSMul Λ (PadicAlgCl p) := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
    infer_instance
  have alg : letI := φ₀.toAlgebra
      Algebra.IsAlgebraic Λ (PadicAlgCl p) := by
    letI := φ₀.toAlgebra
    haveI : IsScalarTower ℤ_[p] Λ (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq' h₀.symm
    haveI : Algebra.IsAlgebraic ℤ_[p] (PadicAlgCl p) := ⟨fun x =>
      (IsFractionRing.isAlgebraic_iff ℤ_[p] ℚ_[p] (PadicAlgCl p)).2
        (Algebra.IsAlgebraic.isAlgebraic x)⟩
    exact Algebra.IsAlgebraic.extendScalars (R := ℤ_[p]) (FaithfulSMul.algebraMap_injective _ _)
  obtain ⟨g, hg⟩ : ∃ g : PadicAlgCl p →+* PadicAlgCl p, ∀ x, g (φ₀ x) = φ₁ x := by
    let f := @IsAlgClosed.lift (PadicAlgCl p) _ _ Λ _ _ (PadicAlgCl p) _ _ φ₀.toAlgebra
      φ₁.toAlgebra (tf φ₀ (injective_of_comp φ₀ h₀)) (tf φ₁ (injective_of_comp φ₁ h₁)) alg
    exact ⟨@AlgHom.toRingHom _ _ _ _ _ _ φ₀.toAlgebra φ₁.toAlgebra f,
      fun x => @AlgHom.commutes _ _ _ _ _ _ φ₀.toAlgebra φ₁.toAlgebra f x⟩
  have hq : g.comp (algebraMap ℚ_[p] (PadicAlgCl p)) = algebraMap ℚ_[p] (PadicAlgCl p) := by
    apply IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[p])
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq ℤ_[p] ℚ_[p] (PadicAlgCl p)]
    ext a
    exact (congrArg g (RingHom.congr_fun h₀ a).symm).trans
      ((hg _).trans (RingHom.congr_fun h₁ a))
  let g' : PadicAlgCl p →ₐ[ℚ_[p]] PadicAlgCl p := { g with commutes' := RingHom.congr_fun hq }
  exact ⟨AlgEquiv.ofBijective g' (Algebra.IsAlgebraic.algHom_bijective g'), hg⟩

theorem exists_extension (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    ∃ γ : ℂ_[p] ≃+* ℂ_[p], (∀ y : PadicAlgCl p, γ (y : ℂ_[p]) = ((σ y : PadicAlgCl p) : ℂ_[p])) ∧
      ∀ z, ‖γ z‖ = ‖z‖ := by
  have hn : ∀ (g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (x : PadicAlgCl p), ‖g x‖ = ‖x‖ :=
    fun g x => (spectralNorm_eq_of_equiv g x).symm
  have hi : ∀ g : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p,
      Isometry (g : PadicAlgCl p → PadicAlgCl p) :=
    fun g => AddMonoidHomClass.isometry_of_norm g (hn g)
  let γ : ℂ_[p] ≃+* ℂ_[p] := UniformSpace.Completion.mapRingEquiv σ.toRingEquiv
    (hi σ).continuous (hi σ.symm).continuous
  have hc : ∀ y : PadicAlgCl p, γ (y : ℂ_[p]) = ((σ y : PadicAlgCl p) : ℂ_[p]) :=
    fun y => UniformSpace.Completion.map_coe (hi σ).uniformContinuous y
  have hcont : Continuous γ := UniformSpace.Completion.continuous_map
  refine ⟨γ, hc, fun z => ?_⟩
  induction z using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_eq hcont.norm continuous_norm
  | ih x => rw [hc, PadicComplex.norm_extends, PadicComplex.norm_extends, hn]

theorem exists_isIsom_comp : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ]
    [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ] (t₀ t : Λ →+* 𝓞_ℂ_[p]),
    ∃ γ : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p], IsIsom ℂ_[p] (Valued.v : Valuation ℂ_[p] NNReal) γ ∧
      t = (γ : 𝓞_ℂ_[p] →+* 𝓞_ℂ_[p]).comp t₀ := by
  intro p _ Λ _ _ _ _ _ t₀ t
  obtain ⟨φ₀, e₀, h₀⟩ := exists_lift t₀
  obtain ⟨φ₁, e₁, h₁⟩ := exists_lift t
  obtain ⟨σ, hσ⟩ := exists_algEquiv φ₀ φ₁ h₀ h₁
  obtain ⟨γC, hc, hn⟩ := exists_extension σ
  have hn' : ∀ z, ‖γC.symm z‖ = ‖z‖ := fun z => by rw [← hn, γC.apply_symm_apply]
  let γ : 𝓞_ℂ_[p] ≃+* 𝓞_ℂ_[p] :=
    { toFun := fun x => ⟨γC x, (mem_iff_norm p _).2 ((hn _).trans_le ((mem_iff_norm p _).1 x.2))⟩
      invFun := fun x =>
        ⟨γC.symm x, (mem_iff_norm p _).2 ((hn' _).trans_le ((mem_iff_norm p _).1 x.2))⟩
      left_inv := fun x => Subtype.ext (γC.symm_apply_apply _)
      right_inv := fun x => Subtype.ext (γC.apply_symm_apply _)
      map_mul' := fun x y => Subtype.ext (map_mul γC _ _)
      map_add' := fun x y => Subtype.ext (map_add γC _ _) }
  refine ⟨γ, ⟨γC, fun x => rfl, fun z => ?_⟩, ?_⟩
  · apply NNReal.coe_injective
    rw [valuation_coe_eq_norm, valuation_coe_eq_norm, hn]
  · ext x
    change ((t x : 𝓞_ℂ_[p]) : ℂ_[p]) = γC ((t₀ x : 𝓞_ℂ_[p]) : ℂ_[p])
    rw [← e₀, ← e₁, ← PadicComplex.coe_eq, ← PadicComplex.coe_eq, hc, hσ]

end GlobalTheory.EmbConj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftEtaleSheafOfLinearMapsExactStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_etaleSheafOfLinearMaps_exact : ∀ (R : Type) [CommRing R] (J X : Shv R), Module.Injective (ULift.{1} R) (X ⟶ J) → ∀ (A B C : ModuleCat.{1} (ULift.{1} R)) (u : A ⟶ B) (v : B ⟶ C), (∀ b, v.hom b = 0 → ∃ a, u.hom a = b) → ∀ f : X ⟶ (homSh J).obj (op B), f ≫ (homSh J).map u.op = 0 → ∃ g : X ⟶ (homSh J).obj (op C), g ≫ (homSh J).map v.op = f := by
  first | (exact @GlobalTheory.EtC.lift_homSh) | (exact GlobalTheory.EtC.lift_homSh) | (intros; apply GlobalTheory.EtC.lift_homSh  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMaximalHeightSuccDim
section
open scoped TensorProduct

namespace GlobalTheory.FibreMax

attribute [local instance] Algebra.TensorProduct.rightAlgebra in

theorem exists_isMaximal_height_ge (k : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k]
    [CharZero k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [FaithfulSMul k A] (d : ℕ) (hd : ringKrullDim (FractionRing k ⊗[k] A) = d) :
    ∃ M : Ideal A, M.IsMaximal ∧ ((d + 1 : ℕ) : ℕ∞) ≤ M.height := by
  classical
  have hloc := IsLocalization.tensorRight (S := A) (FractionRing k) (nonZeroDivisors k)
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k) ≤ nonZeroDivisors A :=
    Submonoid.map_le_iff_le_comap.mpr fun x hx ↦ mem_nonZeroDivisors_of_ne_zero
      (by simpa using nonZeroDivisors.ne_zero hx)
  have : IsDomain (FractionRing k ⊗[k] A) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hle
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.1 hd.ge
  let f : PrimeSpectrum (FractionRing k ⊗[k] A) → PrimeSpectrum A :=
    PrimeSpectrum.comap (algebraMap A (FractionRing k ⊗[k] A))
  have hf : StrictMono f :=
    Monotone.strictMono_of_injective (fun _ _ h ↦ Ideal.comap_mono h)
      (PrimeSpectrum.localization_comap_injective _ (Algebra.algebraMapSubmonoid A (nonZeroDivisors k)))
  let q := f l.last
  have hq : ∀ c : k, c ≠ 0 → algebraMap k A c ∉ q.asIdeal := by
    intro c hc h
    have hu : IsUnit (algebraMap A (FractionRing k ⊗[k] A) (algebraMap k A c)) :=
      IsLocalization.map_units (FractionRing k ⊗[k] A)
        (⟨algebraMap k A c, c, mem_nonZeroDivisors_of_ne_zero hc, rfl⟩ :
          Algebra.algebraMapSubmonoid A (nonZeroDivisors k))
    exact l.last.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h hu)
  obtain ⟨M, hM, hqM⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
  have hne : q.asIdeal ≠ M := by
    intro heq
    haveI := ReciprocityTheory.AnForm.R.IntegerToRational.isJacobsonRing_int
    haveI : Algebra.FiniteType ℤ k := inferInstance
    haveI : Algebra.FiniteType ℤ A := Algebra.FiniteType.trans (S := k) inferInstance inferInstance
    letI := Ideal.Quotient.field M
    haveI : Module.Finite ℤ (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing ℤ (A ⧸ M)
    have hinj : Function.Injective (algebraMap ℤ (A ⧸ M)) := by
      refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
      have h1 : algebraMap ℤ (A ⧸ M) x = Ideal.Quotient.mk M (algebraMap k A (x : k)) := by simp
      rw [h1, Ideal.Quotient.eq_zero_iff_mem, ← heq] at hx
      by_contra hx0
      exact hq (x : k) (Int.cast_ne_zero.2 hx0) hx
    exact Int.not_isField ((Algebra.IsIntegral.isField_iff_isField hinj).2 (Field.toIsField _))
  let Mp : PrimeSpectrum A := ⟨M, hM.isPrime⟩
  have hlt : (l.map f hf).last < Mp := by
    change q < Mp
    exact lt_of_le_of_ne hqM fun h ↦ hne (congrArg PrimeSpectrum.asIdeal h)
  let L := (l.map f hf).snoc Mp hlt
  have hlen : L.length = d + 1 := by simp [L, hl]
  refine ⟨M, hM, ?_⟩
  rw [show M = Mp.asIdeal from rfl, PrimeSpectrum.height_eq_orderHeight, ← hlen]
  exact Order.length_le_height (by simp [L])

end GlobalTheory.FibreMax
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroForallComplexPointSeparateStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ne_zero_forall_complexPoint_separate' : ∀ (B A F : Type) [CommRing B] [IsDomain B] [IsNoetherianRing B] [CommRing A] [Algebra B A] [Algebra.FiniteType B A] [Field F] (j₁ j₂ : A →+* F), j₁.comp (algebraMap B A) = j₂.comp (algebraMap B A) → Function.Injective (j₁.comp (algebraMap B A)) → ∀ a : A, j₁ a ≠ j₂ a → ∃ q : B, q ≠ 0 ∧ ∀ φ : B →+* ℂ, φ q ≠ 0 → ∃ y₁ y₂ : A →+* ℂ, y₁.comp (algebraMap B A) = φ ∧ y₂.comp (algebraMap B A) = φ ∧ y₁ a ≠ y₂ a := by
  first | exact @GlobalTheory.exists_ne_zero_forall_complexPoint_separate | exact GlobalTheory.exists_ne_zero_forall_complexPoint_separate | (intros; apply GlobalTheory.exists_ne_zero_forall_complexPoint_separate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPeriodCohomologyClassOfRichBasedStatement
section
open CategoryTheory GlobalTheory.CatCoh GlobalTheory.AnPer GlobalTheory.AnPer.Charts TopologicalSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_period_cohomologyClass_of_rich_based : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), K.Rich → K.Based → ∀ c : H1 K.Oc, ∃ per : Λ →+ Hol F.V, c = K.perCl per := by
  first | exact @GlobalTheory.AnPer.Charts.exists_perCl | exact GlobalTheory.AnPer.Charts.exists_perCl | (intros; apply GlobalTheory.AnPer.Charts.exists_perCl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPullbackMulPOfPTorsionInvariantStatement
section
open TensorProduct Coalgebra Bialgebra CategoryTheory WithConv GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pullback_mulP_of_pTorsion_invariant : ∀ {p : ℕ} {R : Type} [CommRing R] (G : PDivGroup p R) (n : ℕ) (F : G.A (n + 1) ⊗[R] G.A (n + 1)), ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).rTensor (G.A (n + 1)) F = 0 → ((G.transl n).toLinearMap - (TensorProduct.mk R (G.A (n + 1)) (G.A 1)).flip 1).lTensor (G.A (n + 1)) F = 0 → ∃ c : G.A n ⊗[R] G.A n, pullbackTwo (G.mulP n) c = F := by
  first | exact @GlobalTheory.PDivGroup.exists_tensorSquare_mulP_eq | exact GlobalTheory.PDivGroup.exists_tensorSquare_mulP_eq | (intros; apply GlobalTheory.PDivGroup.exists_tensorSquare_mulP_eq <;> assumption)
end

