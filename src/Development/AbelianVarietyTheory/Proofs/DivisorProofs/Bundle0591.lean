import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0517
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0579
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0549
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0580
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0575
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0005
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0030
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0022
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0031
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0163
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0581
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCPullbackBijectiveFiniteStrictlyHenselian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeMellinGaussIntegralNonzeroInteger
section
noncomputable section

open NumberField MeasureTheory

namespace GlobalTheory.HeckeMellinOne

theorem hmon_eq_mul (n : ℤ) {z : ℂ} (hz : z ≠ 0) :
    GlobalTheory.HeckeTheta.hmon n z = ((‖z‖ : ℝ) : ℂ) ^ n.natAbs * (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) := by
  have hn : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hz
  have hc : starRingEnd ℂ z * z = ((‖z‖ : ℝ) : ℂ) ^ 2 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  unfold GlobalTheory.HeckeTheta.hmon
  split_ifs with h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp only [Int.toNat_natCast, Int.natAbs_natCast, zpow_neg, zpow_natCast]
    rw [← inv_pow, ← mul_pow]
    congr 1
    field_simp
    linear_combination hc
  · obtain ⟨m, hm⟩ : ∃ m : ℕ, -n = m := ⟨(-n).toNat, by omega⟩
    have hm' : n.natAbs = m := by omega
    rw [hm, hm', Int.toNat_natCast, zpow_natCast, ← mul_pow]
    congr 1
    field_simp

theorem ofReal_prod_cpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℂ) :
    (((∏ j ∈ t, f j : ℝ)) : ℂ) ^ w = ∏ j ∈ t, ((f j : ℝ) : ℂ) ^ w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Complex.ofReal_mul,
      Complex.mul_cpow_ofReal_nonneg (hf a) (Finset.prod_nonneg fun j _ => hf j), ih]

theorem real_factor (r σ a G : ℝ) (k : ℕ) (hr : 0 < r) (hk : (k : ℝ) = a) :
    r ^ k * G * (2 * Real.pi * r ^ 2) ^ (-(σ + a / 2)) =
      (2 * Real.pi) ^ (-(σ + a / 2)) * G * (r ^ 2) ^ (-σ) := by
  subst hk
  have h2π : 0 < 2 * Real.pi := by positivity
  rw [Real.rpow_def_of_pos (by positivity), Real.rpow_def_of_pos h2π, Real.rpow_def_of_pos (by positivity),
    Real.log_mul h2π.ne' (by positivity), Real.log_pow, ← Real.exp_log (pow_pos hr k), Real.log_pow]
  have key : Real.exp (k * Real.log r) * Real.exp ((Real.log (2 * Real.pi) + (2 : ℕ) * Real.log r) * -(σ + k / 2)) =
      Real.exp (Real.log (2 * Real.pi) * -(σ + k / 2)) * Real.exp ((2 : ℕ) * Real.log r * -σ) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; push_cast; ring
  linear_combination G * key

theorem complex_factor (z : ℂ) (hz : z ≠ 0) (n : ℤ) (s G : ℂ) :
    2 * (GlobalTheory.HeckeTheta.hmon n z * G *
      ((2 * Real.pi * ‖z‖ ^ 2 : ℝ) : ℂ) ^ (-(s + ((|n| : ℤ) : ℂ) / 2))) =
      2 * (2 * (Real.pi : ℂ)) ^ (-(s + ((|n| : ℤ) : ℂ) / 2)) * G *
        ((z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) * ((‖z‖ ^ 2 : ℝ) : ℂ) ^ (-s)) := by
  have hr : 0 < ‖z‖ := norm_pos_iff.2 hz
  have h2π : 0 < 2 * Real.pi := by positivity
  have e2 : (2 * (Real.pi : ℂ)) = ((2 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  have hk : ((n.natAbs : ℕ) : ℂ) = ((|n| : ℤ) : ℂ) := by
    rw [← Int.cast_natCast, Int.natCast_natAbs]
  rw [hmon_eq_mul n hz, e2, ← Complex.cpow_natCast,
    Complex.cpow_def_of_ne_zero (by exact_mod_cast hr.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (by positivity : (0:ℝ) < 2 * Real.pi * ‖z‖ ^ 2).ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast h2π.ne'),
    Complex.cpow_def_of_ne_zero (by exact_mod_cast (by positivity : (0:ℝ) < ‖z‖ ^ 2).ne'),
    ← Complex.ofReal_log hr.le, ← Complex.ofReal_log (by positivity), ← Complex.ofReal_log h2π.le,
    ← Complex.ofReal_log (by positivity), Real.log_mul h2π.ne' (by positivity), Real.log_pow, hk]
  have key : Complex.exp (((Real.log ‖z‖ : ℝ) : ℂ) * ((|n| : ℤ) : ℂ)) *
      Complex.exp (((Real.log (2 * Real.pi) + (2 : ℕ) * Real.log ‖z‖ : ℝ) : ℂ) * -(s + ((|n| : ℤ) : ℂ) / 2)) =
      Complex.exp (((Real.log (2 * Real.pi) : ℝ) : ℂ) * -(s + ((|n| : ℤ) : ℂ) / 2)) *
      Complex.exp ((((2 : ℕ) * Real.log ‖z‖ : ℝ) : ℂ) * -s) := by
    rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; push_cast; ring
  linear_combination (2 * (z / ((‖z‖ : ℝ) : ℂ)) ^ (-n) * G) * key

end GlobalTheory.HeckeMellinOne

namespace GlobalTheory.HeckeMellinOne

theorem real_prod_rpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℝ) :
    (∏ j ∈ t, f j) ^ w = ∏ j ∈ t, f j ^ w := by
  classical
  induction t using Finset.induction_on with
  | empty => simp
  | insert a t ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      Real.mul_rpow (hf a) (Finset.prod_nonneg fun j _ => hf j), ih]

theorem mellin_term : ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ), GlobalTheory.CMVal.IsCMType φ → ∀ (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ α : 𝓞 K, α ≠ 0 → Integrable (GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K))) ∧ 2 ^ Fintype.card I * ∫ y, GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y = GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor n s * GlobalTheory.HeckeStrip.wt φ n (α : K) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℂ) ^ (-s) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s (GlobalTheory.HeckeTheta.emb φ (α : K)) y‖ = (∏ i, (2 * Real.pi) ^ (-(s.re + (|n i| : ℝ) / 2)) * Real.Gamma (s.re + (|n i| : ℝ) / 2)) * ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) ^ (-s.re) := by
  intro K _ _ _ I _ φ hφ n s hs α hα
  have hαK : (α : K) ≠ 0 := by exact_mod_cast hα
  have hv : ∀ i, GlobalTheory.HeckeTheta.emb φ (α : K) i ≠ 0 := fun i => (map_ne_zero (φ i)).2 hαK
  obtain ⟨hint, hI, hN⟩ := GlobalTheory.T.integral_heckeMellinGaussIntegrand_eq_prod_gamma I n s hs _ hv
  have hnorm := GlobalTheory.T.cmType_prod_norm_sq_eq_absNorm_span K I φ hφ α
  refine ⟨hint, ?_, ?_⟩
  · rw [hI, ← Complex.ofReal_natCast, ← hnorm, ofReal_prod_cpow _ _ (fun i => by positivity),
      ← Finset.card_univ, Finset.pow_card_mul_prod]
    unfold GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds.archFactor GlobalTheory.HeckeStrip.wt
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [complex_factor _ (hv i)]
    simp only [GlobalTheory.HeckeTheta.emb]
    ring
  · rw [hN, ← hnorm, real_prod_rpow _ _ (fun i => by positivity), ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact real_factor _ _ _ _ _ (norm_pos_iff.2 (hv i)) (by rw [Nat.cast_natAbs, Int.cast_abs])

end GlobalTheory.HeckeMellinOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HensIsLocalRingAndIsLocalHomOf
section
open IsLocalRing

noncomputable section

namespace GlobalTheory.Henselisation

namespace LocalLimit

variable {R : Type} [CommRing R] [IsLocalRing R]

theorem directedSystem_trans :
    DirectedSystem (fun i : EtNbhd R => i.B) (fun i j h => ⇑(EtNbhd.trans h : i.B →+* j.B)) where
  map_self := fun i x => (GlobalTheory.T.pointedEtaleNbhd_transitionMap_directedSystem R).1 i x
  map_map := fun {k j i} hij hjk x => (GlobalTheory.T.pointedEtaleNbhd_transitionMap_directedSystem R).2 i j k hij hjk x

theorem directed : IsDirected (EtNbhd R) (· ≤ ·) := GlobalTheory.T.pointedEtaleNeighbourhoodLocalRing_isDirected R

theorem of_injective (i : EtNbhd R) : Function.Injective (Hens.of i) := by
  haveI := directedSystem_trans (R := R)
  haveI := directed (R := R)
  exact Ring.DirectLimit.of_injective (G := fun i : EtNbhd R => i.B)
    (fun i j h => EtNbhd.trans h) (fun i j h => (GlobalTheory.T.etaleNbhdLocalRingTransitionMap_isLocalHom_injective R i j h).2) i

theorem exists_of (z : Hens R) : ∃ (i : EtNbhd R) (x : i.B), Hens.of i x = z := by
  haveI := directed (R := R)
  exact Ring.DirectLimit.exists_of z

theorem of_trans {i j : EtNbhd R} (h : i ≤ j) (x : i.B) :
    Hens.of j (EtNbhd.trans h x) = Hens.of i x :=
  Ring.DirectLimit.of_f (G := fun i : EtNbhd R => i.B) (f := fun _ _ h => ⇑(EtNbhd.trans h)) h x

theorem nontrivial : Nontrivial (Hens R) := by
  refine nontrivial_of_ne (1 : Hens R) 0 ?_
  intro h
  rw [← map_one (Hens.of (EtNbhd.base (R := R))), ← map_zero (Hens.of (EtNbhd.base (R := R)))] at h
  exact one_ne_zero (of_injective _ h)

theorem isUnit_or_isUnit_of_add_one {a b : Hens R} (hab : a + b = 1) : IsUnit a ∨ IsUnit b := by
  obtain ⟨i, x, rfl⟩ := exists_of a
  obtain ⟨j, y, rfl⟩ := exists_of b
  haveI := directed (R := R)
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have h1 : EtNbhd.trans hik x + EtNbhd.trans hjk y = 1 := by
    apply of_injective k
    rw [map_add, of_trans, of_trans, map_one, hab]
  rcases IsLocalRing.isUnit_or_isUnit_of_add_one h1 with h | h
  · left
    rw [← of_trans hik]
    exact h.map _
  · right
    rw [← of_trans hjk]
    exact h.map _

theorem isLocalHom_of (i : EtNbhd R) : IsLocalHom (Hens.of i) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨u, hu⟩ := hx
  obtain ⟨j, y, hy⟩ := exists_of (↑u⁻¹ : Hens R)
  haveI := directed (R := R)
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have h1 : EtNbhd.trans hik x * EtNbhd.trans hjk y = 1 := by
    apply of_injective k
    rw [map_mul, of_trans, of_trans, map_one, hy, ← hu, Units.mul_inv]
  haveI := (GlobalTheory.T.etaleNbhdLocalRingTransitionMap_isLocalHom_injective R i k hik).1
  exact isUnit_of_map_unit (EtNbhd.trans hik) x (IsUnit.of_mul_eq_one _ h1)

end LocalLimit

theorem hens_isLocalRing_and_isLocalHom_of :
    ∀ (R : Type) [CommRing R] [IsLocalRing R], IsLocalRing (Hens R) ∧ ∀ i : EtNbhd R, IsLocalHom (Hens.of i) := by
  intro R _ _
  haveI := LocalLimit.nontrivial (R := R)
  exact ⟨IsLocalRing.of_is_unit_or_is_unit_of_add_one LocalLimit.isUnit_or_isUnit_of_add_one,
    LocalLimit.isLocalHom_of⟩

end GlobalTheory.Henselisation

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralClosureEtaleAtOfHeightLeOnePurity
section
open IsLocalRing Polynomial

noncomputable section

namespace GlobalTheory.KeyOriginEnlarge

theorem atPrime_isDomain_isIntegrallyClosed_isNoetherian_injective : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime],
    IsDomain (Localization.AtPrime QA) ∧ IsIntegrallyClosed (Localization.AtPrime QA) ∧
      IsNoetherianRing (Localization.AtPrime QA) ∧
      Function.Injective (algebraMap A (Localization.AtPrime QA)) := by
  intro A _ _ _ _ EA _ _ _ _ _ QA _
  obtain ⟨hd, hn⟩ := GlobalTheory.isDomain_and_isIntegrallyClosed_atPrime_of_etale (Polynomial A) QA
    (Localization.AtPrime QA)
  haveI : IsNoetherianRing EA := Algebra.FiniteType.isNoetherianRing (Polynomial A) EA
  refine ⟨hd, hn, inferInstance, ?_⟩
  haveI := hd
  haveI : Module.Flat (Polynomial A) (Localization.AtPrime QA) :=
    Module.Flat.trans (Polynomial A) EA (Localization.AtPrime QA)
  have h1 : Function.Injective (algebraMap (Polynomial A) (Localization.AtPrime QA)) :=
    FaithfulSMul.algebraMap_injective (Polynomial A) (Localization.AtPrime QA)
  have h2 : algebraMap A (Localization.AtPrime QA) =
      (algebraMap (Polynomial A) (Localization.AtPrime QA)).comp (algebraMap A (Polynomial A)) :=
    IsScalarTower.algebraMap_eq _ _ _
  rw [h2]
  exact h1.comp Polynomial.C_injective

theorem closureEtaleAt_of_comap_height_le_one : ∀ (q : ℕ) (A : Type) [CommRing A] [IsDomain A] [IsLocalRing A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    [Algebra.EssFiniteType ℤ A]
    (EA : Type) [CommRing EA] [Algebra (Polynomial A) EA] [Algebra A EA]
    [IsScalarTower A (Polynomial A) EA] [Algebra.Etale (Polynomial A) EA]
    (QA : Ideal EA) [QA.IsPrime]
    (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA]
    (actA : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)] DA)),
    GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA q actA →
    (∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime], P.height ≤ 1 →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P) →
    ∀ (P : Ideal (Localization.AtPrime QA)) [P.IsPrime],
      (P.comap (algebraMap A (Localization.AtPrime QA))).height ≤ 1 →
      GlobalTheory.KeyOriginEnlarge.ClosureEtaleAt A (Localization.AtPrime QA) DA P := by
  intro q A _ _ _ _ _ _ EA _ _ _ _ _ QA _ DA _ _ actA htors hyp P _ hP
  obtain ⟨hdom, hic, hnoeth, hinj⟩ :=
    atPrime_isDomain_isIntegrallyClosed_isNoetherian_injective A EA QA
  haveI := GlobalTheory.T.cyclic_torsor_etale _ DA q actA htors
  haveI : Module.Finite (GlobalTheory.LocAcyc.GenFib A (Localization.AtPrime QA)) DA := htors.1
  letI := GlobalTheory.KeyOriginNoeth.closureAlg A (Localization.AtPrime QA) DA
  haveI := GlobalTheory.T.closure_finite_over_base A (Localization.AtPrime QA) hinj DA
  exact GlobalTheory.T.etale_atPrime_of_regular_of_isIntegrallyClosedIn (Localization.AtPrime QA)
    (GlobalTheory.KeyOriginNoeth.closure A (Localization.AtPrime QA) DA)
    (GlobalTheory.T.isIntegrallyClosedIn_etale_genFib_of_injective A (Localization.AtPrime QA) hinj DA) P (GlobalTheory.T.regular_height_one_localization A EA QA P hP)
    (fun P' _ _ hh => hyp P' hh)

end GlobalTheory.KeyOriginEnlarge
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleCharacterOfProduct
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
namespace GlobalTheory.IrrPi

theorem isChar_of_irr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrrChar ℂ ℂ χ) : IsChar ℂ ℂ χ := by
  obtain ⟨n, ρ, _, h⟩ := h
  exact ⟨n, ρ, h⟩

theorem pair_prod {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)] [∀ i, Finite (G i)]
    (a b : ∀ i, G i → ℂ) :
    pair (fun x : ∀ i, G i => ∏ i, a i (x i)) (fun x => ∏ i, b i (x i)) = ∏ i, pair (a i) (b i) := by
  classical
  have := fun i => Fintype.ofFinite (G i)
  simp only [pair, finsum_eq_sum_of_fintype, Finset.prod_mul_distrib, Nat.card_pi, Nat.cast_prod,
    Finset.prod_inv_distrib, Finset.prod_univ_sum, Fintype.piFinset_univ, Pi.inv_apply]

theorem irr_one {G : Type} [Group G] [Finite G] {χ : G → ℂ} (h : IsIrrChar ℂ ℂ χ) :
    ∃ n : ℕ, n ≠ 0 ∧ χ 1 = n := by
  obtain ⟨n, hn, h0⟩ := (isChar_restrict_conj_one ℂ ℂ G χ (isChar_of_irr h)).2.2
  refine ⟨n, fun h1 => ?_, hn⟩
  have := pair_self_of_isIrrChar_algClosed ℂ G χ h
  rw [h0 h1] at this
  simp [pair] at this

theorem irr_mulSingle {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] {χ : (∀ i, G i) → ℂ} (h : IsIrrChar ℂ ℂ χ) (i : ι) (a : G i) (y : ∀ i, G i)
    (hy : y i = 1) : χ 1 * χ (Pi.mulSingle i a * y) = χ (Pi.mulSingle i a) * χ y := by
  have := Fintype.ofFinite (∀ i, G i)
  have h1 := irrChar_one_mul_finsum_conj_mul _ χ h (Pi.mulSingle i a) y
  have hc := (isChar_restrict_conj_one ℂ ℂ _ χ (isChar_of_irr h)).2.1
  have h2 : ∀ k : ∀ i, G i, χ (k * Pi.mulSingle i a * k⁻¹ * y) = χ (Pi.mulSingle i a * y) := by
    intro k
    rw [← hc (Pi.mulSingle i a * y) (Pi.mulSingle i (k i)⁻¹)]
    congr 1
    funext j
    by_cases hj : j = i
    · subst hj
      simp [hy]
    · simp [Pi.mulSingle_eq_of_ne hj]
  simp only [h2, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
  rw [Nat.card_eq_fintype_card] at h1
  have hN : (Fintype.card (∀ i, G i) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  apply mul_left_cancel₀ hN
  rw [← h1]
  ring

theorem irr_factor {ι : Type} [Fintype ι] [DecidableEq ι] {G : ι → Type} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] {χ : (∀ i, G i) → ℂ} (h : IsIrrChar ℂ ℂ χ) (x : ∀ i, G i) :
    χ x = χ 1 * ∏ i, (χ (Pi.mulSingle i (x i)) / χ 1) := by
  obtain ⟨n, hn, h1⟩ := irr_one h
  have h0 : χ 1 ≠ 0 := by rw [h1]; exact_mod_cast hn
  have key : ∀ s : Finset ι, χ (fun j => if j ∈ s then x j else 1) =
      χ 1 * ∏ i ∈ s, (χ (Pi.mulSingle i (x i)) / χ 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.notMem_empty, if_false, Finset.prod_empty, mul_one]
      rfl
    | insert i s hi ih =>
      have e : (fun j => if j ∈ insert i s then x j else 1) =
          Pi.mulSingle i (x i) * (fun j => if j ∈ s then x j else 1) := by
        funext j
        by_cases hj : j = i
        · subst hj
          simp [hi]
        · simp [Pi.mulSingle_eq_of_ne hj, hj]
      have := irr_mulSingle h i (x i) (fun j => if j ∈ s then x j else 1) (by simp [hi])
      rw [e, Finset.prod_insert hi]
      apply mul_left_cancel₀ h0
      rw [this, ih]
      field_simp
  simpa using key Finset.univ

theorem exists_irr_pair_ne {G : Type} [Group G] [Finite G] {φ : G → ℂ} (h : φ ∈ Virt ℂ ℂ G)
    (h1 : φ 1 ≠ 0) : ∃ ψ, IsIrrChar ℂ ℂ ψ ∧ pair φ ψ ≠ 0 := by
  classical
  have := Fintype.ofFinite G
  obtain ⟨c, hc, hφ, -⟩ := virt_expand G φ h
  have hne : c.support.Nonempty := by
    rw [Finsupp.support_nonempty_iff]
    rintro rfl
    rw [hφ] at h1
    simp at h1
  obtain ⟨ψ, hψ⟩ := hne
  refine ⟨ψ, hc ψ hψ, ?_⟩
  have e : pair φ ψ = ∑ χ ∈ c.support, (c χ : ℂ) * pair χ ψ := by
    rw [hφ]
    simp only [pair, finsum_eq_sum_of_fintype, Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
      zsmul_eq_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
    simp only [Pi.mul_apply, Pi.intCast_apply]
    ring
  rw [e, Finset.sum_eq_single ψ]
  · rw [pair_self_of_isIrrChar_algClosed ℂ G ψ (hc ψ hψ), mul_one]
    exact_mod_cast Finsupp.mem_support_iff.1 hψ
  · intro b hb hbψ
    rw [pair_eq_zero_of_isIrrChar_ne G b ψ (hc b hb) (hc ψ hψ) hbψ, mul_zero]
  · intro h
    exact absurd hψ h

theorem prod_mem_virt {ι : Type} [Fintype ι] {G : ι → Type} [∀ i, Group (G i)]
    [∀ i, Finite (G i)] (ψ : ∀ i, G i → ℂ) (h : ∀ i, ψ i ∈ Virt ℂ ℂ (G i)) :
    (fun x : ∀ i, G i => ∏ i, ψ i (x i)) ∈ Virt ℂ ℂ (∀ i, G i) := by
  classical
  have key : ∀ s : Finset ι, (fun x : ∀ i, G i => ∏ i ∈ s, ψ i (x i)) ∈ Virt ℂ ℂ (∀ i, G i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact AddSubgroup.subset_closure (by simpa using isChar_one ℂ ℂ (∀ i, G i))
    | insert i s hi ih =>
      simp only [Finset.prod_insert hi]
      exact (virt_mul_comap_conj_ind_linear (∀ i, G i)).1 _
        ((virt_mul_comap_conj_ind_linear (G i)).2.1 _ (h i) _ (Pi.evalMonoidHom G i)) _ ih
  exact key _

end GlobalTheory.IrrPi

namespace GlobalTheory
open IrrPi

theorem irrChar_pi_eq_prod : ∀ (ι : Type) [Fintype ι] (G : ι → Type) [∀ i, Group (G i)] [∀ i, Finite (G i)] (χ : (∀ i, G i) → ℂ), IsIrrChar ℂ ℂ χ → ∃ ψ : ∀ i, G i → ℂ, (∀ i, IsIrrChar ℂ ℂ (ψ i)) ∧ ∀ x, χ x = ∏ i, ψ i (x i) := by
  intro ι _ G _ _ χ h
  classical
  obtain ⟨n, hn, h1⟩ := irr_one h
  have h0 : χ 1 ≠ 0 := by rw [h1]; exact_mod_cast hn
  have hφ : ∀ i, ∃ ψ, IsIrrChar ℂ ℂ ψ ∧ pair (fun a : G i => χ (Pi.mulSingle i a)) ψ ≠ 0 := by
    intro i
    refine exists_irr_pair_ne (AddSubgroup.subset_closure
      ((isChar_restrict_conj_one ℂ ℂ _ χ (isChar_of_irr h)).1 _ (MonoidHom.mulSingle G i))) ?_
    simpa using h0
  choose ψ hψ hp using hφ
  refine ⟨ψ, hψ, ?_⟩
  have hV := prod_mem_virt ψ fun i => AddSubgroup.subset_closure (isChar_of_irr (hψ i))
  set Ψ : (∀ i, G i) → ℂ := fun x => ∏ i, ψ i (x i) with hΨ
  have hN : (Nat.card (∀ i, G i) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hnorm : ∑ᶠ g, Ψ g * star (Ψ g) = (Nat.card (∀ i, G i) : ℂ) := by
    have : pair Ψ Ψ = 1 := by
      rw [hΨ, pair_prod]
      exact Finset.prod_eq_one fun i _ => pair_self_of_isIrrChar_algClosed ℂ _ _ (hψ i)
    simp only [star_virt_eq_inv _ Ψ hV]
    unfold pair at this
    field_simp at this
    exact this
  have hpair : pair χ Ψ ≠ 0 := by
    have e : pair χ Ψ = χ 1 * pair (fun x : ∀ i, G i => ∏ i, χ (Pi.mulSingle i (x i)) / χ 1) Ψ := by
      unfold pair
      have := Fintype.ofFinite (∀ i, G i)
      simp only [finsum_eq_sum_of_fintype, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [irr_factor h x]
      ring
    rw [e, hΨ, pair_prod (fun i (a : G i) => χ (Pi.mulSingle i a) / χ 1) ψ]
    refine mul_ne_zero h0 (Finset.prod_ne_zero_iff.2 fun i _ => ?_)
    have e2 : pair (fun a => χ (Pi.mulSingle i a) / χ 1) (ψ i) =
        pair (fun a : G i => χ (Pi.mulSingle i a)) (ψ i) / χ 1 := by
      unfold pair
      have := Fintype.ofFinite (G i)
      simp only [finsum_eq_sum_of_fintype, Finset.mul_sum, Finset.sum_div]
      refine Finset.sum_congr rfl fun x _ => ?_
      ring
    rw [e2]
    exact div_ne_zero (hp i) h0
  rcases (irr_of_norm_one _ Ψ hV hnorm).1 with hI | hI
  · by_contra hne
    exact hpair (pair_eq_zero_of_isIrrChar_ne _ χ Ψ h hI fun e => hne fun x => congrFun e x)
  · exfalso
    choose m hm hm1 using fun i => irr_one (hψ i)
    obtain ⟨k, hk, hk1⟩ := irr_one hI
    have : ((k + ∏ i, m i : ℕ) : ℂ) = 0 := by
      push_cast
      rw [← hk1]
      simp [hΨ, hm1]
    have : k + ∏ i, m i = 0 := by exact_mod_cast this
    omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyDirectedOfBasis
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory.ThickGlue

set_option backward.isDefEq.respectTransparency false in

theorem isLocallyDirected_of_basis : ∀ {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens), (∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : B₀, x ∈ U → x ∈ V → ∃ W ∈ 𝒰, x ∈ W ∧ W ≤ U ∧ W ≤ V) → ∀ (F : 𝒰 ⥤ Scheme.{0}), (∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)) → ∀ (e : ∀ U : 𝒰, U.1.toScheme ⟶ F.obj U), (∀ U, Function.Injective (e U)) → (∀ U, Function.Surjective (e U)) → (∀ {U V : 𝒰} (h : U.1 ≤ V.1), B₀.homOfLE h ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) → (F ⋙ Scheme.forget).IsLocallyDirected := by
  intro B₀ 𝒰 hbas F _hF e hinj hsurj hnat
  have hnat' : ∀ {U V : 𝒰} (f : U ⟶ V) (x : U.1.toScheme),
      F.map f (e U x) = e V (B₀.homOfLE (show U.1 ≤ V.1 from f.le) x) := by
    intro U V f x
    rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hnat]
    rfl
  have key : ∀ {U V : 𝒰} (x : U.1.toScheme) (y : V.1.toScheme), x.1 = y.1 →
      ∃ (W : 𝒰) (f : W ⟶ U) (g : W ⟶ V) (z : F.obj W),
        F.map f z = e U x ∧ F.map g z = e V y := by
    intro U V x y h
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 x.1 x.2 (h ▸ y.2)
    refine ⟨⟨W, hW⟩, homOfLE h1, homOfLE h2, e ⟨W, hW⟩ ⟨x.1, hxW⟩, ?_, ?_⟩
    · rw [hnat']; congr 1; apply Subtype.ext; simp
    · rw [hnat']; congr 1; apply Subtype.ext; simpa using h
  constructor
  intro U V W f g x y h
  obtain ⟨x, rfl⟩ := hsurj U x
  obtain ⟨y, rfl⟩ := hsurj V y
  have h' : F.map f (e U x) = F.map g (e V y) := h
  rw [hnat', hnat'] at h'
  have h'' := congrArg Subtype.val (hinj _ h')
  exact key x y (by simpa using h'')

end GlobalTheory.ThickGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LaurentCPullbackBijectiveFiniteStrictlyHenselianStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.laurentC_pullback_bijective_finite_strictlyHenselian : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) → ∀ (T : Type) [CommRing T] [Algebra A T],
  Module.Finite A T → ∀ i : ℤ, Function.Bijective (pull _ (spMap (LaurentPolynomial.C : T →+* LaurentPolynomial T)) (tw q i) 0) := by
  first | (exact @GlobalTheory.EtC.SpecMapPullbackFunctoriality.laurent_C_pull_bijective) | (exact GlobalTheory.EtC.SpecMapPullbackFunctoriality.laurent_C_pull_bijective) | (intros; apply GlobalTheory.EtC.SpecMapPullbackFunctoriality.laurent_C_pull_bijective <;> assumption)
end

