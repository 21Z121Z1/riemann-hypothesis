import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0186
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0187
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ChapterMu
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.CuspidalUnitaryTwistsClaim
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0172
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0147
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralQExpansionEqLSeries

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumDirectionIndepStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_direction_indep : ∀ (j L : ℕ) (v w : ℤ × ℤ) (Φ : ℤ × ℤ → ℂ) (τ : ℍ), 1 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → Kills L v Φ → Kills L w Φ → lat j 0 L v Φ τ = lat j 0 L w Φ τ := by
  first | exact @GlobalTheory.EisM.lat_indep | exact GlobalTheory.EisM.lat_indep | (intros; apply GlobalTheory.EisM.lat_indep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumModerateMeasurablStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_moderate_measurable_tendsto : ∀ (j L : ℕ) (Φ : ℤ × ℤ → ℂ), 2 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖Φ x‖ ≤ C) → (∃ (C : ℝ) (A : ℕ), ∀ (s : ℝ) (τ : ℍ), 0 ≤ s → s ≤ 1 → ‖lat j s L (0, 1) Φ τ‖ ≤ C * (τ.im ^ A + (τ.im ^ A)⁻¹)) ∧ (∀ s : ℝ, Measurable (lat j s L (0, 1) Φ)) ∧ ∀ τ : ℍ, Tendsto (fun s : ℝ => lat j s L (0, 1) Φ τ) (𝓝[>] 0) (𝓝 (lat j 0 L (0, 1) Φ τ)) := by
  first | exact @GlobalTheory.EisM.LatBd.lat_mod_meas_tendsto | exact GlobalTheory.EisM.LatBd.lat_mod_meas_tendsto | (intros; apply GlobalTheory.EisM.LatBd.lat_mod_meas_tendsto <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RegularizedEisensteinLatticeSumQExpansionStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regularizedEisensteinLatticeSum_qExpansion : ∀ (j L : ℕ) (b : ℤ → ℂ) (φ : ZMod L → ℂ), 1 ≤ j → 0 < L → (∃ C : ℝ, ∀ x, ‖b x‖ ≤ C) → hat φ 0 = 0 → (∀ x y : ℤ, b (-x) * φ (-(y : ZMod L)) = (-1) ^ j * (b x * φ y)) → ∃ c : ℂ, PolyB (eis j c (hat φ) b) ∧ ∀ τ : ℍ, lat j 0 L (0, 1) (latF L b φ) τ = 2 * (-2 * π * Complex.I / L) ^ j / (j - 1).factorial * qs (eis j c (hat φ) b) τ := by
  first | exact @GlobalTheory.LatQ.lat_qexp | exact GlobalTheory.LatQ.lat_qexp | (intros; apply GlobalTheory.LatQ.lat_qexp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SeriesRepresentationWeightLowerBoundStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.series_representation_weight_lower_bound : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (L : Lev g N) (τ : (ZMod g)[X] → GG g N → ℂ), IsSeries τ → ∀ f ∈ sqSet g N, ∃ w : ℝ, conv (zc (τ f)) L.e 1 = (w : ℂ) * L.e 1 ∧ (1 - 1 / (g : ℝ)) * ((torusCard g f : ℝ))⁻¹ ≤ w := by
  first | exact @GlobalTheory.BadShare.series_weight_lower_bound | exact GlobalTheory.BadShare.series_weight_lower_bound | (intros; apply GlobalTheory.BadShare.series_weight_lower_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelFunctionTransformationStatement
section
open scoped UpperHalfPlane MatrixGroups Manifold
open GlobalTheory.Sieg GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_function_transformation : ∀ (c : ℕ) (x : Fin 2 → ℚ) (γ : SL(2, ℤ)) (τ : ℍ), admitted c x → sg c x (γ • τ) = sg c (act x γ) τ := by
  first | exact @GlobalTheory.Sieg.sg_smul | exact GlobalTheory.Sieg.sg_smul | (intros; apply GlobalTheory.Sieg.sg_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.Sl2CoprimeFactorizationUniqueStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sl2_mul_eq_of_coprime_det_factorization : ∀ (a c : ℤ), IsCoprime a c → c ≠ 0 → ∀ (y y' β β' : Matrix (Fin 2) (Fin 2) ℤ), y.det = a → y'.det = a → β.det = c → β'.det = c → y * β = y' * β' → ∃ g : SL(2, ℤ), (g : Matrix (Fin 2) (Fin 2) ℤ) * β = β' := by
  first | exact @GlobalTheory.sl2_right_factor_of_coprime_factorizations | exact GlobalTheory.sl2_right_factor_of_coprime_factorizations | (intros; apply GlobalTheory.sl2_right_factor_of_coprime_factorizations <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SmallTracesSubgroupGaloisTowerTopStatement
section
open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallTraces_subgroup_galois_towerTop : ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], p ≠ 2 → IsClo p Ω → ∀ (T : Tower p Ω) (H : Subgroup (Gal p Ω)), H ≤ ⨅ n, Gn T n → ∀ (S : Finset Ω) (j : ℕ), 1 ≤ j → ∃ (y : Ω) (E : Finset (Gal p Ω)), IsInt p y ∧ (∀ g ∈ E, g ∈ H) ∧ (∀ h ∈ H, ∃! g, g ∈ E ∧ h y = g y ∧ ∀ s ∈ S, h s = g s) ∧ ∑ g ∈ E, g y = T.ζ j - 1 := by
  first | exact @GlobalTheory.K5.small_traces_subgroup | exact GlobalTheory.K5.small_traces_subgroup | (intros; apply GlobalTheory.K5.small_traces_subgroup <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SturmSumOverCharactersEqZero
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem sturm_sum_coef_zero : ∀ (k L N : ℕ), 0 < L → N ∣ L → ∃ B : ℕ, ∀ a : DirichletCharacter ℂ N → ℕ → ℂ,
    (∀ ε, MF k L (ch ε) (a ε)) → (∀ n < B, (∑ ε, a ε) n = 0) → ∑ ε, a ε = 0 := by
  classical
  intro k L N hL hN
  have hΓ : (1 : ℝ) ∈ (Gamma1 L : Subgroup (GL (Fin 2) ℝ)).strictPeriods := by
    simp [strictPeriods_Gamma1]
  haveI : NeZero L := ⟨hL.ne'⟩
  obtain ⟨m, hm⟩ := exists_sturmBound_modularForm_arithmetic hΓ (k : ℤ)
  refine ⟨m, fun a ha hz => ?_⟩
  choose f hf using fun ε => modularForm_gammaOne_of_MF k L N ε (a ε) hL hN (ha ε)
  have hc : ∀ ε n, (qExpansion 1 (f ε)).coeff n = a ε n := by
    intro ε n
    have := coef_qs (a ε) (ha ε).1 n
    unfold coef at this
    rw [← this, hf]
  have hsum : ∀ (s : Finset (DirichletCharacter ℂ N)) (n : ℕ),
      (qExpansion 1 ⇑(∑ ε ∈ s, f ε)).coeff n = ∑ ε ∈ s, a ε n := by
    intro s n
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Finset.sum_empty, ModularForm.coe_zero, qExpansion_zero, map_zero]
    | insert e s he ih =>
      rw [Finset.sum_insert he, ModularForm.coe_add, ModularForm.qExpansion_add one_pos hΓ, map_add, ih, hc, Finset.sum_insert he]
  have h0 : ∑ ε, f ε = 0 := hm _ fun n hn => by
    rw [hsum]
    simpa [Finset.sum_apply] using hz n hn
  funext n
  have := hsum Finset.univ n
  rw [h0] at this
  rw [ModularForm.coe_zero, qExpansion_zero, map_zero] at this
  rw [Finset.sum_apply, ← this]
  rfl

example : ∀ (k L N : ℕ), 0 < L → N ∣ L → ∃ B : ℕ, ∀ a : DirichletCharacter ℂ N → ℕ → ℂ, (∀ ε, MF k L (ch ε) (a ε)) → (∀ n < B, (∑ ε, a ε) n = 0) → ∑ ε, a ε = 0 := sturm_sum_coef_zero

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TeichmullerRoots
section
noncomputable section

open Polynomial

namespace GlobalTheory.Compare.TeichmullerRoots

open Formalism.BasicNotions Formalism.CyclotomicNorms GlobalTheory.IndefiniteRowSideFullHecke.FactorSeriesSupport

section Roots

variable {g : ℕ} [Fact g.Prime]

theorem frob_comp : (frobenius (Fbar g) g).comp (algebraMap (ZMod g) (Fbar g)) = algebraMap (ZMod g) (Fbar g) :=
  Subsingleton.elim _ _

theorem rootsBar_frob (f : (ZMod g)[X]) : (rootsBar f).map (fun x => x ^ g) = rootsBar f := by
  have h := Polynomial.roots_map_of_injective_of_card_eq_natDegree
    (p := f.map (algebraMap (ZMod g) (Fbar g))) (f := frobenius (Fbar g) g) (RingHom.injective _)
    IsAlgClosed.card_roots_eq_natDegree
  rw [Polynomial.map_map, frob_comp] at h
  exact h

theorem card_rootsBar (f : (ZMod g)[X]) : (rootsBar f).card = f.natDegree := by
  unfold rootsBar
  rw [IsAlgClosed.card_roots_eq_natDegree, natDegree_map]

theorem zero_mem_rootsBar {f : (ZMod g)[X]} (hf : f.Monic) : 0 ∈ rootsBar f ↔ f.coeff 0 = 0 := by
  unfold rootsBar
  rw [mem_roots (hf.map _).ne_zero, IsRoot, ← coeff_zero_eq_eval_zero, coeff_map]
  exact map_eq_zero_iff _ (RingHom.injective _)

theorem exists_monic_of_stable (S : Multiset (Fbar g)) (hS : S.map (fun x => x ^ g) = S) :
    ∃ f : (ZMod g)[X], f.Monic ∧ rootsBar f = S := by
  set P : (Fbar g)[X] := (S.map fun x => X - C x).prod with hP
  have hm : P.Monic := monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C x
  have hfix : P.map (frobenius (Fbar g) g) = P := by
    rw [hP, Polynomial.map_multiset_prod, Multiset.map_map]
    conv_rhs => rw [← hS, Multiset.map_map]
    congr 1
    apply Multiset.map_congr rfl
    intro x _
    simp [frobenius_def]
  have hl : P ∈ lifts (algebraMap (ZMod g) (Fbar g)) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    have h1 : P.coeff n ^ g = P.coeff n := by
      have := congrArg (fun q => q.coeff n) hfix
      simpa [frobenius_def] using this
    have h2 : P.coeff n ∈ (⊥ : Subfield (Fbar g)) := (Subfield.mem_bot_iff_pow_eq_self _ g).2 h1
    rw [Subfield.bot_eq_of_zMod_algebra g] at h2
    exact h2
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hl hm
  refine ⟨q, hqm, ?_⟩
  unfold rootsBar
  rw [hq, hP, roots_multiset_prod_X_sub_C]

theorem root_pow_rootExp {N : ℕ} {f : (ZMod g)[X]} (hf : IsLabel N f) {x : Fbar g} (hx : x ∈ rootsBar f) :
    x ^ rootExp N g = 1 := by
  have hx0 : x ≠ 0 := fun h => hf.2.2 ((zero_mem_rootsBar hf.1).1 (h ▸ hx))
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have hroot : aeval x f = 0 := by
    have := (mem_roots (hf.1.map _).ne_zero).1 hx
    rwa [IsRoot, eval_map_algebraMap] at this
  have hd : (minpoly (ZMod g) x).natDegree ≤ N := by
    rw [← hf.2.1]
    exact natDegree_le_of_dvd (minpoly.dvd _ _ hroot) hf.1.ne_zero
  have hd1 : 1 ≤ (minpoly (ZMod g) x).natDegree := minpoly.natDegree_pos hint
  set K := IntermediateField.adjoin (ZMod g) ({x} : Set (Fbar g))
  haveI : FiniteDimensional (ZMod g) K := IntermediateField.adjoin.finiteDimensional hint
  haveI : Finite K := Module.finite_of_finite (ZMod g)
  letI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = g ^ (minpoly (ZMod g) x).natDegree := by
    rw [Module.card_eq_pow_finrank (K := ZMod g), ZMod.card, IntermediateField.adjoin.finrank hint]
  let y : K := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx0 (congrArg Subtype.val h)
  have h1 := FiniteField.pow_card_sub_one_eq_one y hy
  rw [hc] at h1
  have h2 : x ^ (g ^ (minpoly (ZMod g) x).natDegree - 1) = 1 := by
    have := congrArg Subtype.val h1
    simpa [y] using this
  obtain ⟨c, hc⟩ : g ^ (minpoly (ZMod g) x).natDegree - 1 ∣ rootExp N g :=
    Finset.dvd_lcm (f := fun d => g ^ d - 1) (Finset.mem_Icc.2 ⟨hd1, hd⟩)
  rw [hc, pow_mul, h2, one_pow]

theorem roots_reverse_prod {F : Type} [Field F] (S : Multiset F) (hS : 0 ∉ S) :
    ((S.map fun x => X - C x).prod.reverse).roots = S.map fun x => x⁻¹ := by
  induction S using Multiset.induction_on with
  | empty => simp [reverse]
  | cons x S ih =>
    have hx : x ≠ 0 := fun h => hS (h ▸ Multiset.mem_cons_self _ _)
    have hS' : 0 ∉ S := fun h => hS (Multiset.mem_cons_of_mem h)
    have hm : (S.map fun x => X - C x).prod.Monic :=
      monic_multiset_prod_of_monic _ _ fun x _ => monic_X_sub_C x
    have e : (X - C x).reverse = C (-x) * (X - C x⁻¹) := by
      have : (X - C x) = X + C (-x) := by simp [sub_eq_add_neg]
      rw [this, reverse_add_C, natDegree_X]
      have hX : (X : F[X]).reverse = 1 := by
        have := reverse_mul_X (1 : F[X])
        simpa [reverse] using this
      rw [hX, mul_sub, ← C_mul, neg_mul, mul_inv_cancel₀ hx]
      simp; ring
    rw [Multiset.map_cons, Multiset.prod_cons, reverse_mul_of_domain, roots_mul, ih hS', e,
      roots_C_mul _ (neg_ne_zero.2 hx), roots_X_sub_C, Multiset.map_cons, Multiset.singleton_add]
    exact mul_ne_zero (by rw [Ne, reverse_eq_zero]; exact X_sub_C_ne_zero x)
      (by rw [Ne, reverse_eq_zero]; exact hm.ne_zero)

theorem dual_spec {f : (ZMod g)[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    (C (f.coeff 0)⁻¹ * f.reverse).Monic ∧ IsPowLabel (-1) f (C (f.coeff 0)⁻¹ * f.reverse) := by
  constructor
  · apply monic_C_mul_of_mul_leadingCoeff_eq_one
    rw [reverse_leadingCoeff, trailingCoeff_eq_coeff_zero h0, inv_mul_cancel₀ h0]
  · have e : f.map (algebraMap (ZMod g) (Fbar g)) = ((rootsBar f).map fun x => X - C x).prod :=
      (Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq (hm.map _)
        (IsAlgClosed.card_roots_eq_natDegree)).symm
    have e2 : f.reverse.map (algebraMap (ZMod g) (Fbar g)) = (f.map (algebraMap (ZMod g) (Fbar g))).reverse := by
      rw [reverse, reverse, natDegree_map, reflect_map]
    unfold IsPowLabel
    simp only [zpow_neg_one]
    rw [← roots_reverse_prod _ (fun h => h0 ((zero_mem_rootsBar hm).1 h)), ← e, ← e2]
    unfold rootsBar
    rw [Polynomial.map_mul, map_C, roots_C_mul]
    exact (_root_.map_ne_zero _).2 (inv_ne_zero h0)

theorem teich_injective (t : Fbar g →* ℂ) (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) :
    Function.Injective t := by
  have hne : ∀ x, x ≠ 0 → t x ≠ 0 := fun x hx => ((IsUnit.mk0 x hx).map t).ne_zero
  have h0 : t 0 = 0 := by
    classical
    obtain ⟨y, hy⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Fbar g))
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hy
    by_contra h
    have : t 0 * t y = t 0 * t 1 := by rw [← map_mul, ← map_mul, zero_mul, zero_mul]
    exact hy.2 (ht _ _ hy.1 one_ne_zero (mul_left_cancel₀ h this))
  intro x y h
  by_cases hx : x = 0
  · by_cases hy : y = 0
    · rw [hx, hy]
    · exact absurd (by rw [← h, hx, h0]) (hne y hy)
  · by_cases hy : y = 0
    · exact absurd (by rw [h, hy, h0]) (hne x hx)
    · exact ht x y hx hy h

theorem teich_zpow (t : Fbar g →* ℂ) {x : Fbar g} (hx : x ≠ 0) (a : ℤ) : t (x ^ a) = t x ^ a := by
  have h1 : t ((Units.mk0 x hx ^ a : (Fbar g)ˣ) : Fbar g) = ((Units.map t (Units.mk0 x hx) ^ a : ℂˣ) : ℂ) := by
    rw [← map_zpow]; rfl
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val] at h1
  exact h1

end Roots

theorem exists_exponent (α : ℂ ≃+* ℂ) {M : ℕ} (hM : M ≠ 0) :
    ∃ a : ℤ, ∀ ζ : ℂ, ζ ^ M = 1 → α ζ = ζ ^ a := by
  haveI : NeZero M := ⟨hM⟩
  have hp := Complex.isPrimitiveRoot_exp M hM
  obtain ⟨a, -, ha⟩ := hp.eq_pow_of_pow_eq_one (ξ := α (Complex.exp (2 * Real.pi * Complex.I / M)))
    (by rw [← map_pow, hp.pow_eq_one, map_one])
  refine ⟨a, fun ζ hζ => ?_⟩
  obtain ⟨i, -, rfl⟩ := hp.eq_pow_of_pow_eq_one hζ
  rw [map_pow, ← ha, zpow_natCast, ← pow_mul, ← pow_mul, mul_comm a i]

variable (D : D7)

theorem labAct_eq (k : Fin 2) (α : ℂ ≃+* ℂ) (a : ℤ)
    (ha : ∀ ζ : ℂ, ζ ^ rootExp D.R.r (D.host.g k) = 1 → α ζ = ζ ^ a)
    {f f' : (ZMod (D.host.g k))[X]} (hf : IsLabel D.R.r f) (hm : f'.Monic)
    (hp : haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; IsPowLabel a f f') :
    Formalism.MainNotions.ArithmeticCylinders.labAct D α k f = f' := by
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  have hinj := teich_injective (D.ntypes.teichC k) (D.ntypes.teichC_inj k)
  have e : (rootsBar f).map
      (fun x => Function.invFun (D.ntypes.teichC k) (α (D.ntypes.teichC k x))) =
      (rootsBar f).map fun x => x ^ a := by
    apply Multiset.map_congr rfl
    intro x hx
    have hx0 : x ≠ 0 := fun h => hf.2.2 ((zero_mem_rootsBar hf.1).1 (h ▸ hx))
    rw [ha _ (by rw [← map_pow, root_pow_rootExp hf hx, map_one]), ← teich_zpow _ hx0]
    exact Function.leftInverse_invFun hinj _
  have hs := Classical.epsilon_spec (p := fun q : (ZMod (D.host.g k))[X] => q.Monic ∧
    rootsBar q = (rootsBar f).map
      (fun x => Function.invFun (D.ntypes.teichC k) (α (D.ntypes.teichC k x))))
    ⟨f', hm, hp.trans e.symm⟩
  exact IsPowLabel.unique (a := a) (f := f) (hs.2.trans e) hp hs.1 hm

theorem atPlace_eq (k : Fin 2) (v : D.nd.PlG k) (f : (ZMod (D.host.g k))[X]) :
    Formalism.MainNotions.ArithmeticCylinders.atPlace D k v (D.ntypes.eSer k f) = (serAt D k v f).1 := by
  unfold Formalism.MainNotions.ArithmeticCylinders.atPlace serAt atFactor
  change _ = MonoidAlgebra.ofCoeff (Finsupp.mapDomain _ _)
  congr!
  funext h
  simp only [MonoidHom.mulSingle_apply, MonoidHom.coe_coe]
  congr!

end GlobalTheory.Compare.TeichmullerRoots

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnitStripIntegralQExpansionEqLSeriesStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitStrip_integral_qExpansion_eq_LSeries : ∀ (h b : ℕ → ℂ) (w : ℝ), 0 < w → PolyB h → PolyB b → h 0 = 0 → LSeriesSummable (fun n => conj (h n) * b n) w → IntegrableOn (fun τ : ℍ => conj (qs h τ) * qs b τ * ((τ.im ^ (w + 1) : ℝ) : ℂ)) strip → ∫ τ in strip, conj (qs h τ) * qs b τ * ((τ.im ^ (w + 1) : ℝ) : ℂ) = ((Real.Gamma w / (4 * π) ^ w : ℝ) : ℂ) * LSeries (fun n => conj (h n) * b n) w := by
  first | exact @GlobalTheory.EisM.strip_eq_LSeries | exact GlobalTheory.EisM.strip_eq_LSeries | (intros; apply GlobalTheory.EisM.strip_eq_LSeries <;> assumption)
end

