import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0097
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0104
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0109
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0110
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlTwoInvariantHolomorphicMemAdjoinJInvariant
section
noncomputable section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.LevelOne

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ}

theorem eq_const_of_nonneg [IsAlgClosure ℚ Ω] (X : Tower Ω ε) (h : X.K) (hinv : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h)
    (φ : ℂ → ℂ) (hd : DifferentiableOn ℂ φ Hs) (ha : X.an h = (φ : Mero))
    (hneg : ∀ r : ℚ, r < 0 → (X.exp h).coeff r = 0) :
    h = algebraMap Ω X.K ((X.exp h).coeff 0) := by
  set a0 := (X.exp h).coeff 0 with ha0
  have hsupp : ∀ r : ℚ, (X.exp h).coeff r ≠ 0 → ∃ n : ℕ, r = n := by
    intro r hr
    obtain ⟨m, rfl⟩ := GlobalTheory.T.exponents_integral_of_translation_invariant X h (hinv _) r hr
    have hm : 0 ≤ m := by
      by_contra hm
      exact hr (hneg _ (by exact_mod_cast (not_le.1 hm)))
    exact ⟨m.toNat, by rw [← Int.cast_natCast, Int.toNat_of_nonneg hm]⟩
  obtain ⟨B, t, hB⟩ := GlobalTheory.T.modularTower_function_tendsto_constTerm_exponential X h φ hd.continuousOn ha hsupp
  have hinvφ := GlobalTheory.T.modularTower_function_slTwoInt_invariant X h φ hd.continuousOn ha hinv
  have hexp1 : ∀ z : ℂ, t < z.im → Real.exp (-(2 * Real.pi * (z.im - t))) ≤ 1 := by
    intro z hz
    rw [Real.exp_le_one_iff]
    have : 0 < z.im - t := by linarith
    have := Real.pi_pos
    nlinarith
  obtain ⟨c, hc⟩ := GlobalTheory.T.const_of_slTwoInt_invariant_bounded_upperHalfPlane φ hd hinvφ ⟨‖ε a0‖ + |B|, t, fun z hz hzt => by
    have h1 := hB z hz hzt
    have h2 := hexp1 z hzt
    have h3 : B * Real.exp (-(2 * Real.pi * (z.im - t))) ≤ |B| := by
      calc B * Real.exp (-(2 * Real.pi * (z.im - t))) ≤ |B| * Real.exp (-(2 * Real.pi * (z.im - t))) :=
            mul_le_mul_of_nonneg_right (le_abs_self B) (Real.exp_pos _).le
        _ ≤ |B| * 1 := mul_le_mul_of_nonneg_left h2 (abs_nonneg B)
        _ = |B| := mul_one _
    calc ‖φ z‖ = ‖(φ z - ε a0) + ε a0‖ := by ring_nf
      _ ≤ ‖φ z - ε a0‖ + ‖ε a0‖ := norm_add_le _ _
      _ ≤ ‖ε a0‖ + |B| := by linarith⟩
  have hca : c = ε a0 := by
    have hle : ∀ s : ℝ, max t 0 < s → ‖c - ε a0‖ ≤ B * Real.exp (-(2 * Real.pi * (s - t))) := by
      intro s hs
      have hs0 : 0 < s := lt_of_le_of_lt (le_max_right _ _) hs
      have hst : t < s := lt_of_le_of_lt (le_max_left _ _) hs
      have hz : ((s : ℂ) * Complex.I) ∈ Hs := by simp [Hs, hs0]
      have := hB _ hz (by simpa using hst)
      rw [hc _ hz] at this
      simpa using this
    have ht : Filter.Tendsto (fun s : ℝ => B * Real.exp (-(2 * Real.pi * (s - t)))) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun s : ℝ => 2 * Real.pi * (s - t)) Filter.atTop Filter.atTop := by
        apply Filter.Tendsto.const_mul_atTop Real.two_pi_pos
        exact Filter.tendsto_atTop_add_const_right _ _ Filter.tendsto_id
      have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul B
      simpa using h2
    have h0 : ‖c - ε a0‖ ≤ 0 := ge_of_tendsto ht (Filter.eventually_gt_atTop (max t 0) |>.mono hle)
    have := norm_le_zero_iff.1 h0
    exact sub_eq_zero.1 this
  apply SiegelModel.an_injective X
  rw [ha, X.an_c]
  exact SiegelModel.germ_eq_of_eqOn fun z hz => by rw [hc z hz, hca]

theorem mem_adjoin_j : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε),
    Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ h : X.K,
    (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)) →
    h ∈ Algebra.adjoin Ω {X.jK} := by
  intro Ω _ _ _ ε X _ hj
  obtain ⟨ψ, hψ, hψa⟩ := hj
  have key : ∀ n : ℕ, ∀ h : X.K, (∀ γ : SL(2, ℤ), X.sl (ofSL γ) h = h) →
      (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h = (φ : Mero)) →
      (∀ r : ℚ, r < -(n : ℚ) → (X.exp h).coeff r = 0) → h ∈ Algebra.adjoin Ω {X.jK} := by
    intro n
    induction n with
    | zero =>
      intro h hinv hol hneg
      obtain ⟨φ, hd, ha⟩ := hol
      rw [eq_const_of_nonneg X h hinv φ hd ha (by simpa using hneg)]
      exact Subalgebra.algebraMap_mem _ _
    | succ n ih =>
      intro h hinv hol hneg
      obtain ⟨φ, hd, ha⟩ := hol
      obtain ⟨c, hcdef⟩ : ∃ c : Ω, c = (X.exp h).coeff (-((n + 1 : ℕ) : ℚ)) := ⟨_, rfl⟩
      obtain ⟨h', hh'⟩ : ∃ h' : X.K, h' = h - algebraMap Ω X.K c * X.jK ^ (n + 1) := ⟨_, rfl⟩
      have hj := GlobalTheory.T.hahnSeries_pow_of_leading_qInv (X.exp X.jK) X.j_exp.1 X.j_exp.2.1 (n + 1)
      have hinv' : ∀ γ : SL(2, ℤ), X.sl (ofSL γ) h' = h' := by
        intro γ
        rw [hh', map_sub, map_mul, map_pow, X.j_inv, hinv, AlgEquiv.commutes]
      have hol' : ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an h' = (φ : Mero) := by
        refine ⟨fun z => φ z - ε c * ψ z ^ (n + 1), ?_, ?_⟩
        · exact hd.sub ((hψ.pow _).const_mul _)
        · rw [hh', map_sub, map_mul, map_pow, X.an_c, ha, hψa]
          rfl
      have hneg' : ∀ r : ℚ, r < -(n : ℚ) → (X.exp h').coeff r = 0 := by
        intro r hr
        by_contra hrz
        obtain ⟨m, rfl⟩ := GlobalTheory.T.exponents_integral_of_translation_invariant X h' (hinv' _) r hrz
        apply hrz
        have hcoe : (X.exp h').coeff (m : ℚ) =
            (X.exp h).coeff m - c * ((X.exp X.jK) ^ (n + 1)).coeff m := by
          rw [hh', map_sub, map_mul, AlgHom.commutes, map_pow, HahnSeries.coeff_sub, HahnSeries.algebraMap_apply',
            PowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, HahnSeries.ofPowerSeries_C,
            HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]
        rw [hcoe]
        have hm : m ≤ -((n : ℤ) + 1) := by
          have : (m : ℚ) < -(n : ℚ) := hr
          have : m < -(n : ℤ) := by exact_mod_cast this
          omega
        rcases hm.lt_or_eq with hlt | heq
        · have hq : (m : ℚ) < -((n + 1 : ℕ) : ℚ) := by push_cast; exact_mod_cast hlt
          rw [hneg _ hq, hj.2 _ hq]
          ring
        · have hq : (m : ℚ) = -((n + 1 : ℕ) : ℚ) := by rw [heq]; push_cast; ring
          rw [hq, hj.1, hcdef]
          ring
      have hmem := ih h' hinv' hol' hneg'
      have hsum : h = h' + algebraMap Ω X.K c * X.jK ^ (n + 1) := by rw [hh']; abel
      have hjm : X.jK ∈ Algebra.adjoin Ω {X.jK} := Algebra.self_mem_adjoin_singleton Ω X.jK
      rw [hsum]
      exact add_mem hmem (mul_mem (Subalgebra.algebraMap_mem _ _) (pow_mem hjm _))
  intro h hinv hol
  refine key ⌈-(X.exp h).order⌉₊ h hinv hol fun r hr => HahnSeries.coeff_eq_zero_of_lt_order ?_
  have := Nat.le_ceil (-(X.exp h).order)
  linarith

end GlobalTheory.KZ.LevelOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.StripsExhaustParabolicUnipotentRadicalStatement
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel GlobalTheory.PsType
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.strips_exhaust_parabolicUnipotentRadical : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (ψ : Fin (r + t) → kˣ →* ℂˣ) (ϖ : k), (∀ i, IsSmoothChar (ψ i)) → ϖ ≠ 0 → valuation k ϖ < 1 → (∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k ϖ) → ∀ y ∈ unipRad k (two (stdSum (rfl : r + t = r + t))), ∃ m, y ∈ strip ψ r ϖ m := by
  first | exact @GlobalTheory.PsType.strip_exhaust | exact GlobalTheory.PsType.strip_exhaust | (intros; apply GlobalTheory.PsType.strip_exhaust <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaDerivationHahnSeriesLeibnizAddConstStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaDerivationHahnSeries_leibniz_add_const : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] (s : ℚ) (P Q : HahnSeries ℚ Ω), theta s (P * Q) = theta s P * Q + P * theta s Q ∧ theta s (P + Q) = theta s P + theta s Q ∧ ∀ c : Ω, theta s (HahnSeries.C c) = 0 := by
  first | exact @GlobalTheory.Glue.theta_leibniz_add_const | exact GlobalTheory.Glue.theta_leibniz_add_const | (intros; apply GlobalTheory.Glue.theta_leibniz_add_const <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UniformCongruenceLevelGamma1CapGamma0
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups

namespace GlobalTheory.KZ.H3

theorem gamma_le_of_dvd {M M' : ℕ} (h : M ∣ M') :
    CongruenceSubgroup.Gamma M' ≤ CongruenceSubgroup.Gamma M := by
  intro δ hδ
  rw [CongruenceSubgroup.Gamma_mem] at hδ ⊢
  have key : ∀ x : ℤ, ((x : ZMod M) = ZMod.castHom h (ZMod M) (x : ZMod M')) := fun x => by
    rw [map_intCast]
  obtain ⟨h1, h2, h3, h4⟩ := hδ
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key, h1, map_one]
  · rw [key, h2, map_zero]
  · rw [key, h3, map_zero]
  · rw [key, h4, map_one]

theorem unif_level : ∀ (N l : ℕ) (R : Type) [CommRing R] (Φ : SL(2, ℤ) → MvPolynomial (Fin 2) R), 0 < N → 0 < l →
    (∃ M : ℕ, 0 < M ∧ ∀ δ ∈ CongruenceSubgroup.Gamma M, ∀ δ' ∈ CongruenceSubgroup.Gamma M, Φ (δ * δ') = Φ δ + Φ δ') →
    (∀ γ ∈ Gam N l, Near (fun δ => slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ (γ * δ * γ⁻¹))) Φ) →
    ∃ M : ℕ, 0 < M ∧ ∀ γ ∈ Gam N l, ∀ δ ∈ CongruenceSubgroup.Gamma M,
      slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ (γ * δ * γ⁻¹)) = Φ δ := by
  intro N l R _ Φ hN hl _ hinv
  obtain ⟨hmul, hone, -, -, -, -, -⟩ := GlobalTheory.T.twoVarPolySubstMatrix_basic_laws R

  let H : ℕ → Subgroup SL(2, ℤ) := fun M =>
    { carrier := {γ | ∀ δ ∈ CongruenceSubgroup.Gamma M,
        slP (γ : Matrix (Fin 2) (Fin 2) ℤ) (Φ (γ * δ * γ⁻¹)) = Φ δ}
      mul_mem' := by
        intro a b ha hb δ hδ
        have hn : b * δ * b⁻¹ ∈ CongruenceSubgroup.Gamma M :=
          (CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ b
        have e : a * b * δ * (a * b)⁻¹ = a * (b * δ * b⁻¹) * a⁻¹ := by group
        show slP ((a * b : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (Φ (a * b * δ * (a * b)⁻¹)) = Φ δ
        rw [e, Matrix.SpecialLinearGroup.coe_mul, hmul, ha _ hn, hb _ hδ]
      one_mem' := by
        intro δ _
        simp only [one_mul, inv_one, mul_one, Matrix.SpecialLinearGroup.coe_one, hone]
      inv_mem' := by
        intro a ha δ hδ
        have hn : a⁻¹ * δ * a⁻¹⁻¹ ∈ CongruenceSubgroup.Gamma M :=
          (CongruenceSubgroup.Gamma_normal M).conj_mem δ hδ a⁻¹
        have h1 := ha _ hn
        have e : a * (a⁻¹ * δ * a⁻¹⁻¹) * a⁻¹ = δ := by group
        rw [e] at h1
        show slP ((a⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (Φ (a⁻¹ * δ * a⁻¹⁻¹)) = Φ δ
        rw [← h1, ← hmul, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one, hone] }
  have Hmono : ∀ {M M' : ℕ}, M ∣ M' → H M ≤ H M' := by
    intro M M' hd γ hγ δ hδ
    exact hγ δ (gamma_le_of_dvd hd hδ)
  haveI : NeZero N := ⟨hN.ne'⟩
  haveI : NeZero l := ⟨hl.ne'⟩
  haveI : Group.FG SL(2, ℤ) := by
    rw [Group.fg_iff]
    exact ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators, Set.toFinite _⟩
  haveI : (Gam N l).FiniteIndex := by unfold Gam; infer_instance
  haveI : Group.FG (Gam N l) := Subgroup.fg_of_index_ne_zero _
  obtain ⟨S, hS⟩ := (Group.fg_def).1 this
  choose Mf hMf hMeq using fun s : Gam N l => hinv s.1 s.2
  let M := ∏ s ∈ S, Mf s
  have hMpos : 0 < M := Finset.prod_pos fun s _ => hMf s
  refine ⟨M, hMpos, ?_⟩
  have hle : Subgroup.closure (S : Set (Gam N l)) ≤ (H M).comap (Gam N l).subtype := by
    rw [Subgroup.closure_le]
    intro s hs
    have hd : Mf s ∣ M := Finset.dvd_prod_of_mem _ hs
    apply Hmono hd
    intro δ hδ
    exact hMeq s δ hδ
  intro γ hγ δ hδ
  have : (⟨γ, hγ⟩ : Gam N l) ∈ Subgroup.closure (S : Set (Gam N l)) := by rw [hS]; trivial
  exact hle this δ hδ

end GlobalTheory.KZ.H3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnitsStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperHalfPlaneCodiscreteGerm_identity_and_units : Nontrivial Mero ∧ (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (a : Mero) = (b : Mero) → ∀ z ∈ Hs, a z = b z) ∧ ∀ a : ℂ → ℂ, DifferentiableOn ℂ a Hs → (a : Mero) ≠ 0 → (∀ᶠ z in Filter.codiscreteWithin Hs, a z ≠ 0) ∧ IsUnit (a : Mero) := by
  first | exact @GlobalTheory.FN.germ_main | exact GlobalTheory.FN.germ_main | (intros; apply GlobalTheory.FN.germ_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneEqZeroOfVanishAboveImStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperHalfPlane_eq_zero_of_vanish_above_im : ∀ (f : ℍ → ℂ) (C : ℝ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → (∀ τ : ℍ, C < τ.im → f τ = 0) → f = 0 := by
  first | exact @GlobalTheory.upperHalfPlane_eq_zero_of_vanish_high | exact GlobalTheory.upperHalfPlane_eq_zero_of_vanish_high | (intros; apply GlobalTheory.upperHalfPlane_eq_zero_of_vanish_high <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrictStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperHalfPlane_germ_ringHom_and_restrict : (∃ A : (ℍ → ℂ) →+* Mero, ∀ f, A f = germ f) ∧ (∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ↔ DifferentiableOn ℂ (up f) Hs) ∧ (∀ a b : ℂ → ℂ, (∀ z ∈ Hs, a z = b z) → (a : Mero) = (b : Mero)) ∧ (∀ a : ℂ → ℂ, germ (fun τ : ℍ => a τ) = (a : Mero)) ∧ ∀ τ : ℍ, (τ : ℂ) ∈ Hs := by
  first | exact @GlobalTheory.FN.germ_ringHom_and_restrict | exact GlobalTheory.FN.germ_ringHom_and_restrict | (intros; apply GlobalTheory.FN.germ_ringHom_and_restrict <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicGermProperties
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
open Filter Topology

namespace GlobalTheory.KZ.Germ

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_Hs : IsPreconnected Hs := (convex_halfSpace_im_gt 0).isPreconnected

theorem eventually_of_germ_eq {φ ψ : ℂ → ℂ} (h : (φ : Mero) = (ψ : Mero)) :
    ∀ τ ∈ Hs, ∀ᶠ z in 𝓝[≠] τ, φ z = ψ z := by
  intro τ hτ
  have h1 := (mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 (Filter.Germ.coe_eq.mp h)) τ hτ
  have h2 : Hs ∈ 𝓝[≠] τ := mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hτ)
  filter_upwards [h1, h2] with z hz1 hz2
  rcases hz1 with hz | hz
  · exact hz
  · exact absurd hz2 hz

theorem eq_zero_or_eq_zero {a b : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (hb : DifferentiableOn ℂ b Hs)
    (h : ∀ z ∈ Hs, a z * b z = 0) : (∀ z ∈ Hs, a z = 0) ∨ (∀ z ∈ Hs, b z = 0) := by
  by_cases hA : ∀ z ∈ Hs, a z = 0
  · exact Or.inl hA
  · right
    push_neg at hA
    obtain ⟨z₀, hz₀, hne⟩ := hA
    have hcont : ContinuousAt a z₀ := (ha.continuousOn).continuousAt (isOpen_Hs.mem_nhds hz₀)
    have hev : ∀ᶠ z in 𝓝 z₀, a z ≠ 0 := hcont.eventually_ne hne
    have hb0 : b =ᶠ[𝓝 z₀] 0 := by
      filter_upwards [hev, isOpen_Hs.mem_nhds hz₀] with z hz1 hz2
      have := h z hz2
      simpa [hz1] using this
    intro z hz
    exact (hb.analyticOnNhd isOpen_Hs).eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_Hs hz₀ hb0 hz

theorem exists_eq_zero_of_prod {ι : Type} [DecidableEq ι] (s : Finset ι) (f : ι → ℂ → ℂ)
    (hf : ∀ i ∈ s, DifferentiableOn ℂ (f i) Hs) (h : ∀ z ∈ Hs, ∏ i ∈ s, f i z = 0) :
    ∃ i ∈ s, ∀ z ∈ Hs, f i z = 0 := by
  induction s using Finset.induction_on with
  | empty =>
    exfalso
    have hI : Complex.I ∈ Hs := by show (0 : ℝ) < Complex.I.im; simp
    simpa using h _ hI
  | insert j s hj ih =>
    have hP : DifferentiableOn ℂ (fun z => ∏ i ∈ s, f i z) Hs := by
      have := DifferentiableOn.finset_prod (u := s) (f := f) (fun i hi => hf i (Finset.mem_insert_of_mem hi))
      rw [show (fun z => ∏ i ∈ s, f i z) = ∏ i ∈ s, f i from by funext z; simp [Finset.prod_apply]]
      exact this
    rcases eq_zero_or_eq_zero (hf j (Finset.mem_insert_self j s)) hP
        (fun z hz => by have := h z hz; rwa [Finset.prod_insert hj] at this) with h1 | h1
    · exact ⟨j, Finset.mem_insert_self j s, h1⟩
    · obtain ⟨i, hi, hi'⟩ := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)) h1
      exact ⟨i, Finset.mem_insert_of_mem hi, hi'⟩

theorem tendsto_mob (g : GQ) {x : ℂ} (hx : x ∈ Hs) : Tendsto (mob g) (𝓝[≠] x) (𝓝[≠] (mob g x)) := by
  obtain ⟨hH, hmul, hone, hdiff, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_basic_laws
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · exact ((hdiff g).continuousOn.continuousAt (isOpen_Hs.mem_nhds hx)).tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hx)] with z hz1 hz2
    intro heq
    apply hz1
    show z = x
    have e1 : mob g⁻¹ (mob g z) = z := by rw [← hmul _ _ z hz2, inv_mul_cancel, hone]
    have e2 : mob g⁻¹ (mob g x) = x := by rw [← hmul _ _ x hx, inv_mul_cancel, hone]
    have : mob g z = mob g x := heq
    rw [← e1, this, e2]

theorem germ_comp (g : GQ) (φ ψ : ℂ → ℂ) (h : (φ : Mero) = (ψ : Mero)) :
    ((fun z => φ (mob g z) : ℂ → ℂ) : Mero) = ((fun z => ψ (mob g z) : ℂ → ℂ) : Mero) := by
  obtain ⟨hH, -, -, -, -, -⟩ := GlobalTheory.T.glTwoPosRatMobius_basic_laws
  apply Filter.Germ.coe_eq.mpr
  apply mem_codiscreteWithin_iff_forall_mem_nhdsNE.2
  intro x hx
  have h1 := (tendsto_mob g hx).eventually (eventually_of_germ_eq h (mob g x) (hH g x hx))
  filter_upwards [h1] with z hz
  exact Or.inl hz

theorem main : (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (((a : Mero) = (b : Mero)) ↔ ∀ z ∈ Hs, a z = b z)) ∧ (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (∀ z ∈ Hs, a z * b z = 0) → (∀ z ∈ Hs, a z = 0) ∨ (∀ z ∈ Hs, b z = 0)) ∧ (∀ (g : GQ) (φ ψ : ℂ → ℂ), (φ : Mero) = (ψ : Mero) → ((fun z => φ (mob g z) : ℂ → ℂ) : Mero) = ((fun z => ψ (mob g z) : ℂ → ℂ) : Mero)) ∧ (∀ (φ ψ : ℂ → ℂ), (φ : Mero) = (ψ : Mero) → ∀ τ ∈ Hs, ∀ᶠ z in nhdsWithin τ {τ}ᶜ, φ z = ψ z) ∧ (∀ (m : ℕ) (a b : ℂ → ℂ), 0 < m → DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (∀ z ∈ Hs, a z ^ m = b z ^ m) → ∃ k : ℕ, ∀ z ∈ Hs, a z = Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ)) * b z) := by
  refine ⟨?_, fun a b ha hb h => eq_zero_or_eq_zero ha hb h, germ_comp, fun φ ψ h => eventually_of_germ_eq h, ?_⟩
  · intro a b ha hb
    constructor
    · intro hab z hz
      have hI : Complex.I ∈ Hs := by show (0 : ℝ) < Complex.I.im; simp
      exact (ha.analyticOnNhd isOpen_Hs).eqOn_of_preconnected_of_frequently_eq (hb.analyticOnNhd isOpen_Hs)
        isPreconnected_Hs hI (eventually_of_germ_eq hab _ hI).frequently hz
    · intro h
      apply Filter.Germ.coe_eq.mpr
      filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
      exact h z hz
  · intro m a b hm ha hb h
    have hm0 : m ≠ 0 := hm.ne'
    haveI : NeZero m := ⟨hm0⟩
    have hζ := Complex.isPrimitiveRoot_exp m hm0
    obtain ⟨ξ, hξ, hξ'⟩ := exists_eq_zero_of_prod (Polynomial.nthRootsFinset m (1 : ℂ)) (fun ξ z => a z - ξ * b z)
      (fun ξ _ => ha.sub (hb.const_mul ξ))
      (fun z hz => by rw [← hζ.pow_sub_pow_eq_prod_sub_mul (a z) (b z) hm, h z hz, sub_self])
    have hξm : ξ ^ m = 1 := (Polynomial.mem_nthRootsFinset hm (1 : ℂ)).1 hξ
    obtain ⟨k, -, hk⟩ := hζ.eq_pow_of_pow_eq_one hξm
    refine ⟨k, fun z hz => ?_⟩
    have e : Complex.exp (2 * Real.pi * Complex.I * (k : ℂ) / (m : ℂ)) = ξ := by
      rw [← hk, ← Complex.exp_nat_mul]; congr 1; ring
    rw [e]
    exact sub_eq_zero.mp (hξ' z hz)

end GlobalTheory.KZ.Germ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicMulEqZeroIffStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.upperHalfPlane_holomorphic_mul_eq_zero_iff : ∀ f g : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g → (∀ τ, f τ * g τ = 0) → f = 0 ∨ g = 0 := by
  first | exact @GlobalTheory.fn_mul_eq_zero_dom | exact GlobalTheory.fn_mul_eq_zero_dom | (intros; apply GlobalTheory.fn_mul_eq_zero_dom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringNonunitsPowModEqZeroStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuationSubring_nonunits_pow_modEq_zero : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ x ∈ A.nonunits, ∃ k : ℕ, CgA A l 1 (x ^ k) 0 := by
  first | exact @GlobalTheory.cgA_pow_of_mem_nonunits | exact GlobalTheory.cgA_pow_of_mem_nonunits | (intros; apply GlobalTheory.cgA_pow_of_mem_nonunits <;> assumption)
end

