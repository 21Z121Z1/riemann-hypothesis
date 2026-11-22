import Mathlib
import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula
import Formalism.GL3MeanSquares.Bundle0001
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0090
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0089
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringLeOfResidueIndependent
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WhittakerTranslatesCornerLinearIndependent
import Development.AbelianVarietyTheory.Definitions.Foundations.StandardFiveNontrivial

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TailAndSumBound
section
open Finset Filter Topology

namespace GlobalTheory.GoodCharacterTail

open Formalism.HermitianLattices.GL2PrimeSums

theorem tail_le (a : ℕ → ℂ) (S : ℂ)
    (hS : Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, a n / (n : ℂ)) atTop (𝓝 S))
    (Z B : ℝ) (hZ : 1 ≤ Z)
    (hB : ∀ U : ℝ, Z ≤ U → ‖psum a Z‖ / Z + (∫ u in Z..U, ‖psum a u‖ / u ^ 2) ≤ B) :
    ‖S - ∑ n ∈ Icc 1 ⌊Z⌋₊, a n / (n : ℂ)‖ ≤ B := by
  obtain ⟨I, hI, hG⟩ := GlobalTheory.TailIntegralOfSummatory.tail_integral a S hS Z hZ
  have hZ0 : (0 : ℝ) < Z := by linarith
  have hZc : (Z : ℂ) ≠ 0 := by exact_mod_cast hZ0.ne'
  have h1 : Gchi a S Z = Z * (∑ n ∈ Icc 1 ⌊Z⌋₊, a n / (n : ℂ)) - psum a Z - Z * S := by
    unfold Gchi psum
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    congr 1
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  have h2 : S - ∑ n ∈ Icc 1 ⌊Z⌋₊, a n / (n : ℂ) = I - psum a Z / Z := by
    rw [h1] at hG
    field_simp
    linear_combination -hG
  have h3 : ‖I‖ ≤ B - ‖psum a Z‖ / Z := by
    refine le_of_tendsto hI.norm ?_
    filter_upwards [eventually_ge_atTop Z] with U hU
    have h4 := intervalIntegral.norm_integral_le_integral_norm
      (f := fun u : ℝ => psum a u / (u : ℂ) ^ 2) (μ := MeasureTheory.volume) hU
    have h5 : (fun u : ℝ => ‖psum a u / (u : ℂ) ^ 2‖) = fun u : ℝ => ‖psum a u‖ / u ^ 2 := by
      funext u
      rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [h5] at h4
    have := hB U hU
    linarith
  rw [h2]
  have h6 := norm_sub_le I (psum a Z / Z)
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hZ0] at h6
  linarith

theorem eventually_log_le (k δ : ℝ) (hk : 0 < k) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, Real.log x ≤ k * x ^ δ := by
  have h := (isLittleO_log_rpow_atTop hδ).bound hk
  filter_upwards [h, eventually_ge_atTop (0 : ℝ)] with x hx hx0
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 _)] at hx
  exact (le_abs_self _).trans hx

theorem tail_and_sum_bound : Formalism.HermitianLattices.GL2PrimeSums.TailSumBound := by
  intro ε hε hε1 C₁ c₁ CM hC₁ hc₁ hCM
  obtain ⟨C, c, hC, hc, hZ⟩ := GlobalTheory.T.gl2a2_integral_bound_of_sums C₁ c₁ hC₁ hc₁
  have e1 := eventually_log_le (1 / 400) (ε / 4) (by norm_num) (by linarith)
  have e2 := eventually_log_le c (ε / 6) hc (by linarith)
  have e3 := (tendsto_rpow_atTop (show 0 < ε / 2 by linarith)).eventually_ge_atTop (5 * C)
  have e4 := (tendsto_rpow_atTop (show 0 < ε / 6 by linarith)).eventually_ge_atTop 2
  have e5 := Real.tendsto_log_atTop.eventually_ge_atTop 1
  have e6 := eventually_ge_atTop (2 : ℝ)
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and (e4.and (e5.and e6)))))
  refine ⟨x₀, 400 + CM + 1, ?_⟩
  intro x hx Q hQ hQ1 hQ2 a S hS hM H1 H2
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hx₀ x hx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hQ3 : 3 ≤ Q := by
    have h := Real.add_one_le_exp (Real.log Q)
    rw [Real.exp_log hQ] at h
    linarith
  have hz2 : 2 ≤ x ^ (400 : ℝ) := by
    have : x ^ (1 : ℝ) ≤ x ^ (400 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
    rw [Real.rpow_one] at this
    linarith
  have hlz : Real.log (x ^ (400 : ℝ)) = 400 * Real.log x := Real.log_rpow hx0 _
  have ht := tail_le a S hS (x ^ (400 : ℝ)) _ (by linarith)
    (fun U hU => hZ Q a hQ3 H1 H2 _ U hz2 hU)
  have hp : (x ^ (400 : ℝ)) ^ (-(1 : ℝ) / 400) = x⁻¹ := by
    rw [← Real.rpow_mul hx0.le, ← Real.rpow_neg_one]
    norm_num
  have hl : Real.log (x ^ (400 : ℝ) * Q) = 400 * Real.log x + Real.log Q := by
    rw [Real.log_mul (by positivity) hQ.ne', hlz]
  rw [hp, hl] at ht
  have hsq : x ^ (ε / 4) * x ^ (ε / 4) = x ^ (ε / 2) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hsq2 : x ^ (ε / 2) * x ^ (ε / 2) = x ^ ε := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hL : (400 * Real.log x + Real.log Q) ^ 2 ≤ 4 * x ^ (ε / 2) := by
    have a1 : 0 ≤ 400 * Real.log x + Real.log Q := by linarith
    have a2 : 400 * Real.log x + Real.log Q ≤ 2 * x ^ (ε / 4) := by linarith
    have := pow_le_pow_left₀ a1 a2 2
    nlinarith
  have hQc : x * Q ^ (-c) ≤ 1 := by
    rw [Real.rpow_def_of_pos hQ]
    nth_rewrite 1 [← Real.exp_log hx0]
    rw [← Real.exp_add, Real.exp_le_one_iff]
    have := mul_le_mul_of_nonneg_left hQ1 hc.le
    linarith
  have h1e : 1 ≤ x ^ (ε / 2) := Real.one_le_rpow hx1 (by linarith)
  have key : x * ‖S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ x ^ ε := by
    have b1 := mul_le_mul_of_nonneg_left ht hx0.le
    have b2 : x * (C * (x⁻¹ * (400 * Real.log x + Real.log Q) ^ 2 + Q ^ (-c))) =
        C * ((400 * Real.log x + Real.log Q) ^ 2 + x * Q ^ (-c)) := by
      field_simp
    rw [b2] at b1
    have b3 : C * ((400 * Real.log x + Real.log Q) ^ 2 + x * Q ^ (-c)) ≤ C * (5 * x ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC.le
    have b4 : 5 * C * x ^ (ε / 2) ≤ x ^ (ε / 2) * x ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right f3 (by linarith)
    linarith
  refine ⟨?_, ?_⟩
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hx0]
    exact key
  · have c1 : x ^ ε ≤ x := by
      have : x ^ ε ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 hε1.le
      rwa [Real.rpow_one] at this
    have c2 : ‖S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ 1 := by
      have : x * ‖S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ x * 1 := by linarith
      exact le_of_mul_le_mul_left this hx0
    have c3 : ‖∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ)‖ ≤ 400 * Real.log x + CM := by
      rw [← hlz]
      refine le_trans ((norm_sum_le _ _).trans (le_of_eq ?_)) (hM _ (by linarith))
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [norm_div, Complex.norm_natCast]
    have c4 := norm_add_le (S - ∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ))
      (∑ n ∈ Icc 1 ⌊x ^ (400 : ℝ)⌋₊, a n / (n : ℂ))
    rw [sub_add_cancel] at c4
    nlinarith

end GlobalTheory.GoodCharacterTail
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoDimRepQuadraticRelationStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.two_dim_rep_quadratic_relation : ∀ {E : Type} [Field E] [IsAlgClosed E], (2 : E) ≠ 0 → ∀ {G : Type} [Group G] (ρ : G →* GL (Fin 2) E), (∀ W : Submodule E (Fin 2 → E), (∀ g w, w ∈ W → (ρ g : Matrix (Fin 2) (Fin 2) E) *ᵥ w ∈ W) → W = ⊥ ∨ W = ⊤) → ∀ {U : Type} [AddCommGroup U] [Module E U] [FiniteDimensional E U] (σ : G →* Module.End E U), (∀ g, σ g * σ g - Matrix.trace (ρ g : Matrix (Fin 2) (Fin 2) E) • σ g + Matrix.det (ρ g : Matrix (Fin 2) (Fin 2) E) • (1 : Module.End E U) = 0) → ∃ (m : ℕ) (π : Fin m → U →ₗ[E] (Fin 2 → E)) (s : Fin m → (Fin 2 → E) →ₗ[E] U), (∀ i g, π i ∘ₗ σ g = Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) E) ∘ₗ π i) ∧ (∀ i g, σ g ∘ₗ s i = s i ∘ₗ Matrix.toLin' (ρ g : Matrix (Fin 2) (Fin 2) E)) ∧ (∀ i j, π i ∘ₗ s j = if i = j then LinearMap.id else 0) ∧ ∑ i, s i ∘ₗ π i = LinearMap.id := by
  first | exact @GlobalTheory.CayleyHamiltonId.isotypic_of_quadratic_relation | exact GlobalTheory.CayleyHamiltonId.isotypic_of_quadratic_relation | (intros; apply GlobalTheory.CayleyHamiltonId.isotypic_of_quadratic_relation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwoVarPolySubstMatrixBasicLawsStatement
section
open GlobalTheory.KZ GlobalTheory.KZ.H3 Matrix
open scoped MatrixGroups TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoVarPolySubstMatrix_basic_laws : ∀ (R : Type) [CommRing R], (∀ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), slP (m * m') p = slP m' (slP m p)) ∧ (∀ p : MvPolynomial (Fin 2) R, slP 1 p = p) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (w : ℕ) (p : MvPolynomial (Fin 2) R), p.IsHomogeneous w → (slP m p).IsHomogeneous w) ∧ (∀ (m : Matrix (Fin 2) (Fin 2) ℤ) (u : Fin 2 → R) (p : MvPolynomial (Fin 2) R), MvPolynomial.eval u (slP m p) = MvPolynomial.eval (m.map (Int.castRingHom R) *ᵥ u) p) ∧ (∀ (S : Type) [CommRing S] (f : R →+* S) (m : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), MvPolynomial.map f (slP m p) = slP m (MvPolynomial.map f p)) ∧ (∀ (m m' : Matrix (Fin 2) (Fin 2) ℤ) (p : MvPolynomial (Fin 2) R), (∀ i j, (m i j : R) = (m' i j : R)) → slP m p = slP m' p) ∧ (∀ (w : ℕ) (p : MvPolynomial (Fin 2) R), p.IsHomogeneous w → slP (-1) p = (-1 : R) ^ w • p) := by
  first | exact @GlobalTheory.KZ.polySlash_laws | exact GlobalTheory.KZ.polySlash_laws | (intros; apply GlobalTheory.KZ.polySlash_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnits
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)
open Filter Topology

namespace GlobalTheory.FN

theorem isOpen_Hs : IsOpen Hs := isOpen_lt continuous_const Complex.continuous_im

theorem isPreconnected_Hs : IsPreconnected Hs := (convex_halfSpace_im_gt 0).isPreconnected

theorem codiscreteWithin_Hs_neBot : (Filter.codiscreteWithin Hs).NeBot := by
  rw [Filter.neBot_iff]
  intro h
  have h0 : (∅ : Set ℂ) ∈ Filter.codiscreteWithin Hs := h ▸ Filter.mem_bot
  rw [mem_codiscreteWithin_iff_forall_mem_nhdsNE] at h0
  have hI : Complex.I ∈ Hs := by show (0 : ℝ) < Complex.I.im; simp
  have h1 := h0 Complex.I hI
  rw [Set.empty_union] at h1
  have h2 : Hs ∈ 𝓝[≠] Complex.I := mem_nhdsWithin_of_mem_nhds (isOpen_Hs.mem_nhds hI)
  have h3 : (∅ : Set ℂ) ∈ 𝓝[≠] Complex.I := by
    have := Filter.inter_mem h2 h1
    simpa using this
  exact (Filter.empty_mem_iff_bot.mp h3 ▸ (inferInstance : (𝓝[≠] Complex.I).NeBot)).ne rfl

theorem eqOn_zero_of_germ_eq_zero {a : ℂ → ℂ} (ha : DifferentiableOn ℂ a Hs) (h0 : (a : Mero) = 0) :
    ∀ z ∈ Hs, a z = 0 := by
  haveI := codiscreteWithin_Hs_neBot
  have han : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs
  rcases han.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_Hs with h | h
  · exact fun z hz => h hz
  · exfalso
    have he : a =ᶠ[Filter.codiscreteWithin Hs] (0 : ℂ → ℂ) := Filter.Germ.coe_eq.mp h0
    obtain ⟨z, hz1, hz2⟩ := (h.and he).exists
    exact hz1 hz2

theorem germ_main : Nontrivial Mero ∧ (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (a : Mero) = (b : Mero) → ∀ z ∈ Hs, a z = b z) ∧ ∀ a : ℂ → ℂ, DifferentiableOn ℂ a Hs → (a : Mero) ≠ 0 → (∀ᶠ z in Filter.codiscreteWithin Hs, a z ≠ 0) ∧ IsUnit (a : Mero) := by
  haveI := codiscreteWithin_Hs_neBot
  refine ⟨inferInstance, ?_, ?_⟩
  · intro a b ha hb hab z hz
    have h0 : ((a - b : ℂ → ℂ) : Mero) = 0 := by
      rw [Filter.Germ.coe_sub, hab, sub_self]
    have := eqOn_zero_of_germ_eq_zero (ha.sub hb) h0 z hz
    simpa [sub_eq_zero] using this
  · intro a ha hne
    have han : AnalyticOnNhd ℂ a Hs := ha.analyticOnNhd isOpen_Hs
    have hev : ∀ᶠ z in Filter.codiscreteWithin Hs, a z ≠ 0 := by
      rcases han.eqOn_zero_or_eventually_ne_zero_of_preconnected isPreconnected_Hs with h | h
      · exfalso
        apply hne
        rw [← Filter.Germ.coe_zero, Filter.Germ.coe_eq]
        filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
        exact h hz
      · exact h
    refine ⟨hev, ?_⟩
    refine ⟨⟨(a : Mero), ((fun z => (a z)⁻¹ : ℂ → ℂ) : Mero), ?_, ?_⟩, rfl⟩
    · rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq]
      filter_upwards [hev] with z hz
      simp [hz]
    · rw [← Filter.Germ.coe_mul, ← Filter.Germ.coe_one, Filter.Germ.coe_eq]
      filter_upwards [hev] with z hz
      simp [hz]

example : Nontrivial Mero ∧ (∀ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs → DifferentiableOn ℂ b Hs → (a : Mero) = (b : Mero) → ∀ z ∈ Hs, a z = b z) ∧ ∀ a : ℂ → ℂ, DifferentiableOn ℂ a Hs → (a : Mero) ≠ 0 → (∀ᶠ z in Filter.codiscreteWithin Hs, a z ≠ 0) ∧ IsUnit (a : Mero) := germ_main

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneEqZeroOfVanishAboveIm
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem upperHalfPlane_eq_zero_of_vanish_high :
    ∀ (f : ℍ → ℂ) (C : ℝ), MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f →
      (∀ τ : ℍ, C < τ.im → f τ = 0) → f = 0 := by
  intro f C hf hC
  have hd : DifferentiableOn ℂ (f ∘ UpperHalfPlane.ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp hf
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have han := hd.analyticOnNhd hopen
  have hpc : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  set z₀ : ℂ := ((|C| + 1 : ℝ) : ℂ) * Complex.I with hz₀
  have hz₀im : z₀.im = |C| + 1 := by simp [hz₀]
  have hmem : z₀ ∈ {z : ℂ | 0 < z.im} := by
    show 0 < z₀.im
    rw [hz₀im]; positivity
  have hev : (f ∘ UpperHalfPlane.ofComplex) =ᶠ[nhds z₀] 0 := by
    have hopen2 : IsOpen {z : ℂ | max C 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
    have hin : z₀ ∈ {z : ℂ | max C 0 < z.im} := by
      show max C 0 < z₀.im
      rw [hz₀im]
      have := le_abs_self C
      have := abs_nonneg C
      exact max_lt (by linarith) (by linarith)
    filter_upwards [hopen2.mem_nhds hin] with z hz
    have hz' : max C 0 < z.im := hz
    have h0 : 0 < z.im := lt_of_le_of_lt (le_max_right _ _) hz'
    have h1 : C < z.im := lt_of_le_of_lt (le_max_left _ _) hz'
    simp only [Function.comp_apply, Pi.zero_apply, UpperHalfPlane.ofComplex_apply_of_im_pos h0]
    exact hC _ h1
  have heq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpc hmem hev
  funext τ
  have := heq (show (τ : ℂ) ∈ {z : ℂ | 0 < z.im} from τ.im_pos)
  simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrict
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem FN.germ_ringHom_and_restrict : (∃ A : (ℍ → ℂ) →+* Mero, ∀ f, A f = germ f) ∧ (∀ f : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ↔ DifferentiableOn ℂ (up f) Hs) ∧ (∀ a b : ℂ → ℂ, (∀ z ∈ Hs, a z = b z) → (a : Mero) = (b : Mero)) ∧ (∀ a : ℂ → ℂ, germ (fun τ : ℍ => a τ) = (a : Mero)) ∧ ∀ τ : ℍ, (τ : ℂ) ∈ Hs := by
  refine ⟨⟨(Filter.Germ.coeRingHom _).comp (Pi.ringHom fun z => Pi.evalRingHom (fun _ : ℍ => ℂ) (UpperHalfPlane.ofComplex z)), fun f => rfl⟩, fun f => ?_, ?_, ?_, fun τ => τ.2⟩
  · exact UpperHalfPlane.mdifferentiable_iff
  · intro a b h
    rw [Filter.Germ.coe_eq]
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz using h z hz
  · intro a
    unfold germ up
    rw [Filter.Germ.coe_eq]
    filter_upwards [Filter.self_mem_codiscreteWithin Hs] with z hz
    simp [UpperHalfPlane.ofComplex_apply_of_im_pos hz]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneHolomorphicMulEqZeroIff
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory

theorem fn_mul_eq_zero_dom : ∀ f g : ℍ → ℂ, MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g → (∀ τ, f τ * g τ = 0) → f = 0 ∨ g = 0 := by
  intro f g hf hg hfg
  have hF := (UpperHalfPlane.mdifferentiable_iff.mp hf).analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hG := (UpperHalfPlane.mdifferentiable_iff.mp hg).analyticOnNhd UpperHalfPlane.isOpen_upperHalfPlaneSet
  have hU : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have hne : ({z : ℂ | 0 < z.im}).Nonempty := ⟨Complex.I, by simp⟩
  rcases AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero hF hG (fun z _ => by simp [Function.comp_apply, hfg]) hU with h | h
  · left
    funext τ
    have := h (τ : ℂ) τ.im_pos
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using this
  · right
    funext τ
    have := h (τ : ℂ) τ.im_pos
    simpa [Function.comp_apply, UpperHalfPlane.ofComplex_apply] using this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringLeOfResidueIndependentStatement
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuationSubring_le_of_residue_independent : ∀ {F : Type} [Field F] {L : Type} [Field L] [Algebra F L] (t : L) (V : ValuationSubring F) (Φ : Polynomial (Polynomial F)) (ω : L), Φ.Monic → (∀ i j, (Φ.coeff i).coeff j ∈ V) → Φ.eval₂ (Polynomial.aeval t).toRingHom ω = 0 → (∀ x : L, ∃ Q : Polynomial F, Q ≠ 0 ∧ ∃ R : Polynomial (Polynomial F), Polynomial.aeval t Q * x = R.eval₂ (Polynomial.aeval t).toRingHom ω) → ∀ W₁ W₂ : ValuationSubring L, ((∀ a : F, algebraMap F L a ∈ W₁ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W₁.valuation (Polynomial.aeval t P) = 1)) → ((∀ a : F, algebraMap F L a ∈ W₂ ↔ a ∈ V) ∧ (∀ P : Polynomial F, (∀ i, P.coeff i ∈ V) → (∃ i, P.coeff i ≠ 0 ∧ P.coeff i ∈ V ∧ (P.coeff i)⁻¹ ∈ V) → W₂.valuation (Polynomial.aeval t P) = 1)) → (∀ R : Polynomial (Polynomial F), R.natDegree < Φ.natDegree → (∀ i j, (R.coeff i).coeff j ∈ V) → R.eval₂ (Polynomial.aeval t).toRingHom ω ∈ W₁.nonunits → ∀ i j, (R.coeff i).coeff j ∈ V.nonunits) → W₁ ≤ W₂ := by
  first | exact @GlobalTheory.BertiniNoether.le_of_residue_independent | exact GlobalTheory.BertiniNoether.le_of_residue_independent | (intros; apply GlobalTheory.BertiniNoether.le_of_residue_independent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationSubringNonunitsPowModEqZero
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory

open Polynomial in

theorem cgA_pow_of_mem_nonunits {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (l : ℕ)
    [hl : Fact l.Prime] (A : ValuationSubring Ω) (hlA : ((l : ℕ) : Ω) ∈ A.nonunits)
    (x : Ω) (hx : x ∈ A.nonunits) : ∃ k : ℕ, CgA A l 1 (x ^ k) 0 := by
  classical
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap ℚ Ω).injective
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  have hl0 : ((l : ℕ) : Ω) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  have hvl : A.valuation (l : Ω) < 1 := (A.mem_nonunits_iff).1 hlA
  have hvx : A.valuation x < 1 := (A.mem_nonunits_iff).1 hx
  have hvl0 : A.valuation (l : Ω) ≠ 0 := by simpa using hl0
  have key : ∀ k : ℕ, A.valuation x ^ k ≤ A.valuation (l : Ω) → CgA A l 1 (x ^ k) 0 := by
    intro k hk
    refine ⟨x ^ k / l, ?_, ?_⟩
    · rw [← A.valuation_le_one_iff, map_div₀, map_pow]
      exact (div_le_one₀ (zero_lt_iff.2 hvl0)).2 hk
    · rw [sub_zero, pow_one]; field_simp
  by_contra H
  push_neg at H
  have hlt : ∀ k : ℕ, A.valuation (l : Ω) < A.valuation x ^ k :=
    fun k => not_le.1 (fun h => H k (key k h))
  have hx0 : x ≠ 0 := by
    intro h
    have := hlt 1
    simp [h] at this
  have hvx0 : A.valuation x ≠ 0 := by simpa using hx0

  have hint : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n =>
    (A.valuation_le_one_iff _).2 (intCast_mem A n)
  have hdvd : ∀ n : ℤ, (l : ℤ) ∣ n → A.valuation (n : Ω) ≤ A.valuation (l : Ω) := by
    rintro n ⟨m, rfl⟩
    push_cast
    rw [map_mul]
    exact mul_le_of_le_one_right' (hint m)
  have hpl : Prime (l : ℤ) := Nat.prime_iff_prime_int.mp hl.out
  have hunit : ∀ n : ℤ, ¬ (l : ℤ) ∣ n → A.valuation (n : Ω) = 1 := by
    intro n hn
    refine le_antisymm (hint n) (not_lt.1 fun h => ?_)
    obtain ⟨a, b, hab⟩ := (Prime.coprime_iff_not_dvd hpl).2 hn
    have h1 : ((a : Ω) * (l : Ω) + (b : Ω) * (n : Ω)) = 1 := by exact_mod_cast hab
    have h2 : A.valuation ((a : Ω) * (l : Ω) + (b : Ω) * (n : Ω)) < 1 := by
      apply Valuation.map_add_lt
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint a)) hvl
      · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint b)) h
    rw [h1, map_one] at h2
    exact lt_irrefl _ h2

  obtain ⟨p, hp0, hpx⟩ := (IsFractionRing.isAlgebraic_iff ℤ ℚ Ω).2 (Algebra.IsAlgebraic.isAlgebraic x)
  set q := p.primPart with hqdef
  have hqprim : q.IsPrimitive := isPrimitive_primPart p
  have hqx : aeval x q = 0 := by
    have hc : p.content ≠ 0 := by
      intro h; exact hp0 ((content_eq_zero_iff).1 h)
    have h := hpx
    rw [eq_C_content_mul_primPart p, map_mul, aeval_C] at h
    rcases mul_eq_zero.1 h with h' | h'
    · exfalso; apply hc; simpa using h'
    · exact h'
  have hex : ∃ i, ¬ (l : ℤ) ∣ q.coeff i := by
    by_contra h
    push_neg at h
    have hu := hqprim (l : ℤ) ((C_dvd_iff_dvd_coeff _ _).2 h)
    exact hpl.not_unit hu
  set i0 := Nat.find hex with hi0
  have hi0spec : ¬ (l : ℤ) ∣ q.coeff i0 := Nat.find_spec hex
  have hi0min : ∀ i < i0, (l : ℤ) ∣ q.coeff i := fun i hi => by
    simpa using Nat.find_min hex hi
  have hi0deg : i0 < q.natDegree + 1 := by
    by_contra h
    apply hi0spec
    rw [coeff_eq_zero_of_natDegree_lt (by omega)]
    exact dvd_zero _
  set f : ℕ → Ω := fun i => (q.coeff i : Ω) * x ^ i with hf
  have hsum : aeval x q = ∑ i ∈ Finset.range (q.natDegree + 1), f i := by
    rw [aeval_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hf, zsmul_eq_mul]
  have hfi0 : A.valuation (f i0) = A.valuation x ^ i0 := by
    simp only [hf, map_mul, map_pow, hunit _ hi0spec, one_mul]
  have hg : A.valuation x ^ i0 ≠ 0 := pow_ne_zero _ hvx0
  have hrest : A.valuation (∑ i ∈ (Finset.range (q.natDegree + 1)).erase i0, f i)
      < A.valuation x ^ i0 := by
    apply Valuation.map_sum_lt _ hg
    intro i hi
    have hne : i ≠ i0 := Finset.ne_of_mem_erase hi
    simp only [hf, map_mul, map_pow]
    rcases lt_or_gt_of_ne hne with h | h
    · calc A.valuation (q.coeff i : Ω) * A.valuation x ^ i
            ≤ A.valuation (l : Ω) * 1 :=
              mul_le_mul' (hdvd _ (hi0min i h)) (pow_le_one₀ zero_le' hvx.le)
        _ = A.valuation (l : Ω) := mul_one _
        _ < A.valuation x ^ i0 := hlt i0
    · calc A.valuation (q.coeff i : Ω) * A.valuation x ^ i
            ≤ 1 * A.valuation x ^ i := mul_le_mul' (hint _) le_rfl
        _ = A.valuation x ^ i := one_mul _
        _ < A.valuation x ^ i0 := pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 hvx0) hvx h
  have htot : A.valuation (aeval x q) = A.valuation x ^ i0 := by
    rw [hsum, ← Finset.add_sum_erase _ _ (Finset.mem_range.2 hi0deg),
      Valuation.map_add_eq_of_lt_left _ (by rw [hfi0]; exact hrest), hfi0]
  rw [hqx, map_zero] at htot
  exact hg htot.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WhittakerTranslatesCornerLinearIndependentStatement
section
open Polynomial Classical GlobalTheory.BadShare
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.whittaker_translates_corner_linearIndependent : ∀ (g : ℕ) [Fact g.Prime] (N : ℕ), ∀ (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (ρ : Representation ℂ (GG g N) M), ∀ (L : Lev g N), L.sharp = false → ∀ (x : M), x ≠ 0 → (∀ u, IsUp g N u → ρ u x = L.chi u • x) → ∀ k : ℕ, k < N → ∀ φ : GG g N → ℂ, (∀ h, φ h ≠ 0 → (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (h : GG g N).val a b = if a = b then 1 else 0)) → ∑ h, φ h • ρ h x = 0 → ∀ h₀ : GG g N, ∑ u ∈ Finset.univ.filter (fun u : GG g N => IsUp g N u ∧ (∀ a b : Fin N, (k ≤ (a : ℕ) ∨ k ≤ (b : ℕ)) → (u : GG g N).val a b = if a = b then 1 else 0)), φ (h₀ * u) * L.chi u = 0 := by
  first | exact @GlobalTheory.BadShare.Indep.translates_independent | exact GlobalTheory.BadShare.Indep.translates_independent | (intros; apply GlobalTheory.BadShare.Indep.translates_independent <;> assumption)
end

