import Mathlib
import ReciprocityTheory.AnalyticForms.MaIntEmpty
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.LeviLine
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm Filter Topology Polynomial

noncomputable section

section Line

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fderiv_fderiv_apply_eq_deriv_deriv {φ : E → ℝ} (hφ : ContDiffAt ℝ 2 φ 0) (v : E) :
    fderiv ℝ (fderiv ℝ φ) 0 v v = deriv (deriv fun t : ℝ => φ (t • v)) 0 := by
  have hev : ∀ᶠ y in 𝓝 (0 : E), DifferentiableAt ℝ φ y :=
    (hφ.eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have hlin : ∀ t : ℝ, HasDerivAt (fun t : ℝ => t • v) v t := fun t => by
    simpa using (hasDerivAt_id t).smul_const v
  have hline : Tendsto (fun t : ℝ => t • v) (𝓝 0) (𝓝 0) := by
    have : Continuous fun t : ℝ => t • v := continuous_id.smul continuous_const
    simpa using this.tendsto 0
  have hder : (deriv fun t : ℝ => φ (t • v)) =ᶠ[𝓝 0] fun t => fderiv ℝ φ (t • v) v := by
    filter_upwards [hline.eventually hev] with t ht
    exact (ht.hasFDerivAt.comp_hasDerivAt t (hlin t)).deriv
  rw [hder.deriv_eq]
  have h2 : DifferentiableAt ℝ (fderiv ℝ φ) 0 :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have h3 : HasDerivAt ((fderiv ℝ φ) ∘ fun t : ℝ => t • v) (fderiv ℝ (fderiv ℝ φ) 0 v) 0 :=
    h2.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hlin 0) (by simp)
  have h4 := h3.clm_apply (hasDerivAt_const (0 : ℝ) v)
  simpa using h4.deriv.symm

end Line

section Levi

variable {ι : Type*} [Fintype ι]

theorem levi_finset_sum {κ : Type*} (s : Finset κ) (F : κ → (ι → ℂ) → ℝ)
    (hF : ∀ j ∈ s, ContDiffAt ℝ 2 (F j) 0) (w : ι → ℂ) :
    levi (fun z => ∑ j ∈ s, F j z) 0 w = ∑ j ∈ s, levi (F j) 0 w := by
  have hev : ∀ᶠ z in 𝓝 (0 : ι → ℂ), ∀ j ∈ s, DifferentiableAt ℝ (F j) z := by
    rw [Filter.eventually_all_finset]
    intro j hj
    exact ((hF j hj).eventually (by simp)).mono fun y hy => hy.differentiableAt (by simp)
  have h1 : fderiv ℝ (fun z => ∑ j ∈ s, F j z) =ᶠ[𝓝 0] fun z => ∑ j ∈ s, fderiv ℝ (F j) z := by
    filter_upwards [hev] with z hz
    simpa only [Finset.sum_fn] using fderiv_sum hz
  have h2 : fderiv ℝ (fderiv ℝ fun z => ∑ j ∈ s, F j z) 0 =
      ∑ j ∈ s, fderiv ℝ (fderiv ℝ (F j)) 0 := by
    rw [h1.fderiv_eq]
    simpa only [Finset.sum_fn] using fderiv_sum fun j hj =>
      ((hF j hj).fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  simp only [levi, h2, _root_.sum_apply]
  rw [← Finset.sum_add_distrib, Finset.sum_div]

theorem levi_eq_deriv_deriv {φ : (ι → ℂ) → ℝ} (hφ : ContDiffAt ℝ 2 φ 0) (w : ι → ℂ) :
    levi φ 0 w = (deriv (deriv fun t : ℝ => φ (t • w)) 0 +
      deriv (deriv fun t : ℝ => φ (t • (Complex.I • w))) 0) / 4 := by
  simp only [levi, fderiv_fderiv_apply_eq_deriv_deriv hφ]

end Levi

section LogPoly

theorem deriv_deriv_log_norm_eval (Q : ℂ[X]) (h0 : Q.coeff 0 = 1) (h1 : Q.coeff 1 = 0) :
    deriv (deriv fun t : ℝ => Real.log ‖Q.eval (t : ℂ)‖) 0 = 2 * (Q.coeff 2).re := by
  set f : ℝ → ℂ := fun t => Q.eval (t : ℂ) with hfdef
  have hf : ∀ t : ℝ, HasDerivAt f (Q.derivative.eval (t : ℂ)) t := fun t =>
    (Q.hasDerivAt (t : ℂ)).comp_ofReal
  have hf' : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Q.derivative.eval (t : ℂ))
      (Q.derivative.derivative.eval (t : ℂ)) t := fun t =>
    (Q.derivative.hasDerivAt (t : ℂ)).comp_ofReal
  have hf0 : f 0 = 1 := by simp [f, ← Polynomial.coeff_zero_eq_eval_zero, h0]
  have hslit : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ Complex.slitPlane := by
    have hc : Continuous f := Q.continuous.comp Complex.continuous_ofReal
    exact hc.continuousAt.eventually
      (Complex.isOpen_slitPlane.mem_nhds (by rw [hf0]; exact Complex.one_mem_slitPlane))
  have hD : (deriv fun t : ℝ => Real.log ‖f t‖) =ᶠ[𝓝 0]
      fun t => Complex.reCLM (Q.derivative.eval (t : ℂ) / f t) := by
    filter_upwards [hslit] with t ht
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t ((hf t).clog_real ht)
    have he : (fun t : ℝ => Real.log ‖f t‖) = Complex.reCLM ∘ fun t => Complex.log (f t) := by
      funext t; simp [Complex.log_re]
    rw [he]; exact h2.deriv
  rw [hD.deriv_eq]
  have hq := (hf' 0).div (hf 0) (by rw [hf0]; exact one_ne_zero)
  have h3 := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hq
  rw [show (fun t : ℝ => Complex.reCLM (Q.derivative.eval (t : ℂ) / f t)) =
    Complex.reCLM ∘ ((fun t : ℝ => Q.derivative.eval (t : ℂ)) / f) from rfl, h3.deriv]
  have e1 : Q.derivative.eval ((0 : ℝ) : ℂ) = 0 := by
    rw [Complex.ofReal_zero, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
    simp [h1]
  have e2 : Q.derivative.derivative.eval ((0 : ℝ) : ℂ) = 2 * Q.coeff 2 := by
    rw [Complex.ofReal_zero, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative,
      Polynomial.coeff_derivative]
    norm_num [mul_comm]
  rw [hf0, e1, e2]
  simp

end LogPoly

end

end GroundTheory.Heights₂.Heights.FourB
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.PKrullHeightOne
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB

open Ideal

theorem KrullHeightOne.exists_prime_colon {A : Type*} [CommRing A] [IsNoetherianRing A]
    (p q : A) (hqp : ¬ q ∣ p) :
    ∃ (a : A) (P : Ideal A), P.IsPrime ∧ ¬ q ∣ a * p ∧ ∀ x, x ∈ P ↔ q ∣ x * (a * p) := by
  let mk := Ideal.Quotient.mk (Ideal.span {q})
  let M := Submodule.span A {mk p}
  have hx : (⟨mk p, Submodule.mem_span_singleton_self _⟩ : M) ≠ 0 := by
    intro h
    apply hqp
    have : mk p = 0 := congrArg Subtype.val h
    rwa [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at this
  obtain ⟨P, hP, -⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing A _ hx
  obtain ⟨hPp, y, hy⟩ := isAssociatedPrime_iff.1 hP
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 y.2
  have key : ∀ x, x ∈ P ↔ q ∣ x * (a * p) := by
    intro x
    rw [hy, Submodule.mem_colon_singleton, Submodule.mem_bot, ← Subtype.val_inj]
    change x • (y : A ⧸ Ideal.span {q}) = 0 ↔ _
    rw [← ha, smul_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
      Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton, mul_assoc]
  refine ⟨a, P, hPp, fun h => hPp.ne_top ?_, key⟩
  rw [Ideal.eq_top_iff_one, key, one_mul]
  exact h

theorem KrullHeightOne.proof : KrullHeightOne.Statement := by
  intro A _ _ _ _ p q hpq
  obtain ⟨hq, hqp⟩ := hpq
  obtain ⟨a, P, hPp, hb, hP⟩ := KrullHeightOne.exists_prime_colon p q hqp
  have hqP : q ∈ P := (hP q).2 (dvd_mul_right q _)
  have hPbot : P ≠ ⊥ := fun h => hq (by rw [h, Ideal.mem_bot] at hqP; exact hqP)

  have hex : ∃ u ∈ P, ∃ w ∉ P, u * (a * p) = q * w := by
    by_contra hne
    have hne' : ∀ u ∈ P, ∀ w, u * (a * p) = q * w → w ∈ P := by
      intro u hu w huw
      by_contra hw
      exact hne ⟨u, hu, w, hw, huw⟩
    have hqK : algebraMap A (FractionRing A) q ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A (FractionRing A))).2 hq
    let N : Submodule A (FractionRing A) := Submodule.map (Algebra.linearMap A (FractionRing A)) P
    have hN : N ≠ ⊥ := by
      intro h
      have : algebraMap A (FractionRing A) q ∈ N := Submodule.mem_map_of_mem hqP
      rw [h, Submodule.mem_bot] at this
      exact hqK this
    have hNfg : N.FG := (IsNoetherian.noetherian P).map _
    have hy : IsIntegral A (algebraMap A (FractionRing A) (a * p) / algebraMap A (FractionRing A) q) := by
      refine isIntegral_of_smul_mem_submodule N hN hNfg _ ?_
      intro n hn
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hn
      obtain ⟨w, hw⟩ := (hP x).1 hx
      have hwP : w ∈ P := hne' x hx w hw
      refine Submodule.mem_map.2 ⟨w, hwP, ?_⟩
      show algebraMap A (FractionRing A) w =
        algebraMap A (FractionRing A) (a * p) / algebraMap A (FractionRing A) q *
          algebraMap A (FractionRing A) x
      rw [div_mul_eq_mul_div, eq_div_iff hqK, ← map_mul, ← map_mul, mul_comm (a * p) x, hw,
        mul_comm]
    obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hy
    apply hb
    refine ⟨z, IsFractionRing.injective A (FractionRing A) ?_⟩
    rw [map_mul _ q z, hz]
    exact (mul_div_cancel₀ _ hqK).symm
  obtain ⟨u, hu, w, hw, huw⟩ := hex

  have hmin : P ∈ (Ideal.span {u}).minimalPrimes := by
    refine ⟨⟨hPp, (Ideal.span_singleton_le_iff_mem _).2 hu⟩, ?_⟩
    rintro Q ⟨hQ, huQ⟩ hQP x hx
    obtain ⟨v, hv⟩ := (hP x).1 hx
    have h1 : x * w = u * v := by
      apply mul_left_cancel₀ hq
      linear_combination (-x) * huw + u * hv
    have h2 : x * w ∈ Q := by
      rw [h1]
      exact Q.mul_mem_right v ((Ideal.span_singleton_le_iff_mem _).1 huQ)
    rcases hQ.mem_or_mem h2 with h | h
    · exact h
    · exact absurd (hQP h) hw
  have : (Ideal.span {u}).IsPrincipal := ⟨⟨u, rfl⟩⟩
  have := hPp
  have hle : P.height ≤ 1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hmin
  have hge : 1 ≤ P.height :=
    Order.one_le_iff_ne_zero.2 fun h => hPbot (Ideal.height_eq_zero_iff_eq_bot.1 h)
  refine ⟨P, hPp, le_antisymm hle hge, w, hw, u * a, P.mul_mem_right a hu, ?_⟩
  linear_combination -huw

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FourB
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsClosedPointGenericFibre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open IsDedekindDomain NumberField

noncomputable section

def ClosedPointOfGenericFibre.Hyp (R : Type) [CommRing R] (M : Ideal R) (g : R) : Prop :=
  M.IsMaximal ∧ g ≠ 0

def ClosedPointOfGenericFibre.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (R : Type) [CommRing R] [IsDomain R] [Algebra (𝓞 F) R]
    [Module.Flat (𝓞 F) R] [Algebra.FiniteType (𝓞 F) R] (M : Ideal R) (g : R),
    ClosedPointOfGenericFibre.Hyp R M g →
    ∃ Q : Ideal R, Q.IsPrime ∧ Q ≤ M ∧ Q.comap (algebraMap (𝓞 F) R) = ⊥ ∧ g ∉ Q ∧
      Algebra.IsAlgebraic (𝓞 F) (R ⧸ Q)

def ClosedPointOfGenericFibre.exampleIdeal : Ideal (Polynomial (𝓞 ℚ)) :=
  RingHom.ker ((Ideal.Quotient.mk placeTwo.asIdeal).comp (Polynomial.evalRingHom 0))

end

end GroundTheory.Heights₂.Heights.FourB
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsFSDensity
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open ReciprocityTheory.AnForm

def FubiniStudyChartDensity.Statement : Prop :=
  ∀ (N : ℕ) (z w : Fin N → ℂ),
    0 ≤ levi (fun y : Fin N → ℂ => (1 / 2) * Real.log (1 + ∑ i, ‖y i‖ ^ 2)) z w ∧
      maDens (fun _ y => (1 / 2) * Real.log (1 + ∑ i, ‖y i‖ ^ 2)) z =
        (N.factorial : ℝ) / (Real.pi ^ N * (1 + ∑ i, ‖z i‖ ^ 2) ^ (N + 1))

end GroundTheory.Heights₂.Heights.FourB
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.StatementsIntegralPointAlgebraic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open IsDedekindDomain NumberField

noncomputable section

def IntegralPointOfAlgebraicDomain.Hyp (F : Type) [Field F] [NumberField F] (S : Type) [CommRing S]
    [Algebra (𝓞 F) S] (v : HeightOneSpectrum (𝓞 F)) (M : Ideal S) : Prop :=
  Function.Injective (algebraMap (𝓞 F) S) ∧ Algebra.IsAlgebraic (𝓞 F) S ∧ M.IsMaximal ∧
    M.comap (algebraMap (𝓞 F) S) = v.asIdeal

def IntegralPointOfAlgebraicDomain.Statement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (S : Type) [CommRing S] [IsDomain S] [Algebra (𝓞 F) S]
    [Algebra.FiniteType (𝓞 F) S] (v : HeightOneSpectrum (𝓞 F)) (M : Ideal S),
    IntegralPointOfAlgebraicDomain.Hyp F S v M →
    ∃ (L : Type) (_ : Field L) (_ : Algebra (v.adicCompletion F) L)
      (_ : FiniteDimensional (v.adicCompletion F) L) (y : S →+* L),
      y.comp (algebraMap (𝓞 F) S) =
          (algebraMap (v.adicCompletion F) L).comp
            ((algebraMap F (v.adicCompletion F)).comp (algebraMap (𝓞 F) F)) ∧
        Function.Injective y ∧
        (∀ a : S, (completionIntegersTo F v L).IsIntegralElem (y a)) ∧
        (∀ a ∉ M, ∃ b : L, b * y a = 1 ∧ (completionIntegersTo F v L).IsIntegralElem b) ∧
        ∀ a ∈ M, ∀ b : L, b * y a = 1 → ¬ (completionIntegersTo F v L).IsIntegralElem b

end

end GroundTheory.Heights₂.Heights.FourB
end

