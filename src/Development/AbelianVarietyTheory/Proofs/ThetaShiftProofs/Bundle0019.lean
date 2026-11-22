import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0021
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.FinLocalCutAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0019
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.HolomorphicHomDetermined
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSectionsSpanAffine

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FreqRealNonnegIntegral
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.FjFreq

open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem exists_emb_of_freq (la : Wt X.Ψ r) (ν : X.Ψ → ℝ)
    (hν : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k) :
    ∃ ω : E, ∀ τ : X.Ψ, (ν τ : ℂ) = τ.1 ω := by
  refine X.exists_emb_eq (fun τ => (ν τ : ℂ)) fun γ => ?_
  have hN : ((X.m * X.chiOrd la : ℕ) : ℝ) ≠ 0 := by
    have := Nat.mul_pos X.m_pos (chiOrd_pos X la); positivity
  have hγ : IsIntegral ℤ (γ : E) := RingOfIntegers.isIntegral_coe γ
  have hcγ : IsIntegral ℤ (cc (γ : E)) := map_isIntegral_int (IsCMField.complexConj E) hγ
  have ha : cc ((γ : E) + cc (γ : E)) = (γ : E) + cc (γ : E) := by
    rw [cc_add', cc_cc', add_comm]
  obtain ⟨k, hk⟩ := hν _ ((mem_periods_iff X la _).2 ⟨_, ha, hγ.add hcγ, rfl⟩)
  refine ⟨(k : ℚ) / (4 * (X.m * X.chiOrd la : ℕ)), ?_⟩
  have h1 : ∑ τ, ν τ * per X la ((γ : E) + cc (γ : E)) τ =
      2 * ((X.m * X.chiOrd la : ℕ) : ℝ) * ∑ τ : X.Ψ, ν τ * (τ.1 (γ : E)).re := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    simp only [per, map_add, emb_cc', Complex.add_re, Complex.conj_re]
    ring
  rw [h1] at hk
  simp only [Complex.re_sum, Complex.re_ofReal_mul]
  rw [Rat.cast_div, Rat.cast_mul, Rat.cast_natCast, Rat.cast_intCast, ← hk]
  field_simp
  norm_num

theorem fj_transv (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) (hP : X.IsSec la P) {ξ : Fin r → E} (hξ : X.IsIso ξ)
    (ν : X.Ψ → ℝ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {s : E} (hs : cc s = s) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ)
    (hγm : (γ : Matrix (Fin r) (Fin r) E) = transvMat X.Gm ξ (s * X.κ0)) (hχ : X.χ la γ = 1) :
    X.fj la ξ ν P (X.flow ξ (fun τ => (((τ.1 s).re : ℝ) : ℂ)) x) = X.fj la ξ ν P x := by
  have hact : ∀ y, lact γ y = X.flow ξ (fun τ => (((τ.1 s).re : ℝ) : ℂ)) y := by
    intro y
    funext τ
    simp only [lact, Data.flow]
    rw [hγm, transvMat_map X ξ τ _ _ ?_]
    rw [map_mul, emb_kappa, ← emb_real hs]
    ring
  have key : ∀ t : X.Ψ → ℝ, P (X.flow ξ (fun τ => (t τ : ℂ)) (X.flow ξ (fun τ => (((τ.1 s).re : ℝ) : ℂ)) x)) =
      P (X.flow ξ (fun τ => (t τ : ℂ)) x) := by
    intro t
    rw [flow_flow X hξ.2.1, add_comm, ← flow_flow X hξ.2.1, ← hact]
    exact (hP.2.2 γ hγ _ (flow_real_mem_dom X hξ.2.1 t x hx)).trans (by rw [hχ, one_mul]; rfl)
  unfold Data.fj
  simp only [key]

end GlobalTheory.FjFreq

namespace GlobalTheory.FjFreq

open ReciprocityTheory.ChartRestriction.G.FD.EmbeddingHermitianPairs ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity ReciprocityTheory.ChartRestriction.G.FD.RealEmbeddingCharacters

theorem freq_real_nonneg_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsBddSec la P → ∀ ξ, X.IsIso ξ → ∀ (ν : X.Ψ → ℝ), ∀ x ∈ X.dom, X.fj la ξ ν P x ≠ 0 → ∃ ν₀ : E, cc ν₀ = ν₀ ∧ (∀ τ : X.Ψ, ν τ = (τ.1 ν₀).re) ∧ (∀ τ : E →+* ℂ, 0 ≤ (τ ν₀).re) ∧ ∀ s : E, cc s = s → (∃ γ ∈ X.Γ, (γ : Matrix (Fin r) (Fin r) E) = transvMat X.Gm ξ (s * X.κ0) ∧ X.χ la γ = 1) → ∃ m : ℤ, Algebra.trace ℚ E (ν₀ * s) = m := by
  intro E _ _ _ r X la P hP ξ hξ ν x hx hne
  have hν : ∀ p ∈ X.periods la, ∃ k : ℤ, 2 * ∑ τ, ν τ * p τ = k := by
    by_contra h
    exact hne (by unfold Data.fj; rw [if_neg h])
  obtain ⟨ω, hω⟩ := exists_emb_of_freq X la ν hν
  have hre : ∀ τ : X.Ψ, ν τ = (τ.1 ω).re := fun τ => by rw [← hω, Complex.ofReal_re]
  obtain ⟨C, hC⟩ := hP.2
  have hnn := (moderateCoefficientPositivity_holds r X la P C 0 hP.1 (fun y hy => by simpa using hC y hy)).1 ξ hξ ν x hx hne
  refine ⟨ω, ?_, hre, ?_, ?_⟩
  · obtain ⟨τ⟩ := X.nonempty_Psi
    apply τ.1.injective
    rw [emb_cc', ← hω, Complex.conj_ofReal]
  · intro σ
    by_cases hσ : σ ∈ X.Ψ
    · exact (hre ⟨σ, hσ⟩) ▸ hnn ⟨σ, hσ⟩
    · have hc : ComplexEmbedding.conjugate σ ∈ X.Ψ := (X.conj_mem_iff σ).2 hσ
      have h1 := hnn ⟨_, hc⟩
      rw [hre] at h1
      simpa [ComplexEmbedding.conjugate_coe_eq] using h1
  · rintro s hs ⟨γ, hγ, hγm, hχ⟩
    have h1 := X.fj_flow_real la ξ hξ ν P hP.1 hP.2 x hx (fun τ => (τ.1 s).re)
    rw [fj_transv X la P hP.1 hξ ν hx hs hγ hγm hχ] at h1
    have h2 : Complex.exp (4 * Real.pi * Complex.I * ∑ τ, (ν τ : ℂ) * (((τ.1 s).re : ℝ) : ℂ)) = 1 :=
      mul_right_cancel₀ hne (by rw [one_mul]; exact h1.symm)
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
    refine ⟨n, ?_⟩
    have h3 : ((Algebra.trace ℚ E (ω * s) : ℚ) : ℂ) = 2 * ∑ τ, (ν τ : ℂ) * (((τ.1 s).re : ℝ) : ℂ) := by
      rw [X.trace_eq_Psi, Finset.mul_sum]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [map_mul, ← hω, emb_real hs, Complex.ofReal_re, map_mul, Complex.conj_ofReal, Complex.conj_ofReal]
      ring
    have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
    have h4 : ((Algebra.trace ℚ E (ω * s) : ℚ) : ℂ) = (n : ℂ) := by
      apply mul_right_cancel₀ hpi
      rw [h3, ← hn]
      ring
    exact_mod_cast h4

end GlobalTheory.FjFreq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsIntegralDiscrMulOfTraceInt
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField in
open scoped LaurentSeries in

theorem _root_.GlobalTheory.ArcQ.pairE_properties : ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] (ξ : Module.Dual ℤ X), (∀ (a : 𝓞 E) x, _root_.GlobalTheory.ArcQ.pairE ξ (a • x) = (a : E) * _root_.GlobalTheory.ArcQ.pairE ξ x) ∧ (∀ x y, _root_.GlobalTheory.ArcQ.pairE ξ (x + y) = _root_.GlobalTheory.ArcQ.pairE (E := E) ξ x + _root_.GlobalTheory.ArcQ.pairE ξ y) ∧ (∀ x, Algebra.trace ℚ E (_root_.GlobalTheory.ArcQ.pairE ξ x) = ξ x) ∧ (∀ x, IsIntegral ℤ ((NumberField.discr E : E) * _root_.GlobalTheory.ArcQ.pairE ξ x)) ∧ ∀ (K : Type) [Field K] (τK : E →+* K) x, _root_.GlobalTheory.ArcQ.xiVal τK ξ x = τK (_root_.GlobalTheory.ArcQ.pairE ξ x) := by
  intro E _ _ X _ _ ξ
  classical
  set b := RingOfIntegers.basis E with hbdef
  have hB := traceForm_nondegenerate ℚ E
  set d := (Algebra.traceForm ℚ E).dualBasis hB (integralBasis E) with hd
  have hP : ∀ x, _root_.GlobalTheory.ArcQ.pairE ξ x = ∑ i, d i * (ξ (b i • x) : E) := fun x => rfl
  have hexp : ∀ y : 𝓞 E, algebraMap (𝓞 E) E y = ∑ k, (b.repr y k : E) * integralBasis E k := by
    intro y
    conv_lhs => rw [← b.sum_repr y]
    simp [integralBasis_apply, zsmul_eq_mul, b]
  have hdual : ∀ i k, Algebra.trace ℚ E (d i * integralBasis E k) = if k = i then 1 else 0 := by
    intro i k
    rw [← Algebra.traceForm_apply]
    exact LinearMap.BilinForm.apply_dualBasis_left hB _ i k
  have hL : ∀ (y : 𝓞 E) i, Algebra.trace ℚ E (d i * algebraMap (𝓞 E) E y) = (b.repr y i : ℚ) := by
    intro y i
    have e : ∀ k, d i * ((b.repr y k : E) * integralBasis E k) =
        (b.repr y k : ℚ) • (d i * integralBasis E k) := by
      intro k
      rw [Algebra.smul_def]
      simp only [eq_ratCast, Rat.cast_intCast]
      ring
    rw [hexp y, Finset.mul_sum, map_sum]
    simp_rw [e, map_smul, hdual, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
  have hC : ∀ x (y : 𝓞 E), Algebra.trace ℚ E (_root_.GlobalTheory.ArcQ.pairE ξ x * algebraMap (𝓞 E) E y) =
      (ξ (y • x) : ℚ) := by
    intro x y
    have e : ∀ i, d i * (ξ (b i • x) : E) * algebraMap (𝓞 E) E y =
        (ξ (b i • x) : ℚ) • (d i * algebraMap (𝓞 E) E y) := by
      intro i
      rw [Algebra.smul_def]
      simp only [eq_ratCast, Rat.cast_intCast]
      ring
    rw [hP, Finset.sum_mul, map_sum]
    simp_rw [e, map_smul, hL, smul_eq_mul]
    conv_rhs => rw [← b.sum_repr y]
    simp only [Finset.sum_smul, map_sum, smul_assoc, map_zsmul, smul_eq_mul, Int.cast_sum,
      Int.cast_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have huniq : ∀ y y' : E, (∀ k, Algebra.trace ℚ E (y * integralBasis E k) =
      Algebra.trace ℚ E (y' * integralBasis E k)) → y = y' := by
    intro y y' h
    rw [← d.sum_repr y, ← d.sum_repr y']
    simp_rw [hd, LinearMap.BilinForm.dualBasis_repr_apply, Algebra.traceForm_apply, h]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a x
    apply huniq
    intro k
    have e : (a : E) * _root_.GlobalTheory.ArcQ.pairE ξ x * integralBasis E k =
        _root_.GlobalTheory.ArcQ.pairE ξ x * algebraMap (𝓞 E) E (b k * a) := by
      rw [integralBasis_apply, map_mul]
      show (algebraMap (𝓞 E) E a) * _ * _ = _
      ring
    rw [e, hC, integralBasis_apply, hC, mul_smul]
  · intro x y
    simp only [hP, smul_add, map_add, Int.cast_add, mul_add, Finset.sum_add_distrib]
  · intro x
    have := hC x 1
    simpa using this
  · intro x
    rw [hP, Finset.mul_sum]
    refine IsIntegral.sum _ fun i _ => ?_
    have hdi : IsIntegral ℤ ((NumberField.discr E : E) * d i) := by
      have h := isIntegral_discr_mul_of_mem_traceDual (A := ℤ) (K := ℚ) (L := E) (B := 𝓞 E)
        (1 : Submodule (𝓞 E) E) (b := integralBasis E)
        (fun k => by rw [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _)
        (a := 1) (x := d i) (Submodule.one_le.1 le_rfl) (by
          rw [Submodule.mem_traceDual]
          intro a ha
          obtain ⟨y, rfl⟩ := Submodule.mem_one.1 ha
          rw [Algebra.traceForm_apply, hL]
          exact ⟨b.repr y i, rfl⟩)
      rw [← coe_discr, Algebra.smul_def, mul_one] at h
      simpa using h
    have hξ : IsIntegral ℤ ((ξ (b i • x) : ℤ) : E) := by
      simpa using (isIntegral_algebraMap (R := ℤ) (A := E) (x := ξ (b i • x)))
    rw [← mul_assoc]
    exact hdi.mul hξ
  · intro K _ τK x
    show ∑ i, τK (d i) * (ξ (b i • x) : K) = τK (_root_.GlobalTheory.ArcQ.pairE ξ x)
    rw [hP]
    simp [map_sum, map_mul, map_intCast]

end GlobalTheory.ArcQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NfacParallelFlowV
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries

namespace GlobalTheory.ArcQ

section FlowNorm

open ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal ReciprocityTheory.ChartRestriction.G.FD.PositiveMinorUnits ReciprocityTheory.ChartRestriction.G.FD.MajorantFamilyNorms ReciprocityTheory.ChartRestriction.G.AR.Up.FactorialDivisibilityBounds

theorem sum_step_telescope (L : ℕ → ℝ) (m : ℝ) {p r : ℕ} (hp : p ≤ r) :
    ∑ k ∈ Finset.range r, (if p ≤ k then m else -m) * (L (k + 1) - L k) = m * (L r + L 0 - 2 * L p) := by
  rw [← Finset.sum_range_add_sum_Ico _ hp]
  have h1 : ∑ k ∈ Finset.range p, (if p ≤ k then m else -m) * (L (k + 1) - L k) = -m * (L p - L 0) := by
    rw [← Finset.sum_range_sub L p, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_neg (by have := Finset.mem_range.mp hk; omega)]
  have h2 : ∑ k ∈ Finset.Ico p r, (if p ≤ k then m else -m) * (L (k + 1) - L k) = m * (L r - L p) := by
    rw [← Finset.sum_Ico_sub L hp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [if_pos (Finset.mem_Ico.mp hk).1]
  rw [h1, h2]; ring

theorem nfac_parallel_flowV {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (e : X.Ψ → Fin r → ℂ) (he : X.IsIsoV e) (la : Wt X.Ψ r) (m : ℝ)
    (hla : ∀ τ (j : Fin r), (la τ j : ℝ) = if X.p0 ≤ (j : ℕ) then m else -m)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (s : X.Ψ → ℂ) (hT : X.flowV e s x ∈ X.dom) :
    X.nfac la (X.flowV e s x) * (∏ τ, (X.ttV e (X.flowV e s x) τ)⁻¹) ^ m =
      X.nfac la x * (∏ τ, (X.ttV e x τ)⁻¹) ^ m := by
  have hρ : ∀ τ, 0 < rho X e s x τ X.p0 := fun τ => rho_pos X e he hx s hT τ _ X.p0_le
  have hr : ∀ τ, rfac X la x (X.flowV e s x) τ = (rho X e s x τ X.p0)⁻¹ ^ m := by
    intro τ
    have hsg := hsg_of X hx τ
    rw [rfac_eq X e he hx s hT τ la]
    set L : ℕ → ℝ := fun i => Real.log (rho X e s x τ i) with hLdef
    have hL0 : L 0 = 0 := by simp [L, rho, mN_zero]
    have hLr : L r = 0 := by
      simp [L, rho, mN_top (hG_of X τ) X.p0 (mat x τ) (hx τ).1 hsg (e τ) (he τ).1]
    have hsum : ∑ i : Fin r, (la τ i : ℝ) / 2 *
        (Real.log (rho X e s x τ ((i : ℕ) + 1)) - Real.log (rho X e s x τ i)) =
        ∑ k ∈ Finset.range r, (if X.p0 ≤ k then m / 2 else -(m / 2)) * (L (k + 1) - L k) := by
      rw [← Fin.sum_univ_eq_sum_range
        (fun k => (if X.p0 ≤ k then m / 2 else -(m / 2)) * (L (k + 1) - L k)) r]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hla]
      split_ifs <;> simp only [L] <;> ring
    rw [hsum, sum_step_telescope L (m / 2) X.p0_le, hL0, hLr,
      Real.rpow_def_of_pos (inv_pos.mpr (hρ τ)), Real.log_inv]
    congr 1
    simp only [L]; ring
  have hm : ∀ τ, 0 < mN τ.1 X.Gm (mat x τ) (e τ) X.p0 := fun τ =>
    mN_pos (hG_of X τ) X.p0 X.p0_le (mat x τ) (hx τ).1 (hsg_of X hx τ) (e τ) (he τ).1 (he τ).2
  have htpos : ∀ τ, 0 ≤ (X.ttV e x τ)⁻¹ := fun τ => by
    have := hm τ
    have := c_pos X τ
    rw [Data.ttV, maj_eq X hx e τ (he τ).1]
    positivity
  have ht : ∀ τ, (X.ttV e (X.flowV e s x) τ)⁻¹ = (rho X e s x τ X.p0)⁻¹ * (X.ttV e x τ)⁻¹ := by
    intro τ
    have h1 := hρ τ
    have h2 := hm τ
    have h3 := c_pos X τ
    rw [Data.ttV, Data.ttV, maj_flow X hx e τ (he τ).1 s h1.ne', maj_eq X hx e τ (he τ).1]
    simp only [rho] at h1 ⊢
    field_simp
  have hN := FlowCoefficientBounds.nfac_pos X hT la
  have hdiv := nfac_div X la x (X.flowV e s x)
  rw [div_eq_iff hN.ne', Finset.prod_congr rfl fun τ _ => hr τ,
    Real.finsetProd_rpow _ _ (fun τ _ => (inv_pos.mpr (hρ τ)).le)] at hdiv
  rw [hdiv, Finset.prod_congr rfl fun τ _ => ht τ, Finset.prod_mul_distrib,
    Real.mul_rpow (Finset.prod_nonneg fun τ _ => (inv_pos.mpr (hρ τ)).le)
      (Finset.prod_nonneg fun τ _ => htpos τ)]
  ring

end FlowNorm

theorem nfac_parallel_flow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (n : ℕ) (ξ' : Fin r → E), Even n → (U.X k).IsIso ξ' → ∀ x ∈ (U.X k).dom, ∀ s : (U.X k).Ψ → ℂ, (U.X k).flow ξ' s x ∈ (U.X k).dom → (U.X k).nfac (laU U 0 n k) ((U.X k).flow ξ' s x) * (∏ τ, ((U.X k).tt ξ' ((U.X k).flow ξ' s x) τ)⁻¹) ^ ((n : ℝ) / 2) = (U.X k).nfac (laU U 0 n k) x * (∏ τ, ((U.X k).tt ξ' x τ)⁻¹) ^ ((n : ℝ) / 2) := by
  intro E _ _ _ H Dw l Xo c σ r U k n ξ' hn hξ x hx s hT
  have hiso : (U.X k).IsIsoV ((U.X k).embV ξ') := fun τ =>
    ⟨by rw [show (U.X k).embV ξ' τ = Data.emb τ.1 ξ' from rfl, hermC_emb, hξ.2.1, map_zero],
      emb_ne_zero τ.1 hξ.2.2⟩
  refine nfac_parallel_flowV (U.X k) ((U.X k).embV ξ') hiso (laU U 0 n k) ((n : ℝ) / 2) ?_ hx s hT
  intro τ j
  obtain ⟨m, rfl⟩ := hn
  have h2 : (m + m) / 2 = m := by omega
  simp only [laU, h2]
  split_ifs <;> simp

end GlobalTheory.ArcQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarisationSectionGeneratesOfSpecialFibre
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames

namespace GlobalTheory.GenDvr

open IsLocalRing ReciprocityTheory.ChartRestriction.G.H1

theorem generates_of_generic_line {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {X X' : Scheme.{0}}
    (p : X ⟶ Sp V) [Flat p] {p' : X' ⟶ Sp (FractionRing V)} {φ : X' ⟶ X}
    (hφ : IsPullback φ p' p (spMap (algebraMap V (FractionRing V)))) {L : LB X} {L' : LB X'} (hL : L.IsLB)
    (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (b : L'.Sec)
    (hb : ∀ s : L'.Sec, ∃ a : FractionRing V, ∀ i, s.f i = constFn p' _ a * b.f i)
    (θ : L.Sec) {g : X} (hg : p g = closedPoint V) (hθ : g ∈ Out.nonzeroLocus θ) (σ : L.Sec) :
    ∃! a : V, ∀ i, σ.f i = constFn p _ a * θ.f i := by
  obtain ⟨k₀, hb₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hθ
  have hk₀ : g ∈ L.U k₀ := X.basicOpen_le _ hb₀
  have un : IsUnit (gs (𝟙 _) g _ (θ.f k₀)) := by
    rw [gs_eq (𝟙 _) g _ hk₀]; exact (X.mem_basicOpen _ _ hk₀).1 hb₀
  obtain ⟨w, gw'⟩ := hw
  have down := sec_pull_down ((isGen_iff w).1 gw') hL hL'
  obtain ⟨θ', hθ'⟩ := down θ
  have : IsDominant (spMap (algebraMap V (FractionRing V))) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V (FractionRing V))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap V (FractionRing V)))
  have : IsSchemeTheoreticallyDominant φ := IsSchemeTheoreticallyDominant.of_isPullback hφ.flip
  have : QuasiCompact φ := MorphismProperty.of_isPullback (P := @QuasiCompact) hφ.flip inferInstance

  have inj : ∀ (σ τ σK τK : _) (r : V), (∀ (Z : Scheme.{0}) (q : Z ⟶ X') (y : Z) j k, φ (q y) ∈ L.U j →
      q y ∈ L'.U k → gs (q ≫ φ) y _ (LB.Sec.f σ j) = (gw w q y j k).val * gs q y _ (LB.Sec.f σK k)) →
      (∀ (Z : Scheme.{0}) (q : Z ⟶ X') (y : Z) j k, φ (q y) ∈ L.U j →
      q y ∈ L'.U k → gs (q ≫ φ) y _ (LB.Sec.f τ j) = (gw w q y j k).val * gs q y _ (LB.Sec.f τK k)) →
      (∀ k, LB.Sec.f σK k = constFn p' _ (algebraMap V _ r) * LB.Sec.f τK k) →
      ∀ j, LB.Sec.f σ j = constFn p _ r * LB.Sec.f τ j := by
    intro σ τ σK τK r h₁ h₂ h₃ j
    refine φ.app_injective _ (fn_ext fun y hy => ?_)
    obtain ⟨k, hk⟩ := exists_chart hL' y
    refine (gs_pull (𝟙 _) φ y _ hy _).trans (Eq.trans ?_ (gs_pull (𝟙 _) φ y _ hy _).symm)
    rw [gs_mul (𝟙 _ ≫ φ) y _ hy, gs_constFn _ _ (𝟙 _ ≫ φ) y hy, h₁ _ (𝟙 _) y j k hy hk, h₂ _ (𝟙 _) y j k hy hk,
      (sec_eq_iff _ _ _ _).1 h₃ k y hk, Category.id_comp, hφ.w, cst_comp, mul_left_comm]
  have mulc : ∀ {s t u : L'.Sec} {a a' : FractionRing V}, (∀ k, s.f k = constFn p' _ a * t.f k) →
      (∀ k, t.f k = constFn p' _ a' * u.f k) → ∀ k, s.f k = constFn p' _ (a * a') * u.f k :=
    fun h h' => (sec_eq_iff _ _ _ _).2 fun k y hy => by
      rw [(sec_eq_iff _ _ _ _).1 h k y hy, (sec_eq_iff _ _ _ _).1 h' k y hy, cst_mul, _root_.mul_assoc]
  have invc : ∀ {s t : L'.Sec} {a : FractionRing V}, a ≠ 0 → (∀ k, s.f k = constFn p' _ a * t.f k) →
      ∀ k, t.f k = constFn p' _ a⁻¹ * s.f k := fun ha h => (sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 h k y hy, ← _root_.mul_assoc, ← cst_mul, inv_mul_cancel₀ ha, cst_one, _root_.one_mul]
  have unit : ∀ (σ : L.Sec) (r : V), (∀ j, θ.f j = constFn p _ r * σ.f j) → IsUnit r := fun σ r h => by
    by_contra hr
    rw [(sec_eq_iff _ _ _ _).1 h k₀ g hk₀] at un
    exact cst_not_isUnit p g hg hr (isUnit_of_mul_isUnit_left un)
  obtain ⟨a₀, ha₀⟩ := hb θ'
  have h₀ : a₀ ≠ 0 := fun h => not_isUnit_zero (unit θ 0 (inj θ θ θ' θ' 0 hθ' hθ' ((sec_eq_iff _ _ _ _).2 fun k y hy => by
    rw [(sec_eq_iff _ _ _ _).1 ha₀ k y hy, h, map_zero, ← _root_.mul_assoc, ← cst_mul, mul_zero])))
  obtain ⟨σK, hσK⟩ := down σ
  obtain ⟨a, ha⟩ : ∃ a : FractionRing V, ∀ i, σK.f i = constFn p' _ a * θ'.f i := by
    obtain ⟨a, ha⟩ := hb σK
    exact ⟨a * a₀⁻¹, mulc ha (invc h₀ ha₀)⟩
  obtain ⟨r, hr⟩ : ∃ r : V, ∀ i, σ.f i = constFn p _ r * θ.f i := by
    by_cases h : IsLocalization.IsInteger V a
    · obtain ⟨r, rfl⟩ := h
      exact ⟨r, inj σ θ σK θ' r hσK hθ' ha⟩
    · have hne : a ≠ 0 := fun e => h (e ▸ IsLocalization.isInteger_zero)
      obtain ⟨r, hr⟩ := (ValuationRing.isInteger_or_isInteger V a).resolve_left h
      obtain ⟨u, rfl⟩ := unit σ r (inj θ σ θ' σK r hθ' hσK (hr ▸ invc hne ha))
      exact absurd ⟨(u⁻¹ : Vˣ), by rw [← inv_inv a, ← hr, map_units_inv]⟩ h
  refine ⟨r, hr, fun r' hr' => ?_⟩
  by_contra hne
  have e : cst p g (r' - r) * gs (𝟙 _) g _ (θ.f k₀) = cst p g (r' - r) * 0 := by
    rw [cst_sub, sub_mul, ← (sec_eq_iff _ _ _ _).1 hr' k₀ g hk₀, ← (sec_eq_iff _ _ _ _).1 hr k₀ g hk₀, sub_self, mul_zero]
  exact un.ne_zero (cst_regular p g (sub_ne_zero.2 hne) e)

theorem resG_appTop_toΓ {V : Type} [CommRing V] {X : Scheme.{0}} (p : X ⟶ Sp V) (U : X.Opens) (a : V) :
    resG X (le_top : U ≤ ⊤) (p.appTop.hom (toΓ V a)) = constFn p U a := rfl

theorem generates_of_nonzero_on_special_fibre : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X) (_ : SABMap t' Xo.univ.t x) (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))) (θ : LB.Sec G.PP.L), (∃ g : G.G.left, G.G.hom g = IsLocalRing.closedPoint T.V ∧ g ∈ Out.nonzeroLocus θ) → ∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i, σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i := by
  intro _ h₂ E _ _ _ H Dw l Xo _ T G t' x m₁ m₂ θ ⟨g, hg, hθ⟩ σ
  have := G.semi.smooth
  obtain ⟨b, hb⟩ := globalSections_rank_one_fibre h₂.secTwist amplePt Xo.univ m₁
  obtain ⟨w, hw, -⟩ := m₂.lin
  exact generates_of_generic_line G.G.hom m₂.cart.1 G.PP.isLB t'.PP.isLB ⟨w, hw⟩ b (fun s => (hb s).exists) θ hg hθ σ

end GlobalTheory.GenDvr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SecScalOfIsPullSec
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SpanFrame

open GlobalTheory.AmpleSpan

theorem secScal_of_isPullSec {S : Scheme.{0}} (A : Over S) [GrpObj A] {L : LB A.left} (hL : L.IsLB) (a : ℤ)
    {T T' : Over S} (k : T' ⟶ T) {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')}
    (H : IsPullSec A L a (k ▷ A) (whiskerRight_snd k A) s s') :
    GeneratorPullback.SecScal L (fun _ : Fin 1 => (snd T' A).left) (fun _ => a) s' (fun _ : Fin 1 => (snd T A).left) (fun _ => a) s
      (k ▷ A).left 1 := by
  have e : (k ▷ A).left ≫ (snd T A).left = (snd T' A).left := by rw [← Over.comp_left, whiskerRight_snd]
  refine (secScal_const_iff hL e).2 fun i Z r z hz => ?_
  have hm : r z ∈ LB.wchart L (fun _ : Fin 1 => (snd T' A).left) (fun _ => i) := Set.mem_iInter.2 fun _ => hz
  have le := chart_le_res A L (k ▷ A) (whiskerRight_snd k A) a (fun _ => i)
  refine Eq.symm ((congrArg (gs r z _) (H fun _ => i)).trans ?_)
  exact (gs_res r z le hm _).trans (gs_pull r (k ▷ A).left z _ (le (x := r z) hm) _)

theorem valR_of_secScal {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K'] {ε : K → ℤ}
    {ε' : K' → ℤ} {χ : Y ⟶ X} {χ' : Y' ⟶ X} {h : Y' ⟶ Y} (e : h ≫ χ = χ')
    {s' : LB.Sec (LB.LinComb L (fun _ : K' => χ') ε')} {s : LB.Sec (LB.LinComb L (fun _ : K => χ) ε)}
    (H : GeneratorPullback.SecScal L (fun _ => χ') ε' s' (fun _ => χ) ε s h 1) {R : Type} [CommRing R] (x : Sp R ⟶ Y') (j : L.ι)
    (hx : ⊤ ≤ (x ≫ χ') ⁻¹ᵁ L.U j) :
    valR (x ≫ h) (LB.wchart L (fun _ : K => χ) (fun _ => j)) (s.f fun _ => j) =
      valR x (LB.wchart L (fun _ : K' => χ') (fun _ => j)) (s'.f fun _ => j) := by
  subst e
  have E := H (fun _ => j) (fun _ => j) (by rintro (a | a) (b | b) _ <;> rfl)
  have hm : ⊤ ≤ x ⁻¹ᵁ (LB.wchart L (fun _ : K' => h ≫ χ) (fun _ => j) ⊓ LB.wchart L (fun _ : K => h ≫ χ) (fun _ => j)) :=
    fun z hz => ⟨Set.mem_iInter.2 fun _ => hx hz, Set.mem_iInter.2 fun _ => hx hz⟩
  have E' := congrArg (valR x _) E
  rw [HolHom.valR_res _ _ _ hm, resTop, map_one, one_mul] at E'
  exact (HolHom.valR_comp _ _ _ _).trans (E'.trans (HolHom.valR_res _ _ _ hm))

theorem exists_span_powOver (hS : SecBaseChangeSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {N : ℕ}
    (hN : 1 ≤ N) {U : S.Opens} (hU : IsAffineOpen U) :
    ∃ (m : ℕ) (b : Fin m → LB.Sec (powOver P.A P.L U N)), ∀ (X' Y' : Scheme.{0}) [IsAffine Y']
      (h : X' ⟶ (P.A.hom ⁻¹ᵁ U).toScheme) (f' : X' ⟶ Y') (g : Y' ⟶ U.toScheme), IsPullback h f' (P.A.hom ∣_ U) g →
      ∀ (K : Type) [Fintype K] (ε : K → ℤ) (φ : X' ⟶ P.A.left), h ≫ (P.A.hom ⁻¹ᵁ U).ι = φ → ∑ k, ε k = N →
      ∀ b' : Fin m → LB.Sec (LB.LinComb P.L (fun _ : K => φ) ε),
        (∀ i, GeneratorPullback.SecScal P.L _ _ (b' i) (fun _ : Fin N => (P.A.hom ⁻¹ᵁ U).ι) (fun _ => 1) (b i) h 1) →
        ∀ s, InSpan f' b' s := by
  obtain ⟨m, b₀, hb₀⟩ := exists_sections_span_affine hS S P N hN U hU
  obtain ⟨h₀, e₀, -, -, hE⟩ := translate_powOver_LPow P.A P.isLB N (U := U) (overRes (T := baseOver S) U)
    (𝟙 U.toScheme) (by simp)
  obtain ⟨E, hE⟩ := hE (IsIso.id _)
  refine ⟨m + 1, fun i => E.symm (b₀ i), fun X' Y' _ h f' g sq K _ ε φ e hε b' hb' s => ?_⟩
  let T' : Over S := Over.mk (g ≫ U.ι)
  have : IsAffine T'.left := ‹IsAffine Y'›
  let k : T' ⟶ overRes (T := baseOver S) U := Over.homMk g (by simp [T'])
  obtain ⟨h', e', sq', -, -⟩ := translate_powOver_LPow P.A P.isLB N (U := U) T' g rfl
  let b'' : Fin (m + 1) → LB.Sec (LPow P.A P.L N T') := fun i =>
    SecM.toSec P.A (SecAff.pull P.A P.L N k (SecM.ofSec P.A (b₀ i)))
  have hb'' : ∀ i, IsPullSec P.A P.L N (k ▷ P.A) (whiskerRight_snd k P.A) (b₀ i) (b'' i) := fun i =>
    (SecAff.isPullSec_iff P.A P.L N _ _ _).2 rfl
  have hsp := hb₀ T' k b'' hb''
  let θ := sq.isoIsPullback _ _ sq'
  have θ₁ : θ.hom ≫ h' = h := sq.isoIsPullback_hom_fst _ _ sq'
  have θ₂ : θ.hom ≫ (fst T' P.A).left = f' := sq.isoIsPullback_hom_snd _ _ sq'
  have θ₃ : θ.hom ≫ (snd T' P.A).left = φ := by rw [← e', ← Category.assoc, θ₁, e]
  obtain ⟨F, hF⟩ := exists_equiv_secScal P.isLB (h := θ.hom) (formEq_const (K := Fin 1) (K' := K)
    (ε := fun _ => (N : ℤ)) (ε' := ε) θ₃ (by simp [hε]))
  have θ₄ : θ.hom ≫ (k ▷ P.A).left ≫ h₀ = h := by
    rw [← cancel_mono (P.A.hom ⁻¹ᵁ U).ι, Category.assoc, Category.assoc, e₀, ← Over.comp_left, whiskerRight_snd, θ₃, e]
  refine InSpan.secScal P.isLB (h := θ.hom) (f := (fst T' P.A).left) (g := 𝟙 Y') (θ₂.trans (Category.comp_id _).symm)
    (t := b'') (s := F.symm s) ((inSpan_iff_mem_span P.A b'' _).2 (by rw [hsp]; trivial)) (fun i => ?_)
    ((hF _ _).2 (F.apply_symm_apply s))
  refine (secScal_iff_sval P.isLB).2 fun Z r z J hJ => ?_
  rw [← SectionScalarValuation.secScal_sval (hb' i) r z hJ, ← SectionScalarValuation.secScal_sval (secScal_of_isPullSec P.A P.isLB N k (hb'' i)) _ z hJ,
    ← SectionScalarValuation.secScal_sval ((hE _ _).2 (E.apply_symm_apply (b₀ i))) _ z hJ, Category.assoc, Category.assoc, θ₄]

end GlobalTheory.SpanFrame
end
end

