import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0011
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0009
import Development.AutomorphicSpectrum.PublishedTheorems.PublishedGlobalResults.HasInfCharOfIsRegAlg
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0542
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0524
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0545
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0447

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.KernelFourierIntegrationByParts
section
open Ad3 Ad3.S MeasureTheory Complex Filter Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.HalfIntegral

lemma KK_one_eq (α β : ℂ) (t : ℝ) :
    KK α β 1 t = ((1 : ℂ) + (-I) * t) ^ (-α) * ((1 : ℂ) + I * t) ^ (-β) := by
  simp [KK, sub_eq_add_neg]

lemma mem_slit (c : ℂ) (hc : c.re = 0) (t : ℝ) : (1 : ℂ) + c * t ∈ slitPlane := by
  rw [Complex.mem_slitPlane_iff]
  left
  simp [hc]

lemma hasDerivAt_factor (a c : ℂ) (hc : c.re = 0) (t : ℝ) :
    HasDerivAt (fun u : ℝ => ((1 : ℂ) + c * u) ^ (-a))
      (-a * c * ((1 : ℂ) + c * t) ^ (-(a + 1))) t := by
  have h1 : HasDerivAt (fun z : ℂ => 1 + c * z) c (t : ℂ) := by
    simpa using ((hasDerivAt_id (t : ℂ)).const_mul c).const_add 1
  have h2 := (h1.cpow_const (c := -a) (mem_slit c hc t)).comp_ofReal
  have e : -a - 1 = -(a + 1) := by ring
  rw [e] at h2
  convert h2 using 1
  ring

lemma hasDerivAt_KK (α β : ℂ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => KK α β 1 u)
      (I * α * KK (α + 1) β 1 t - I * β * KK α (β + 1) 1 t) t := by
  have h1 := hasDerivAt_factor α (-I) (by simp) t
  have h2 := hasDerivAt_factor β I (by simp) t
  have h3 := h1.mul h2
  have e : (fun u : ℝ => KK α β 1 u) =
      (fun u : ℝ => ((1 : ℂ) + (-I) * u) ^ (-α) * ((1 : ℂ) + I * u) ^ (-β)) := by
    funext u; exact KK_one_eq α β u
  rw [e]
  refine HasDerivAt.congr_deriv (f := fun u : ℝ => ((1 : ℂ) + (-I) * u) ^ (-α) * ((1 : ℂ) + I * u) ^ (-β)) h3 ?_
  rw [KK_one_eq, KK_one_eq]
  ring

lemma continuous_KK (α β : ℂ) : Continuous fun t : ℝ => KK α β 1 t :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_KK α β t).continuousAt

lemma norm_cpow_le (z w : ℂ) (hz : z ≠ 0) :
    ‖z ^ w‖ ≤ ‖z‖ ^ w.re * Real.exp (Real.pi * |w.im|) := by
  rw [Complex.norm_cpow_of_ne_zero hz, div_eq_mul_inv, ← Real.exp_neg]
  have h : -(arg z * w.im) ≤ Real.pi * |w.im| := by
    calc -(arg z * w.im) ≤ |arg z * w.im| := neg_le_abs _
      _ = |arg z| * |w.im| := abs_mul _ _
      _ ≤ Real.pi * |w.im| := by
        gcongr
        exact Complex.abs_arg_le_pi z
  gcongr

lemma norm_factor (c : ℂ) (hc : c = I ∨ c = -I) (t : ℝ) :
    ‖(1 : ℂ) + c * t‖ = (1 + t ^ 2) ^ (1 / 2 : ℝ) := by
  rw [← Real.sqrt_eq_rpow, Complex.norm_eq_sqrt_sq_add_sq]
  rcases hc with rfl | rfl <;> simp

lemma norm_KK_le (α β : ℂ) (t : ℝ) :
    ‖KK α β 1 t‖ ≤ (Real.exp (Real.pi * |α.im|) * Real.exp (Real.pi * |β.im|)) *
      (1 + t ^ 2) ^ (-(α + β).re / 2) := by
  have hp : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have ne1 : (1 : ℂ) + (-I) * t ≠ 0 := slitPlane_ne_zero (mem_slit _ (by simp) t)
  have ne2 : (1 : ℂ) + I * t ≠ 0 := slitPlane_ne_zero (mem_slit _ (by simp) t)
  have a1 := norm_cpow_le _ (-α) ne1
  have a2 := norm_cpow_le _ (-β) ne2
  rw [norm_factor _ (Or.inr rfl), ← Real.rpow_mul hp.le] at a1
  rw [norm_factor _ (Or.inl rfl), ← Real.rpow_mul hp.le] at a2
  simp only [neg_re, neg_im, abs_neg] at a1 a2
  rw [KK_one_eq, norm_mul]
  calc _ ≤ _ := mul_le_mul a1 a2 (norm_nonneg _) (by positivity)
    _ = _ := by
      have : -(α + β).re / 2 = 1 / 2 * -α.re + 1 / 2 * -β.re := by simp only [add_re]; ring
      rw [this, Real.rpow_add hp]
      ring

lemma integrable_KK (α β : ℂ) (h : 1 < (α + β).re) : Integrable fun t : ℝ => KK α β 1 t := by
  have h0 : Integrable fun t : ℝ => (1 + ‖t‖ ^ 2) ^ (-(α + β).re / 2) :=
    integrable_rpow_neg_one_add_norm_sq (by simpa using h)
  refine (h0.const_mul (Real.exp (Real.pi * |α.im|) * Real.exp (Real.pi * |β.im|))).mono'
    (continuous_KK α β).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
  simpa using norm_KK_le α β t

lemma tendsto_KK (α β : ℂ) (h : 0 < (α + β).re) (l : Filter ℝ) (hl : Tendsto (fun t : ℝ => |t|) l atTop) :
    Tendsto (fun t : ℝ => KK α β 1 t) l (𝓝 0) := by
  have h1 : Tendsto (fun t : ℝ => 1 + t ^ 2) l atTop := by
    refine tendsto_atTop_add_const_left _ _ ?_
    have := (tendsto_pow_atTop (α := ℝ) (n := 2) two_ne_zero).comp hl
    simpa [Function.comp_def] using this
  have h2 : Tendsto (fun t : ℝ => (1 + t ^ 2) ^ (-((α + β).re / 2))) l (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by positivity)).comp h1
  have h3 := h2.const_mul (Real.exp (Real.pi * |α.im|) * Real.exp (Real.pi * |β.im|))
  rw [mul_zero] at h3
  refine squeeze_zero_norm (fun t => ?_) h3
  have := norm_KK_le α β t
  rwa [neg_div] at this

lemma norm_ee_neg (ξ t : ℝ) : ‖ee (-(ξ * t))‖ = 1 := by
  have : (2 * (Real.pi : ℂ) * I * (-((ξ : ℂ) * t))) = ((-(2 * Real.pi * ξ * t) : ℝ) : ℂ) * I := by
    push_cast; ring
  rw [ee, this, Complex.norm_exp_ofReal_mul_I]

lemma hasDerivAt_ee (ξ t : ℝ) :
    HasDerivAt (fun u : ℝ => ee (-(ξ * u))) (-(2 * Real.pi * I * ξ) * ee (-(ξ * t))) t := by
  have h1 : HasDerivAt (fun z : ℂ => (-(2 * Real.pi * I * ξ)) * z) (-(2 * Real.pi * I * ξ)) (t : ℂ) := by
    simpa using (hasDerivAt_id (t : ℂ)).const_mul (-(2 * (Real.pi : ℂ) * I * ξ))
  have h2 := h1.cexp.comp_ofReal
  have e : (fun u : ℝ => ee (-(ξ * u))) = fun u : ℝ => cexp ((-(2 * Real.pi * I * ξ)) * u) := by
    funext u
    simp only [ee]
    congr 1
    ring
  have e2 : ee (-(ξ * t)) = cexp ((-(2 * Real.pi * I * ξ)) * t) := by
    simp only [ee]
    congr 1
    ring
  rw [e, e2]
  exact h2.congr_deriv (by ring)

lemma continuous_ee (ξ : ℝ) : Continuous fun t : ℝ => ee (-(ξ * t)) :=
  continuous_iff_continuousAt.2 fun t => (hasDerivAt_ee ξ t).continuousAt

lemma integrable_KK_ee (α β : ℂ) (h : 1 < (α + β).re) (ξ : ℝ) :
    Integrable fun t : ℝ => KK α β 1 t * ee (-(ξ * t)) := by
  refine (integrable_KK α β h).norm.mono'
    ((continuous_KK α β).mul (continuous_ee ξ)).aestronglyMeasurable
    (Eventually.of_forall fun t => ?_)
  simp [norm_ee_neg]

lemma Phi_ibp (α β : ℂ) (h : 1 < (α + β).re) (ξ : ℝ) :
    2 * Real.pi * ξ * Phi α β ξ = α * Phi (α + 1) β ξ - β * Phi α (β + 1) ξ := by
  have hα : 1 < (α + 1 + β).re := by simp only [add_re, one_re] at *; linarith
  have hβ : 1 < (α + (β + 1)).re := by simp only [add_re, one_re] at *; linarith
  have i1 := (integrable_KK_ee (α + 1) β hα ξ).const_mul (I * α)
  have i2 := (integrable_KK_ee α (β + 1) hβ ξ).const_mul (I * β)
  have i3 := (integrable_KK_ee α β h ξ).const_mul (2 * Real.pi * I * ξ)
  have hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => KK α β 1 u * ee (-(ξ * u)))
      (I * α * (KK (α + 1) β 1 t * ee (-(ξ * t))) - I * β * (KK α (β + 1) 1 t * ee (-(ξ * t))) -
        2 * Real.pi * I * ξ * (KK α β 1 t * ee (-(ξ * t)))) t := by
    intro t
    refine HasDerivAt.congr_deriv (f := fun u : ℝ => KK α β 1 u * ee (-(ξ * u)))
      ((hasDerivAt_KK α β t).mul (hasDerivAt_ee ξ t)) ?_
    ring
  have tz : ∀ l : Filter ℝ, Tendsto (fun t : ℝ => |t|) l atTop →
      Tendsto (fun u : ℝ => KK α β 1 u * ee (-(ξ * u))) l (𝓝 0) := by
    intro l hl
    refine squeeze_zero_norm (fun t => ?_) (tendsto_zero_iff_norm_tendsto_zero.1
      (tendsto_KK α β (by linarith) l hl))
    simp [norm_ee_neg]
  have i12 : Integrable (fun t : ℝ => I * α * (KK (α + 1) β 1 t * ee (-(ξ * t))) -
      I * β * (KK α (β + 1) 1 t * ee (-(ξ * t)))) := i1.sub i2
  have key := integral_of_hasDerivAt_of_tendsto hd (i12.sub i3)
    (tz atBot tendsto_abs_atBot_atTop) (tz atTop tendsto_abs_atTop_atTop)
  rw [integral_sub i12 i3, integral_sub i1 i2, integral_const_mul, integral_const_mul,
    integral_const_mul, sub_zero] at key
  have key' : I * α * Phi (α + 1) β ξ - I * β * Phi α (β + 1) ξ -
      2 * Real.pi * I * ξ * Phi α β ξ = 0 := key
  have : I * (2 * Real.pi * ξ * Phi α β ξ - (α * Phi (α + 1) β ξ - β * Phi α (β + 1) ξ)) = 0 := by
    linear_combination -key'
  rcases mul_eq_zero.1 this with h0 | h0
  · exact absurd h0 I_ne_zero
  · exact sub_eq_zero.1 h0

lemma KK_split (α β : ℂ) (t : ℝ) :
    2 * KK (α + 1) β 1 t = KK α β 1 t + KK (α + 1) (β - 1) 1 t := by
  have ne1 : (1 : ℂ) + (-I) * t ≠ 0 := slitPlane_ne_zero (mem_slit _ (by simp) t)
  have ne2 : (1 : ℂ) + I * t ≠ 0 := slitPlane_ne_zero (mem_slit _ (by simp) t)
  have e1 : ((1 : ℂ) + (-I) * t) ^ (-α) = ((1 : ℂ) + (-I) * t) ^ (-(α + 1)) * ((1 : ℂ) + (-I) * t) := by
    have : -α = -(α + 1) + 1 := by ring
    rw [this, cpow_add _ _ ne1, cpow_one]
  have e2 : ((1 : ℂ) + I * t) ^ (-(β - 1)) = ((1 : ℂ) + I * t) ^ (-β) * ((1 : ℂ) + I * t) := by
    have : -(β - 1) = -β + 1 := by ring
    rw [this, cpow_add _ _ ne2, cpow_one]
  rw [KK_one_eq, KK_one_eq, KK_one_eq, e1, e2]
  ring

lemma Phi_zero (α β : ℂ) (h : 1 < (α + β).re) :
    (α + β - 1) * Phi α β 0 = 2 * α * Phi (α + 1) β 0 := by
  have hα : 1 < (α + 1 + β).re := by simp only [add_re, one_re] at *; linarith
  have hm : 1 < (α + 1 + (β - 1)).re := by
    simp only [add_re, sub_re, one_re] at *; linarith
  have hz : 0 < (α + (β - 1)).re := by
    simp only [add_re, sub_re, one_re] at *; linarith
  have ee0 : ∀ t : ℝ, ee (-(((0 : ℝ) : ℂ) * t)) = 1 := by intro t; simp [ee]
  have P : ∀ a b : ℂ, Phi a b 0 = ∫ t : ℝ, KK a b 1 t := by
    intro a b
    simp only [Phi, ee0, mul_one]
  have i1 := (integrable_KK (α + 1) (β - 1) hm).const_mul (I * α)
  have i2 := (integrable_KK α β h).const_mul (I * (β - 1))
  have hd : ∀ t : ℝ, HasDerivAt (fun u : ℝ => KK α (β - 1) 1 u)
      (I * α * KK (α + 1) (β - 1) 1 t - I * (β - 1) * KK α β 1 t) t := by
    intro t
    have := hasDerivAt_KK α (β - 1) t
    rwa [sub_add_cancel] at this
  have key := integral_of_hasDerivAt_of_tendsto hd (i1.sub i2)
    (tendsto_KK α (β - 1) hz atBot tendsto_abs_atBot_atTop)
    (tendsto_KK α (β - 1) hz atTop tendsto_abs_atTop_atTop)
  rw [integral_sub i1 i2, integral_const_mul, integral_const_mul, sub_zero, ← P, ← P] at key
  have two : 2 * Phi (α + 1) β 0 = Phi α β 0 + Phi (α + 1) (β - 1) 0 := by
    rw [P, P, P, ← integral_const_mul, ← integral_add (integrable_KK α β h)
      (integrable_KK (α + 1) (β - 1) hm)]
    exact integral_congr_ae (Eventually.of_forall fun t => KK_split α β t)
  have key2 : α * Phi (α + 1) (β - 1) 0 = (β - 1) * Phi α β 0 := by
    have : I * (α * Phi (α + 1) (β - 1) 0 - (β - 1) * Phi α β 0) = 0 := by
      linear_combination key
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 I_ne_zero
    · exact sub_eq_zero.1 h0
  linear_combination (-α) * two - key2

theorem kernel_fourier_integration_by_parts : W0 → W1 := fun _ α β h =>
  ⟨fun ξ => Phi_ibp α β h ξ, Phi_zero α β h⟩

end GlobalTheory.CompanionTheory.HalfIntegral

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LatticeSumPartialFourierUnfolding
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Period

variable {D : D7}

theorem rat_sub' {m n : ℕ} (p p₀ : Matrix (Fin m) (Fin n) D.host.E) :
    (rat (p - p₀) : Mx D m n) = rat p - rat p₀ := by
  ext i j
  simp [rat]

theorem psi_inner_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {s : ℕ}
    (q q₀ : Matrix (Fin V.rank) (Fin s) D.host.E) :
    ψ (trA (Matrix.trace (inner V (rat q) (rat q₀)))) = 1 := by
  have h : (inner V (rat q) (rat q₀) : Mx D s s) = rat (qᴴ * (V.gram * q₀)) := by
    change (adj (rat q) ⬝ (gA V ⬝ rat q₀) : Mx D s s) = rat (qᴴ * (V.gram * q₀))
    rw [rat_mul, rat_mul, rat_conjTranspose, gA]
  have ht : ∀ M : Matrix (Fin s) (Fin s) D.host.E,
      Matrix.trace (rat M : Mx D s s) = incA D (Matrix.trace M) := fun M => by
    simp only [rat, Matrix.trace, Matrix.diag, Matrix.map_apply, map_sum]
  rw [h, ht, GlobalTheory.CompanionTheory.ThetaInv.trA_incA]
  exact hψ.2.2.1 _

theorem inner_add_right' (V : HSp D) {s : ℕ} (x y z : Mx D V.rank s) :
    (inner V x (y + z) : Mx D s s) = inner V x y + inner V x z := by
  change (adj x ⬝ (gA V ⬝ (y + z)) : Mx D s s) = adj x ⬝ (gA V ⬝ y) + adj x ⬝ (gA V ⬝ z)
  simp [Matrix.mul_add]

theorem trA_add' (x y : AE D) : trA (x + y) = trA x + trA y := by
  simp [trA]

theorem term_shift {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (V : HSp D) {r s : ℕ}
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E)
    (Φ : Mx D V.rank (r + s) → ℂ)
    (p p₀ : Matrix (Fin V.rank) (Fin r) D.host.E) (q q₀ : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s) :
    cellTerm ψ V b a Φ p q (y₁ + rat p₀) (y₂ + rat q₀) = cellTerm ψ V b a Φ (p - p₀) q y₁ y₂ := by
  have e₁ : y₁ + rat p₀ - rat p = y₁ - rat (p - p₀) := by rw [rat_sub']; abel
  have e₂ : rat p - (y₁ + rat p₀) = rat (p - p₀) - y₁ := by rw [rat_sub']; abel
  have e₃ : ψ (trA (Matrix.trace (inner V (rat q) (y₂ + rat q₀)))) =
      ψ (trA (Matrix.trace (inner V (rat q) y₂))) := by
    rw [inner_add_right', Matrix.trace_add, trA_add', AddChar.map_add_eq_mul, psi_inner_rat hψ, mul_one]
  unfold cellTerm
  rw [e₁, e₂, e₃]

theorem tsum_cellTerm_add_rat : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (V : HSp D) (r s : ℕ)
    (b : Matrix (Fin r) (Fin r) D.host.E) (a : Matrix (Fin (r + s)) (Fin (r + s)) D.host.E) (Φ : Mx D V.rank (r + s) → ℂ)
    (p₀ : Matrix (Fin V.rank) (Fin r) D.host.E) (q₀ : Matrix (Fin V.rank) (Fin s) D.host.E)
    (y₁ : Mx D V.rank r) (y₂ : Mx D V.rank s),
    ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b a Φ pq.1 pq.2 (y₁ + rat p₀) (y₂ + rat q₀) =
      ∑' pq : Matrix (Fin V.rank) (Fin r) D.host.E × Matrix (Fin V.rank) (Fin s) D.host.E,
        cellTerm ψ V b a Φ pq.1 pq.2 y₁ y₂ := by
  intro D ψ hψ V r s b a Φ p₀ q₀ y₁ y₂
  simp only [term_shift hψ]
  exact (Equiv.prodCongr (Equiv.subRight p₀) (Equiv.refl _)).tsum_eq
    (fun pq => cellTerm ψ V b a Φ pq.1 pq.2 y₁ y₂)

end GlobalTheory.CompanionTheory.EisUnfold.Period

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieActionSkewAdjointL2
section
noncomputable section

open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary PositivityTheory.S2.Clozel Filter Topology
open scoped ComplexConjugate InnerProductSpace

namespace GlobalTheory.CompanionTheory.PeterssonSkew

theorem integral_deriv_eq_zero {Q : Type*} [MeasurableSpace Q] (ν : Measure Q) [IsFiniteMeasure ν]
    (u v u' v' : ℝ → Q → ℂ) (C : ℝ)
    (hu : ∀ t q, HasDerivAt (fun s => u s q) (u' t q) t) (hv : ∀ t q, HasDerivAt (fun s => v s q) (v' t q) t)
    (bu : ∀ t q, ‖u t q‖ ≤ C) (bv : ∀ t q, ‖v t q‖ ≤ C) (bu' : ∀ t q, ‖u' t q‖ ≤ C) (bv' : ∀ t q, ‖v' t q‖ ≤ C)
    (mu : ∀ t, AEStronglyMeasurable (u t) ν) (mv : ∀ t, AEStronglyMeasurable (v t) ν)
    (mu' : AEStronglyMeasurable (u' 0) ν) (mv' : AEStronglyMeasurable (v' 0) ν)
    (hc : ∀ t, ∫ q, u t q * conj (v t q) ∂ν = ∫ q, u 0 q * conj (v 0 q) ∂ν) :
    ∫ q, (u' 0 q * conj (v 0 q) + u 0 q * conj (v' 0 q)) ∂ν = 0 := by
  have mc : ∀ {f : Q → ℂ}, AEStronglyMeasurable f ν → AEStronglyMeasurable (fun q => conj (f q)) ν :=
    fun h => Complex.continuous_conj.comp_aestronglyMeasurable h
  have hC : 0 ≤ C ∨ IsEmpty Q := by
    by_cases h : Nonempty Q
    · obtain ⟨q⟩ := h
      exact Or.inl ((norm_nonneg _).trans (bu 0 q))
    · exact Or.inr (not_nonempty_iff.1 h)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := ν) (x₀ := (0 : ℝ)) (s := Set.univ)
    (F := fun t q => u t q * conj (v t q))
    (F' := fun t q => u' t q * conj (v t q) + u t q * conj (v' t q))
    (bound := fun _ => C * C + C * C) Filter.univ_mem
    (Eventually.of_forall fun t => (mu t).mul (mc (mv t)))
    (Integrable.of_bound ((mu 0).mul (mc (mv 0))) (C * C) (Eventually.of_forall fun q => by
      rw [norm_mul, RCLike.norm_conj]
      exact mul_le_mul (bu 0 q) (bv 0 q) (norm_nonneg _) ((norm_nonneg _).trans (bu 0 q))))
    ((mu'.mul (mc (mv 0))).add ((mu 0).mul (mc mv')))
    (Eventually.of_forall fun q t _ => by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul, RCLike.norm_conj]
      · exact mul_le_mul (bu' t q) (bv t q) (norm_nonneg _) ((norm_nonneg _).trans (bu' t q))
      · exact mul_le_mul (bu t q) (bv' t q) (norm_nonneg _) ((norm_nonneg _).trans (bu t q)))
    (integrable_const _)
    (Eventually.of_forall fun q t _ => (hu t q).mul (hv t q).star)
  have h0 : HasDerivAt (fun t : ℝ => ∫ q, u t q * conj (v t q) ∂ν) 0 0 := by
    simp only [hc]
    exact hasDerivAt_const _ _
  exact key.2.unique h0

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

open scoped Matrix.Norms.Operator in

theorem exists_curve (X : Lie E a) : ∃ c : ℝ → Matrix.GeneralLinearGroup (Fin a) (Cinf E), c 0 = 1 ∧
    (∀ s t, c (s + t) = c s * c t) ∧ HasDerivAt (fun t => toL (c t).val) X 0 := by
  set Y : Matrix (Fin a) (Fin a) (Cinf E) := Matrix.of X with hY
  haveI : CompleteSpace (Matrix (Fin a) (Fin a) (Cinf E)) := FiniteDimensional.complete ℝ _
  have hadd : ∀ s t : ℝ, NormedSpace.exp ((s + t) • Y) = NormedSpace.exp (s • Y) * NormedSpace.exp (t • Y) := fun s t => by
    rw [add_smul]
    exact NormedSpace.exp_add_of_commute (((Commute.refl Y).smul_left s).smul_right t)
  have hone : ∀ t : ℝ, NormedSpace.exp (t • Y) * NormedSpace.exp ((-t) • Y) = 1 := fun t => by
    rw [← hadd, add_neg_cancel, zero_smul, NormedSpace.exp_zero]
  refine ⟨fun t => ⟨NormedSpace.exp (t • Y), NormedSpace.exp ((-t) • Y), hone t, by simpa using hone (-t)⟩,
    Units.ext (by simp [NormedSpace.exp_zero]), fun s t => Units.ext (hadd s t), ?_⟩
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) Y (0 : ℝ)
  simp only [zero_smul, NormedSpace.exp_zero, one_mul] at h
  let L : Matrix (Fin a) (Fin a) (Cinf E) →L[ℝ] Lie E a :=
    LinearMap.toContinuousLinearMap (Matrix.ofLinearEquiv ℝ).symm.toLinearMap
  exact L.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h

theorem hasDerivAt_translate {X : Lie E a} {c : ℝ → Matrix.GeneralLinearGroup (Fin a) (Cinf E)} (h0 : c 0 = 1)
    (hadd : ∀ s t, c (s + t) = c s * c t) (hX : HasDerivAt (fun t => toL (c t).val) X 0) (φ : Sm E a) (g : GA E a)
    (t : ℝ) : HasDerivAt (fun s => φ.1 (g * infGL E a (c s))) (lieD X φ.1 (g * infGL E a (c t))) t := by
  have h := hasDerivAt_curve φ (g * infGL E a (c t)) c X h0 hX
  have h2 : HasDerivAt (fun s => φ.1 (g * infGL E a (c t) * infGL E a (c (s - t))))
      (lieD X φ.1 (g * infGL E a (c t))) t := HasDerivAt.comp_sub_const t t (by simpa using h)
  refine h2.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
  simp only [mul_assoc, ← map_mul, ← hadd]
  simp

theorem pet_mul_right (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] {φ ψ : GA E a → ℂ}
    (hφ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ) (hψ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ ψ) (g : GA E a) :
    pet (GlobalTheory.UnitaryBC.latticeGL E a) μ (fun x => φ (x * g)) (fun x => ψ (x * g)) =
      pet (GlobalTheory.UnitaryBC.latticeGL E a) μ φ ψ := by
  rw [← MemL2Quotient.inner_toL2_eq_theta_pairing (hφ.mul_right g) (hψ.mul_right g), ← right_translate_toL2, ← right_translate_toL2, ← MemL2Quotient.inner_toL2_eq_theta_pairing hφ hψ]
  exact LinearIsometry.inner_map_map
    { toLinearMap := (R (GlobalTheory.UnitaryBC.latticeGL E a) μ g :
        L2 (GlobalTheory.UnitaryBC.latticeGL E a) μ →L[ℂ] L2 (GlobalTheory.UnitaryBC.latticeGL E a) μ).toLinearMap
      norm_map' := norm_R g } _ _

theorem pet_lie_add (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (X : Lie E a) (φ ψ : Sm E a)
    (hφ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1) (hψ : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ ψ.1)
    (hφ' : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X φ).1)
    (hψ' : MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X ψ).1)
    (C : ℝ) (bφ : ∀ g, ‖φ.1 g‖ ≤ C) (bψ : ∀ g, ‖ψ.1 g‖ ≤ C)
    (bφ' : ∀ g, ‖(lie E a X φ).1 g‖ ≤ C) (bψ' : ∀ g, ‖(lie E a X ψ).1 g‖ ≤ C) :
    pet (GlobalTheory.UnitaryBC.latticeGL E a) μ (lie E a X φ).1 ψ.1 +
      pet (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 (lie E a X ψ).1 = 0 := by
  haveI := GlobalTheory.CovolGL.isFiniteMeasure_quotMeasure E a μ
  obtain ⟨c, h0, hadd, hX⟩ := exists_curve X
  have e0 : infGL E a (c 0) = 1 := by rw [h0, map_one]
  have key := integral_deriv_eq_zero (GlobalTheory.AutomorphicL2Unitary.quotMeasure (GlobalTheory.UnitaryBC.latticeGL E a) μ)
    (fun t q => φ.1 (q.out * infGL E a (c t))) (fun t q => ψ.1 (q.out * infGL E a (c t)))
    (fun t q => lieD X φ.1 (q.out * infGL E a (c t))) (fun t q => lieD X ψ.1 (q.out * infGL E a (c t))) C
    (fun t q => hasDerivAt_translate h0 hadd hX φ q.out t) (fun t q => hasDerivAt_translate h0 hadd hX ψ q.out t)
    (fun _ _ => bφ _) (fun _ _ => bψ _) (fun _ _ => bφ' _) (fun _ _ => bψ' _)
    (fun t => (hφ.mul_right (infGL E a (c t))).2.1) (fun t => (hψ.mul_right (infGL E a (c t))).2.1)
    (by simp only [e0, mul_one]; exact hφ'.2.1) (by simp only [e0, mul_one]; exact hψ'.2.1)
    (fun t => by
      have h1 := pet_mul_right μ hφ hψ (infGL E a (c t))
      simp only [e0, mul_one]
      exact h1)
  simp only [e0, mul_one] at key
  exact (integral_add (hφ'.integrable_mul_conj hψ) (hφ.integrable_mul_conj hψ')).symm.trans key

theorem lie_skew_adjoint : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a) (hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1), (∀ φ ∈ π.V, ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C) → ∀ (X : Lie E a) (φ ψ : π.V), inner ℂ (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm ψ) (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm (π.op (.lie X) φ)) = -inner ℂ (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm (π.op (.lie X) ψ)) (GlobalTheory.CuspRep.CuspidalL2GL.toL2ₗ μ π.V hm φ) := by
  intro E _ _ _ a μ _ _ π hm hb X φ ψ
  have hL : ∀ f : π.V, ∃ C : ℝ, ∀ g, ‖f.1.1 g‖ ≤ C := fun f => hb f.1 f.2
  obtain ⟨C₁, b₁⟩ := hL φ
  obtain ⟨C₂, b₂⟩ := hL ψ
  obtain ⟨C₃, b₃⟩ := hL (π.op (.lie X) φ)
  obtain ⟨C₄, b₄⟩ := hL (π.op (.lie X) ψ)
  have h := pet_lie_add μ X φ.1 ψ.1 (hm _ φ.2) (hm _ ψ.2) (hm _ (π.op (.lie X) φ).2) (hm _ (π.op (.lie X) ψ).2)
    (max (max C₁ C₂) (max C₃ C₄))
    (fun g => (b₁ g).trans ((le_max_left _ _).trans (le_max_left _ _)))
    (fun g => (b₂ g).trans ((le_max_right _ _).trans (le_max_left _ _)))
    (fun g => (b₃ g).trans ((le_max_left _ _).trans (le_max_right _ _)))
    (fun g => (b₄ g).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have e1 := MemL2Quotient.inner_toL2_eq_theta_pairing (hm _ (π.op (.lie X) φ).2) (hm _ ψ.2)
  have e2 := MemL2Quotient.inner_toL2_eq_theta_pairing (hm _ φ.2) (hm _ (π.op (.lie X) ψ).2)
  change inner ℂ (hm _ ψ.2).toL2 (hm _ (π.op (.lie X) φ).2).toL2 =
    -inner ℂ (hm _ (π.op (.lie X) ψ).2).toL2 (hm _ φ.2).toL2
  rw [e1, e2]
  exact eq_neg_of_add_eq_zero_left h

end GlobalTheory.CompanionTheory.PeterssonSkew
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LieOperatorHermitianSkew
section
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.ClozelHerm

theorem op_lie_single_neg {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ} (π : CuspSub E a)
    (i j : Fin a) (x : Cinf E) :
    π.op (.lie (toL (Matrix.single i j (-x)))) = -π.op (.lie (toL (Matrix.single i j x))) := by
  refine LinearMap.ext fun φ => Subtype.ext ?_
  change lieS E a i j (-x) φ.1 = -(lieS E a i j x φ.1)
  rw [map_neg]
  rfl

theorem EopV_adjoint : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a)
    (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ), IsHerm π B → ∀ (τ : E →+* ℂ) (i j : Fin a) (φ ψ : π.V),
    B (EopV π τ i j φ) ψ = -B φ (EopV π (NumberField.ComplexEmbedding.conjugate τ) i j ψ) := by
  intro E _ _ _ a π B hB τ i j φ ψ
  have e1 : atEmb (ComplexEmbedding.conjugate τ) 1 = atEmb τ 1 := by rw [atEmb_conj, map_one]
  have e2 : atEmb (ComplexEmbedding.conjugate τ) Complex.I = -atEmb τ Complex.I := by
    rw [atEmb_conj, Complex.conj_I, atEmb_eq, atEmb_eq τ Complex.I]
    simp
  have c2 : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by
    rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
    exact Complex.conj_ofReal _
  have s1 := hB.1 (toL (Matrix.single i j (atEmb τ 1))) φ ψ
  have s2 := hB.1 (toL (Matrix.single i j (atEmb τ Complex.I))) φ ψ
  simp only [EopV, e1, e2, op_lie_single_neg, LinearMap.smul_apply, LinearMap.sub_apply, LinearMap.neg_apply, LinearMap.add_apply,
    map_smul, map_sub, map_neg, map_smulₛₗ, c2, Complex.conj_I, smul_eq_mul, s1, s2, RingHom.id_apply, smul_neg,
    sub_neg_eq_add, map_add]
  ring

end GlobalTheory.CompanionTheory.ClozelHerm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGramFibreMeasureStandardVolumeStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Coef
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_gram_fibre_measure_standard_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (hJ : IsHermND σ J) (n : ℕ), 2 * n < M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ mv : HermR (Fv F v) σ n → Measure (Fin n → Fin M → Fv F v ⊗[F] E), GlobalTheory.CompanionTheory.SW.IsGramFib (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ c : HermR (Fv F v) σ n, IsUnit (c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)).det → ∀ A : Set (Fin n → Fin M → Fv F v ⊗[F] E), IsCompact A → IsOpen A → MeasurableSet A ∧ mv c A ≠ ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Coef.finV_compactOpenN | exact GlobalTheory.CompanionTheory.SiegelND.Coef.finV_compactOpenN | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Coef.finV_compactOpenN <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianHasBaseStatement
section
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_hermitian_has_base : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)), HasBase (sigR (Fv F v) σ) (intLoc F E v) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.Base.hasBase_place | exact GlobalTheory.CompanionTheory.KFin.Base.hasBase_place | (intros; apply GlobalTheory.CompanionTheory.KFin.Base.hasBase_place <;> assumption)
end

