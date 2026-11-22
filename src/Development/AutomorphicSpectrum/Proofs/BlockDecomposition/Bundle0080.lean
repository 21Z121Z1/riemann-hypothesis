import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0038
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0007
import Mathlib
import GroundTheory.GlobalFields.TateThesis.Bundle0004
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.StripEntire
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0063
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0073
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0058
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0056
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0030
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0059
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.Splits
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0025
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0012
import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.Descend
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0033
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.FrobeniusReciprocity.SupportedInIffOfFrob
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0043
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0034
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0071
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0035
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0061

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChangeVariablesZeroCount
section
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.CompanionTheory.FSCrofton

theorem clm_apply_eq_sum {d : ℕ} (T : V d →L[ℂ] ℂ) (v : V d) :
    T v = ∑ a, v a * T (EuclideanSpace.single a 1) := by
  conv_lhs => rw [← (EuclideanSpace.basisFun (Fin d) ℂ).sum_repr v]
  simp [map_sum]

theorem abs_det_restrictScalars_toEuclideanCLM {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    |((Matrix.toEuclideanCLM (𝕜 := ℂ) M : V d →L[ℂ] V d).restrictScalars ℝ).det| =
      ‖M.det‖ ^ 2 := by
  have h1 : ((Matrix.toEuclideanCLM (𝕜 := ℂ) M : V d →L[ℂ] V d).restrictScalars ℝ).det =
      Algebra.norm ℝ (LinearMap.det (Matrix.toEuclideanLin M : V d →ₗ[ℂ] V d)) := by
    rw [← LinearMap.det_restrictScalars]
    rfl
  rw [h1, Matrix.toEuclideanLin_eq_toLin, LinearMap.det_toLin, Algebra.norm_complex_eq]
  simp [Complex.normSq_eq_norm_sq]

theorem area_formula_neg_comb (d : ℕ) (β : Type) [Fintype β] (U A : Set (V d)) (f : β → V d → ℂ)
    (C : Fin d → β → ℂ) (h : (Fin d → ℂ) → ℝ≥0∞) (hU : IsOpen U)
    (hf : ∀ j, DifferentiableOn ℂ (f j) U) (hAU : A ⊆ U) (hA : MeasurableSet A)
    (hh : Measurable h) :
    ∫⁻ c : Fin d → ℂ, h c * (({z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0}.encard : ℕ∞) : ℝ≥0∞) =
      ∫⁻ z in A, h (fun k => -∑ j, C k j * f j z) *
        ENNReal.ofReal (‖(Matrix.of C * (Matrix.of fun j a =>
          fderiv ℂ (f j) z (EuclideanSpace.single a 1) : Matrix β (Fin d) ℂ)).det‖ ^ 2) := by
  classical
  let F : V d → Matrix β (Fin d) ℂ := fun z =>
    Matrix.of fun j a => fderiv ℂ (f j) z (EuclideanSpace.single a 1)
  let M : V d → Matrix (Fin d) (Fin d) ℂ := fun z => -(Matrix.of C * F z)
  let g : V d → V d := fun z => WithLp.toLp 2 (fun k => -∑ j, C k j * f j z)
  let L : V d → V d →L[ℂ] V d := fun z => Matrix.toEuclideanCLM (𝕜 := ℂ) (M z)
  let f' : V d → V d →L[ℝ] V d := fun z => (L z).restrictScalars ℝ
  have hderC : ∀ z ∈ A, HasFDerivWithinAt g (L z) A z := by
    intro z hz
    rw [hasFDerivWithinAt_euclidean]
    intro k
    have hj : ∀ j, HasFDerivAt (f j) (fderiv ℂ (f j) z) z := fun j =>
      ((hf j).differentiableAt (hU.mem_nhds (hAU hz))).hasFDerivAt
    have hs : HasFDerivAt (fun w => -∑ j, C k j * f j w)
        (-∑ j, C k j • fderiv ℂ (f j) z) z :=
      (HasFDerivAt.fun_sum fun j _ => (hj j).const_mul (C k j)).neg
    have he : PiLp.proj 2 (fun _ : Fin d => ℂ) k ∘L L z = -∑ j, C k j • fderiv ℂ (f j) z := by
      ext v
      have hv : ∀ j, fderiv ℂ (f j) z v = ∑ a, v a * F z j a := fun j => clm_apply_eq_sum _ v
      change ((Matrix.toEuclideanCLM (𝕜 := ℂ) (M z)) v).ofLp k = _
      rw [Matrix.ofLp_toEuclideanCLM]
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.sum_apply,
        ContinuousLinearMap.smul_apply, smul_eq_mul, hv]
      simp only [M, Matrix.mulVec, dotProduct, Matrix.neg_apply, Matrix.mul_apply, Matrix.of_apply,
        neg_mul, Finset.sum_neg_distrib, neg_inj]
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [he]
    exact hs.hasFDerivWithinAt
  have hder : ∀ z ∈ A, HasFDerivWithinAt g (f' z) A z := fun z hz =>
    (hderC z hz).restrictScalars ℝ
  have hdet : ∀ z, |(f' z).det| = ‖(Matrix.of C * F z).det‖ ^ 2 := by
    intro z
    have := abs_det_restrictScalars_toEuclideanCLM (M z)
    rw [show (M z).det = (-1) ^ Fintype.card (Fin d) * (Matrix.of C * F z).det from
      Matrix.det_neg _] at this
    simpa using this
  have hp : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin d → ℂ))
      (volume : Measure (Fin d → ℂ)) (volume : Measure (V d)) :=
    MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin d → ℂ)).symm
      (GlobalTheory.volume_preserving_ofLp_complex (Fin d))
  have hw := (GroundTheory.Heights₂.Heights.AreaMultiplicityWeight.proof (V d) volume A g f' hA hder).2
    (fun y => h y.ofLp) (hh.comp (MeasurableEquiv.toLp 2 (Fin d → ℂ)).symm.measurable)
  have hfib : ∀ c : Fin d → ℂ, {z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0} =
      {z ∈ A | g z = WithLp.toLp 2 c} := by
    intro c
    ext z
    simp only [Set.mem_setOf_eq, g]
    refine and_congr_right fun _ => ?_
    rw [(WithLp.toLp_injective 2).eq_iff, funext_iff]
    refine forall_congr' fun k => ?_
    rw [neg_eq_iff_add_eq_zero, add_comm]
  calc ∫⁻ c : Fin d → ℂ, h c * (({z ∈ A | ∀ k, c k + ∑ j, C k j * f j z = 0}.encard : ℕ∞) : ℝ≥0∞)
      = ∫⁻ c : Fin d → ℂ, (fun y : V d => (({z ∈ A | g z = y}.encard : ℕ∞) : ℝ≥0∞) * h y.ofLp)
          (MeasurableEquiv.toLp 2 (Fin d → ℂ) c) := by
        refine lintegral_congr fun c => ?_
        rw [hfib c, mul_comm]
        rfl
    _ = ∫⁻ y : V d, (({z ∈ A | g z = y}.encard : ℕ∞) : ℝ≥0∞) * h y.ofLp :=
        hp.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _)
          (fun y : V d => (({z ∈ A | g z = y}.encard : ℕ∞) : ℝ≥0∞) * h y.ofLp)
    _ = ∫⁻ z in A, h (g z).ofLp * ENNReal.ofReal |(f' z).det| := hw.symm
    _ = _ := by
        refine lintegral_congr fun z => ?_
        rw [hdet z]

end GlobalTheory.CompanionTheory.FSCrofton
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousUnitaryMultiplicativeEqArgPow
section
namespace GlobalTheory.CompanionTheory.KlocOp

theorem cstar_char_eq_zpow : ∀ φ : ℂ → ℂ, (∀ z w : ℂ, z ≠ 0 → w ≠ 0 → φ (z * w) = φ z * φ w) →
    ContinuousOn φ {z : ℂ | z ≠ 0} → (∀ z : ℂ, z ≠ 0 → ‖φ z‖ = 1) →
    (∀ r : ℝ, 0 < r → φ (r : ℂ) = 1) →
    ∃ k : ℤ, ∀ z : ℂ, z ≠ 0 → φ z = (z / (‖z‖ : ℂ)) ^ k := by
  intro φ hmul hc hn h1
  have hmem : ∀ z : ℂˣ, φ (z : ℂ) ∈ Submonoid.unitSphere ℂ := fun z => by
    simpa [Submonoid.unitSphere] using hn z z.ne_zero
  let f : ℂˣ → Circle := fun z => ⟨φ (z : ℂ), hmem z⟩
  have hfc : Continuous f := by
    refine Continuous.subtype_mk ?_ _
    exact hc.comp_continuous Units.continuous_val fun z => z.ne_zero
  have hf1 : f 1 = 1 := by
    apply Circle.ext
    have := h1 1 one_pos
    simpa [f] using this
  have hfm : ∀ a b : ℂˣ, f (a * b) = f a * f b := fun a b => by
    apply Circle.ext
    rw [Circle.coe_mul]
    change φ ((a * b : ℂˣ) : ℂ) = φ (a : ℂ) * φ (b : ℂ)
    rw [Units.val_mul]
    exact hmul a b a.ne_zero b.ne_zero
  let χ : ℂˣ →ₜ* Circle :=
    { toFun := f, map_one' := hf1, map_mul' := hfm, continuous_toFun := hfc }
  obtain ⟨⟨m, τ⟩, hp, -⟩ := GroundTheory.Global.existsUnique_complexUnits_circle χ
  have hp' : ∀ z : ℂˣ, φ (z : ℂ) = ((z : ℂ) / (‖(z : ℂ)‖ : ℂ)) ^ m *
      ((‖(z : ℂ)‖ : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) := hp
  have hr : ∀ r : ℝ, 0 < r → (r : ℂ) ^ ((τ : ℂ) * Complex.I) = 1 := by
    intro r hr0
    have hne : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
    have h := hp' (Units.mk0 (r : ℂ) hne)
    rw [Units.val_mk0, h1 r hr0, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr0,
      div_self hne, one_zpow, one_mul] at h
    exact h.symm
  refine ⟨m, fun z hz => ?_⟩
  have h := hp' (Units.mk0 z hz)
  rw [Units.val_mk0, hr _ (norm_pos_iff.mpr hz), mul_one] at h
  exact h

end GlobalTheory.CompanionTheory.KlocOp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CrossingOfWallsAndHeights
section
open Filter Topology PositivityTheory.RgEis

namespace GlobalTheory.CompanionTheory.RgEisCross

theorem sec_inv {G : Type} [Group G] [TopologicalSpace G] {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    {Γ K P : Subgroup G} {c : G → ℂ} {ρ : K →* (W →L[ℂ] W)} {w : W} (hP : IsPar Γ K P c)
    (law : ∀ p ∈ P, ∀ k : K, sec K P c ρ (p * k) w = c p • ρ k⁻¹ w) :
    ∀ γ ∈ Γ, γ ∈ P → ∀ x, sec K P c ρ (γ * x) w = sec K P c ρ x w := by
  intro γ hγ hγP x
  obtain ⟨p, hp, k, hk, rfl⟩ := hP.iwa x
  have h1 := law (γ * p) (P.mul_mem hγP hp) ⟨k, hk⟩
  have h2 := law p hp ⟨k, hk⟩
  simp only at h1 h2
  rw [← mul_assoc, h1, h2, hP.ch.mul γ hγP p hp, hP.ch.rat γ hγ hγP, one_mul]

theorem cross (hSec : SecLaw) (hHt : HtLip) (hSt : PiLocalization₂) (hWL : WallLaw) : Cross := by
  intro G _ _ _ _ _ W _ _ _ K ρ hK hρ Γ Q P P' c η η' β ξ L R D Op H Ω hPQ hP'Q hP hP' hη hη' hβ hξ hW hΩ hx
  haveI : CompleteSpace W := FiniteDimensional.complete ℂ W
  have parRes : ∀ (P : Subgroup G), IsPar Γ K P c → IsPar (Γ ⊓ Q) K P c := fun _ h =>
    ⟨h.closed, h.iwa, ⟨h.ch.mul, h.ch.norm, fun γ hγ hp => h.ch.rat γ hγ.1 hp, h.ch.cont⟩⟩
  have htRes : ∀ (P : Subgroup G) (f : G → ℝ), IsHt Γ K P f → IsHt (Γ ⊓ Q) K P f := fun _ _ h =>
    ⟨h.left, h.right, fun γ hγ hp => h.rat γ hγ.1 hp, h.cont⟩
  obtain ⟨-, -, hbound⟩ := hWL G W K ρ hK hρ (Γ ⊓ Q) P P' c η η' β L R D Op H (parRes P hP) (parRes P' hP')
    (htRes P η hη) (htRes P' η' hη') (htRes P' β hβ) hW
  have hξinv : ∀ γ ∈ Γ, γ ∈ Q → ∀ x, ξ (γ * x) = ξ x := by
    intro γ h1 h2 x
    rw [hξ.left γ h2, hξ.rat γ h1 h2, zero_add]
  have htinv : ∀ (P : Subgroup G) (f : G → ℝ), IsHt Γ K P f → ∀ γ ∈ Γ, γ ∈ P → ∀ x, f (γ * x) = f x := by
    intro P f hf γ h1 h2 x
    rw [hf.left γ h2, hf.rat γ h1 h2, zero_add]
  have iwaQ : Iwa Q K := fun g => by
    obtain ⟨p, hp, k, hk, e⟩ := hP.iwa g
    exact ⟨p, hPQ hp, k, hk, e⟩
  have mξ := hHt G Γ K Q ξ hK iwaQ hξ
  have mη := hHt G Γ K P η hK hP.iwa hη
  have mη' := hHt G Γ K P' η' hK hP'.iwa hη'
  have mβ := hHt G Γ K P' β hK hP'.iwa hβ
  let t : Cos (Γ ⊓ Q) Γ → ℂ × ℂ → G → (L →L[ℂ] W) := fun r l g =>
    Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g)
  have hhol : ∀ r g (p v : ℂ × ℂ), Differentiable ℂ fun τ : ℂ => t r (p + τ • v) g := by
    intro r g p v
    have h1 : Differentiable ℂ fun τ : ℂ => H (p + τ • v).1 (rep r * g) :=
      (hW.hol (rep r * g)).comp (by fun_prop)
    have h2 : Differentiable ℂ fun τ : ℂ => Complex.exp ((p + τ • v).2 * ξ (rep r * g)) := by fun_prop
    exact h2.smul h1
  have hcont : ∀ r, Continuous fun y : (ℂ × ℂ) × G => t r y.1 y.2 := by
    intro r
    have h0 : Continuous fun y : (ℂ × ℂ) × G => rep r * y.2 := by fun_prop
    have h1 : Continuous fun y : (ℂ × ℂ) × G => H y.1.1 (rep r * y.2) :=
      hW.cont.comp (continuous_fst.fst.prodMk h0)
    have h2 : Continuous fun y : (ℂ × ℂ) × G => ξ (rep r * y.2) := hξ.cont.comp h0
    have h3 : Continuous fun y : (ℂ × ℂ) × G => Complex.exp (y.1.2 * ξ (rep r * y.2)) :=
      Complex.continuous_exp.comp ((continuous_fst.snd).mul (Complex.continuous_ofReal.comp h2))
    exact h3.smul h1
  have hdom : ∀ x ∈ Ω, ∀ g, ∃ V ∈ 𝓝 x, ∃ U ∈ 𝓝 g, ∃ u : Cos (Γ ⊓ Q) Γ → ℝ, Summable u ∧
      ∀ l ∈ tube V, ∀ g' ∈ U, ∀ r, ‖t r l g'‖ ≤ u r := by
    intro x hxΩ g
    obtain ⟨a, b, ε, hε, hRa, hbR, hbx, hxa, hconv⟩ := hx x hxΩ
    obtain ⟨M, hM⟩ := hbound a b hRa hbR
    have inv₁ : ∀ γ ∈ Γ, γ ∈ P → ∀ x, (fun x => a * η x) (γ * x) = (fun x => a * η x) x := by
      intro γ h1 h2 x
      simp only [htinv P η hη γ h1 h2 x]
    have inv₂ : ∀ γ ∈ Γ, γ ∈ P' → ∀ x, (fun x => β x - b * η' x) (γ * x) = (fun x => β x - b * η' x) x := by
      intro γ h1 h2 x
      simp only [htinv P' η' hη' γ h1 h2 x, htinv P' β hβ γ h1 h2 x]
    have m₁ : ∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C, |a * η (g * u) - a * η g| ≤ A := by
      intro C hC
      obtain ⟨A, hA⟩ := mη C hC
      refine ⟨|a| * A, fun g u hu => ?_⟩
      rw [← mul_sub, abs_mul]
      exact mul_le_mul_of_nonneg_left (hA g u hu) (abs_nonneg a)
    have m₂ : ∀ C : Set G, IsCompact C → ∃ A : ℝ, ∀ g, ∀ u ∈ C,
        |(β (g * u) - b * η' (g * u)) - (β g - b * η' g)| ≤ A := by
      intro C hC
      obtain ⟨A, hA⟩ := mη' C hC
      obtain ⟨B, hB⟩ := mβ C hC
      refine ⟨B + |b| * A, fun g u hu => ?_⟩
      have e : (β (g * u) - b * η' (g * u)) - (β g - b * η' g) =
          (β (g * u) - β g) - b * (η' (g * u) - η' g) := by ring
      rw [e]
      refine (abs_sub _ _).trans (add_le_add (hB g u hu) ?_)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hA g u hu) (abs_nonneg b)
    have hl : |x.2 - ε - x.2| ≤ ε := by rw [sub_sub_cancel_left, abs_neg, abs_of_pos hε]
    have hr : |x.2 + ε - x.2| ≤ ε := by rw [add_sub_cancel_left, abs_of_pos hε]
    obtain ⟨U, hU, u, hu, hb⟩ := GlobalTheory.T.coarse_lipschitz_exponential_estimate G (L →L[ℂ] W) Γ (Γ ⊓ Q) P P' ξ (fun x => a * η x) (fun x => β x - b * η' x) H a b
      (x.2 - ε) (x.2 + ε) M mξ m₁ m₂ (hW.convR a hRa) (hW.convL b hbR) hM
      (GlobalTheory.T.coset_series_summable_shifted hSt G Γ Q P ξ _ _ hPQ hξinv inv₁ (hconv _ hl).1)
      (GlobalTheory.T.coset_series_summable_shifted hSt G Γ Q P ξ _ _ hPQ hξinv inv₁ (hconv _ hr).1)
      (GlobalTheory.T.coset_series_summable_shifted hSt G Γ Q P' ξ _ _ hP'Q hξinv inv₂ (hconv _ hl).2)
      (GlobalTheory.T.coset_series_summable_shifted hSt G Γ Q P' ξ _ _ hP'Q hξinv inv₂ (hconv _ hr).2) g
    refine ⟨Set.Icc b a ×ˢ Set.Icc (x.2 - ε) (x.2 + ε),
      prod_mem_nhds (Icc_mem_nhds hbx hxa) (Icc_mem_nhds (by linarith) (by linarith)), U, hU, u, hu, ?_⟩
    intro l hl g' hg' r
    obtain ⟨h1, h2⟩ := hl
    exact hb l h1.1 h1.2 h2.1 h2.2 g' hg' r
  obtain ⟨hTG, hsum⟩ := GlobalTheory.T.holomorphic_series_uniform_tube _ _ _ t Ω hhol hcont hdom
  have key : ∀ l ∈ tube Ω, ∀ g (w : L), outer Γ (Γ ⊓ Q) ξ H l g w =
      ∑' r : Cos (Γ ⊓ Q) Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w := by
    intro l hl g w
    have hs : Summable fun r => t r l g := (hsum l hl g).of_norm
    exact (ContinuousLinearMap.apply ℂ W w).map_tsum hs
  obtain ⟨law, -, Ms, hMs⟩ := hSec G W K ρ hK hρ Γ P c hP
  obtain ⟨law', -, Ms', hMs'⟩ := hSec G W K ρ hK hρ Γ P' c hP'
  refine ⟨hTG, hsum, ?_, ?_⟩
  · intro l hl hRl hconv g w
    have hw : (w : W) ∈ secSp K P c ρ := hW.le w.2
    rw [key l hl g w]
    have e : ∀ r : Cos (Γ ⊓ Q) Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w =
        D l.1 • (Complex.exp (l.2 * ξ (rep r * g)) •
          eis (Γ ⊓ Q) K P c ρ (fun x => l.1 * η x) (rep r * g) w) := by
      intro r
      rw [hW.eqR l.1 hRl, smul_comm]
    simp_rw [e]
    rw [tsum_const_smul'']
    congr 1
    refine GlobalTheory.T.section_invariance_coset_sum hSt G W Γ K Q P c ρ ξ (fun x => l.1.re * η x + l.2.re * ξ x) (fun x => l.1 * η x) l.2 w
      (Ms * ‖(w : W)‖) hPQ hξinv ?_ (sec_inv hP (law w hw)) (fun x => hMs x w) hconv ?_ g
    · intro γ h1 h2 x
      simp only [htinv P η hη γ h1 h2 x]
    · intro x
      simp
  · intro l hl hRl hconv g w
    have hw : ((Op l.1 w : secSp K P' c ρ) : W) ∈ secSp K P' c ρ := (Op l.1 w).2
    rw [key l hl g w]
    have e : ∀ r : Cos (Γ ⊓ Q) Γ, Complex.exp (l.2 * ξ (rep r * g)) • H l.1 (rep r * g) w =
        Complex.exp (l.2 * ξ (rep r * g)) •
          eis (Γ ⊓ Q) K P' c ρ (fun x => β x - l.1 * η' x) (rep r * g) (Op l.1 w) := by
      intro r
      rw [hW.eqL l.1 hRl]
    simp_rw [e]
    refine GlobalTheory.T.section_invariance_coset_sum hSt G W Γ K Q P' c ρ ξ (fun x => β x - l.1.re * η' x + l.2.re * ξ x)
      (fun x => (β x : ℂ) - l.1 * η' x) l.2 _ (Ms' * ‖((Op l.1 w : secSp K P' c ρ) : W)‖) hP'Q hξinv ?_
      (sec_inv hP' (law' _ hw)) (fun x => hMs' x _) hconv ?_ g
    · intro γ h1 h2 x
      simp only [htinv P' η' hη' γ h1 h2 x, htinv P' β hβ γ h1 h2 x]
    · intro x
      simp

end GlobalTheory.CompanionTheory.RgEisCross
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetWEqNormSqDetOneAddIStatement
section
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.detW_eq_normSq_det_one_add_I : ∀ (n : ℕ) (b : Matrix (Fin n) (Fin n) ℂ), b.IsHermitian →
    detW b = Complex.normSq (Matrix.det (1 + Complex.I • b)) := by
  first | exact @GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul | exact GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul | (intros; apply GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.detW_eq_normSq_det_one_add_I_smul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DichotomyOfComparableModSquareStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dichotomy_of_comparable_mod_square : ∀ {S : Type} [CommRing S] (ϖ : S), ϖ ∈ (⊥ : Ideal S).jacobson → (∀ f g : S, f ∈ Ideal.span {g, ϖ ^ 2} ∨ g ∈ Ideal.span {f, ϖ ^ 2}) → Dich ϖ := by
  first | exact @GlobalTheory.CompanionTheory.DichMod.dich_of_mod | exact GlobalTheory.CompanionTheory.DichMod.dich_of_mod | (intros; apply GlobalTheory.CompanionTheory.DichMod.dich_of_mod <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DisintegrationInjectiveOpenMapStatement
section
open MeasureTheory Topology
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.disintegration_injective_open_map : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (U : Set V) (fib : X → Measure V), IsOpen U → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι U ν Set.univ fib → ∀ φ : V → ℝ, Continuous φ → (∀ v, 0 ≤ φ v) → ∀ D : X → ℝ, Continuous D → (∀ A : Set X, MeasurableSet A → ∫⁻ v in f ⁻¹' (ι '' A), ENNReal.ofReal (φ v) ∂μ = ∫⁻ s in A, ENNReal.ofReal (D s) ∂ν) → (∀ ε : ℝ, 0 < ε → ∃ K : Set V, IsCompact K ∧ K ⊆ U ∧ ∀ A : Set X, MeasurableSet A → ∫⁻ v in f ⁻¹' (ι '' A) ∩ Kᶜ, ENNReal.ofReal (φ v) ∂μ ≤ ENNReal.ofReal ε * ν A) → ∀ s₀ : X, ∫⁻ v, ENNReal.ofReal (φ v) ∂(fib s₀) = ENNReal.ofReal (D s₀) := by
  first | exact @GlobalTheory.CompanionTheory.FibreDensityLimit.fibre_lintegral_eq_density | exact GlobalTheory.CompanionTheory.FibreDensityLimit.fibre_lintegral_eq_density | (intros; apply GlobalTheory.CompanionTheory.FibreDensityLimit.fibre_lintegral_eq_density <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DividedPowerQuotientExistsStatement
section
open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divided_power_quotient_exists : ∀ {S : Type} [CommRing S] , TF S → ∀ I J : Ideal S, PdI I → (∀ x ∈ I, x ∈ J → ∀ k : ℕ, k ≠ 0 → ∀ y : S, (k.factorial : S) * y = x ^ k → y ∈ J) → ∃ δ : DividedPowers (I.map (Ideal.Quotient.mk J)), IsPd (Ideal.Quotient.mk J) I δ := by
  first | exact @GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient | exact GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient | (intros; apply GlobalTheory.CompanionTheory.PdTF.exists_dividedPowers_map_quotient <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DominantComponentsOfGermStatement
section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dominant_components_of_germ : AnalyticGermComponents.Statement → OpenProjectionDominantComponents.Statement := by
  first | exact @GlobalTheory.CompanionTheory.ComplexSets.openProjectionDominantComponents_of_analyticGermComponents | exact GlobalTheory.CompanionTheory.ComplexSets.openProjectionDominantComponents_of_analyticGermComponents | (intros; apply GlobalTheory.CompanionTheory.ComplexSets.openProjectionDominantComponents_of_analyticGermComponents <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinScalingLawStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_scaling_law : PositivityTheory.RgEis.Scale := by
  first | exact @GlobalTheory.CompanionTheory.RgEisScale.scale | exact GlobalTheory.CompanionTheory.RgEisScale.scale | (intros; apply GlobalTheory.CompanionTheory.RgEisScale.scale <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsContinuousSectionQuotientStatement
section
open MeasureTheory MeasureTheory.Measure GlobalTheory.SplitWeil PositivityTheory.PfBern.Frob
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_continuous_section_quotient : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [LocallyCompactSpace G] [TotallyDisconnectedSpace G] [SecondCountableTopology G] (H : Subgroup G), IsClosed (H : Set G) → ∃ s : G ⧸ H → G, Continuous s ∧ ∀ c : G ⧸ H, ((s c : G) : G ⧸ H) = c := by
  first | exact @GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section | exact GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section | (intros; apply GlobalTheory.CompanionTheory.LGroupSection.exists_continuous_section <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsKill
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.BigStep

def gens {A : Type} [CommRing A] (𝓔 : Set (Set (MvPolynomial (Fin 3) A))) :
    Set (MvPolynomial (𝓔 × Fin 3) A) :=
  {f | ∃ (E : 𝓔) (q : MvPolynomial (Fin 3) A), q ∈ E.1 ∧
    f = MvPolynomial.rename (fun t => (E, t)) q}

theorem exists_kill (p : ℕ) {A : Type} [CommRing A] (r : ℕ → A)
    {𝓔 : Set (Set (MvPolynomial (Fin 3) A))}
    (hfin : ∀ J : Set (Set (MvPolynomial (Fin 3) A)), J.Finite → J ⊆ 𝓔 →
      ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧
        ∀ E ∈ J, Pt (algebraMap A B) E)
    (F : Finset (MvPolynomial (𝓔 × Fin 3) A)) (hF : (F : Set _) ⊆ gens 𝓔) :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧
      ∃ τ : MvPolynomial (𝓔 × Fin 3) A →ₐ[A] B, ∀ g ∈ F, τ g = 0 := by
  classical
  have hg : ∀ g : {g // g ∈ F}, ∃ (E : 𝓔) (q : MvPolynomial (Fin 3) A), q ∈ E.1 ∧
      g.1 = MvPolynomial.rename (fun t => (E, t)) q := fun g => hF g.2
  choose Eg qg hq hgq using hg
  obtain ⟨B₁, i1, i2, hP, hC, hpt⟩ := hfin (Set.range fun g : {g // g ∈ F} => (Eg g).1)
    (Set.finite_range _) (by rintro _ ⟨g, rfl⟩; exact (Eg g).2)
  have hpt' : ∀ E : 𝓔, ∃ y : Fin 3 → B₁, E.1 ∈ (Set.range fun g : {g // g ∈ F} => (Eg g).1) →
      ∀ q ∈ E.1, MvPolynomial.eval₂ (algebraMap A B₁) y q = 0 := by
    intro E
    by_cases h : E.1 ∈ (Set.range fun g : {g // g ∈ F} => (Eg g).1)
    · obtain ⟨y, hy⟩ := hpt _ h
      exact ⟨y, fun _ => hy⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose y hy using hpt'
  refine ⟨B₁, i1, i2, hP, hC, MvPolynomial.aeval (fun v => y v.1 v.2), ?_⟩
  intro g hg
  have e := hgq ⟨g, hg⟩
  simp only at e
  rw [e, MvPolynomial.aeval_rename, MvPolynomial.aeval_def]
  exact hy _ ⟨⟨g, hg⟩, rfl⟩ _ (hq ⟨g, hg⟩)

theorem big_step : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A] (r : ℕ → A) (𝓔 : Set (Set (MvPolynomial (Fin 3) A))), Pf p A → (∀ J : Set (Set (MvPolynomial (Fin 3) A)), J.Finite → J ⊆ 𝓔 → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ ∀ E ∈ J, Pt (algebraMap A B) E) → ∃ (B : Type) (_ : CommRing B) (_ : Algebra A B), Pf p B ∧ Cov p r B ∧ (∀ E ∈ 𝓔, Pt (algebraMap A B) E) ∧ ∀ (T : Type) [CommRing T] (x : A →+* T), Pf p T → (∀ E ∈ 𝓔, Pt x E) → ∃ y : B →+* T, y.comp (algebraMap A B) = x := by
  classical
  intro p _ A _ r 𝓔 hA hfin
  have hpS : (p : MvPolynomial (𝓔 × Fin 3) A) = 0 := by
    have := congrArg (algebraMap A (MvPolynomial (𝓔 × Fin 3) A)) hA.char
    simpa using this
  obtain ⟨B, instB, i, hQ⟩ := GlobalTheory.CompanionTheory.PerfClos.exists_PQ p (MvPolynomial (𝓔 × Fin 3) A)
    (Ideal.span (gens 𝓔)) hpS
  letI instAB : Algebra A B := (i.comp MvPolynomial.C).toAlgebra
  let iA : MvPolynomial (𝓔 × Fin 3) A →ₐ[A] B := { i with commutes' := fun _ => rfl }
  refine ⟨B, instB, instAB, hQ.pf, ?_, ?_, ?_⟩
  · apply GlobalTheory.CompanionTheory.CovCmp.cov_of_solv
    intro m n a c hS
    obtain ⟨k, s, hs⟩ := GlobalTheory.CompanionTheory.PerfectQuotient.solv_pow p A (MvPolynomial (𝓔 × Fin 3) A) B iA
      (Ideal.span (gens 𝓔)) m n a c hA.char hQ hS
    have hT := fun t => Submodule.mem_span_finite_of_mem_span (hs t)
    choose G hGs hGm using hT
    obtain ⟨B₁, i1, i2, hP, hC, τ, hτ⟩ := exists_kill p r hfin (Finset.univ.biUnion G) (by
      intro g hg
      obtain ⟨t, -, ht⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hg)
      exact hGs t ht)
    refine ⟨B₁, i1, i2, hC,
      GlobalTheory.CompanionTheory.PerfectRing.solv_of_solv_pow p A B₁ m n k a c hP ⟨fun j => τ (s j), fun t => ?_⟩⟩
    have hle : Ideal.span (G t : Set (MvPolynomial (𝓔 × Fin 3) A)) ≤ RingHom.ker τ :=
      Ideal.span_le.2 fun g hg =>
        hτ g (Finset.mem_biUnion.2 ⟨t, Finset.mem_univ t, Finset.mem_coe.1 hg⟩)
    have h0 := hle (hGm t)
    rw [RingHom.mem_ker, map_sub, map_sum, AlgHom.commutes, sub_eq_zero] at h0
    simpa only [map_smul] using h0
  · intro E hE
    refine ⟨fun t => i (MvPolynomial.X ((⟨E, hE⟩ : 𝓔), t)), fun q hq => ?_⟩
    have hz : i (MvPolynomial.rename (fun t => ((⟨E, hE⟩ : 𝓔), t)) q) = 0 :=
      (hQ.ker _).2 ⟨0, by
        have h : MvPolynomial.rename (fun t => ((⟨E, hE⟩ : 𝓔), t)) q ∈ Ideal.span (gens 𝓔) :=
          Ideal.subset_span ⟨⟨E, hE⟩, q, hq, rfl⟩
        simpa using h⟩
    have hi : i = MvPolynomial.eval₂Hom (i.comp MvPolynomial.C) (fun v => i (MvPolynomial.X v)) :=
      MvPolynomial.ringHom_ext (by simp) (by simp)
    have hz' : MvPolynomial.eval₂Hom (i.comp MvPolynomial.C) (fun v => i (MvPolynomial.X v))
        (MvPolynomial.rename (fun t => ((⟨E, hE⟩ : 𝓔), t)) q) = 0 := by
      rw [← hi]; exact hz
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename] at hz'
    exact hz'
  · intro T _ x hT hpts
    have hpts' : ∀ E : 𝓔, ∃ y : Fin 3 → T, ∀ q ∈ E.1, MvPolynomial.eval₂ x y q = 0 :=
      fun E => hpts E.1 E.2
    choose y hy using hpts'
    have hle : Ideal.span (gens 𝓔) ≤
        RingHom.ker (MvPolynomial.eval₂Hom x (fun v : 𝓔 × Fin 3 => y v.1 v.2)) := by
      refine Ideal.span_le.2 ?_
      rintro _ ⟨E, q, hq, rfl⟩
      show MvPolynomial.eval₂Hom x (fun v : 𝓔 × Fin 3 => y v.1 v.2) _ = 0
      rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_rename]
      exact hy E q hq
    obtain ⟨ψ, hψ, -⟩ := GlobalTheory.CompanionTheory.PerfectRing.pq_lift p _ B T i _
      (MvPolynomial.eval₂Hom x (fun v : 𝓔 × Fin 3 => y v.1 v.2)) hQ hT (fun g hg => hle hg)
    refine ⟨ψ, RingHom.ext fun a => ?_⟩
    have := RingHom.congr_fun hψ (MvPolynomial.C a)
    show ψ (i (MvPolynomial.C a)) = x a
    simpa using this

end GlobalTheory.CompanionTheory.BigStep
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsScaledNontrivialCharacterStatement
section
open ValuativeRel MeasureTheory Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scaled_nontrivial_character : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (a c : k), valuation k a < 1 → ψ c ≠ 1 → ∃ d : k, ψ d ≠ 1 ∧ (∃ r : ℕ, ∃ μ ∈ 𝒪[k], d = μ * a ^ r * c) ∧ ∀ s ∈ 𝒪[k], ψ (s * a * d) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step | exact GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step | (intros; apply GlobalTheory.CompanionTheory.CharConductor.exists_conductor_step <;> assumption)
end

