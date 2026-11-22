import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0624
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0590
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalZetaIntegralUnfolded
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0641
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0623
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.ArchBaseChangeOfHyp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0323
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0698
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetRepresentatives
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeProjectionEigenform
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDecompositionHomeomorph
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.Bundle0003
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalUnitaryMovesIsotropicFrameStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_unitary_moves_isotropic_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ q : Fin 1 → Fin (M + 2) → E, q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → ∃ g : UJ (σ : E →+* E) (hypOne J), gact σ g q = e0 E M := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne.exists_unitary_e0 | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne.exists_unitary_e0 | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStep.WittOne.exists_unitary_e0 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalZetaIntegralFunctionalEquation
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSZeta

theorem integrableOn_Zg_integrand {μ : Measure G2} {𝓕 : Set G2} {H : G2 → ℂ}
    {Φ : (Fin 2 → 𝔸[ℚ]) → ℂ} (c : HeckeCharacter ℚ) (hH : Aut H) (s : ℂ)
    (mth : Measurable (th Φ))
    (fin : ∫⁻ g in 𝓕, (‖H g‖ₑ * ENNReal.ofReal (Dt g ^ s.re)) * ∑' ξ : NZ, ‖Φ (row ξ.1 g)‖ₑ ∂μ < ∞) :
    IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g) 𝓕 μ := by
  refine ⟨((measurable_w hH c s).mul mth).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  refine lt_of_le_of_lt (lintegral_mono fun g => ?_) fin
  have h1 : ‖cdet c g‖ₑ = 1 := by
    rw [← ofReal_norm_eq_enorm, norm_cdet]; simp
  have h2 : ‖((Dt g : ℝ) : ℂ) ^ s‖ₑ = ENNReal.ofReal (Dt g ^ s.re) := by
    rw [← ofReal_norm_eq_enorm, Complex.norm_cpow_eq_rpow_re_of_pos (Dt_pos g)]
  have h3 : ‖th Φ g‖ₑ ≤ ∑' ξ : NZ, ‖Φ (row ξ.1 g)‖ₑ := enorm_tsum_le_tsum_enorm
  simp only [enorm_mul, h1, h2, mul_one]
  gcongr

theorem integrand_theta_eq {H : G2 → ℂ} {Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ} (c : HeckeCharacter ℚ) (s : ℂ) (g : G2)
    (hth : th Φ g + Φ 0 = (((Dt g)⁻¹ : ℝ) : ℂ) * (th Φ' (inv2 g) + Φ' 0)) :
    H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g =
      H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1) * th Φ' (inv2 g)
        + Φ' 0 * (H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1))
        - Φ 0 * (H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s) := by
  have hD := Dt_ne g
  have hp : ((Dt g : ℝ) : ℂ) ^ (s - 1) = ((Dt g : ℝ) : ℂ) ^ s * (((Dt g)⁻¹ : ℝ) : ℂ) := by
    rw [Complex.cpow_sub _ _ hD, Complex.cpow_one, Complex.ofReal_inv, div_eq_mul_inv]
  have ht : th Φ g = (((Dt g)⁻¹ : ℝ) : ℂ) * (th Φ' (inv2 g) + Φ' 0) - Φ 0 := by
    rw [← hth]; ring
  rw [hp, ht]; ring

theorem setIntegral_lower_det_inverse_twist {μ : Measure G2} {𝓕 : Set G2} {H : G2 → ℂ}
    {Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ} (c : HeckeCharacter ℚ) (hH : Aut H) (s : ℂ)
    (hm : MeasurableSet 𝓕) (hnull : μ {g | Dt g = 1} = 0)
    (hT : ∀ F : G2 → ℂ, Measurable F → LInv F → ∫ g in 𝓕, F (inv2 g) ∂μ = ∫ g in 𝓕, F g ∂μ)
    (mth : Measurable (th Φ')) (lth : LInv (th Φ')) :
    ∫ g in 𝓕 ∩ {g | Dt g < 1}, H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1) * th Φ' (inv2 g) ∂μ =
      Zp μ 𝓕 H c⁻¹ Φ' (1 - s) := by
  have hB : MeasurableSet {g | Dt g < 1} := measurableSet_lt measurable_Dt measurable_const
  have hC : MeasurableSet {g | Dt g ∈ Set.Ioi (1 : ℝ)} := measurable_Dt measurableSet_Ioi
  set G : G2 → ℂ := fun g => H g * cdet c⁻¹ g * ((Dt g : ℝ) : ℂ) ^ (1 - s) * th Φ' g with hG
  have mG : Measurable G := (measurable_w hH c⁻¹ (1 - s)).mul mth
  have lG : LInv G := fun γ g => by
    have := linv_w hH c⁻¹ (1 - s) γ g
    simp only [hG, lth γ g]
    simp only at this
    rw [this]
  have key := hT _ (mG.indicator hC) (linv_ind lG (Set.Ioi (1 : ℝ)))
  have hpt : ∀ g, Set.indicator {g | Dt g ∈ Set.Ioi (1 : ℝ)} G (inv2 g) =
      Set.indicator {g | Dt g < 1} (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1) * th Φ' (inv2 g)) g := by
    intro g
    have hiff : inv2 g ∈ {g | Dt g ∈ Set.Ioi (1 : ℝ)} ↔ g ∈ {g | Dt g < 1} := by
      simp only [Set.mem_setOf_eq, Set.mem_Ioi, module_det_inverse_twist]
      exact one_lt_inv₀ (Dt_pos g)
    by_cases h : g ∈ {g | Dt g < 1}
    · rw [Set.indicator_of_mem (hiff.2 h), Set.indicator_of_mem h]
      simp only [hG, character_det_inverse_twist, inv_inv, module_cpow_det_inverse_twist, Aut.inv2 hH, neg_sub]
    · rw [Set.indicator_of_notMem (fun h' => h (hiff.1 h')), Set.indicator_of_notMem h]
  simp only [hpt] at key
  rw [setIntegral_indicator hB, setIntegral_indicator hC] at key
  rw [key]
  refine setIntegral_congr_set ?_
  have hae : ∀ᵐ g ∂μ, Dt g ≠ 1 := by
    have : μ ({g | Dt g ≠ 1}ᶜ) = 0 := by
      convert hnull using 2
      ext g; simp
    exact this
  refine Filter.eventuallyEq_set.2 ?_
  filter_upwards [hae] with g hg
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ioi]
  exact and_congr_right fun _ => ⟨fun h => h.le, fun h => lt_of_le_of_ne h (Ne.symm hg)⟩

theorem Zg_decomposition : ∀ (μ : Measure G2) (𝓕 : Set G2) (mK : Measure KA) (𝓓 : Set Jd) (H : G2 → ℂ) (Φ Φ' : (Fin 2 → 𝔸[ℚ]) → ℂ) (c : HeckeCharacter ℚ),
  Ad3.R.G1a → Ad3.R.G3 → Set0 μ 𝓕 mK 𝓓 → Aut H → Φ ∈ Adele2.schwartzBruhat2 ℚ → Φ' ∈ Adele2.schwartzBruhat2 ℚ →
  (∀ g, th Φ g + Φ 0 = (((Dt g)⁻¹ : ℝ) : ℂ) * (th Φ' (inv2 g) + Φ' 0)) →
  (∀ t : ℂ, 0 < t.re → IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ t) (𝓕 ∩ {g | Dt g < 1}) μ) →
  ∀ s : ℂ, 1 < s.re → Zg μ 𝓕 H c Φ s = GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c Φ s + GlobalTheory.CompanionTheory.RSZeta.Zp μ 𝓕 H c⁻¹ Φ' (1 - s)
    + Φ' 0 * GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c (s - 1) - Φ 0 * GlobalTheory.CompanionTheory.RSZeta.Jl μ 𝓕 H c s := by
  intro μ 𝓕 mK 𝓓 H Φ Φ' c h1 h3 h0 hH hΦ hΦ' hth hw s hs
  obtain ⟨mth, -, fin⟩ := h3 μ 𝓕 mK 𝓓 h0 H hH Φ hΦ s.re hs
  obtain ⟨mth', lth', -⟩ := h3 μ 𝓕 mK 𝓓 h0 H hH Φ' hΦ' 2 (by norm_num)
  obtain ⟨hnull, -, hT⟩ := h1 μ 𝓕 mK 𝓓 h0
  have hWi := integrableOn_Zg_integrand c hH s mth fin
  have hA : MeasurableSet {g | 1 ≤ Dt g} := measurableSet_le measurable_const measurable_Dt
  have hinv := setIntegral_lower_det_inverse_twist (Φ' := Φ') c hH s h0.meas hnull
    (fun F mF lF => (hT inv2 (Or.inl rfl)).2 F mF lF) mth' lth'
  have hw1 := hw (s - 1) (by simp only [Complex.sub_re, Complex.one_re]; linarith)
  have hw2 := hw s (by linarith)
  have hWB : IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g)
      (𝓕 ∩ {g | Dt g < 1}) μ := hWi.mono_set Set.inter_subset_left
  have hpt := fun g => integrand_theta_eq (H := H) c s g (hth g)
  have hVi : IntegrableOn (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1) * th Φ' (inv2 g))
      (𝓕 ∩ {g | Dt g < 1}) μ := by
    have := (hWB.sub (hw1.const_mul (Φ' 0))).add (hw2.const_mul (Φ 0))
    refine this.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [Pi.add_apply, Pi.sub_apply, hpt g]
    ring
  have hsplit : Zg μ 𝓕 H c Φ s = Zp μ 𝓕 H c Φ s +
      ∫ g in 𝓕 ∩ {g | Dt g < 1}, H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g ∂μ := by
    have hd : 𝓕 \ {g | 1 ≤ Dt g} = 𝓕 ∩ {g | Dt g < 1} := by
      ext g; simp
    rw [← hd]
    exact (integral_inter_add_diff hA hWi).symm
  have hB : ∫ g in 𝓕 ∩ {g | Dt g < 1}, H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ s * th Φ g ∂μ =
      Zp μ 𝓕 H c⁻¹ Φ' (1 - s) + Φ' 0 * Jl μ 𝓕 H c (s - 1) - Φ 0 * Jl μ 𝓕 H c s := by
    have i1 : Integrable (fun g => H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1) * th Φ' (inv2 g)
        + Φ' 0 * (H g * cdet c g * ((Dt g : ℝ) : ℂ) ^ (s - 1))) (μ.restrict (𝓕 ∩ {g | Dt g < 1})) :=
      hVi.add (hw1.const_mul _)
    simp only [hpt]
    rw [integral_sub i1 (hw2.const_mul _), integral_add hVi (hw1.const_mul _),
      integral_const_mul, integral_const_mul, hinv, Jl, Jl]
  rw [hsplit, hB]; ring

end GlobalTheory.CompanionTheory.RSZeta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GlobalZetaIntegralUnfoldedStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.global_zeta_integral_unfolded : Ad3.R.G2c → Ad3.R.G3 → Ad3.R.G3a → Ad3.R.G5 := by
  first | exact @GlobalTheory.CompanionTheory.RankinUnfold.unfolding | exact GlobalTheory.CompanionTheory.RankinUnfold.unfolding | (intros; apply GlobalTheory.CompanionTheory.RankinUnfold.unfolding <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GramFrameIdentities
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.ColumnSplitting

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem sand {k l a b c : ℕ} (G : Mx D k k) (x : Mx D k l) (u : Mx D l a) (y : Mx D k b) (v : Mx D b c) :
    adj (x ⬝ u) ⬝ (G ⬝ (y ⬝ v)) = adj u ⬝ ((adj x ⬝ (G ⬝ y)) ⬝ v) := by
  simp only [adj_mul, Matrix.mul_assoc]

theorem gram_ww (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : GA D W) :
    adj (ww W x₀ h) ⬝ (gA W ⬝ ww W x₀ h) = rat (gramQ W x₀) := by
  have hu := mt_unitary W h⁻¹
  have hr : adj (rat x₀) ⬝ (gA W ⬝ rat x₀) = rat (gramQ W x₀) :=
    gram_rat W (a := x₀) (b := x₀) (c := gramQ W x₀) (by
      show x₀ᴴ * W.gram * x₀ = x₀ᴴ * (W.gram * x₀)
      rw [Matrix.mul_assoc])
  have e : adj (ww W x₀ h) ⬝ (gA W ⬝ ww W x₀ h)
      = adj (rat x₀) ⬝ ((adj (mt W h⁻¹) ⬝ (gA W ⬝ mt W h⁻¹)) ⬝ rat x₀) :=
    sand (gA W) (mt W h⁻¹) (rat x₀) (mt W h⁻¹) (rat x₀)
  rw [e, hu, hr]

theorem frame_perp (d : HypDec B W t) {a c : ℕ} (u : Mx D t a) (w : Mx D W.rank a) (v : Mx D t c) :
    adj (d.jX ⬝ u + d.j0 ⬝ w) ⬝ (gA B ⬝ (d.jX ⬝ v)) = 0 := by
  rw [adj_add, Matrix.add_mul, sand, sand, d.gram_XX, d.gram_0X]
  simp

theorem frame_gram (d : HypDec B W t) {a : ℕ} (u : Mx D t a) (w : Mx D W.rank a) :
    adj (d.jX ⬝ u + d.j0 ⬝ w) ⬝ (gA B ⬝ (d.jX ⬝ u + d.j0 ⬝ w)) = adj w ⬝ (gA W ⬝ w) := by
  have h1 := frame_perp d u w u
  have h2 : adj (d.jX ⬝ u + d.j0 ⬝ w) ⬝ (gA B ⬝ (d.j0 ⬝ w)) = adj w ⬝ (gA W ⬝ w) := by
    rw [adj_add, Matrix.add_mul, sand, sand, d.wittDecomp_gram_X_anisotropic, d.gram_00]
    simp
  rw [Matrix.mul_add, Matrix.mul_add, h1, h2, zero_add]

theorem pair_gram (d : HypDec B W t) (b₀ : HermE D W.rank) (hdet : b₀.1.det ≠ 0) (ξ : Mx D B.rank W.rank) (v : Mx D t t)
    (y : Mx D W.rank t) (hg : adj ξ ⬝ (gA B ⬝ ξ) = rat b₀.1) (hp : adj ξ ⬝ (gA B ⬝ (d.jX ⬝ v)) = 0) :
    yv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v) = y ∧ qv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v) = 0 := by
  have h2 : adj ξ ⬝ (gA B ⬝ (ξ ⬝ y + d.jX ⬝ v)) = rat b₀.1 ⬝ y := by
    rw [Matrix.mul_add, Matrix.mul_add, hp, add_zero, ← Matrix.mul_assoc (gA B), ← Matrix.mul_assoc (adj ξ), hg]
  have hinv : rat b₀.1⁻¹ ⬝ rat b₀.1 = (1 : Mx D W.rank W.rank) := by
    rw [← rat_mul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hdet), rat_one]
  have h3 : yv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v) = y := by
    show rat b₀.1⁻¹ ⬝ (adj ξ ⬝ (gA B ⬝ (ξ ⬝ y + d.jX ⬝ v))) = y
    rw [h2, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hxξ : adj (d.jX ⬝ v) ⬝ (gA B ⬝ ξ) = 0 := by
    have := gram_swap B hp
    rwa [adj_zero] at this
  have hxx : adj (d.jX ⬝ v) ⬝ (gA B ⬝ (d.jX ⬝ v)) = 0 := by
    rw [sand, d.gram_XX]
    simp
  have hq : adj (d.jX ⬝ v) ⬝ (gA B ⬝ (ξ ⬝ y + d.jX ⬝ v)) = 0 := by
    rw [Matrix.mul_add, Matrix.mul_add, hxx, add_zero, ← Matrix.mul_assoc (gA B), ← Matrix.mul_assoc (adj (d.jX ⬝ v)),
      hxξ, Matrix.zero_mul]
  have h4 : ip B (ξ ⬝ y + d.jX ⬝ v) (ξ ⬝ y + d.jX ⬝ v) = adj y ⬝ (rat b₀.1 ⬝ y) := by
    show adj (ξ ⬝ y + d.jX ⬝ v) ⬝ (gA B ⬝ (ξ ⬝ y + d.jX ⬝ v)) = _
    rw [adj_add, Matrix.add_mul, hq, add_zero, adj_mul ξ y, Matrix.mul_assoc, h2]
  refine ⟨h3, ?_⟩
  show ip B (ξ ⬝ y + d.jX ⬝ v) (ξ ⬝ y + d.jX ⬝ v)
    - pr b₀ (yv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v)) (yv B b₀ (ξ, ξ ⬝ y + d.jX ⬝ v)) = 0
  rw [h3, h4]
  exact sub_eq_zero.2 rfl

theorem zp_eq : ZpEq := by
  intro D n t B W d hn b₀ hdet x₀ hx p
  have hg : adj (d.jX ⬝ c1 hn p.2.1 + d.j0 ⬝ ww W x₀ p.1) ⬝ (gA B ⬝ (d.jX ⬝ c1 hn p.2.1 + d.j0 ⬝ ww W x₀ p.1)) = rat b₀.1 := by
    rw [frame_gram, gram_ww, hx]
  have hp := frame_perp d (c1 hn p.2.1) (ww W x₀ p.1) (c2 hn p.2.1)
  obtain ⟨h3, h5⟩ := pair_gram d b₀ hdet _ (c2 hn p.2.1) p.2.2 hg hp
  exact ⟨hg, h3, h5⟩

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarRightInvariantTotallyComplexStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_right_invariant_totally_complex : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)] (μ : Measure (GA E N)) [μ.IsHaarMeasure], μ.IsMulRightInvariant := by
  first | exact @GlobalTheory.CompanionTheory.GAUnimod.isMulRightInvariant_haar_GA | exact GlobalTheory.CompanionTheory.GAUnimod.isMulRightInvariant_haar_GA | (intros; apply GlobalTheory.CompanionTheory.GAUnimod.isMulRightInvariant_haar_GA <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSatakeOfIsSatVecGL
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F PositivityTheory.Rg.BcB.Desc

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SatComp

open GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.LFun.SatCompare

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V}

theorem hasSatake_of_isSatVecGL (hπ : IsIrrSmooth π) {x : V} (α : Fin n → ℂˣ)
    (hx : IsSatVecGL w π x (Finset.univ.val.map α)) : GlobalTheory.SmGL.HasSatake π α := by
  obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExists E w n (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  have hφ0 : φ ≠ 0 := fun e => by simp [e] at h1
  obtain ⟨ho, hc⟩ := isOpen_isCompact_KGL w n
  obtain ⟨y, hy, hy0, ht⟩ := exists_fixed_of_fun _ _ ho (Final.GLintComm E w n) hφ0 ((isSphericalGL_iff α φ).1 hφ)
  have hq : IsSubquot π (psGL (w.adicCompletion E) α) :=
    GlobalTheory.T.isSubquotient_of_same_spherical_hecke_eigenvalues _ _ _ π _ _ hc (Final.GLintComm E w n) hπ (LeviDatum.nInd_isSmooth _ _) x hx.2.1
      hx.1 y hy hy0 fun f hf => by
        obtain ⟨c, e1, e2⟩ := exists_eigenvalue_GL hx (isSatVecGL_of_isSpherical hφ hφ0) f hf
        exact ⟨c, e1, ht f hf c e2⟩
  have hs : IsSpherical π (GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n)) := by
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact (Submodule.ne_bot_iff _).2 ⟨x, hx.2.1, hx.1⟩
  exact ⟨hπ.2, hs, (GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff _ _ π α).1 hq⟩

end GlobalTheory.CompanionTheory.SatComp

open GlobalTheory.CompanionTheory.SatComp in

theorem GlobalTheory.CompanionTheory.SatComp.satComp : SatComp := by
  intro E _ _ _ n π w τ τ' B hs hB hπ hτ'
  obtain ⟨α, rfl, h'⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π ((CG.hasSat_mk π w B).1 hπ) hτ'
  obtain ⟨x, hx⟩ := hB.exists_vec
  have h := hasSatake_of_isSatVecGL ⟨τ.smooth, τ.irred⟩ α hx
  exact GlobalTheory.SmGL.SphUniq.equiv_of_parInd _ _ h.1 h'.1 h.2.2 h'.2.2 h.2.1 h'.2.1

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeCosetRepresentativesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_coset_representatives : Ad3.R.C0 := by
  first | exact @GlobalTheory.CompanionTheory.HeckeCosets.heckeSum_invariant | exact GlobalTheory.CompanionTheory.HeckeCosets.heckeSum_invariant | (intros; apply GlobalTheory.CompanionTheory.HeckeCosets.heckeSum_invariant <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeProjectionEigenformStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_projection_eigenform : Ad3.R.B0 → Ad3.R.C1 → Ad3.R.G1 → Ad3.R.F0b → Ad3.R.F1 → Ad3.R.F3 → Ad3.R.F5 → Ad3.R.G6 := by
  first | exact @GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.g6 | exact GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.g6 | (intros; apply GlobalTheory.CompanionTheory.RankinSelbergHeckeProjection.g6 <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightRightTranslateCompactBoundStatement
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_right_translate_compact_bound : ∀ (D : D7) (n : ℕ) (H : G D n → ℝ≥0), IsHt H → (∃ C : Set (G D n), IsCompact C ∧ ∀ g, ∃ q ∈ P D n, ∃ c ∈ C, g = q * c) →
  ∀ C : Set (G D n), IsCompact C → ∃ κ : ℝ, 1 ≤ κ ∧ ∀ c ∈ C, ∀ x : G D n, (H (x * c) : ℝ) ≤ κ * (H x : ℝ) := by
  first | exact @GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le | exact GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le | (intros; apply GlobalTheory.CompanionTheory.HtRightTranslate.height_mul_le <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianBlockDecompositionHomeomorphStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_block_decomposition_homeomorph : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∃ e : HermR R σ (n + 1) ≃ₜ (HermR R σ 1 × (Fin 1 → Fin n → R ⊗[F] E) × HermR R σ n), (∀ S, ((e S).1 : Matrix (Fin 1) (Fin 1) (R ⊗[F] E)) 0 0 = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 0 ∧ (∀ j : Fin n, (e S).2.1 0 j = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) 0 j.succ) ∧ ∀ i j : Fin n, ((e S).2.2 : Matrix (Fin n) (Fin n) (R ⊗[F] E)) i j = (S : Matrix (Fin (n + 1)) (Fin (n + 1)) (R ⊗[F] E)) i.succ j.succ) ∧ MeasurePreserving e (coordHerm R σ b lam (n + 1)) ((coordHerm R σ b lam 1).prod ((coordW R b lam 1 n).prod (coordHerm R σ b lam n))) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Split.hermSplit | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Split.hermSplit | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Split.hermSplit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormIsoOfBijective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

noncomputable section

namespace GlobalTheory.CompanionTheory.HodgeFormTop

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2 CrystallineSemistableComparison.Pb

section
variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def omEq (a : ℕ) : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a ≃ₗ[K] OmU q ⊤ a := LinearEquiv.refl K (OmU q ⊤ a)

abbrev resTop (a : ℕ) := CH.Mor.restrict (G q a) (inU q ⊤).ι

theorem resTop_pullC_bij (a n : ℕ) : Function.Bijective ((resTop q a).pullC n) :=
  (topRes_pf K _ (G q a) (inU q ⊤) ⊥ (fun T => inTop q T) n).1

theorem resTop_bij (a n : ℕ) : Function.Bijective ((resTop q a).pull n) :=
  CrystallineSemistableComparison.P.mapH_bij _ (fun m => resTop_pullC_bij q a m) n

def resTopEquiv (a : ℕ) : Hdg q a a ≃ₗ[K] HV q ⊤ a a :=
  LinearEquiv.ofBijective ((resTop q a).pull a) (resTop_bij q a a)

def LiftsT.toTop (Λ : LiftsT q) : Lifts q ⊤ where
  v T g := Λ.v T.obj g
  hv T g := Λ.hv T.obj g

theorem isFormT_of_isForm {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (c : HV q ⊤ a a)
    (h : IsForm q ⊤ (a := a) g₀ g c) : IsFormT q g₀ g ((resTopEquiv q a).symm c) := by
  intro Λ
  obtain ⟨f, hf, hc, hz⟩ := h (LiftsT.toTop q Λ)
  obtain ⟨z, rfl⟩ := (resTop_pullC_bij q a a).2 f
  have hd : CH.d (G q a) a z = 0 := by
    apply (resTop_pullC_bij q a (a + 1)).1
    rw [map_zero, ← CH.Mor.d_pullC]
    exact hf
  have hcz : (resTopEquiv q a) ((CH.cx (G q a)).cls z hd) = c := by
    rw [hc]
    exact CrystallineSemistableComparison.P.mapH_cls (resTop q a).hom a z hd _
  refine ⟨z, hd, ?_, fun t => ?_⟩
  · rw [← hcz, LinearEquiv.symm_apply_apply]
  · exact hz (t ⋙ (inU q ⊤).lift (𝟭 _) (fun T => inTop q T))

end

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ),
    (∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e) →
    ∃ e' : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a, CrystallineSemistableComparison.Om.L2.IsOmT q a e' := by
  intro K _ X q a ⟨e, he, hb⟩
  refine ⟨((resTopEquiv q a).trans (LinearEquiv.ofBijective e hb).symm).trans (omEq q a), fun g₀ g => ?_⟩
  exact isFormT_of_isForm q g₀ g _ (he g₀ g)

end GlobalTheory.CompanionTheory.HodgeFormTop
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormOne
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace GlobalTheory.CompanionTheory.HodgeFormUnit

theorem gForm_one {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) :
    CrystallineSemistableComparison.Om.L2.gForm q 1 Fin.elim0 = oneOm K (Sec q ⊤) := by
  apply Subtype.ext
  simp [CrystallineSemistableComparison.Onto.form, oneOm]

theorem e_oneH {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (e : CrystallineSemistableComparison.HT.Hdg q 0 0 ≃ₗ[K] OmU q ⊤ 0) (h : CrystallineSemistableComparison.Om.L2.IsOmT q 0 e) :
    e (CrystallineSemistableComparison.HT.oneH q) = oneOm K (Sec q ⊤) := by
  let Λ : CrystallineSemistableComparison.Om.L2.LiftsT q :=
    { v := fun T g => Function.surjInv Ideal.Quotient.mk_surjective
        (CrystallineSemistableComparison.Pb.ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (CrystallineSemistableComparison.Om.L2.inTop q T) g)
      hv := fun T g => Function.surjInv_eq _ _ }
  obtain ⟨f, hf, hc, hz⟩ := h 1 Fin.elim0 Λ
  have hf' : f = (CrystallineSemistableComparison.Pb.toSq (CrystallineSemistableComparison.Pb.thFil (CrystallineSemistableComparison.smFun X q) (0 : ℕ)) (CrystallineSemistableComparison.Pb.thFil (CrystallineSemistableComparison.smFun X q) (((0 : ℕ) : ℤ) + 1))
      fun T => T.pdPow_zero).pullC 0 (fun s => (1 : (CrystallineSemistableComparison.Pb.thA (CrystallineSemistableComparison.smFun X q)).obj (s.obj (Fin.last 0)))) := by
    funext s
    apply Subtype.ext
    refine (hz s).trans ?_
    have hv : (Λ.form 1 Fin.elim0 s : (s.obj (Fin.last 0)).B) = Λ.v _ 1 := by
      simp [CrystallineSemistableComparison.Om.L2.LiftsT.form]
    have hJ : Λ.v (s.obj (Fin.last 0)) 1 - 1 ∈ (s.obj (Fin.last 0)).J :=
      Ideal.Quotient.eq.1 ((Λ.hv _ 1).trans ((map_one _).trans (map_one _).symm))
    refine Ideal.Quotient.eq.2 ?_
    change Λ.form 1 Fin.elim0 s - 1 ∈ (s.obj (Fin.last 0)).pdPow 1
    rw [hv]
    exact (s.obj (Fin.last 0)).J_le_pdPow_one hJ
  have h1 : CrystallineSemistableComparison.HT.oneH q = e.symm (CrystallineSemistableComparison.Om.L2.gForm q 1 Fin.elim0) := by
    refine Eq.trans ?_ hc.symm
    exact congrArg Submodule.Quotient.mk (Subtype.ext hf'.symm)
  rw [h1, LinearEquiv.apply_symm_apply, gForm_one]

end GlobalTheory.CompanionTheory.HodgeFormUnit
end

