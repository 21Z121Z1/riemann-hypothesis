import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0795
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0789
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0796
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.Bundle0001
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0370
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0375
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitarySchrodinger
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0523
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0460
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0437
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0413
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0450
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0195
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0243
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0236
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0204
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1870
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0771
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0787
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0777
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0778
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0798
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0776
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0779
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCellOpenIndependent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.AllLeaves
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0301
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.CommonEigenvectors.KillPoly
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.DiagonalInfinityValues.InfGLValDiag
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.ExponentialNegativity.NormalisedExistence.ExistsNormed
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0008
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0791
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0786
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0797
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0540
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalProdSpanStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_prodSpan : ∀ {A B : Type} (U₁ : Submodule ℂ (A → ℂ)) (U₂ : Submodule ℂ (B → ℂ)), FiniteDimensional ℂ U₁ → FiniteDimensional ℂ U₂ → FiniteDimensional ℂ (prodSpan U₁ U₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd | exact GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd | (intros; apply GlobalTheory.CompanionTheory.LimV.finiteDimensional_prodSpan_of_fd <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDimensionalTypedDiscreteStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDimensional_typed_discrete : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (V : Submodule ℂ (Sm E N)) (K : Subgroup (GL (Fin N) (Af E))) (W : Submodule ℂ (Kinf E N → ℂ)), IsDiscrete V → IsOpen (K : Set (GL (Fin N) (Af E))) → FiniteDimensional ℂ W → FiniteDimensional ℂ (typed V K W) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.FdV.fd_typed | exact GlobalTheory.CompanionTheory.LimV.FdV.fd_typed | (intros; apply GlobalTheory.CompanionTheory.LimV.FdV.fd_typed <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FlatAbsoluteCharacterStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_absolute_character : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (w : ℂ), FlatFn (absFn (E := E) N w) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.absFn_flat | exact GlobalTheory.CompanionTheory.LimV.absFn_flat | (intros; apply GlobalTheory.CompanionTheory.LimV.absFn_flat <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FockKStable
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.PfSWUS

theorem fockKStable : PositivityTheory.PfSWUS.FockKStable := by
  intro D n V ψ χ θ μ ω H l s ν Φ hStd k hk
  obtain ⟨𝓕, hμ⟩ := hStd.hμ
  have hψ := hStd.hψ
  have hχ := hStd.hχ
  have hr := hStd.hη
  have hθ := hStd.hθ
  have hω := hStd.hω
  have hl := hStd.hl
  have hs := hStd.hs
  have hΦ := hStd.hΦ
  let A : HSp D := Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n
  obtain ⟨ψ₀, μ', lam, κ, omh, hstd, hsk, hlam, hψeq, hchart, hdat, htr⟩ :=
    GlobalTheory.T.exists_weilDatum_doubled_of_schrodingerFormulas D A V ψ hψ χ hχ hr θ hθ μ 𝓕 hμ ω hω
  obtain ⟨lam', hlam', -, l', hl', habs⟩ := GlobalTheory.StdUnn.shift_char_realPar D ψ₀ hstd θ hθ μ' hsk
  have hll : lam' = lam := (algebraMap D.host.F D.host.E).injective (hlam'.trans hlam.symm)
  subst hll
  have hl'' : HasRealPar ψ θ l' := hψeq ▸ hl'
  have hleq : l = l' := GlobalTheory.T.archimedean_parameters_addChar_unique D ψ θ hθ l l' hl hl''
  subst hleq
  obtain ⟨-, hsurj, -⟩ := GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ hstd θ hθ A V μ 𝓕 hμ
  obtain ⟨f, hf, hfΦ⟩ := hsurj Φ.1 Φ.2
  obtain ⟨s', hstd', hcomm⟩ := GlobalTheory.T.exists_standardCartanInvolution_commute_compact D A μ' hsk κ hchart θ hθ
  have hfock : IsFockVec ψ₀ θ (dblSp A) V s' s f :=
    GlobalTheory.T.isFockVector_of_schrodinger_mem_fockSpace D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs f hf (hfΦ ▸ hΦ)
  obtain ⟨hth, N, hN⟩ := hfock
  have hk' : κ (κ.symm k) ∈ K D A.rank := by
    rw [show κ (κ.symm k) = k from κ.apply_symm_apply k]
    exact hk
  have hfock' : IsFockVec ψ₀ θ (dblSp A) V s' s (omh (κ.symm k, 1) f) :=
    ⟨hdat.om_pres _ f hth, N,
      GlobalTheory.T.weilRep_preserves_fockDegree_of_commute_cartan D ψ₀ θ (dblSp A) V 1 χ⁻¹ omh s' s hdat hθ (κ.symm k) (hcomm _ hk') N f hth hN⟩
  have hmem := GlobalTheory.T.schroedingerFunction_fockVector_polynomial_gaussian D ψ₀ hstd θ hθ A V μ 𝓕 hμ μ' hsk s' s hstd' hs l habs _ hfock'
  have htrk := htr (κ.symm k) f hf Φ hfΦ.symm
  rw [show κ (κ.symm k) = k from κ.apply_symm_apply k] at htrk
  exact Eq.mpr (congrArg (fun φ : Mx D V.rank n → ℂ => φ ∈ fockA θ V n l s) htrk) hmem

end GlobalTheory.CompanionTheory.PfSWUS

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiExpansionBounded
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem fold_abs {X ι : Type} [MeasurableSpace X] [Countable ι] (μ : Measure X) [SFinite μ] (S : Set X) (hS : μ S = 1)
    (Z T : X × X → ℂ) (hZ : StronglyMeasurable Z) (hT : StronglyMeasurable T) (B B₂ : ℝ)
    (hB : ∀ v, ‖Z v‖ ≤ B) (hB₂ : ∀ v, ‖T v‖ ≤ B₂)
    (c a : ι → X → ℂ) (hc : ∀ i, StronglyMeasurable (c i)) (hc1 : ∀ i x, ‖c i x‖ = 1)
    (ha : ∀ y, Summable fun i => ‖a i y‖) (hTs : ∀ y x, T (y, x) = ∑' i, c i x * a i y) :
    ∫ y in S, ∑' i, (∫ x in S, c i x * Z (y, x) ∂μ) * a i y ∂μ = ∫ v in S ×ˢ S, Z v * T v ∂(μ.prod μ) := by
  haveI : IsFiniteMeasure (μ.restrict S) := ⟨by simp [hS]⟩
  have hZs : ∀ y, StronglyMeasurable fun x => Z (y, x) := fun y => hZ.comp_measurable measurable_prodMk_left
  have inner : ∀ y, ∑' i, (∫ x in S, c i x * Z (y, x) ∂μ) * a i y = ∫ x in S, Z (y, x) * T (y, x) ∂μ := by
    intro y
    have hint : ∀ i, Integrable (fun x => c i x * Z (y, x) * a i y) (μ.restrict S) := by
      intro i
      refine Integrable.of_bound ((((hc i).mul (hZs y)).mul stronglyMeasurable_const).aestronglyMeasurable)
        (B * ‖a i y‖) (ae_of_all _ fun x => ?_)
      rw [norm_mul, norm_mul, hc1, one_mul]
      exact mul_le_mul_of_nonneg_right (hB _) (norm_nonneg _)
    have hsum : Summable fun i => ∫ x in S, ‖c i x * Z (y, x) * a i y‖ ∂μ := by
      have h : ∀ i, ∫ x in S, ‖c i x * Z (y, x) * a i y‖ ∂μ = (∫ x in S, ‖Z (y, x)‖ ∂μ) * ‖a i y‖ := by
        intro i
        simp only [norm_mul, hc1, one_mul]
        exact integral_mul_const _ _
      simp only [h]
      exact (ha y).mul_left _
    have h1 := integral_tsum_of_summable_integral_norm hint hsum
    calc ∑' i, (∫ x in S, c i x * Z (y, x) ∂μ) * a i y
        = ∑' i, ∫ x in S, c i x * Z (y, x) * a i y ∂μ :=
          tsum_congr fun i => (integral_mul_const _ _).symm
      _ = ∫ x in S, ∑' i, c i x * Z (y, x) * a i y ∂μ := h1
      _ = ∫ x in S, Z (y, x) * T (y, x) ∂μ := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          show ∑' i, c i x * Z (y, x) * a i y = Z (y, x) * T (y, x)
          rw [hTs, ← tsum_mul_left]
          exact tsum_congr fun i => by ring
  simp only [inner]
  haveI hfin : IsFiniteMeasure ((μ.prod μ).restrict (S ×ˢ S)) := by
    rw [← Measure.prod_restrict]; infer_instance
  have hi : IntegrableOn (fun v => Z v * T v) (S ×ˢ S) (μ.prod μ) := by
    refine Integrable.of_bound ((hZ.mul hT).aestronglyMeasurable) (B * B₂) (ae_of_all _ fun v => ?_)
    rw [norm_mul]
    exact mul_le_mul (hB v) (hB₂ v) (norm_nonneg _) ((norm_nonneg _).trans (hB v))
  exact (setIntegral_prod (fun v => Z v * T v) hi).symm

theorem fj_fold_mean : ∀ {D : D7} {n ρ p : ℕ} {hn : ρ + p = n} (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) (F : G D n → ℂ), LeftInv (GF D n) F → ∀ (g : G D n) (θ : InfFam D), IsInfFam θ → ∀ φ ∈ schwartzA θ ρ p, ∀ B : ℝ, (∀ y x, ‖zc M m ψ b₀ F (M.nzx 0 x * (M.sh y * g))‖ ≤ B) → StronglyMeasurable (fun v : Mx D ρ p × Mx D ρ p => zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g))) → FJ M m ψ b₀ F g φ = ∫ v in m.𝓕 ×ˢ m.𝓕, zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g)) * conj (th ψ b₀ φ 0 v.2 v.1) ∂(m.μ.prod m.μ) := by
  intro D n ρ p hn M m ψ hψ b₀ F hF g θ hθ φ hφ B hB hZ
  obtain ⟨hH, hfd, h1⟩ := m.hμ
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D ρ p
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  haveI : SFinite m.μ := inferInstance
  haveI : IsFiniteMeasure (m.μ.restrict m.𝓕) := ⟨by simp [h1]⟩
  haveI : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.toEquiv.injective.countable
  haveI : Countable (Matrix (Fin ρ) (Fin p) D.host.E) :=
    inferInstanceAs (Countable (Fin ρ → Fin p → D.host.E))
  obtain ⟨-, -, hnorm, -, -, hcont⟩ := GlobalTheory.T.heisenberg_character_bilinear_laws (ρ := ρ) (p := p) ψ hψ b₀
  have hφc : Continuous φ := GlobalTheory.RegSch.CentreWeilComm.continuous_of_mem hθ ⟨φ, hφ⟩
  have hφi : Integrable φ m.μ := GlobalTheory.RegSch.CentreWeilComm.integrable_of_mem hθ m.μ ⟨φ, hφ⟩
  obtain ⟨B₂, hB₂⟩ := GlobalTheory.T.exists_bound_lattice_sum_norm_schwartzA θ hθ φ hφ
  have hD := GlobalTheory.T.stronglyMeasurable_twisted_lattice_sum ψ hψ b₀ φ hφc.stronglyMeasurable (fun y => (hB₂ y).1)
  set Z : Mx D ρ p × Mx D ρ p → ℂ := fun v => zc M m ψ b₀ F (M.nzx 0 v.2 * (M.sh v.1 * g)) with hZdef
  have hpcm : StronglyMeasurable fun y => pc M m ψ b₀ F (M.sh y * g) :=
    hZ.integral_prod_right' (ν := m.μ.restrict m.𝓕)
  have hpcb : ∀ y, ‖pc M m ψ b₀ F (M.sh y * g)‖ ≤ B := by
    intro y
    have h := norm_integral_le_of_norm_le_const (μ := m.μ.restrict m.𝓕)
      (f := fun x => zc M m ψ b₀ F (M.nzx 0 x * (M.sh y * g))) (C := B) (ae_of_all _ fun x => hB y x)
    show ‖∫ x in m.𝓕, zc M m ψ b₀ F (M.nzx 0 x * (M.sh y * g)) ∂m.μ‖ ≤ B
    simpa [Measure.real, h1] using h
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hpcb 0)
  have hP : Integrable (fun y => pc M m ψ b₀ F (M.sh y * g) * conj (φ y)) m.μ := by
    refine (hφi.norm.const_mul B).mono'
      (hpcm.aestronglyMeasurable.mul (Complex.continuous_conj.comp hφc).aestronglyMeasurable) (ae_of_all _ fun y => ?_)
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (hpcb y) (norm_nonneg _)
  have hPξ : ∀ (y : Mx D ρ p) (ξ : Matrix (Fin ρ) (Fin p) D.host.E),
      pc M m ψ b₀ F (M.sh (rt ξ + y) * g) * conj (φ (rt ξ + y)) =
        (∫ x in m.𝓕, conj (chv ψ b₀ x (rt ξ)) * Z (y, x) ∂m.μ) * conj (φ (rt ξ + y)) := by
    intro y ξ
    rw [← GlobalTheory.CompanionTheory.FJE.sh_add M (rt ξ) y, mul_assoc, GlobalTheory.T.partial_coefficient_heisenberg_expansion M m ψ hψ b₀ F hF ξ (M.sh y * g)]
  have hfold := GlobalTheory.T.integral_eq_fundamental_domain_lattice_sum m _ hP
  have hmain := fold_abs m.μ m.𝓕 h1 Z (fun v => conj (dsum ψ b₀ φ v.2 v.1)) hZ
    (Complex.continuous_conj.comp_stronglyMeasurable hD) B B₂ (fun v => hB v.1 v.2)
    (fun v => ?_)
    (fun (ξ : Matrix (Fin ρ) (Fin p) D.host.E) x => conj (chv ψ b₀ x (rt ξ)))
    (fun (ξ : Matrix (Fin ρ) (Fin p) D.host.E) y => conj (φ (rt ξ + y)))
    (fun ξ => (Complex.continuous_conj.comp
      (hcont.comp (continuous_id.prodMk continuous_const))).stronglyMeasurable)
    (fun ξ x => by rw [RCLike.norm_conj]; exact hnorm _ _)
    (fun y => by simpa only [RCLike.norm_conj] using (hB₂ y).1)
    (fun y x => by
      show conj (dsum ψ b₀ φ x y) = _
      rw [dsum, Complex.conj_tsum]
      exact tsum_congr fun ξ => map_mul _ _ _)
  · show ∫ y, pc M m ψ b₀ F (M.sh y * g) * conj (φ y) ∂m.μ = _
    rw [hfold]
    simp only [hPξ]
    rw [hmain]
    simp only [th_zero]
    rfl
  · rw [RCLike.norm_conj, dsum]
    have hs : Summable fun ξ : Matrix (Fin ρ) (Fin p) D.host.E => ‖chv ψ b₀ v.2 (rt ξ) * φ (rt ξ + v.1)‖ := by
      simpa only [norm_mul, hnorm, one_mul] using (hB₂ v.1).1
    refine (norm_tsum_le_tsum_norm hs).trans ?_
    simpa only [norm_mul, hnorm, one_mul] using (hB₂ v.1).2

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCellOpenIndependentStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.free_cell_open_independent : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ n : ℕ, IsOpen (freeCell (R ⊗[F] E) M n) ∧ (∀ X ∈ freeCell (R ⊗[F] E) M n, LinearIndependent (R ⊗[F] E) X) ∧ (∀ X : Fin (n + 1) → Fin (M + 2) → R ⊗[F] E, LinearIndependent (R ⊗[F] E) X → gramR R σ (hypOne J) X = 0 → IsUnit (X 0 0) → X ∈ freeCell (R ⊗[F] E) M n) ∧ (∀ (x : Fin 1 → Fin (M + 2) → R ⊗[F] E) (a s : Fin 1 → Fin n → R ⊗[F] E) (Y : Fin n → Fin M → R ⊗[F] E), IsUnit (x 0 0) → LinearIndependent (R ⊗[F] E) Y → chartS R σ J x a s Y ∈ freeCell (R ⊗[F] E) M n) ∧ Measurable (fun p : (Fin 1 → Fin (M + 2) → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin 1 → Fin n → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) => chartS R σ J p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Cell.freeCell_props | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Cell.freeCell_props | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.Cell.freeCell_props <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasDerivAtTorusTranslateStatement
section
open scoped ENNReal
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs GlobalTheory.CompanionTheory.Conc
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasDerivAt_torus_translate : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (r s : ℕ) (F : Sm E (r + s)) (g : GA E (r + s)) (t : ℝ),
  HasDerivAt (fun t : ℝ => F.1 (g * aT E (r + s) r t))
    (((∑ τ : E →+* ℂ, ∑ i : Fin r, Eop (a := r + s) τ (Fin.castAdd s i) (Fin.castAdd s i)) F).1 (g * aT E (r + s) r t)) t := by
  first | exact @GlobalTheory.CompanionTheory.Conc.TorusDeriv.hasDerivAt_aT_right | exact GlobalTheory.CompanionTheory.Conc.TorusDeriv.hasDerivAt_aT_right | (intros; apply GlobalTheory.CompanionTheory.Conc.TorusDeriv.hasDerivAt_aT_right <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicFreeVectorsSameGram
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeTrans

section Form

variable {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)

theorem hform_add_right (x y z : Fin n → A) :
    hform s J x (y + z) = hform s J x y + hform s J x z := by
  simp only [hform, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem hform_add_left (x y z : Fin n → A) :
    hform s J (x + y) z = hform s J x z + hform s J y z := by
  simp only [hform, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

theorem hform_smul_right (t : A) (x y : Fin n → A) :
    hform s J x (t • y) = t * hform s J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem hform_smul_left (t : A) (x y : Fin n → A) :
    hform s J (t • x) y = s t * hform s J x y := by
  simp only [hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

end Form

theorem exists_hyperbolic_partner {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {σ : E →ₐ[F] E} (hσ : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E}
    (hJ : IsHermND σ J) (R : Type) [CommRing R] [Algebra F R] (x y : Fin M → R ⊗[F] E)
    (hxx : hR R σ J x x = 0) (hxy : hR R σ J x y = 1) :
    ∃ y₁ : Fin M → R ⊗[F] E, hR R σ J x y₁ = 1 ∧ hR R σ J y₁ x = 1 ∧ hR R σ J y₁ y₁ = 0 := by
  have herm : ∀ u v : Fin M → R ⊗[F] E, sigR R σ (hR R σ J u v) = hR R σ J v u := by
    intro u v
    have h : ∀ a b, sigR R σ (gramR R σ J ![u, v] b a) = gramR R σ J ![u, v] a b :=
      GlobalTheory.CompanionTheory.SW.HermTop.gramR_mem R (GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ) hJ.1 ![u, v]
    simpa [gramR] using h 1 0
  have hyx : hR R σ J y x = 1 := by rw [← herm, hxy, map_one]
  set c : R ⊗[F] E := algebraMap F (R ⊗[F] E) (1 / 2) with hc
  have hcc : c + c = 1 := by
    rw [hc, ← map_add, ← map_one (algebraMap F (R ⊗[F] E))]
    norm_num
  have hsc : sigR R σ c = c := AlgHom.commutes (Algebra.TensorProduct.map (AlgHom.id F R) σ) _
  set q := hR R σ J y y with hq
  have hsq : sigR R σ q = q := herm y y
  refine ⟨y + (-(c * q)) • x, ?_, ?_, ?_⟩
  · have : hR R σ J x (y + (-(c * q)) • x) = hR R σ J x y + -(c * q) * hR R σ J x x := by
      simp only [hR, hform_add_right, hform_smul_right]
    rw [this, hxx, hxy]
    ring
  · have : hR R σ J (y + (-(c * q)) • x) x =
        hR R σ J y x + sigR R σ (-(c * q)) * hR R σ J x x := by
      simp only [hR, hform_add_left, hform_smul_left]
    rw [this, hxx, hyx]
    ring
  · have : hR R σ J (y + (-(c * q)) • x) (y + (-(c * q)) • x) =
        hR R σ J y y + -(c * q) * hR R σ J y x + (sigR R σ (-(c * q)) * hR R σ J x y +
          sigR R σ (-(c * q)) * (-(c * q) * hR R σ J x x)) := by
      simp only [hR, hform_add_left, hform_add_right, hform_smul_left, hform_smul_right]
      ring
    rw [this, hxx, hxy, hyx, ← hq, map_neg, map_mul, hsc, hsq]
    linear_combination (-q) * hcc

theorem transitive_free_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ X Y : Fin 1 → Fin M → R ⊗[F] E, LinearIndependent (R ⊗[F] E) X → LinearIndependent (R ⊗[F] E) Y → gramR R σ J X = 0 → gramR R σ J Y = 0 → ∃ h : HA R σ J, actW R σ J h X = Y := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hL X Y hX hY gX gY
  haveI : IsArtinianRing R := hL.2.2.2.2.1
  haveI : IsReduced R := hL.2.2.2.2.2.1
  have hconst : ∀ Z : Fin 1 → Fin M → R ⊗[F] E, (fun _ : Fin 1 => Z 0) = Z := by
    intro Z
    funext a
    rw [Subsingleton.elim a 0]
  have hlx : LinearIndependent (R ⊗[F] E) (fun _ : Fin 1 => X 0) := by rwa [hconst]
  have hly : LinearIndependent (R ⊗[F] E) (fun _ : Fin 1 => Y 0) := by rwa [hconst]
  have hxx : hR R σ J (X 0) (X 0) = 0 := congrFun (congrFun gX 0) 0
  have hyy : hR R σ J (Y 0) (Y 0) = 0 := congrFun (congrFun gY 0) 0
  obtain ⟨y, hy⟩ := GlobalTheory.T.hermitian_form_primitive_vector_pairing F E σ hσ M J hJ R hL (X 0) hlx
  obtain ⟨y', hy'⟩ := GlobalTheory.T.hermitian_form_primitive_vector_pairing F E σ hσ M J hJ R hL (Y 0) hly
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_hyperbolic_partner hσ hJ R (X 0) y hxx hy
  obtain ⟨u', hu1', hu2', hu3'⟩ := exists_hyperbolic_partner hσ hJ R (Y 0) y' hyy hy'
  have hG : gramR R σ J ![X 0, u] = !![0, 1; 1, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gramR, hxx, hu1, hu2, hu3]
  have hG' : gramR R σ J ![Y 0, u'] = !![0, 1; 1, 0] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [gramR, hyy, hu1', hu2', hu3']
  have hdet : IsUnit (gramR R σ J ![X 0, u]).det := by
    rw [hG, Matrix.det_fin_two_of]
    simp
  obtain ⟨h, hh⟩ := GlobalTheory.T.witt_extension_artinian_ring F E σ hσ M J hJ R 2 ![X 0, u] ![Y 0, u'] (hG.trans hG'.symm) hdet
  refine ⟨h, ?_⟩
  funext a
  rw [Subsingleton.elim a 0]
  simpa [actW, actTup] using congrFun hh 0

end GlobalTheory.CompanionTheory.WeilSiegel.FreeTrans
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviFactorOfUnipotentDecompStatement
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_factor_of_unipotent_decomp : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {r s : ℕ} (u : BlockIx (r + s) r → Ad E) (m : GA E r × GA E s) (k : Kinf E (r + s)) (c : GL (Fin (r + s)) (Af E)), c ∈ KO E (r + s) → unip u * lev (Ad E) r s m = cf (r + s) k c → ∃ (k₁ : Kinf E r) (c₁ : GL (Fin r) (Af E)) (k₂ : Kinf E s) (c₂ : GL (Fin s) (Af E)), c₁ ∈ KO E r ∧ c₂ ∈ KO E s ∧ m = (cf r k₁ c₁, cf s k₂ c₂) := by
  first | exact @GlobalTheory.CompanionTheory.LimV.LeviCf.levi_cf_integral | exact GlobalTheory.CompanionTheory.LimV.LeviCf.levi_cf_integral | (intros; apply GlobalTheory.CompanionTheory.LimV.LeviCf.levi_cf_integral <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentExtendByUnitVectorStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_extend_by_unit_vector : ∀ (K : Type) [CommRing K] (M n : ℕ) (α : K), IsUnit α → ∀ (c : Fin n → K) (X : Fin n → Fin M → K), LinearIndependent K (vec α c X : Fin (n + 1) → Fin (M + 1) → K) ↔ LinearIndependent K X := by
  first | exact @GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree.linearIndependent_vec_iff | exact GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree.linearIndependent_vec_iff | (intros; apply GlobalTheory.CompanionTheory.SW.PiLocalization₂.VecFree.linearIndependent_vec_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LinearIndependentUnitaryActionIffStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearIndependent_unitary_action_iff : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (M n : ℕ) (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), LinearIndependent (R ⊗[F] E) (actW R σ J h X) ↔ LinearIndependent (R ⊗[F] E) X := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree.actW_linearIndependent_iff | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree.actW_linearIndependent_iff | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.ActFree.actW_linearIndependent_iff <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureExtensionByOneStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fibre_measure_extension_by_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∃ m₀ : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E), StageData σ J t n b lam m₁ m₀ s B₀ a κ₁ cm := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.ToOld.stageData_of_stageDataF | exact GlobalTheory.CompanionTheory.SW.StageF.ToOld.stageData_of_stageDataF | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.ToOld.stageData_of_stageDataF <;> assumption)
end

