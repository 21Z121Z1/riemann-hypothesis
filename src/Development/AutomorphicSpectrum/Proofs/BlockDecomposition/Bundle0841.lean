import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0834
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0823
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0013
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0810
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0811
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NondegenerateCharacterCellFactorization
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0801
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0827
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0113
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0788
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0620
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0084
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0052
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneRightInjective
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0023
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0051
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarFibrationFormula
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.PsiSide
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0835
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0429
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0042
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0471
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0477
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0460
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0814
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0470
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0481
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0463
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0821
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0831
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0833
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0508
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeriesFactorizableRestrictionFinite
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateIntegralFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIdentityOfLocalDensities
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryBlockInvertibleCriterion

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RowsProportionalOfTransformStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rows_proportional_of_transform : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a b c d a₂ b₂ c₂ d₂ : Matrix (Fin p) (Fin p) K) (ζ ζ₂ : Matrix (Fin ρ) (Fin ρ) K)
      (η η₂ : Matrix (Fin ρ) (Fin p) K) (T : Matrix (Fin n) (Fin n) K),
    rowC hn η₂ a₂ c₂ = T * rowC hn η a c → rowD hn σ ζ₂ η₂ b₂ d₂ = T * rowD hn σ ζ η b d →
    (∃ T' : Matrix (Fin p) (Fin p) K, c₂ = T' * c ∧ d₂ = T' * d) ∧
    (IsUnit (blk4 a b c d).det → a₂ = a → b₂ = b → c₂ = c → d₂ = d → ζ₂ = ζ ∧ η₂ = η) := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.lowerRows_determine | exact GlobalTheory.CompanionTheory.ZUnf.lowerRows_determine | (intros; apply GlobalTheory.CompanionTheory.ZUnf.lowerRows_determine <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarExtensionFibreMeasure
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeStage

theorem sigmaFinite_of_integrable {V : Type} [TopologicalSpace V] [LocallyCompactSpace V]
    [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] {U : Set V} (hU : IsOpen U)
    {μ : Measure V} (h0 : μ Uᶜ = 0)
    (hint : ∀ φ : V → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ U → Integrable φ μ) :
    SigmaFinite μ := by
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  let K := CompactExhaustion.choice U
  have hfin : ∀ n, μ (Subtype.val '' K n) < ∞ := by
    intro n
    have hLc : IsCompact (Subtype.val '' K n) := (K.isCompact n).image continuous_subtype_val
    have hLU : Subtype.val '' K n ⊆ U := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    obtain ⟨f, hf1, hfc, hfs, hf01⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hLc hU hLU
    have hi := hint f f.continuous hfc hfs
    have hle : μ (Subtype.val '' K n) ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := by
      calc μ (Subtype.val '' K n) = ∫⁻ x in Subtype.val '' K n, 1 ∂μ := by simp
        _ = ∫⁻ x in Subtype.val '' K n, ENNReal.ofReal (f x) ∂μ :=
            setLIntegral_congr_fun hLc.measurableSet fun x hx => by simp [hf1 hx]
        _ ≤ ∫⁻ x, ENNReal.ofReal (f x) ∂μ := setLIntegral_le_lintegral _ _
    exact hle.trans_lt hi.lintegral_lt_top
  refine ⟨⟨⟨fun n => Subtype.val '' K n ∪ Uᶜ, fun _ => Set.mem_univ _, fun n => ?_, ?_⟩⟩⟩
  · exact (measure_union_le _ _).trans_lt (ENNReal.add_lt_top.2 ⟨hfin n, by simp [h0]⟩)
  · refine Set.eq_univ_of_forall fun x => ?_
    by_cases hx : x ∈ U
    · exact Set.mem_iUnion.2 ⟨K.find ⟨x, hx⟩, Or.inl ⟨⟨x, hx⟩, K.mem_find _, rfl⟩⟩
    · exact Set.mem_iUnion.2 ⟨0, Or.inr hx⟩

end GlobalTheory.CompanionTheory.WeilSiegel.FreeStage

namespace GlobalTheory.CompanionTheory.WeilSiegel.FreeStage

open GlobalTheory.CompanionTheory.SW.StageMeasure in
set_option maxHeartbeats 4000000 in

theorem fibre_block_stages_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (hT : ∀ a b, σ (T b a) = T a b) (hT' : ∀ a b, σ (blockOne (algebraMap F E t) T b a) = blockOne (algebraMap F E t) T a b), ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ m m₁ m', IsGramFibFree R σ (blockOne (algebraMap F E t) J) (n + 1) (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1)) m → IsGramFib R σ (blockOne (algebraMap F E t) J) 1 (coordW R b lam 1 (M + 1)) (coordHerm R σ b lam 1) m₁ → IsGramFibFree R σ J n (coordW R b lam n M) (coordHerm R σ b lam n) m' → ∀ c : ℝ≥0, (coordK R b lam).map (fun y => inclR R (algebraMap F E t) * y) = c • coordK R b lam → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → ∃ Ψ : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable Ψ ∧ (∀ h : HA R σ (blockOne (algebraMap F E t) J), Ψ (actW R σ _ h (fun _ => Fin.cons 1 (fun _ => 0))) = ∫⁻ X, φ (actW R σ _ h (consTup X)) ∂(m' (hermOf R σ T hT))) ∧ ∫⁻ X, φ X ∂(m (hermOf R σ _ hT')) = (c : ℝ≥0∞) ^ n * ∫⁻ y, Ψ y ∂(m₁ (hermScal R σ (algebraMap F R t))) := by
  intro F E _ _ _ _ _ σ hCM M J hJ t ht n T hT hT' R _ _ _ _ _ hR d b lam hlam m m₁ m' hm hm₁ hm' c hc φ hφ
  obtain ⟨i₁, i₂, i₃, i₄, -⟩ := id hR
  obtain ⟨k₁, k₂, k₃, k₄, -, -, -, hBorel, -, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hCM R
  obtain ⟨-, hW, hH⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hCM R d b lam hlam
  have hJ' := GlobalTheory.T.block_one_scalar_preserves_nondegenerate F E σ M J hJ t ht
  obtain ⟨g₁, g₂, g₃, g₄, g₅, gAct⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM (M + 1) _ hJ' R
  obtain ⟨u₁, u₂, u₃, u₄, u₅, uAct⟩ := GlobalTheory.T.adelic_unitary_group_locally_compact F E σ hCM M J hJ R
  have hgram : gramR R σ (blockOne (algebraMap F E t) J)
      (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) =
      (hermScal R σ (algebraMap F R t) : HermR R σ 1) := by
    rw [gram_first, inclR_algebraMap]
    rfl
  have hunit : IsUnit (gramR R σ (blockOne (algebraMap F E t) J)
      (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E))).det := by
    rw [gram_first]
    have e := Matrix.det_fin_one (Matrix.of fun (_ _ : Fin 1) => inclR (F := F) R (algebraMap F E t))
    show IsUnit (Matrix.det (Matrix.of fun (_ _ : Fin 1) => inclR (F := F) R (algebraMap F E t)))
    rw [e]
    exact ((isUnit_iff_ne_zero.2 (by simpa using ht)).map (inclR (F := F) R))
  obtain ⟨s, hsm, hs₁, hs₂⟩ := GlobalTheory.T.rank_one_gram_measurable_section F E σ hCM (M + 1) _ hJ' R hR _ hunit
  have hs₁' := fun y (hy : gramR R σ (blockOne (algebraMap F E t) J) y =
      (hermScal R σ (algebraMap F R t) : HermR R σ 1)) => hs₁ y (hy.trans hgram.symm)
  have hs₂' : ∀ C : Set (Fin 1 → Fin (M + 1) → R ⊗[F] E), IsCompact C →
      ∃ C' : Set (HA R σ (blockOne (algebraMap F E t) J)), IsCompact C' ∧ ∀ y ∈ C,
        gramR R σ (blockOne (algebraMap F E t) J) y =
          (hermScal R σ (algebraMap F R t) : HermR R σ 1) → s y ∈ C' := by
    intro C hC
    obtain ⟨C', hC', h⟩ := hs₂ C hC
    exact ⟨C', hC', fun y hy hg => h y hy (hg.trans hgram.symm)⟩
  obtain ⟨B, hBo, hTB, fib, hfib, hfibT⟩ := GlobalTheory.T.scalar_extension_fibre_formula F E σ hCM M J hJ t ht n T hT hT' R hR
    d b lam hlam m₁ m' hm₁ hm' c hc s hsm hs₁' hs₂'
  obtain ⟨h₁, h₂, h₃, h₄, hlift⟩ := GlobalTheory.T.hermitian_matrices_locally_compact_borel F E σ hCM R (n + 1)
  obtain ⟨g, hgc, hg⟩ := hlift (M + 1) _ hJ'
  have hWn := hW (n + 1) (M + 1)
  have hHn := hH (n + 1)
  have hBn := hBorel (n + 1) (M + 1)
  have hU' : gramR R σ (blockOne (algebraMap F E t) J) ⁻¹' (Subtype.val '' B) = g ⁻¹' B := by
    ext X
    simp [hg X]
  have hfree := GlobalTheory.T.linearly_independent_frames_open F E σ hCM R hR (n + 1) (M + 1)
  have hm₀ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily (coordW R b lam (n + 1) (M + 1))
      (gramR R σ (blockOne (algebraMap F E t) J)) Subtype.val
      (g ⁻¹' Set.univ ∩ {X | LinearIndependent (R ⊗[F] E) X})
      (coordHerm R σ b lam (n + 1)) Set.univ m := by
    rw [Set.preimage_univ, Set.univ_inter]
    exact hm
  rw [hU'] at hfib
  have hmT : fib (hermOf R σ _ hT') = m (hermOf R σ _ hT') :=
    GlobalTheory.T.measurable_embedding_of_injective_proper _ _ _ (coordW R b lam (n + 1) (M + 1)) (coordHerm R σ b lam (n + 1))
      (gramR R σ (blockOne (algebraMap F E t) J)) g Subtype.val Subtype.val_injective hgc hg _ hfree
      Set.univ B isOpen_univ hBo (Set.subset_univ _) m fib hm₀ hfib _ hTB
  have hBa := hBorel (n + 1) (M + 1)
  have hBb := hBorel n M
  have hBc := hBorel 1 (M + 1)
  have hact : Measurable fun p : HA R σ (blockOne (algebraMap F E t) J) × (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) =>
      actW R σ _ p.1 p.2 := (gAct (n + 1)).1.measurable
  have hactu : ∀ u : HA R σ J, Measurable (actW R σ J u : (Fin n → Fin M → R ⊗[F] E) → Fin n → Fin M → R ⊗[F] E) :=
    fun u => ((uAct n).1.comp (Continuous.prodMk_right u)).measurable
  have hframe : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      actW R σ _ (s p.1) (consTup p.2) :=
    hact.comp ((hsm.comp measurable_fst).prodMk (measurable_consTup.comp measurable_snd))
  have hF : Measurable fun p : (Fin 1 → Fin (M + 1) → R ⊗[F] E) × (Fin n → Fin M → R ⊗[F] E) =>
      φ (actW R σ _ (s p.1) (consTup p.2)) := hφ.comp hframe
  haveI hσ : SigmaFinite (m' (hermOf R σ T hT)) := by
    refine sigmaFinite_of_integrable (GlobalTheory.T.linearly_independent_frames_open F E σ hCM R hR n M) ?_ ?_
    · exact measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_right) (hm'.1 _)
    · intro f hfc hfs hft
      exact (hm'.2.2 f hfc hfs hft).1 _ (Set.mem_univ _)
  refine ⟨fun y => ∫⁻ X, φ (actW R σ _ (s y) (consTup X)) ∂(m' (hermOf R σ T hT)),
    hF.lintegral_prod_right', ?_, ?_⟩
  · intro h
    obtain ⟨ι, -, hιm, hιr, -, hιa⟩ := GlobalTheory.CompanionTheory.SW.StabFirst.stab_first F E σ hCM M J hJ t ht R
    have hy := hs₁' (actW R σ _ h (fun _ => Fin.cons 1 (fun _ => 0)))
      (((gAct 1).2.2.2 h _).trans hgram)
    set y := actW R σ _ h (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) with hydef
    have hfix : actW R σ _ ((s y)⁻¹ * h) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) =
        (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) := by
      calc actW R σ _ ((s y)⁻¹ * h) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E))
          = actW R σ _ (s y)⁻¹ y := (gAct 1).2.2.1 _ _ _
        _ = actW R σ _ (s y)⁻¹ (actW R σ _ (s y) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E))) := by
            rw [hy]
        _ = actW R σ _ ((s y)⁻¹ * s y) (fun _ : Fin 1 => (Fin.cons 1 (fun _ => 0) : Fin (M + 1) → R ⊗[F] E)) :=
            ((gAct 1).2.2.1 _ _ _).symm
        _ = _ := by rw [inv_mul_cancel, (gAct 1).2.1]
    obtain ⟨u, hu⟩ := (hιr _).2 hfix
    have hh : h = s y * ι u := by rw [hu, mul_inv_cancel_left]
    have hX : ∀ X : Fin n → Fin M → R ⊗[F] E,
        actW R σ _ h (consTup X) = actW R σ _ (s y) (consTup (actW R σ J u X)) := by
      intro X
      rw [hh, (gAct (n + 1)).2.2.1, hιa]
    have hinv := GlobalTheory.T.local_gram_fibration_disintegration F E σ hCM M J hJ R hR n _ _ m' (hW n M) (hH n) hm' u (hermOf R σ T hT)
    have hmeas : Measurable fun X : Fin n → Fin M → R ⊗[F] E => φ (actW R σ _ (s y) (consTup X)) :=
      hφ.comp (hact.comp ((measurable_const (a := s y)).prodMk measurable_consTup))
    calc ∫⁻ X, φ (actW R σ _ (s y) (consTup X)) ∂(m' (hermOf R σ T hT))
        = ∫⁻ X, φ (actW R σ _ (s y) (consTup X)) ∂((m' (hermOf R σ T hT)).map (actW R σ J u)) := by rw [hinv]
      _ = ∫⁻ X, φ (actW R σ _ (s y) (consTup (actW R σ J u X))) ∂(m' (hermOf R σ T hT)) :=
          lintegral_map hmeas (hactu u)
      _ = ∫⁻ X, φ (actW R σ _ h (consTup X)) ∂(m' (hermOf R σ T hT)) := by simp only [hX]
  · rw [← hmT, hfibT, lintegral_smul_measure, lintegral_map hφ hframe, lintegral_prod _ hF.aemeasurable]
    simp [ENNReal.smul_def]

end GlobalTheory.CompanionTheory.WeilSiegel.FreeStage
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalarFibrationFormulaStatement
section
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scalar_fibration_formula : Scal := by
  first | exact @GlobalTheory.CompanionTheory.RgBase.ScalFib.scal | exact GlobalTheory.CompanionTheory.RgBase.ScalFib.scal | (intros; apply GlobalTheory.CompanionTheory.RgBase.ScalFib.scal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelParabolicQuotientIffRowsStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_parabolic_quotient_iff_rows : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n : ℕ} (x r : Matrix (Fin (n + n)) (Fin (n + n)) K),
    IsUnit r.det → IsUnitary σ (blk4 0 1 (-1) 0) x → IsUnitary σ (blk4 0 1 (-1) 0) r →
    (IsSiegelP (x * r⁻¹) ↔ ∃ T : Matrix (Fin n) (Fin n) K, lowerC x = T * lowerC r ∧ GlobalTheory.CompanionTheory.RatPtsUnn.blkD x = T * GlobalTheory.CompanionTheory.RatPtsUnn.blkD r) := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.siegel_mul_inv_iff_rows | exact GlobalTheory.CompanionTheory.ZUnf.siegel_mul_inv_iff_rows | (intros; apply GlobalTheory.CompanionTheory.ZUnf.siegel_mul_inv_iff_rows <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SiegelWeilRankOneBaseCaseStatement
section
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_weil_rank_one_base_case : Prop1 → Simil → Hasse → Cnt → PositivityTheory.SiegelWeilFormula.Densx.BaseOne := by
  first | exact @GlobalTheory.CompanionTheory.Base1.baseOne_of_parts | exact GlobalTheory.CompanionTheory.Base1.baseOne_of_parts | (intros; apply GlobalTheory.CompanionTheory.Base1.baseOne_of_parts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimilitudeOfScalarFormulaStatement
section
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitude_of_scalar_formula : Scal → Simil := by
  first | exact @GlobalTheory.CompanionTheory.SW.BaseSimil.simil | exact GlobalTheory.CompanionTheory.SW.BaseSimil.simil | (intros; apply GlobalTheory.CompanionTheory.SW.BaseSimil.simil <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SmoothTensorFixedParabolicNearOne
section
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.Stab

theorem hRep_fix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (τ : Representation ℂ (Mir k i) V) (σ : Representation ℂ (GL (Fin t) k) W), IsSmooth τ → IsSmooth σ → ∀ z : V ⊗[ℂ] W, ∃ U ∈ nhds (1 : Mir k (i + t)), ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ U → hRep τ σ h z = z := by
  intro k _ _ _ _ i t V W _ _ _ _ τ σ hτ hσ z
  have hs : IsSmooth (hRep τ σ) :=
    isSmooth_comp (isSmooth_extTensor hτ hσ) _ (GlobalTheory.CompanionTheory.BZPhiPG.Onto.continuous_pgProj k i t)
  obtain ⟨O, hO, e⟩ := isOpen_induced_iff.1 (hs z)
  have hmem : ∀ h : HPG k i t, (h : Mir k (i + t)) ∈ O ↔ hRep τ σ h z = z := fun h =>
    Set.ext_iff.1 e h
  have h1 : (1 : Mir k (i + t)) ∈ O := (hmem 1).2 (by simp)
  exact ⟨O, hO.mem_nhds h1, fun h hh => (hmem h).1 hh⟩

end GlobalTheory.CompanionTheory.BZPsiPG.Stab
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardLatticeMeasureEqOne
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.CoordLat

theorem coordW_latV_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ v, coordW (Fv F v) b (lam v) 1 1 (latV b v) = 1 := by
  intro F E _ _ _ _ _ σ hσ d b lam hlam v
  obtain ⟨t1, t2, t3, t4, -⟩ := GlobalTheory.T.completion_is_local_ring F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  haveI := (hlam v).1
  have hK : IsHomeomorph (GlobalTheory.CompanionTheory.SW.WBox.cK (F := F) (E := E) (Fv F v) b) :=
    (GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Fv F v)).2.2.2.2.2.2.1 d b
  have mv := GlobalTheory.CompanionTheory.SW.WBox.map_coordW (Fv F v) hK (lam v) 1 1
  have hset : (latV b v : Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)) =
      (GlobalTheory.CompanionTheory.SW.WBox.eW (Fv F v) hK 1 1) ⁻¹'
        Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact ⟨fun h p => h p.1 p.2.1 p.2.2, fun h a i k => h (a, i, k)⟩
  rw [hset, mv.measure_preimage_equiv, Measure.pi_pi]
  simp [(hlam v).2]

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.CoordLat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TamagawaFourierIntegrable
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.NoFrame

theorem pair_abs {X Y : Type} [MeasurableSpace X] [MeasurableSpace Y] (μ : Measure X) [SFinite μ]
    (ν : Measure Y) [SFinite ν] (k : X → Y → ℂ) (e : X → X → ℂ)
    (hk : Measurable (Function.uncurry k)) (he : Measurable (Function.uncurry e))
    (hkn : ∀ v y, ‖k v y‖ = 1) (hen : ∀ v z, ‖e v z‖ = 1)
    (φ : Y → ℂ) (hφ : Integrable φ ν) (hJ : Integrable (fun v => ∫ y, φ y * k v y ∂ν) μ)
    (Φ : X → ℂ) (hΦ : Integrable Φ μ) (H : X → ℂ) (hHi : Integrable H μ)
    (hH : ∀ v, H v = ∫ z, Φ z * e v z ∂μ) (hinv : ∀ y, ∫ v, H v * k v y ∂μ = 0) :
    ∫ z, (∫ v, (∫ y, φ y * k v y ∂ν) * e v z ∂μ) * Φ z ∂μ = 0 := by
  have h1 : Integrable (Function.uncurry fun (z v : X) =>
      (∫ y, φ y * k v y ∂ν) * e v z * Φ z) (μ.prod μ) := by
    refine Integrable.mono (hΦ.mul_prod hJ) ?_ ?_
    · have hm1 : AEStronglyMeasurable (fun p : X × X => ∫ y, φ y * k p.2 y ∂ν) (μ.prod μ) :=
        hJ.aestronglyMeasurable.comp_snd
      have hm2 : AEStronglyMeasurable (fun p : X × X => e p.2 p.1) (μ.prod μ) :=
        (he.comp measurable_swap).aestronglyMeasurable
      have hm3 : AEStronglyMeasurable (fun p : X × X => Φ p.1) (μ.prod μ) :=
        hΦ.aestronglyMeasurable.comp_fst
      exact (hm1.mul hm2).mul hm3
    · refine Filter.Eventually.of_forall ?_
      rintro ⟨z, v⟩
      simp only [Function.uncurry_apply_pair, norm_mul, hen, mul_one]
      exact le_of_eq (mul_comm _ _)
  have h2 : Integrable (Function.uncurry fun (v : X) (y : Y) => φ y * k v y * H v) (μ.prod ν) := by
    refine Integrable.mono (hHi.mul_prod hφ) ?_ ?_
    · have hm1 : AEStronglyMeasurable (fun p : X × Y => φ p.2) (μ.prod ν) :=
        hφ.aestronglyMeasurable.comp_snd
      have hm2 : AEStronglyMeasurable (fun p : X × Y => k p.1 p.2) (μ.prod ν) :=
        hk.aestronglyMeasurable
      have hm3 : AEStronglyMeasurable (fun p : X × Y => H p.1) (μ.prod ν) :=
        hHi.aestronglyMeasurable.comp_fst
      exact (hm1.mul hm2).mul hm3
    · refine Filter.Eventually.of_forall ?_
      rintro ⟨v, y⟩
      simp only [Function.uncurry_apply_pair, norm_mul, hkn, mul_one]
      exact le_of_eq (mul_comm _ _)
  calc ∫ z, (∫ v, (∫ y, φ y * k v y ∂ν) * e v z ∂μ) * Φ z ∂μ
      = ∫ z, ∫ v, (∫ y, φ y * k v y ∂ν) * e v z * Φ z ∂μ ∂μ := by
        congr 1; funext z
        exact (integral_mul_const (Φ z) _).symm
    _ = ∫ v, ∫ z, (∫ y, φ y * k v y ∂ν) * e v z * Φ z ∂μ ∂μ := integral_integral_swap h1
    _ = ∫ v, (∫ y, φ y * k v y ∂ν) * H v ∂μ := by
        congr 1; funext v
        rw [hH v, ← integral_const_mul]
        congr 1; funext z; ring
    _ = ∫ v, ∫ y, φ y * k v y * H v ∂ν ∂μ := by
        congr 1; funext v
        exact (integral_mul_const (H v) _).symm
    _ = ∫ y, ∫ v, φ y * k v y * H v ∂μ ∂ν := integral_integral_swap h2
    _ = ∫ y, φ y * ∫ v, H v * k v y ∂μ ∂ν := by
        congr 1; funext y
        rw [← integral_const_mul]
        congr 1; funext v; ring
    _ = 0 := by simp [hinv]

theorem haar_facts {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] :
    SFinite μ ∧ μ.IsNegInvariant :=
  ⟨inferInstance, inferInstance⟩

theorem pair_ring {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [SecondCountableTopology R]
    {κ : Type} [Fintype κ] [MeasurableSpace (κ → R)] [BorelSpace (κ → R)] (μ : Measure (κ → R)) [SFinite μ]
    [μ.IsNegInvariant] (ψ : AddChar R ℂ) (hc : Continuous ψ) (hn : ∀ x, ‖ψ x‖ = 1)
    {Y : Type} [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → R)
    (hφ : Integrable φ ν) (hg : Measurable g)
    (hJ : Integrable (fun v : κ → R => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ)
    (Φ : (κ → R) → ℂ) (hΦi : Integrable Φ μ)
    (hHi : Integrable (fun w : κ → R => ∫ z, Φ z * ψ (z ⬝ᵥ w) ∂μ) μ)
    (hinv : ∀ x, ∫ y, (∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ) * ψ (y ⬝ᵥ x) ∂μ = Φ (-x))
    (h0 : ∀ y, Φ (g y) = 0) :
    ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0 := by
  have hdot : Continuous (fun p : (κ → R) × (κ → R) => p.1 ⬝ᵥ p.2) :=
    continuous_fst.dotProduct continuous_snd
  have hk : Measurable (Function.uncurry fun (v : κ → R) (y : Y) => ψ (v ⬝ᵥ g y)) := by
    have hm : Measurable (fun p : (κ → R) × (κ → R) => ψ (p.1 ⬝ᵥ p.2)) :=
      (hc.comp hdot).measurable
    exact hm.comp (measurable_fst.prodMk (hg.comp measurable_snd))
  have he : Measurable (Function.uncurry fun (v z : κ → R) => ψ (-(v ⬝ᵥ z))) :=
    (hc.comp hdot.neg).measurable
  have hHi' : Integrable (fun w : κ → R => ∫ z, Φ z * ψ (-(w ⬝ᵥ z)) ∂μ) μ := by
    refine hHi.comp_neg.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [dotProduct_neg]
    congr 1; funext z
    rw [dotProduct_comm]
  have hinv' : ∀ y, ∫ v, (∫ z, Φ z * ψ (-(v ⬝ᵥ z)) ∂μ) * ψ (v ⬝ᵥ g y) ∂μ = 0 := by
    intro y
    have h1 := hinv (-(g y))
    rw [neg_neg, h0 y] at h1
    refine (integral_neg_eq_self
      (fun v => (∫ z, Φ z * ψ (-(v ⬝ᵥ z)) ∂μ) * ψ (v ⬝ᵥ g y)) μ).symm.trans (Eq.trans ?_ h1)
    congr 1; funext v
    simp only [neg_dotProduct, neg_neg, dotProduct_neg]
    congr 1; congr 1; funext z
    rw [dotProduct_comm]
  exact pair_abs μ ν (fun v y => ψ (v ⬝ᵥ g y)) (fun v z => ψ (-(v ⬝ᵥ z))) hk he
    (fun v y => hn _) (fun v z => hn _) φ hφ hJ Φ hΦi _ hHi' (fun v => rfl) hinv'

theorem pair_vanish : ∀ (F : Type) [Field F] [NumberField F], NumberField.IsTotallyReal F → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ (κ : Type) [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)] (μ : Measure (κ → AF F)), GlobalTheory.SWLit.IsTamagawa F κ μ → ∀ (Y : Type) [MeasurableSpace Y] (ν : Measure Y) [SFinite ν] (φ : Y → ℂ) (g : Y → κ → AF F), Integrable φ ν → Measurable g → Integrable (fun v : κ → AF F => ∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) μ → ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, (∀ y, Φ (g y) = 0) → ∫ z, (∫ v, (∫ y, φ y * ψ (v ⬝ᵥ g y) ∂ν) * ψ (-(v ⬝ᵥ z)) ∂μ) * Φ z ∂μ = 0 := by
  intro F _ _ hF ψ hψ κ _ _ _ μ hμ Y _ ν _ φ g hφ hg hJ Φ hΦ h0
  have hH : μ.IsAddHaarMeasure := hμ.1
  obtain ⟨hS, hN⟩ := haar_facts μ
  have hc : Continuous ψ := hψ.1
  have hn : ∀ x, ‖ψ x‖ = 1 := hψ.2.1
  obtain ⟨-, -, hint⟩ := GlobalTheory.SplitSvN.schA_facts hF hΦ
  have hinv := GlobalTheory.TamFourier.fourier_inversion_tamagawa F hF ψ hψ κ μ hμ Φ hΦ
  have hHi : Integrable (fun w => ∫ z, Φ z * ψ (z ⬝ᵥ w) ∂μ) μ := by
    by_contra hni
    have hzero : ∀ x, Φ x = 0 := by
      intro x
      have h1 := hinv (-x)
      rw [neg_neg] at h1
      rw [← h1]
      apply integral_undef
      intro hi
      apply hni
      exact integrable_of_mul_unimodular μ (fun y => ∫ z, Φ z * ψ (z ⬝ᵥ y) ∂μ)
        (fun y => ψ (y ⬝ᵥ -x)) hi
        ((hc.comp (continuous_id.dotProduct continuous_const)).aestronglyMeasurable) (fun y => hn _)
    apply hni
    have hfun : (fun w => ∫ z, Φ z * ψ (z ⬝ᵥ w) ∂μ) = fun _ => (0 : ℂ) := by
      funext w; simp [hzero]
    rw [hfun]
    exact integrable_zero _ _ _
  exact pair_ring μ ψ hc hn ν φ g hφ hg hJ Φ (hint μ hH) hHi hinv h0

end GlobalTheory.CompanionTheory.WeilSiegel.NoFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TateIntegralFormulaStatement
section
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_integral_formula : Tate := by
  first | exact @GlobalTheory.CompanionTheory.TateRes.tate | exact GlobalTheory.CompanionTheory.TateRes.tate | (intros; apply GlobalTheory.CompanionTheory.TateRes.tate <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIdentityOfLocalDensitiesStatement
section
open PositivityTheory.Rg.Base1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_identity_of_local_densities : Scal → LocR → ThetaId := by
  first | exact @GlobalTheory.CompanionTheory.RgBase.Theta.thetaId | exact GlobalTheory.CompanionTheory.RgBase.Theta.thetaId | (intros; apply GlobalTheory.CompanionTheory.RgBase.Theta.thetaId <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryBlockInvertibleCriterionStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.Eis GlobalTheory.CompanionTheory.SwUnf
open PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.LeftInvSect GlobalTheory.CompanionTheory.Hypotheses₂.WeilU
open PositivityTheory.Rg.Rsw
open GlobalTheory.CompanionTheory.ZUnf GlobalTheory.Eis

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_block_invertible_criterion : ∀ {K : Type} [Field K] (σ : K →+* K), (∀ x, σ (σ x) = x) → ∀ {n ρ p : ℕ} (hn : ρ + p = n) (a₁ b₁ Z : Matrix (Fin ρ) (Fin ρ) K) (a₂ b₂ X Y : Matrix (Fin ρ) (Fin p) K)
      (a₃ b₃ W : Matrix (Fin p) (Fin ρ) K) (a₄ b₄ c' d' : Matrix (Fin p) (Fin p) K),
    IsUnitary σ (blk4 0 1 (-1) 0) (blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d')) →
    IsUnit (blk4 (bl hn a₁ a₂ a₃ a₄) (bl hn b₁ b₂ b₃ b₄) (bl hn (-1) X 0 c') (bl hn Z Y W d')).det →
    ∃ (ζ : Matrix (Fin ρ) (Fin ρ) K) (η : Matrix (Fin ρ) (Fin p) K) (T : Matrix (Fin n) (Fin n) K),
      IsUnit (blk4 (a₄ + a₃ * X) (b₄ + a₃ * Y) c' d').det ∧ IsUnitary σ (blk4 0 1 (-1) 0) (blk4 (a₄ + a₃ * X) (b₄ + a₃ * Y) c' d') ∧
      cT σ ζ = ζ ∧ bl hn (-1) X 0 c' = T * rowC hn η (a₄ + a₃ * X) c' ∧ bl hn Z Y W d' = T * rowD hn σ ζ η (b₄ + a₃ * Y) d' := by
  first | exact @GlobalTheory.CompanionTheory.ZUnf.NormalRow.normal_form | exact GlobalTheory.CompanionTheory.ZUnf.NormalRow.normal_form | (intros; apply GlobalTheory.CompanionTheory.ZUnf.NormalRow.normal_form <;> assumption)
end
end

