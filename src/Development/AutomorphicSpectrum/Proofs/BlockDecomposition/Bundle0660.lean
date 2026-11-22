import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0563
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0629
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0041
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0016
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral
import GroundTheory.AutomorphicForms.GL2.GJMatrixLocal
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0633
import GroundTheory.LocalFields.LocalZetaEpsilon
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1369
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1414
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DetGramRatOneNeZero
import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.UnitaryBaseChangeCharacters.UnitaryBaseChangeLemmas.ToComplBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FintypeResidue
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0601
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0630
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0598
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnitScalingLatticeMeasure
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0631
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorIntegerRingAlmostAllPlaces
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalRankOneDensityUniformizerPower
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0048
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0500
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFibreMeasureUnramifiedVolume
section
open scoped Matrix NNReal ENNReal TensorProduct
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.WhitFree GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.AvgFree MeasureTheory

namespace GlobalTheory.CompanionTheory.AvgFree.Lim

theorem tendsto_of_squeeze (a : ℕ → ℝ) (b : ℕ → ℕ → ℝ) (t e : ℕ → ℝ) (L : ℝ)
    (he : Filter.Tendsto e Filter.atTop (nhds 0)) (ht : Filter.Tendsto t Filter.atTop (nhds L))
    (hb : ∀ j, Filter.Tendsto (b j) Filter.atTop (nhds (t j)))
    (h1 : ∀ j k, b j k ≤ a k) (h2 : ∀ j k, a k ≤ b j k + e j) :
    Filter.Tendsto a Filter.atTop (nhds L) := by
  rw [Metric.tendsto_nhds]
  intro δ hδ
  have hδ3 : 0 < δ / 3 := by positivity
  have e1 := he.eventually (Metric.ball_mem_nhds _ hδ3)
  have e2 := ht.eventually (Metric.ball_mem_nhds _ hδ3)
  obtain ⟨j, hj1, hj2⟩ := (e1.and e2).exists
  have e3 := (hb j).eventually (Metric.ball_mem_nhds _ hδ3)
  filter_upwards [e3] with k hk
  rw [Real.dist_eq] at hj1 hj2 hk
  have p1 := abs_lt.1 hj1
  have p2 := abs_lt.1 hj2
  have p3 := abs_lt.1 hk
  have p4 := h1 j k
  have p5 := h2 j k
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

theorem le_of_forall_mean_le {H : Type} [TopologicalSpace H] [LocallyCompactSpace H] [MeasurableSpace H]
    [OpensMeasurableSpace H] (ν : Measure H) [ν.IsOpenPosMeasure] [IsFiniteMeasureOnCompacts ν]
    (G : H → ℝ≥0∞) (hGc : Continuous fun y => (G y).toReal) (hGf : ∀ y, G y ≠ ⊤) (D : ℝ≥0)
    (hD : ∀ Y, MeasurableSet Y → ∫⁻ y in Y, G y ∂ν ≤ D * ν Y) (c : H) : G c ≤ D := by
  by_contra hlt
  have hlt' : (D : ℝ≥0∞) < G c := not_le.1 hlt
  have hr : (D : ℝ) < (G c).toReal := by
    have := (ENNReal.toReal_lt_toReal ENNReal.coe_ne_top (hGf c)).2 hlt'
    simpa using this
  obtain ⟨r, hr1, hr2⟩ := exists_between hr
  have hO : IsOpen {y | r < (G y).toReal} := isOpen_lt continuous_const hGc
  obtain ⟨K, hK, hcK, hKO⟩ := exists_compact_subset hO hr2
  have hYm : MeasurableSet (interior K) := isOpen_interior.measurableSet
  have hpos : ν (interior K) ≠ 0 := isOpen_interior.measure_ne_zero ν ⟨c, hcK⟩
  have hfin : ν (interior K) ≠ ⊤ := ne_top_of_le_ne_top hK.measure_lt_top.ne (measure_mono interior_subset)
  have h1 : ENNReal.ofReal r * ν (interior K) ≤ ∫⁻ y in interior K, G y ∂ν := by
    rw [← setLIntegral_const]
    refine setLIntegral_mono' hYm fun y hy => ?_
    have hy' : r < (G y).toReal := hKO (interior_subset hy)
    rw [← ENNReal.ofReal_toReal (hGf y)]
    exact ENNReal.ofReal_le_ofReal hy'.le
  have h2 := h1.trans (hD _ hYm)
  have hr0 : 0 ≤ r := (NNReal.coe_nonneg D).trans hr1.le
  have hnr : 0 < (ν (interior K)).toReal := ENNReal.toReal_pos hpos hfin
  have h3 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hfin) h2
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hr0, ENNReal.coe_toReal] at h3
  exact absurd (le_of_mul_le_mul_right h3 hnr) (not_le.2 hr1)

end GlobalTheory.CompanionTheory.AvgFree.Lim

open GlobalTheory.CompanionTheory.AvgFree.Lim GlobalTheory.CompanionTheory.Hypotheses₂.OneV.AvgV in

theorem GlobalTheory.CompanionTheory.AvgFree.Lim.avg_tendsto_free : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (lv : Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdV v lv → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), HeckeCharacterZeroLocus.SiegelWeilU.IsHermND σ J → ∀ (n : ℕ) (mv : (HermR (Fv F v) σ n) → Measure (Fin n → Fin M → (Fv F v ⊗[F] E))), IsGramFibFree (Fv F v) σ J n (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) mv → ∀ (c : (HermR (Fv F v) σ n)) (A : Set (Fin n → Fin M → (Fv F v ⊗[F] E))), IsCompact A → IsOpen A → ∀ Tt : ℕ → Set (Fin n → Fin M → (Fv F v ⊗[F] E)), Monotone Tt → (∀ j, IsCompact (Tt j) ∧ IsOpen (Tt j) ∧ Tt j ⊆ A ∧ Tt j ⊆ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X}) → A ∩ {X : (Fin n → Fin M → (Fv F v ⊗[F] E)) | LinearIndependent (Fv F v ⊗[F] E) X} ⊆ ⋃ j, Tt j → ∀ ε : ℕ → ℝ≥0, Filter.Tendsto ε Filter.atTop (nhds 0) → (∀ (j : ℕ) (Y : Set (HermR (Fv F v) σ n)), MeasurableSet Y → (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) ((A \ Tt j) ∩ gramIn (Fv F v) σ J Y) ≤ ε j * (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) Y) → mv c A ≠ ⊤ ∧ ∀ U : ℕ → Set (HermR (Fv F v) σ n), (∀ k, IsCompact (U k) ∧ IsOpen (U k) ∧ (0 : (HermR (Fv F v) σ n)) ∈ U k) → Filter.Tendsto U Filter.atTop (nhds (0 : (HermR (Fv F v) σ n))).smallSets → (∀ k, MeasurableSet (A ∩ gramNear (Fv F v) σ J c (U k)) ∧ (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (A ∩ gramNear (Fv F v) σ J c (U k)) ≠ ⊤) ∧ Filter.Tendsto (fun k => ((GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M) (A ∩ gramNear (Fv F v) σ J c (U k))).toReal / ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (U k)).toReal) Filter.atTop (nhds (mv c A).toReal) := by
  intro F E _ _ _ _ _ σ hσ d b v lv hlv M J hJ n mv hmv c A hAc hAo Tt hTm hT hcov ε hε hden
  obtain ⟨r1, r2, r3, r4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI := r1
  haveI := r2
  haveI := r3
  haveI := r4
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨a1, a2, a3, a4, -, -, -, a8, a9, a10⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hσ (Fv F v)
  haveI := a1
  haveI := a2
  haveI := a3
  haveI := a4
  haveI := a8 n M
  haveI := hlv.1
  obtain ⟨-, hW, hH⟩ := GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hσ (Fv F v) d b lv hlv.1
  haveI := hW n M
  haveI := hH n
  haveI : BorelSpace (HermR (Fv F v) σ n) := ⟨rfl⟩
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → Fv F v ⊗[F] E))
  haveI : LocallyCompactSpace (Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → Fv F v ⊗[F] E))
  haveI : LocallyCompactSpace (HermR (Fv F v) σ n) := (a9 n).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (HermR (Fv F v) σ n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n).IsNegInvariant :=
    Measure.IsAddHaarMeasure.isNegInvariant_of_regular _
  have I := GlobalTheory.T.local_fibre_measure_unramified_formula F E σ hσ d b v lv hlv M J hJ n mv hmv
  have hAm : MeasurableSet A := hAo.measurableSet

  obtain ⟨h0m, -, -, C, hC⟩ := I (Tt 0) (hT 0).1 (hT 0).2.1 (hT 0).2.2.2
  have hsplit : ∀ (j : ℕ) (Y : Set (HermR (Fv F v) σ n)), MeasurableSet Y →
      GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (A ∩ gramIn (Fv F v) σ J Y) ≤
        GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (Tt j ∩ gramIn (Fv F v) σ J Y) +
          ε j * GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n Y := by
    intro j Y hY
    refine (measure_mono ?_).trans ((measure_union_le (Tt j ∩ gramIn (Fv F v) σ J Y)
      ((A \ Tt j) ∩ gramIn (Fv F v) σ J Y)).trans (by gcongr; exact hden j Y hY))
    intro X hX
    by_cases h : X ∈ Tt j
    · exact Or.inl ⟨h, hX.2⟩
    · exact Or.inr ⟨⟨hX.1, h⟩, hX.2⟩
  have hbd : ∀ j, mv c (Tt j) ≤ ((C + ε 0 : ℝ≥0) : ℝ≥0∞) := by
    intro j
    obtain ⟨hjm, hjc, hjf, -⟩ := I (Tt j) (hT j).1 (hT j).2.1 (hT j).2.2.2
    refine le_of_forall_mean_le (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (fun y => mv y (Tt j)) hjc hjf _
      (fun Y hY => ?_) c
    rw [← hjm Y hY]
    refine (measure_mono (Set.inter_subset_inter_left _ (hT j).2.2.1)).trans ((hsplit 0 Y hY).trans ?_)
    rw [h0m Y hY, ENNReal.coe_add, add_mul]
    gcongr
    rw [← setLIntegral_const]
    exact setLIntegral_mono' hY fun y _ => hC y

  have hle : mv c A ≤ mv c (⋃ j, Tt j) := by
    have hcar := hmv.1 c
    refine (measure_mono (t := (⋃ j, Tt j) ∪ (gramR (Fv F v) σ J ⁻¹' {(c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))} ∩
      {X : Fin n → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X})ᶜ) ?_).trans
      ((measure_union_le _ _).trans ?_)
    · intro X hX
      by_cases h : X ∈ (gramR (Fv F v) σ J ⁻¹' {(c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))} ∩
        {X : Fin n → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X})
      · exact Or.inl (hcov ⟨hX, h.2⟩)
      · exact Or.inr h
    · have hcar' : mv c (gramR (Fv F v) σ J ⁻¹' {(c : Matrix (Fin n) (Fin n) (Fv F v ⊗[F] E))} ∩
        {X : Fin n → Fin M → Fv F v ⊗[F] E | LinearIndependent (Fv F v ⊗[F] E) X})ᶜ = 0 := hcar
      rw [hcar', add_zero]
  have hsup : mv c (⋃ j, Tt j) = ⨆ j, mv c (Tt j) := hTm.measure_iUnion
  have heq : mv c A = ⨆ j, mv c (Tt j) :=
    le_antisymm (hle.trans hsup.le) (iSup_le fun j => measure_mono (hT j).2.2.1)
  have hfin : mv c A ≠ ⊤ := by
    rw [heq]
    exact ne_top_of_le_ne_top ENNReal.coe_ne_top (iSup_le hbd)
  have hlim : Filter.Tendsto (fun j => mv c (Tt j)) Filter.atTop (nhds (mv c A)) := by
    rw [heq]
    exact tendsto_atTop_iSup fun i j hij => measure_mono (hTm hij)
  refine ⟨hfin, fun U hU hUt => ?_⟩

  have hinv := GlobalTheory.CompanionTheory.SW.HermTop.sigma_sigma hσ
  let Q : (Fin n → Fin M → Fv F v ⊗[F] E) → HermR (Fv F v) σ n := fun X =>
    ⟨gramR (Fv F v) σ J X, GlobalTheory.CompanionTheory.SW.HermTop.gramR_mem (Fv F v) hinv hJ.1 X⟩
  have hQc : Continuous Q := (a10 n M J).subtype_mk _
  have hnear : ∀ W : Set (HermR (Fv F v) σ n), gramNear (Fv F v) σ J c W = (fun X => c - Q X) ⁻¹' W := by
    intro W
    ext X
    constructor
    · rintro ⟨u, hu, e⟩
      have : c - Q X = u := Subtype.ext e
      show c - Q X ∈ W
      rwa [this]
    · intro h
      exact ⟨c - Q X, h, rfl⟩
  let S : ℕ → Set (HermR (Fv F v) σ n) := fun k => (fun y => c - y) ⁻¹' U k
  have hgram : ∀ k, gramNear (Fv F v) σ J c (U k) = gramIn (Fv F v) σ J (S k) := by
    intro k
    rw [hnear]
    ext X
    constructor
    · intro h
      exact ⟨Q X, h, rfl⟩
    · rintro ⟨y, hy, e⟩
      have : y = Q X := Subtype.ext e.symm
      rw [this] at hy
      exact hy
  have hSo : ∀ k, IsOpen (S k) := fun k => (hU k).2.1.preimage (continuous_const.sub continuous_id)
  have hSm : ∀ k, MeasurableSet (S k) := fun k => (hSo k).measurableSet
  have hSc : ∀ k, c ∈ S k := fun k => by
    show c - c ∈ U k
    rw [sub_self]
    exact (hU k).2.2
  have hSU : ∀ k, GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (S k) = GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k) := fun k =>
    (Measure.measurePreserving_sub_left _ c).measure_preimage (hU k).2.1.measurableSet.nullMeasurableSet
  have hpos : ∀ k, GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (S k) ≠ 0 := fun k =>
    (hSo k).measure_ne_zero _ ⟨c, hSc k⟩
  have htop : ∀ k, GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (S k) ≠ ⊤ := fun k => by
    rw [hSU]
    exact (hU k).1.measure_lt_top.ne
  have hl : Filter.Tendsto S Filter.atTop (nhds c).smallSets := by
    rw [Filter.tendsto_smallSets_iff]
    intro t ht
    have hcont : Filter.Tendsto (fun u : HermR (Fv F v) σ n => c - u) (nhds 0) (nhds c) := by
      have : Continuous fun u : HermR (Fv F v) σ n => c - u := continuous_const.sub continuous_id
      simpa using this.tendsto 0
    have h0 := (Filter.tendsto_smallSets_iff.1 hUt) _ (hcont ht)
    filter_upwards [h0] with k hk s hs
    have := hk hs
    simpa using this
  have hAfin : ∀ B : Set (Fin n → Fin M → Fv F v ⊗[F] E), B ⊆ A → GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M B ≠ ⊤ :=
    fun B hB => ne_top_of_le_ne_top hAc.measure_lt_top.ne (measure_mono hB)
  refine ⟨fun k => ?_, ?_⟩
  · refine ⟨?_, hAfin _ Set.inter_subset_left⟩
    rw [hnear]
    exact (hAo.inter ((hU k).2.1.preimage (continuous_const.sub hQc))).measurableSet
  · refine tendsto_of_squeeze _
      (fun j k => (GlobalTheory.CompanionTheory.SW.coordW (Fv F v) b lv n M (Tt j ∩ gramIn (Fv F v) σ J (S k))).toReal /
        (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k)).toReal)
      (fun j => (mv c (Tt j)).toReal) (fun j => (ε j : ℝ)) _ ?_ ((ENNReal.tendsto_toReal hfin).comp hlim) ?_ ?_ ?_
    · have h := NNReal.tendsto_coe.2 hε
      rwa [NNReal.coe_zero] at h
    · intro j
      obtain ⟨hjm, hjc, hjf, -⟩ := I (Tt j) (hT j).1 (hT j).2.1 (hT j).2.2.2
      have key := tendsto_mean (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n) (fun y => mv y (Tt j)) c hjc.continuousAt
        (Filter.Eventually.of_forall hjf) S hSm hl hpos htop
      refine key.congr fun k => ?_
      rw [hSU k, hjm (S k) (hSm k)]
    · intro j k
      rw [hgram k]
      refine div_le_div_of_nonneg_right (ENNReal.toReal_mono (hAfin _ Set.inter_subset_left) ?_) ENNReal.toReal_nonneg
      exact measure_mono (Set.inter_subset_inter_left _ (hT j).2.2.1)
    · intro j k
      rw [hgram k]
      have hp : 0 < (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b lv n (U k)).toReal := by
        rw [← hSU k]
        exact ENNReal.toReal_pos (hpos k) (htop k)
      have hs := hsplit j (S k) (hSm k)
      rw [hSU k] at hs
      have hr := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hAfin _ (Set.inter_subset_inter_left _ (hT j).2.2.1 |>.trans Set.inter_subset_left),
        ENNReal.mul_ne_top ENNReal.coe_ne_top (by rw [← hSU k]; exact htop k)⟩) hs
      rw [ENNReal.toReal_add (hAfin _ (Set.inter_subset_inter_left _ (hT j).2.2.1 |>.trans Set.inter_subset_left))
        (ENNReal.mul_ne_top ENNReal.coe_ne_top (by rw [← hSU k]; exact htop k)), ENNReal.toReal_mul, ENNReal.coe_toReal] at hr
      rw [div_le_iff₀ hp, add_mul, div_mul_cancel₀ _ hp.ne']
      exact hr
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFourierCosetIndValBall
section
open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt restrictedTensor2 vecAt awayIntegral awayBox)
open GroundTheory.Automorphic.GJMatrix (cosetInd localTensor localFourierPi localMeasurePi)
open Ad3 Ad3.R
open scoped NumberField.AdeleRing ValuativeRel ENNReal ComplexConjugate SchwartzMap nonZeroDivisors Classical

namespace GlobalTheory.CompanionTheory.RSFT

theorem localFourier_cosetInd_valBall : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (N : ℤ) (a y : F), localFourier (selfDualMeasure ψ) ψ (cosetInd (valBall F N) a) y = (ψ (a * y) : ℂ) * (((residueCard F : ℝ) ^ (-N) : ℝ) : ℂ) * (valBall F (-N) : Set F).indicator (fun _ => (1 : ℂ)) y := by
  intro F _ _ _ _ _ _ ψ hψ N a y
  obtain ⟨hc, h1, h0⟩ := hψ
  have hμ : (GroundTheory.LocalField.selfDualMeasure ψ).real (valBall F N : Set F) =
      (residueCard F : ℝ) ^ (-N) := by
    rw [measureReal_valBall, selfDualMeasure_real_valBall_zero, h0]
    simp
  have key := localFourier_indicator_valBall (GroundTheory.LocalField.selfDualMeasure ψ) hc h1 N y
  rw [h0, zero_sub, hμ] at key
  have e : (fun x => cosetInd (valBall F N) a (a + x) * (ψ ((a + x) * y) : ℂ)) =
      fun x => (ψ (a * y) : ℂ) *
        ((valBall F N : Set F).indicator (fun _ => (1 : ℂ)) x * (ψ (x * y) : ℂ)) := by
    funext x
    rw [GroundTheory.Automorphic.GJMatrix.cosetInd_apply, add_sub_cancel_left, Set.indicator_apply, add_mul,
      AddChar.map_add_eq_mul, Circle.coe_mul]
    simp only [SetLike.mem_coe]
    ring
  have e2 : localFourier (GroundTheory.LocalField.selfDualMeasure ψ) ψ (cosetInd (valBall F N) a) y =
      (ψ (a * y) : ℂ) * localFourier (GroundTheory.LocalField.selfDualMeasure ψ) ψ
        ((valBall F N : Set F).indicator fun _ => (1 : ℂ)) y := by
    unfold localFourier
    rw [← integral_add_left_eq_self _ a, e, integral_const_mul]
  rw [e2, key, mul_assoc]

end GlobalTheory.CompanionTheory.RSFT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalHermitianClassFirstStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.IndefiniteRowSideFullHecke.SelfReciprocalLocalField PositivityTheory.BCUSide.HermitianLocalForms
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_hermitian_class_first : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (hU : Unr E) (w : Pl E) (hw : ¬ IsSplitAt w) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (hv : w.under (𝓞 (maximalRealSubfield E)) = v), ∀ (n : ℕ) (γ₀ : GL (Fin n) E), γ₀.val.charpoly ∈ Ell E n → ∀ H₀ : Matrix (Fin n) (Fin n) E, IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H₀ → H₀.det ≠ 0 → cT (IsCMField.complexConj E).toRingEquiv.toRingHom γ₀.val * H₀ * γ₀.val = H₀ → (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H₀.map τ = cT (starRingEnd ℂ) Q * Q) → ∀ (m : (w.adicCompletion E)[X]) (r : ℕ) (Q : SelfRecip E r), Q.1 ∣ γ₀.val.charpoly → ∀ x : ((v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q)ˣ, inclPlus Q (v.adicCompletion (maximalRealSubfield E)) (x : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q) = locPhi hU w hw v hv Q m → sgnOn (cj w) ((H₀.map (algebraMap E (w.adicCompletion E))) * aeval (γ₀.val.map (algebraMap E (w.adicCompletion E))) m) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) = ((GlobalTheory.QuadSymbol.eta (maximalRealSubfield E) E (v.adicCompletion (maximalRealSubfield E)) (Units.map (Algebra.norm (v.adicCompletion (maximalRealSubfield E)) : (v.adicCompletion (maximalRealSubfield E)) ⊗[(maximalRealSubfield E)] plus Q →* (v.adicCompletion (maximalRealSubfield E))) x) : ℤ) : ℂ) * sgnOn (cj w) (H₀.map (algebraMap E (w.adicCompletion E))) (atPl w Q.1) (γ₀.val.map (algebraMap E (w.adicCompletion E))) := by
  first | exact @GlobalTheory.CompanionTheory.LocalSignInert.main | exact GlobalTheory.CompanionTheory.LocalSignInert.main | (intros; apply GlobalTheory.CompanionTheory.LocalSignInert.main <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInnerProductLeftIntegral
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.LFUDom

namespace GlobalTheory.CompanionTheory.LFUDom

theorem mul_integral_of_integral {F : Type} [Field F] [ValuativeRel F]
    (A : Matrix (Fin 2) (Fin 2) F) (X : Matrix (Fin 2) (Fin 3) F)
    (hA : ∀ i j, A i j ∈ 𝒪[F]) (hX : ∀ i j, X i j ∈ 𝒪[F]) :
    ∀ i j, (A * X) i j ∈ 𝒪[F] := by
  intro i j
  rw [Matrix.mul_apply]
  exact sum_mem fun k _ => mul_mem (hA i k) (hX k j)

theorem Φ0_integral_mul {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (κ : GL (Fin 2) F) (hκ : κ ∈ integralGL F 2)
    (X : Matrix (Fin 2) (Fin 3) F) :
    Ad3.LFS.Φ0 F ((κ : Matrix (Fin 2) (Fin 2) F) * X) = Ad3.LFS.Φ0 F X := by
  obtain ⟨h1, h2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hκ
  have hiff : (∀ i j, ((κ : Matrix (Fin 2) (Fin 2) F) * X) i j ∈ 𝒪[F]) ↔
      ∀ i j, X i j ∈ 𝒪[F] := by
    refine ⟨fun h => ?_, mul_integral_of_integral _ _ h1⟩
    have hk : ((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
        ((κ : Matrix (Fin 2) (Fin 2) F) * X) = X := by
      rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]
    have := mul_integral_of_integral _ _ h2 h
    rwa [hk] at this
  unfold Ad3.LFS.Φ0
  by_cases hX : ∀ i j, X i j ∈ 𝒪[F]
  · rw [Set.indicator_of_mem (by exact hiff.2 hX), Set.indicator_of_mem (by exact hX)]
    rfl
  · rw [Set.indicator_of_notMem (by exact fun h => hX (hiff.1 h)), Set.indicator_of_notMem (by exact hX)]

theorem inn_Φ0_integral_mul : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (κ : GL (Fin 2) F), κ ∈ integralGL F 2 → ∀ (h : GL (Fin 2) F) (g : GL (Fin 3) F),
    Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) (κ * h) g = Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h g := by
  intro F _ _ _ _ _ _ ψ κ hκ h g
  unfold Ad3.LFS.inn
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only
  rw [Units.val_mul, Matrix.mul_assoc, Matrix.mul_assoc, Φ0_integral_mul κ hκ, Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.LFUDom
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalInnerProductSupport
section
noncomputable section

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.Iwasawa GroundTheory.Automorphic.GLnLocal
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.LFUDom

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem entries_iff (h : GL (Fin 2) F) (l : Fin 3 → ℤ) (x : Fin 2 → F) :
    (∀ i j, ((h : Matrix (Fin 2) (Fin 2) F) * Ad3.LFS.blk x *
        ((torusPow F 3 l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) i j ∈ 𝒪[F]) ↔
    (∀ a b, ((h * torusPow F 2 ![l 0, l 1] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) ∧
    ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F] := by
  simp only [Units.val_mul, coe_torusPow, Matrix.mul_diagonal, Fin.forall_fin_succ, Fin.forall_fin_two,
    Ad3.LFS.blk]
  simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two, Fin.sum_univ_three, Matrix.diagonal_apply]
  have e : ∀ a b c d t : F, t * a * b + t * c * d = (a * b + c * d) * t := fun a b c d t => by ring
  simp only [e]
  tauto

end

theorem innred : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle) (h : GL (Fin 2) F) (l : Fin 3 → ℤ),
  ((¬ ∀ a b, ((h * torusPow F 2 ![l 0, l 1] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) →
    Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h (torusPow F 3 l) = 0) ∧
  ((∀ a b, ((h * torusPow F 2 ![l 0, l 1] : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) a b ∈ 𝒪[F]) →
    Ad3.LFS.inn ψ (Ad3.LFS.Φ0 F) h (torusPow F 3 l) =
      ∫ x, Set.indicator {x : Fin 2 → F | ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]} (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ)) x ∂Ad3.LFS.vol2 ψ) := by
  intro F _ _ _ _ _ _ ψ h l
  have h1 : ∀ X : Matrix (Fin 2) (Fin 3) F, (∀ i j, X i j ∈ 𝒪[F]) → Ad3.LFS.Φ0 F X = 1 := fun X hX =>
    Set.indicator_of_mem (s := {X : Matrix (Fin 2) (Fin 3) F | ∀ i j, X i j ∈ 𝒪[F]}) hX 1
  have h0 : ∀ X : Matrix (Fin 2) (Fin 3) F, (¬ ∀ i j, X i j ∈ 𝒪[F]) → Ad3.LFS.Φ0 F X = 0 := fun X hX =>
    Set.indicator_of_notMem (s := {X : Matrix (Fin 2) (Fin 3) F | ∀ i j, X i j ∈ 𝒪[F]}) hX 1
  refine ⟨fun hn => ?_, fun hy => ?_⟩
  · unfold Ad3.LFS.inn
    have hz : ∀ x : Fin 2 → F, Ad3.LFS.Φ0 F ((h : Matrix (Fin 2) (Fin 2) F) * Ad3.LFS.blk x *
        ((torusPow F 3 l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) = 0 := fun x =>
      h0 _ fun q => hn ((entries_iff h l x).1 q).1
    simp [hz]
  · unfold Ad3.LFS.inn
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]
    · beta_reduce
      rw [h1 _ ((entries_iff h l x).2 ⟨hy, hx⟩), one_mul]
      exact (Set.indicator_of_mem (s := {x : Fin 2 → F | ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]}) (a := x) hx
        (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ))).symm
    · beta_reduce
      rw [h0 _ fun q => hx ((entries_iff h l x).1 q).2, zero_mul]
      exact (Set.indicator_of_notMem (s := {x : Fin 2 → F | ∀ i, (((torusPow F 2 ![l 2, l 2] * h : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ x) i ∈ 𝒪[F]}) (a := x) hx
        (fun x : Fin 2 → F => ((ψ (-x 1) : Circle) : ℂ))).symm

end GlobalTheory.CompanionTheory.LFUDom
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalRankOneZeroFibreVolumeStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_rank_one_zero_fibre_volume : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (h₂ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b) (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ (c : Fv F v ⊗[F] E) (a : ℝ≥0) (t : Fv F v), IsUnit c → a ≠ 0 → (coordK (Fv F v) b lam).map (fun x => c * x) = a • coordK (Fv F v) b lam → algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ c * c → ‖t‖ = (a : ℝ)⁻¹ → ∀ A : Set (Fin 1 → Fin M → Fv F v ⊗[F] E), MeasurableSet A → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) {y | scalT c y ∈ A} = (a : ℝ≥0∞) ^ (M - 1) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₂) A := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ScaleFib.mass_scalT | exact GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ScaleFib.mass_scalT | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ScaleFib.mass_scalT <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnitScalingLatticeMeasureStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unit_scaling_lattice_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m' : Measure (Fin n → Fin M → Fv F v ⊗[F] E)) (c : Fv F v ⊗[F] E) (a : ℝ≥0), IsUnit c → c ∈ intK b v → (coordK (Fv F v) b lam).map (fun x => c * x) = a • coordK (Fv F v) b lam → ∀ y ∈ primV σ J b v, ∃ g : HA (Fv F v) σ (hypOne J), actW (Fv F v) σ (hypOne J) g (e0 _ M) = scalT c y ∧ stageInt (Fv F v) σ J b lam m' ((latV b v).indicator 1) g = (a : ℝ≥0∞) ^ n * m' (latV b v) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypMass.StageVal.stageInt_primV | exact GlobalTheory.CompanionTheory.WeilSiegel.HypMass.StageVal.stageInt_primV | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypMass.StageVal.stageInt_primV <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalUnitScalingNormMeasureStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypMass

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_unit_scaling_norm_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (c : Fv F v ⊗[F] E) (t : Fv F v) (w : ℕ), IsUnit c → algebraMap (Fv F v) (Fv F v ⊗[F] E) t = sigR (Fv F v) σ c * c → ‖t‖ = ((qv v : ℝ) ^ w)⁻¹ → (coordK (Fv F v) b lam).map (fun x => c * x) = (qv v ^ w) • coordK (Fv F v) b lam := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale.coordK_map_mul | exact GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale.coordK_map_mul | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypMass.ContentScale.coordK_map_mul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalVolumeRankOneStandardStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_volume_rank_one_standard : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 3 ≤ M → ∀ (h₀ : ∀ a b : Fin 1, σ ((0 : Matrix (Fin 1) (Fin 1) E) b a) = (0 : Matrix (Fin 1) (Fin 1) E) a b), ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin M → Fv F v ⊗[F] E)), IsGramFibFree (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ (a e : ℕ), 0 < a → Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ e → ¬ Ideal.span {(a : 𝓞 F)} ≤ v.asIdeal ^ (e + 1) → m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) {X : Fin 1 → Fin M → Fv F v ⊗[F] E | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v} = ENNReal.ofReal ((Ideal.absNorm v.asIdeal : ℝ) ^ (e * (2 * M - 2))) * m (hermOf (Fv F v) σ (0 : Matrix (Fin 1) (Fin 1) E) h₀) (latV b v) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero.mass_dilated_lattice | exact GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero.mass_dilated_lattice | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.Free.ScaleZero.mass_dilated_lattice <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorShiftStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_pairing_conductor_shift : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (p : Mir k n) (v : V) (v' : V') (A : ℂ), EvVal ν ψ T B v v' A → EvVal ν ψ T B (T (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v) (T' (levi k (n + 1) (p : GL (Fin (n + 1)) k)) v') (((detChar (Fin (n + 1)) (absPow k ((s + 1 : ℕ) : ℂ)) (p : GL (Fin (n + 1)) k) : ℂˣ) : ℂ) * A) := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.evVal_conj | exact GlobalTheory.CompanionTheory.MirPair.evVal_conj | (intros; apply GlobalTheory.CompanionTheory.MirPair.evVal_conj <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicPairingConductorVanishingStatement
section
open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZSeg GlobalTheory.BZMir GlobalTheory.SplitWeil GlobalTheory.CompanionTheory.MirFourier GlobalTheory.CompanionTheory.BZOnto.PerpSmall ValuativeRel Zc
open scoped Topology
open GlobalTheory.CompanionTheory.MirPair

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_pairing_exists_eventual_value : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] (ψ : AddChar k Circle) (c : kˣ) {n : ℕ} {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (T : Representation ℂ (Mir k (n + 1)) V) (T' : Representation ℂ (Mir k (n + 1)) V') (B : V →ₗ[ℂ] V' →ₗ[ℂ] ℂ) (s : ℕ), Continuous ψ → HasConductor ψ c → IsSmooth T → IsSmooth T' → TwInv T T' B s → ∀ (v : V) (v' : V'), ∃ A, EvVal ν ψ T B v v' A := by
  first | exact @GlobalTheory.CompanionTheory.MirPair.exists_evVal | exact GlobalTheory.CompanionTheory.MirPair.exists_evVal | (intros; apply GlobalTheory.CompanionTheory.MirPair.exists_evVal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MixedCycleReadExistsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_cycle_read_exists : GlobalTheory.CompanionTheory.MixZ.ExistsRead := by
  first | exact @GlobalTheory.CompanionTheory.MixZ.existsRead | exact GlobalTheory.CompanionTheory.MixZ.existsRead | (intros; apply GlobalTheory.CompanionTheory.MixZ.existsRead <;> assumption)
end

