import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0545
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0915
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0522
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0058
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0015
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ArakelovCycleHeights.QpSndStr
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0523
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.IdeleGroups.ClassGroup
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0520
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0542
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicSplitTorusIwasawaUnitaryGroup

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreVolumeCoverCountable
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.FibreDensity

theorem tail_le {V ι : Type} [Countable ι] [MeasurableSpace V] (ρ : Measure V) {Z A B W : Set V}
    {P : ι → Set V} {c : ι → ℝ≥0} {T : Finset ι} {e : ℝ≥0∞}
    (hZ : ρ Zᶜ = 0) (hcov : A ∩ Z ⊆ ⋃ i, P i) (hB : A ∩ (⋃ i ∈ T, P i) ⊆ B)
    (hP : ∀ i, ρ (P i ∩ W) ≤ (c i : ℝ≥0∞) * e) :
    ρ ((A \ B) ∩ W) ≤ (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)) * e := by
  have hsub : (A \ B) ∩ W ⊆ Zᶜ ∪ ⋃ i : {x // x ∉ T}, P i ∩ W := by
    rintro x ⟨⟨hxA, hxB⟩, hxW⟩
    by_cases hxZ : x ∈ Z
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.1 (hcov ⟨hxA, hxZ⟩)
      by_cases hiT : i ∈ T
      · exact absurd (hB ⟨hxA, Set.mem_iUnion₂.2 ⟨i, hiT, hi⟩⟩) hxB
      · exact Or.inr (Set.mem_iUnion.2 ⟨⟨i, hiT⟩, hi, hxW⟩)
    · exact Or.inl hxZ
  calc ρ ((A \ B) ∩ W) ≤ ρ (Zᶜ ∪ ⋃ i : {x // x ∉ T}, P i ∩ W) := measure_mono hsub
    _ ≤ ρ Zᶜ + ρ (⋃ i : {x // x ∉ T}, P i ∩ W) := measure_union_le _ _
    _ ≤ 0 + ∑' i : {x // x ∉ T}, ρ (P i ∩ W) := add_le_add hZ.le (measure_iUnion_le _)
    _ ≤ 0 + ∑' i : {x // x ∉ T}, (c i : ℝ≥0∞) * e :=
        add_le_add le_rfl (ENNReal.tsum_le_tsum fun i => hP i)
    _ = (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)) * e := by rw [zero_add, ENNReal.tsum_mul_right]

theorem near_compact_open {V K : Type} [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V]
    [T2Space V] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K]
    {μ : Measure V} {lam : Measure K} {Q : V → K} {Z : Set V} {m : K → Measure V}
    (hQ : Continuous Q) (h : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ Q id Z lam Set.univ m)
    [IsLocallyFiniteMeasure lam] {B : Set V} (hBc : IsCompact B) (hBo : IsOpen B) (hBZ : B ⊆ Z)
    (s₀ : K) {η : ℝ} (hη : 0 < η) :
    ∃ U ∈ 𝓝 s₀, ∀ S : Set K, MeasurableSet S → S ⊆ U → lam S ≠ ⊤ ∧ μ (B ∩ Q ⁻¹' S) ≠ ⊤ ∧
      ((m s₀ B).toReal - η) * (lam S).toReal ≤ (μ (B ∩ Q ⁻¹' S)).toReal ∧
      (μ (B ∩ Q ⁻¹' S)).toReal ≤ ((m s₀ B).toReal + η) * (lam S).toReal := by
  obtain ⟨h1, h2, h3⟩ := h
  have hBm : MeasurableSet B := hBo.measurableSet
  have hφc : Continuous (B.indicator (1 : V → ℝ)) := by
    refine continuous_indicator ?_ continuous_one.continuousOn
    intro a ha
    simp [frontier, hBc.isClosed.closure_eq, hBo.interior_eq] at ha
  have hφs : HasCompactSupport (B.indicator (1 : V → ℝ)) :=
    HasCompactSupport.intro hBc fun x hx => by simp [hx]
  have hφt : tsupport (B.indicator (1 : V → ℝ)) ⊆ Z :=
    (closure_minimal Set.support_indicator_subset hBc.isClosed).trans hBZ
  obtain ⟨hint, hcont⟩ := h3 _ hφc hφs hφt
  have hfin : ∀ b, m b B ≠ ⊤ := fun b => by
    have h4 := (integrable_indicator_iff hBm).1 (hint b (Set.mem_univ b))
    exact ((integrableOn_const_iff).1 h4).resolve_left (by rw [enorm_eq_zero]; exact (one_ne_zero : (1 : ℝ) ≠ 0)) |>.ne
  have hg : Continuous (fun b => (m b B).toReal) := by
    have he : (fun b => ∫ v, B.indicator (1 : V → ℝ) v ∂(m b)) = fun b => (m b B).toReal :=
      funext fun b => integral_indicator_one hBm
    rw [← he]
    exact continuousOn_univ.1 hcont
  have hform : ∀ S : Set K, MeasurableSet S → μ (B ∩ Q ⁻¹' S) = ∫⁻ b in S, m b B ∂lam := by
    intro S hS
    have hX : MeasurableSet (B ∩ Q ⁻¹' S) := hBm.inter (hQ.measurable hS)
    have e1 := h2 ((B ∩ Q ⁻¹' S).indicator 1) (measurable_one.indicator hX)
    simp_rw [lintegral_indicator_one hX] at e1
    rw [Measure.restrict_apply hX, Set.inter_eq_left.2 (Set.inter_subset_left.trans hBZ)] at e1
    rw [e1, ← lintegral_indicator hS]
    refine lintegral_congr fun b => ?_
    by_cases hb : b ∈ S
    · rw [Set.indicator_of_mem hb]
      refine le_antisymm (measure_mono Set.inter_subset_left) ?_
      calc m b B ≤ m b (B ∩ Q ⁻¹' S ∪ (Q ⁻¹' {id b} ∩ Z)ᶜ) := by
            refine measure_mono fun v hv => ?_
            by_cases hv' : v ∈ Q ⁻¹' {id b} ∩ Z
            · have hq : Q v = b := hv'.1
              exact Or.inl ⟨hv, show Q v ∈ S by rw [hq]; exact hb⟩
            · exact Or.inr hv'
        _ ≤ m b (B ∩ Q ⁻¹' S) + m b (Q ⁻¹' {id b} ∩ Z)ᶜ := measure_union_le _ _
        _ = m b (B ∩ Q ⁻¹' S) := by rw [h1 b, add_zero]
    · simp only [hb, not_false_eq_true, Set.indicator_of_notMem]
      refine measure_mono_null (t := (Q ⁻¹' {id b} ∩ Z)ᶜ) ?_ (h1 b)
      intro v hv hv'
      apply hb
      have hq : Q v = b := hv'.1
      rw [← hq]; exact hv.2
  obtain ⟨U', hU'n, hU'fin⟩ := lam.finiteAt_nhds s₀
  have hgn : (fun b => (m b B).toReal) ⁻¹' Set.Ioo ((m s₀ B).toReal - η) ((m s₀ B).toReal + η) ∈ 𝓝 s₀ :=
    hg.continuousAt.preimage_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith))
  refine ⟨U' ∩ (fun b => (m b B).toReal) ⁻¹' Set.Ioo ((m s₀ B).toReal - η) ((m s₀ B).toReal + η),
    Filter.inter_mem hU'n hgn, fun S hS hSU => ?_⟩
  have hlam : lam S ≠ ⊤ := (lt_of_le_of_lt (measure_mono (hSU.trans Set.inter_subset_left)) hU'fin).ne
  have hmb : ∀ b ∈ S, m b B = ENNReal.ofReal (m b B).toReal := fun b _ => (ENNReal.ofReal_toReal (hfin b)).symm
  have hup : μ (B ∩ Q ⁻¹' S) ≤ ENNReal.ofReal ((m s₀ B).toReal + η) * lam S := by
    rw [hform S hS, ← setLIntegral_const]
    refine setLIntegral_mono' hS fun b hb => ?_
    rw [hmb b hb]
    exact ENNReal.ofReal_le_ofReal (hSU hb).2.2.le
  have hμfin : μ (B ∩ Q ⁻¹' S) ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlam) hup
  have hg0 : 0 ≤ (m s₀ B).toReal := ENNReal.toReal_nonneg
  have hl0 : 0 ≤ (lam S).toReal := ENNReal.toReal_nonneg
  have hx0 : 0 ≤ (μ (B ∩ Q ⁻¹' S)).toReal := ENNReal.toReal_nonneg
  have hhi : (μ (B ∩ Q ⁻¹' S)).toReal ≤ ((m s₀ B).toReal + η) * (lam S).toReal := by
    have h5 := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hlam) hup
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at h5
  refine ⟨hlam, hμfin, ?_, hhi⟩
  by_cases hc : (m s₀ B).toReal - η ≤ 0
  · nlinarith
  · have hlow : ENNReal.ofReal ((m s₀ B).toReal - η) * lam S ≤ μ (B ∩ Q ⁻¹' S) := by
      rw [hform S hS, ← setLIntegral_const]
      refine setLIntegral_mono' hS fun b hb => ?_
      rw [hmb b hb]
      exact ENNReal.ofReal_le_ofReal (hSU hb).2.1.le
    have h6 := ENNReal.toReal_mono hμfin hlow
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith)] at h6

theorem density_of_summable_cover : ∀ (V K ι : Type) [Countable ι] [TopologicalSpace V] [MeasurableSpace V] [BorelSpace V] [T2Space V] [TopologicalSpace K] [MeasurableSpace K] [BorelSpace K] [T2Space K] (μ : Measure V) (lam : Measure K) (Q : V → K) (Z : Set V) (m : K → Measure V), Continuous Q → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ Q id Z lam Set.univ m → ∀ [IsLocallyFiniteMeasure lam], μ Zᶜ = 0 → ∀ A : Set V, IsCompact A → IsOpen A → ∀ (P : ι → Set V) (c : ι → ℝ≥0), (∀ i, IsCompact (P i) ∧ IsOpen (P i) ∧ P i ⊆ Z) → A ∩ Z ⊆ ⋃ i, P i → Summable c → (∀ i (S : Set K), MeasurableSet S → μ (P i ∩ Q ⁻¹' S) ≤ (c i : ℝ≥0∞) * lam S) → (∀ i s, m s (P i) ≤ (c i : ℝ≥0∞)) → ∀ s₀ : K, m s₀ A < ⊤ ∧ ∀ ε : ℝ, 0 < ε → ∃ U ∈ 𝓝 s₀, ∀ S : Set K, MeasurableSet S → S ⊆ U → |(μ (A ∩ Q ⁻¹' S)).toReal - (m s₀ A).toReal * (lam S).toReal| ≤ ε * (lam S).toReal := by
  intro V K ι _ _ _ _ _ _ _ _ _ μ lam Q Z m hQ h _ hZ A hAc hAo P c hP hcov hc hPS hPm s₀
  have hmZ : ∀ s, m s Zᶜ = 0 := fun s =>
    measure_mono_null (Set.compl_subset_compl.2 Set.inter_subset_right) (h.1 s)
  have hcfin : ∑' i, (c i : ℝ≥0∞) ≠ ⊤ := ENNReal.tsum_coe_ne_top_iff_summable.2 hc
  have hA1 : m s₀ A < ⊤ := by
    calc m s₀ A ≤ m s₀ (A ∩ Z ∪ Zᶜ) := by
          refine measure_mono fun x hx => ?_
          by_cases hz : x ∈ Z
          · exact Or.inl ⟨hx, hz⟩
          · exact Or.inr hz
      _ ≤ m s₀ (A ∩ Z) + m s₀ Zᶜ := measure_union_le _ _
      _ = m s₀ (A ∩ Z) := by rw [hmZ, add_zero]
      _ ≤ m s₀ (⋃ i, P i) := measure_mono hcov
      _ ≤ ∑' i, m s₀ (P i) := measure_iUnion_le _
      _ ≤ ∑' i, (c i : ℝ≥0∞) := ENNReal.tsum_le_tsum fun i => hPm i s₀
      _ < ⊤ := lt_top_iff_ne_top.2 hcfin
  refine ⟨hA1, fun ε hε => ?_⟩
  obtain ⟨T, hT⟩ := ((ENNReal.tendsto_tsum_compl_atTop_zero hcfin).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.2 (by positivity : (0 : ℝ) < ε / 3)))).exists
  have htne : (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)) ≠ ⊤ := ne_top_of_lt hT
  have htR : (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)).toReal < ε / 3 := ENNReal.toReal_lt_of_lt_ofReal hT
  have hBc : IsCompact (A ∩ ⋃ i ∈ T, P i) :=
    hAc.inter_right (isClosed_biUnion_finset fun i _ => (hP i).1.isClosed)
  have hBo : IsOpen (A ∩ ⋃ i ∈ T, P i) :=
    hAo.inter (isOpen_iUnion fun i => isOpen_iUnion fun _ => (hP i).2.1)
  have hBZ : A ∩ ⋃ i ∈ T, P i ⊆ Z := fun x hx => by
    obtain ⟨i, -, hi⟩ := Set.mem_iUnion₂.1 hx.2
    exact (hP i).2.2 hi
  obtain ⟨U, hUn, hU⟩ := near_compact_open hQ h hBc hBo hBZ s₀ (η := ε / 3) (by positivity)
  refine ⟨U, hUn, fun S hS hSU => ?_⟩
  obtain ⟨hlam, hμB, hlo, hhi⟩ := hU S hS hSU
  have htail := tail_le μ (W := Q ⁻¹' S) (e := lam S) (T := T) hZ hcov
    (B := A ∩ ⋃ i ∈ T, P i) Set.Subset.rfl (fun i => hPS i S hS)
  have hAW1 : μ ((A ∩ ⋃ i ∈ T, P i) ∩ Q ⁻¹' S) ≤ μ (A ∩ Q ⁻¹' S) :=
    measure_mono (Set.inter_subset_inter_left _ Set.inter_subset_left)
  have hAW2 : μ (A ∩ Q ⁻¹' S) ≤ μ ((A ∩ ⋃ i ∈ T, P i) ∩ Q ⁻¹' S) +
      (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)) * lam S := by
    calc μ (A ∩ Q ⁻¹' S) ≤ μ ((A ∩ ⋃ i ∈ T, P i) ∩ Q ⁻¹' S ∪ (A \ (A ∩ ⋃ i ∈ T, P i)) ∩ Q ⁻¹' S) := by
          refine measure_mono fun x hx => ?_
          by_cases hxB : x ∈ A ∩ ⋃ i ∈ T, P i
          · exact Or.inl ⟨hxB, hx.2⟩
          · exact Or.inr ⟨⟨hx.1, hxB⟩, hx.2⟩
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := add_le_add le_rfl htail
  have ht2 := tail_le (m s₀) (W := Set.univ) (e := 1) (T := T) (hmZ s₀) hcov
    (B := A ∩ ⋃ i ∈ T, P i) Set.Subset.rfl (fun i => by rw [Set.inter_univ, mul_one]; exact hPm i s₀)
  rw [Set.inter_univ, mul_one] at ht2
  have hm1 : m s₀ (A ∩ ⋃ i ∈ T, P i) ≤ m s₀ A := measure_mono Set.inter_subset_left
  have hm2 : m s₀ A ≤ m s₀ (A ∩ ⋃ i ∈ T, P i) + ∑' i : {x // x ∉ T}, (c i : ℝ≥0∞) := by
    calc m s₀ A ≤ m s₀ ((A ∩ ⋃ i ∈ T, P i) ∪ A \ (A ∩ ⋃ i ∈ T, P i)) := by
          refine measure_mono fun x hx => ?_
          by_cases hxB : x ∈ A ∩ ⋃ i ∈ T, P i
          · exact Or.inl hxB
          · exact Or.inr ⟨hx, hxB⟩
      _ ≤ _ := measure_union_le _ _
      _ ≤ _ := add_le_add le_rfl ht2
  have hmBfin : m s₀ (A ∩ ⋃ i ∈ T, P i) ≠ ⊤ := ne_top_of_le_ne_top hA1.ne hm1
  have htl : (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)) * lam S ≠ ⊤ := ENNReal.mul_ne_top htne hlam
  have hμA : μ (A ∩ Q ⁻¹' S) ≠ ⊤ := ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hμB, htl⟩) hAW2
  have hx1 := ENNReal.toReal_mono hμA hAW1
  have hx2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hμB, htl⟩) hAW2
  rw [ENNReal.toReal_add hμB htl, ENNReal.toReal_mul] at hx2
  have ha1 := ENNReal.toReal_mono hA1.ne hm1
  have ha2 := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hmBfin, htne⟩) hm2
  rw [ENNReal.toReal_add hmBfin htne] at ha2
  have hl : 0 ≤ (lam S).toReal := ENNReal.toReal_nonneg
  have ht0 : 0 ≤ (∑' i : {x // x ∉ T}, (c i : ℝ≥0∞)).toReal := ENNReal.toReal_nonneg
  have p1 := mul_le_mul_of_nonneg_right ha1 hl
  have p2 := mul_le_mul_of_nonneg_right ha2 hl
  have p3 := mul_le_mul_of_nonneg_right htR.le hl
  have p4 := mul_nonneg hε.le hl
  rw [abs_le]
  constructor <;> nlinarith

end GlobalTheory.CompanionTheory.WeilSiegel.FibreDensity
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteAdelicIntegralInvariantOpenSubgroup
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Hua
open NumberField

open scoped Topology

noncomputable section

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Period

def HasCO (G : Type) [AddGroup G] [TopologicalSpace G] : Prop :=
  ∀ W ∈ 𝓝 (0 : G), ∃ P : AddSubgroup G, IsOpen (P : Set G) ∧ IsCompact (P : Set G) ∧ (P : Set G) ⊆ W

theorem HasCO.pi {ι : Type} [Finite ι] {G : ι → Type} [∀ i, AddGroup (G i)]
    [∀ i, TopologicalSpace (G i)] (h : ∀ i, HasCO (G i)) : HasCO (∀ i, G i) := by
  intro W hW
  rw [nhds_pi] at hW
  obtain ⟨I, t, ht, hsub⟩ := Filter.mem_pi'.1 hW
  choose P hPo hPc hPW using fun i => h i (t i) (ht i)
  have hcoe : ((AddSubgroup.pi Set.univ P : AddSubgroup (∀ i, G i)) : Set (∀ i, G i)) =
      Set.univ.pi fun i => (P i : Set (G i)) := by
    ext x
    simp [AddSubgroup.mem_pi]
  refine ⟨AddSubgroup.pi Set.univ P, ?_, ?_, ?_⟩
  · rw [hcoe]
    exact isOpen_set_pi Set.finite_univ fun i _ => hPo i
  · rw [hcoe]
    exact isCompact_univ_pi hPc
  · intro x hx
    rw [hcoe] at hx
    exact hsub fun i _ => hPW i (hx i (Set.mem_univ i))

theorem HasCO.comap {G H : Type} [AddGroup G] [TopologicalSpace G] [AddGroup H] [TopologicalSpace H]
    (h : HasCO H) (f : G →+ H) (hf : IsHomeomorph f) : HasCO G := by
  intro W hW
  let e : G ≃ₜ H := hf.homeomorph f
  have he : ∀ x, e x = f x := fun _ => rfl
  have h0 : e.symm 0 = 0 := by
    apply e.injective
    rw [e.apply_symm_apply, he, map_zero]
  have hW' : e.symm ⁻¹' W ∈ 𝓝 (0 : H) := by
    apply e.symm.continuous.continuousAt.preimage_mem_nhds
    rwa [h0]
  obtain ⟨P, hPo, hPc, hPW⟩ := h _ hW'
  refine ⟨P.comap f, hPo.preimage hf.continuous, ?_, ?_⟩
  · have : ((P.comap f : AddSubgroup G) : Set G) = e.symm '' (P : Set H) := by
      ext x
      constructor
      · intro hx
        exact ⟨e x, hx, by simp⟩
      · rintro ⟨y, hy, rfl⟩
        change f (e.symm y) ∈ P
        rw [← he]
        simpa using hy
    rw [this]
    exact hPc.image e.symm.continuous
  · intro x hx
    have h1 : e.symm (e x) ∈ W := hPW (by rw [he]; exact hx)
    rwa [e.symm_apply_apply] at h1

theorem HasCO.sub {G : Type} [AddGroup G] [TopologicalSpace G] (h : HasCO G) (S : AddSubgroup G)
    (hS : IsClosed (S : Set G)) : HasCO S := by
  intro W hW
  obtain ⟨W', hW', hsub⟩ := mem_nhds_subtype (S : Set G) 0 W |>.1 hW
  obtain ⟨P, hPo, hPc, hPW⟩ := h W' hW'
  refine ⟨P.comap S.subtype, hPo.preimage continuous_subtype_val, ?_, ?_⟩
  · have hemb : Topology.IsClosedEmbedding (Subtype.val : S → G) := hS.isClosedEmbedding_subtypeVal
    exact hemb.isCompact_preimage hPc
  · intro x hx
    exact hsub (hPW hx)

theorem small_pow {z : ℂ} (h : ∀ k : ℕ, ‖z ^ k - 1‖ < 1 / 2) : z = 1 :=
  by apply _root_.UpperTheory.Reformulated.B.EqOneOfPowNear.eq_one_of_pow_near <;> assumption

end GlobalTheory.CompanionTheory.SiegelND.Integ.Period

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Period

open GlobalTheory.CompanionTheory.SW.Core in
theorem hasCO_Af (F : Type) [Field F] [NumberField F] : HasCO (Af F) := by
  obtain ⟨h1, h2, h3, hOc, hOo, -, -, hB, -, hNo⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  have hadd : ∀ x ∈ Oh F, ∀ y ∈ Oh F, x + y ∈ Oh F := fun x hx y hy v =>
    add_mem (hx v) (hy v)
  have hneg : ∀ x ∈ Oh F, -x ∈ Oh F := fun x hx v => neg_mem (hx v)
  have hz : (0 : Af F) ∈ Oh F := fun v => zero_mem _
  intro W hW
  obtain ⟨N, hN, hNW⟩ := hB W hW
  let P : AddSubgroup (Af F) :=
    { carrier := {x | ∃ y ∈ Oh F, x = (N : Af F) * y}
      zero_mem' := ⟨0, hz, by simp⟩
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x + y, hadd x hx y hy, by ring⟩
      neg_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨-x, hneg x hx, by ring⟩ }
  refine ⟨P, hNo N hN, ?_, ?_⟩
  · have : (P : Set (Af F)) = (fun y => (N : Af F) * y) '' Oh F := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
      · rintro ⟨y, hy, rfl⟩
        exact ⟨y, hy, rfl⟩
    rw [this]
    exact hOc.image (continuous_const.mul continuous_id)
  · rintro _ ⟨y, hy, rfl⟩
    exact hNW y hy

theorem psiFin_add (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (x y : Af F) :
    psiFin F ψ (x + y) = psiFin F ψ x * psiFin F ψ y := by
  have : pairA F 0 (x + y) = pairA F 0 x + pairA F 0 y :=
    Prod.ext (show (0 : Ainf F) = 0 + 0 by simp) rfl
  simp only [psiFin]
  rw [this, AddChar.map_add_eq_mul]

theorem psiFin_trivial (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ)
    (hψ : IsCharAF F ψ) : ∃ V : AddSubgroup (Af F), IsOpen (V : Set (Af F)) ∧
      ∀ y ∈ V, psiFin F ψ y = 1 := by
  have hc : Continuous (psiFin F ψ) := by
    have : Continuous fun y : Af F => pairA F 0 y := continuous_const.prodMk continuous_id
    exact hψ.1.comp this
  have h0 : psiFin F ψ 0 = 1 := by
    have : pairA F 0 (0 : Af F) = 0 := rfl
    simp [psiFin, this]
  have hB : {y | ‖psiFin F ψ y - 1‖ < 1 / 2} ∈ 𝓝 (0 : Af F) := by
    have : IsOpen {y | ‖psiFin F ψ y - 1‖ < 1 / 2} :=
      isOpen_lt ((hc.sub continuous_const).norm) continuous_const
    exact this.mem_nhds (by simp [h0])
  obtain ⟨P, hPo, -, hPB⟩ := hasCO_Af F _ hB
  refine ⟨P, hPo, fun y hy => small_pow fun k => ?_⟩
  have hk : psiFin F ψ (k • y) = psiFin F ψ y ^ k := by
    induction k with
    | zero =>
      simpa using h0
    | succ k ih =>
      rw [succ_nsmul, psiFin_add, ih, pow_succ]
  rw [← hk]
  exact hPB (P.nsmul_mem hy k)

theorem hasCO_herm (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (n : ℕ) : HasCO (HermR (Af F) σ n) := by
  obtain ⟨a1, a2, a3, -, -, -, -, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : LocallyCompactSpace (Af F) := a1
  haveI : SecondCountableTopology (Af F) := a2
  haveI : T2Space (Af F) := a3
  obtain ⟨-, -, -, -, -, -, hh, -, hcl, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Af F)
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  let b := Module.finBasis F E
  let c : (Af F ⊗[F] E) →+ (Fin (Module.finrank F E) → Af F) :=
    { toFun := fun y k => (Algebra.TensorProduct.basis (Af F) b).repr y k
      map_zero' := by
        funext k
        simp
      map_add' := by
        intro x y
        funext k
        simp }
  have hT : HasCO (Af F ⊗[F] E) :=
    HasCO.comap (HasCO.pi fun _ => hasCO_Af F) c (hh _ b)
  have hM : HasCO (Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) :=
    HasCO.pi (G := fun _ : Fin n => Fin n → Af F ⊗[F] E) fun _ => HasCO.pi fun _ => hT
  exact hM.sub _ (hcl n)

end GlobalTheory.CompanionTheory.SiegelND.Integ.Period

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Period

theorem tube_zero {H Y A : Type} [AddGroup H] [TopologicalSpace H] [TopologicalSpace Y]
    [TopologicalSpace A] (ph : H → Y → A) (hph : Continuous fun p : H × Y => ph p.1 p.2)
    {V : Set A} (hV : IsOpen V) (h0 : ∀ X, ph 0 X ∈ V) {K : Set Y} (hK : IsCompact K) :
    ∃ W ∈ 𝓝 (0 : H), ∀ u ∈ W, ∀ X ∈ K, ph u X ∈ V := by
  have hsub : ({0} : Set H) ×ˢ K ⊆ (fun p : H × Y => ph p.1 p.2) ⁻¹' V := by
    rintro ⟨u, X⟩ ⟨hu, -⟩
    have hu0 : u = 0 := hu
    subst hu0
    exact h0 X
  obtain ⟨W, W', hWo, -, h0W, hKW, hWW⟩ :=
    generalized_tube_lemma isCompact_singleton hK (hV.preimage hph) hsub
  exact ⟨W, hWo.mem_nhds (h0W rfl), fun u hu X hX => hWW (Set.mk_mem_prod hu (hKW hX))⟩

set_option maxHeartbeats 1000000 in

theorem starLoc_periodic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (n : ℕ) (ψ : AddChar (AF F) ℂ), IsCharAF F ψ →
    ∀ μ : Measure (Fin n → Fin M → Af F ⊗[F] E), μ.IsAddHaarMeasure →
    ∀ Q : (Fin n → Fin M → Af F ⊗[F] E) → ℂ, IsSB Q →
    ∃ U : AddSubgroup (HermR (Af F) σ n), IsOpen (U : Set (HermR (Af F) σ n)) ∧
      IsCompact (U : Set (HermR (Af F) σ n)) ∧
      ∀ b, ∀ u ∈ U, starLoc (Af F) σ J (psiFin F ψ) μ Q (b + u) = starLoc (Af F) σ J (psiFin F ψ) μ Q b := by
  intro F E _ _ _ _ _ σ hσ M J n ψ hψ μ _ Q hQ
  obtain ⟨a1, a2, a3, -, -, -, -, -, -, -⟩ := GlobalTheory.T.mem_Oh_iff_and_nat_mul_properties F
  haveI : LocallyCompactSpace (Af F) := a1
  haveI : SecondCountableTopology (Af F) := a2
  haveI : T2Space (Af F) := a3
  obtain ⟨t1, -, -, -, -, htr, -, -, -, hG⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (Af F)
  haveI : IsTopologicalRing (Af F ⊗[F] E) := t1
  obtain ⟨V, hVo, hV⟩ := psiFin_trivial F ψ hψ
  let ph : HermR (Af F) σ n → (Fin n → Fin M → Af F ⊗[F] E) → Af F := fun u X =>
    algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E)
      (Matrix.trace ((u : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) * gramR (Af F) σ J X))
  have hph : Continuous fun p : HermR (Af F) σ n × (Fin n → Fin M → Af F ⊗[F] E) => ph p.1 p.2 := by
    refine continuous_const.mul (htr.comp (Continuous.matrix_trace (Continuous.matrix_mul ?_ ?_)))
    · exact continuous_subtype_val.comp continuous_fst
    · exact (hG n M J).comp continuous_snd
  have hK : IsCompact (tsupport Q) := hQ.2
  have h0 : ∀ X, ph 0 X ∈ (V : Set (Af F)) := fun X => by
    simp [ph, V.zero_mem]
  obtain ⟨W, hW0, hWW⟩ := tube_zero ph hph hVo h0 hK
  obtain ⟨U, hUo, hUc, hUW⟩ := hasCO_herm F E σ hσ n W hW0
  refine ⟨U, hUo, hUc, fun b u hu => ?_⟩
  unfold starLoc
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  by_cases hX : X ∈ tsupport Q
  · have hsplit : ph (b + u) X = ph b X + ph u X := by
      simp only [ph, AddSubgroup.coe_add, add_mul, Matrix.trace_add, map_add, mul_add]
    have hm : ph u X ∈ V := hWW u (hUW (SetLike.mem_coe.2 hu)) X hX
    have h1 : psiFin F ψ (ph u X) = 1 := hV (ph u X) hm
    change Q X * psiFin F ψ (ph (b + u) X) = Q X * psiFin F ψ (ph b X)
    rw [hsplit, psiFin_add, h1, mul_one]
  · have hq : Q X = 0 := image_eq_zero_of_notMem_tsupport hX
    simp [hq]

end GlobalTheory.CompanionTheory.SiegelND.Integ.Period
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionFieldOfPointCoordsTopStatement
section
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.ArithmeticHeightTower GlobalTheory.CompanionTheory.MPDict ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
open GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.function_field_of_point_coords_top : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (x : MP ℤ m n) [CharZero ((MP ℤ m n).residueField x)], blockFnField (ptCoord x) = ⊤ := by
  first | exact @GlobalTheory.CompanionTheory.MPDict.GenTop.blockFnField_ptCoord_eq_top | exact GlobalTheory.CompanionTheory.MPDict.GenTop.blockFnField_ptCoord_eq_top | (intros; apply GlobalTheory.CompanionTheory.MPDict.GenTop.blockFnField_ptCoord_eq_top <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FunctionalEquationOfUnramified
section
open NumberField GroundTheory.Global GroundTheory.Global.IdeleGroup
open scoped nonZeroDivisors

namespace GlobalTheory.CompanionTheory.PartialZeta

theorem fe_of_parts (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (χ : HeckeCharacter F)
    (hD : χ.discrNormConductor = GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F)
    (hG : ∀ s : ℂ, χ.gammaFactor s = Complex.Gammaℝ s ^ Module.finrank ℚ F)
    (hG' : ∀ s : ℂ, (χ⁻¹).gammaFactor s = Complex.Gammaℝ s ^ Module.finrank ℚ F)
    (hR : χ.rootNumber = χ.coeff (differentIdeal ℤ (𝓞 F)))
    (s : ℂ) (h1 : ∀ n : ℕ, s ≠ -2 * n) (h2 : ∀ n : ℕ, 1 - s ≠ -2 * n) :
    (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * χ.continuedLFunction s =
      χ.coeff (differentIdeal ℤ (𝓞 F)) * ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) *
        Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * (χ⁻¹).continuedLFunction (1 - s)) := by
  have nz : ∀ t : ℂ, (∀ n : ℕ, t ≠ -2 * n) → Complex.Gammaℝ t ≠ 0 := by
    intro t ht h0
    obtain ⟨n, hn⟩ := Complex.Gammaℝ_eq_zero_iff.1 h0
    exact ht n (by rw [hn]; ring)
  have key := χ.continuedLFunction_functional_equation (s := s)
    (by rw [hG]; exact pow_ne_zero _ (nz s h1))
    (by rw [hG']; exact pow_ne_zero _ (nz _ h2))
  rw [hG, hG', hD, hR] at key
  exact key

theorem functional_equation_of_unramified :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (χ : HeckeCharacter F),
      standardOpenSubgroup F ≤ χ.toIdele.ker → ∀ s : ℂ, (∀ n : ℕ, s ≠ -2 * n) →
      (∀ n : ℕ, 1 - s ≠ -2 * n) →
      (GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ (s / 2) * Complex.Gammaℝ s ^ Module.finrank ℚ F * χ.continuedLFunction s =
        χ.coeff (differentIdeal ℤ (𝓞 F)) * ((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.dF F : ℂ) ^ ((1 - s) / 2) *
          Complex.Gammaℝ (1 - s) ^ Module.finrank ℚ F * (χ⁻¹).continuedLFunction (1 - s)) := by
  intro F _ _ _ χ hχ s h1 h2
  exact fe_of_parts F χ (discrNormConductor_eq_dF_of_unramified F χ hχ) (gammaFactor_eq_of_unramified F χ hχ)
    (gammaFactor_eq_of_unramified F χ⁻¹ (standardOpenSubgroup_le_ker_inv F χ hχ)) (GlobalTheory.T.root_number_eq_different_coeff F χ hχ) s h1 h2

end GlobalTheory.CompanionTheory.PartialZeta
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsotropicHyperbolicComplementStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_hyperbolic_complement : ∀ {n D : ℕ} (ε : Fin n → Bool) (C : Matrix (Fin n) (Fin D) ℂ), Cᴴ * C = 1 → Cᴴ * Formalism.REAL.Jm ε * C = 0 → ∃ (m : ℕ) (R : Matrix (Fin n) (Fin m) ℂ) (ε' : Fin m → Bool), Rᴴ * R = 1 ∧ Formalism.REAL.Jm ε * R = R * Formalism.REAL.Jm ε' ∧ Cᴴ * R = 0 ∧ C * Cᴴ + Formalism.REAL.Jm ε * C * Cᴴ * Formalism.REAL.Jm ε + R * Rᴴ = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.CompFrame.exists_comp_frame | exact GlobalTheory.CompanionTheory.Dblock.CompFrame.exists_comp_frame | (intros; apply GlobalTheory.CompanionTheory.Dblock.CompFrame.exists_comp_frame <;> assumption)
end

