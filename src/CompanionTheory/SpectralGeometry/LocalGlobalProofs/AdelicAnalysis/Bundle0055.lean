import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0054
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleCompactSets
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0002
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0028
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0026
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0044
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0074
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0014
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0032
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0029

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarInvariantUnitaryActionStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_haar_invariant_unitary_action : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (μ : Measure (Fin 1 → Fin M → AF F ⊗[F] E)), μ.IsAddHaarMeasure → ∀ h : HA (AF F) σ J, μ.map (actW (AF F) σ J h) = μ := by
  first | exact @GlobalTheory.CompanionTheory.SW.HaarInv.actW_map_eq | exact GlobalTheory.CompanionTheory.SW.HaarInv.actW_map_eq | (intros; apply GlobalTheory.CompanionTheory.SW.HaarInv.actW_map_eq <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicHaarScalingByRealIdeleStatement
section
open NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_haar_scaling_by_real_idele : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* InfiniteAdeleRing F, Continuous θ → ∀ [MeasurableSpace (AdeleRing (𝓞 F) F)] [BorelSpace (AdeleRing (𝓞 F) F)] (ι : Type) [Fintype ι] (μ : Measure (ι → AdeleRing (𝓞 F) F)) [μ.IsAddHaarMeasure] (t : ℝ), 0 < t → μ.map (fun x i => (show AdeleRing (𝓞 F) F from (θ t, 1)) * x i) = ENNReal.ofReal ((t ^ (Module.finrank ℚ F * Fintype.card ι))⁻¹) • μ := by
  first | exact @GlobalTheory.CompanionTheory.AdelicFlow.map_scalar | exact GlobalTheory.CompanionTheory.AdelicFlow.map_scalar | (intros; apply GlobalTheory.CompanionTheory.AdelicFlow.map_scalar <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleCompactSetsStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelic_tuple_compact_sets : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ (N : ℕ) (r : ℝ), 0 < N → IsCompact {X : (Fin n → Fin M → AF F ⊗[F] E) | (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧ sizeTup b (projInf X) ≤ r}) ∧ ∀ K : Set (Fin n → Fin M → AF F ⊗[F] E), IsCompact K → ∃ (N : ℕ) (r : ℝ), 0 < N ∧ 0 < r ∧ ∀ X ∈ K, (∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin X) a i) ∈ latV b v) ∧ sizeTup b (projInf X) ≤ r := by
  first | exact @GlobalTheory.CompanionTheory.SW.Cpt.compact_tuples | exact GlobalTheory.CompanionTheory.SW.Cpt.compact_tuples | (intros; apply GlobalTheory.CompanionTheory.SW.Cpt.compact_tuples <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.EulerProductMeasureZero
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.EulerZero

theorem exists_tail_pos {ι : Type} {a : ι → ℝ} (h : Summable (fun v => |a v - 1|)) (S₀ : Finset ι) :
    ∃ S : Finset ι, S₀ ⊆ S ∧ 0 < ∏' v : {v // v ∉ S}, a v.1 := by
  classical
  have hev : ∀ᶠ v in Filter.cofinite, |a v - 1| < 1 :=
    h.tendsto_cofinite_zero.eventually (gt_mem_nhds one_pos)
  have hfin : {v | ¬ |a v - 1| < 1}.Finite := Filter.eventually_cofinite.1 hev
  refine ⟨S₀ ∪ hfin.toFinset, Finset.subset_union_left, ?_⟩
  have hs : Summable (fun v : {v // v ∉ S₀ ∪ hfin.toFinset} => |a v.1 - 1|) :=
    h.comp_injective Subtype.val_injective
  refine (AbsTprod.abs_tprod _ (fun v : {v // v ∉ S₀ ∪ hfin.toFinset} => a v.1) hs).2.2.1 ?_
  rintro ⟨v, hv⟩
  have hv' : |a v - 1| < 1 := by
    by_contra hc
    exact hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hc))
  have := (abs_lt.1 hv').1
  show 0 < a v
  linarith

theorem countable_places (F : Type) [Field F] [NumberField F] :
    Countable (HeightOneSpectrum (𝓞 F)) := by
  haveI : Countable (𝓞 F) := by
    haveI : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    exact RingOfIntegers.coe_injective.countable
  haveI : Countable (Ideal (𝓞 F)) := by
    refine Function.Surjective.countable
      (f := fun s : Finset (𝓞 F) => Ideal.span (s : Set (𝓞 F))) ?_
    intro I
    exact (IsNoetherian.noetherian I : I.FG)
  exact Function.Injective.countable (f := fun la : HeightOneSpectrum (𝓞 F) => la.asIdeal)
    fun a b h => HeightOneSpectrum.ext h

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem exists_measure_intOff {d M n : ℕ} {b : Module.Basis (Fin d) F E}
    {I : Measure (Fin n → Fin M → AF F ⊗[F] E)} {c : ℝ≥0}
    {minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)}
    {m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)}
    (h : IsEulerProd b I c minf m)
    (hmeas : ∀ S, MeasurableSet (intOff (n := n) (M := M) b S)) :
    ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ S, S₀ ⊆ S →
      I (intOff b S) = (c : ℝ≥0∞) * (minf Set.univ * ∏ v ∈ S, m v Set.univ) *
        ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) := by
  obtain ⟨-, -, S₀, hS₀⟩ := h
  refine ⟨S₀, fun S hS => ?_⟩
  have key := hS₀ S hS (fun _ => 1) (fun _ _ => 1) measurable_const (fun _ => measurable_const)
  have hp : pureL b S (fun _ => 1) (fun _ _ => 1) = (intOff (n := n) (M := M) b S).indicator 1 := by
    funext X
    simp [pureL, Set.indicator]
  rw [hp, lintegral_indicator_one (hmeas S)] at key
  simpa using key

end GlobalTheory.CompanionTheory.SW.EulerZero

open GlobalTheory.CompanionTheory.SW.EulerZero in

theorem GlobalTheory.CompanionTheory.SW.EulerZero.euler_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ) (I : Measure (Fin n → Fin M → AF F ⊗[F] E)) (c : ℝ≥0) (minf : Measure (Fin n → Fin M → Ainf F ⊗[F] E)) (m : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fin n → Fin M → Fv F v ⊗[F] E)), (IsEulerProd b I c minf m → I = 0 → c = 0 ∨ minf = 0 ∨ ∃ v, m v = 0) ∧ (IsEulerProd b I c minf m → (minf = 0 ∨ ∃ v, m v = 0) → I = 0) ∧ ((∀ v, m v (latV b v) < ⊤) → Summable (fun v => |(m v (latV b v)).toReal - 1|) → (minf = 0 ∨ ∃ v, m v = 0) → IsEulerProd b 0 c minf m) := by
  intro F E _ _ _ _ _ σ hσ d b n M I c minf m
  obtain ⟨-, -, -, -, hopen, hcof, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hσ d b n M
  obtain ⟨⟨hlc, hsc, ht2⟩, -⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  obtain ⟨-, -, -, -, -, -, -, hborel, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hσ (AF F)
  haveI := hborel n M
  have hmeas : ∀ S, MeasurableSet (intOff (n := n) (M := M) b S) := fun S => (hopen S).measurableSet
  refine ⟨fun h hI => ?_, fun h hz => ?_, fun hfin hsum hz => ?_⟩
  · by_contra hcon
    push_neg at hcon
    obtain ⟨hc, hminf, hm⟩ := hcon
    obtain ⟨S₀, hS₀⟩ := exists_measure_intOff h hmeas
    obtain ⟨S, hS, hpos⟩ := exists_tail_pos h.2.1 S₀
    have key := hS₀ S hS
    rw [hI] at key
    have h1 : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc
    have h2 : minf Set.univ ≠ 0 := by simpa using hminf
    have h3 : ∏ v ∈ S, m v Set.univ ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun v _ => by simpa using hm v
    have h4 : ENNReal.ofReal (∏' v : {v // v ∉ S}, (m v.1 (latV b v.1)).toReal) ≠ 0 := by
      simpa using hpos
    exact (mul_ne_zero (mul_ne_zero h1 (mul_ne_zero h2 h3)) h4) (by simpa using key.symm)
  · obtain ⟨S₀, hS₀⟩ := exists_measure_intOff h hmeas
    classical
    obtain ⟨S₁, hS₁, hzero⟩ : ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), S₀ ⊆ S₁ ∧
        ∀ S, S₁ ⊆ S → minf Set.univ * ∏ v ∈ S, m v Set.univ = 0 := by
      rcases hz with hz | ⟨v, hv⟩
      · exact ⟨S₀, subset_rfl, fun S _ => by simp [hz]⟩
      · refine ⟨insert v S₀, Finset.subset_insert _ _, fun S hS => ?_⟩
        rw [Finset.prod_eq_zero (hS (Finset.mem_insert_self v S₀)) (by simp [hv]), mul_zero]
    haveI := countable_places F
    have hcover : (Set.univ : Set (Fin n → Fin M → AF F ⊗[F] E)) ⊆
        ⋃ T : Finset (HeightOneSpectrum (𝓞 F)), intOff b (S₁ ∪ T) := by
      intro X _
      have hT := Filter.eventually_cofinite.1 (hcof (projFin X))
      refine Set.mem_iUnion.2 ⟨hT.toFinset, fun v hv => ?_⟩
      by_contra hc
      exact hv (Finset.mem_union_right _ (hT.mem_toFinset.2 hc))
    have hnull : I Set.univ = 0 := by
      refine measure_mono_null hcover (measure_iUnion_null fun T => ?_)
      rw [hS₀ _ (hS₁.trans Finset.subset_union_left), hzero _ Finset.subset_union_left]
      simp
    exact Measure.measure_univ_eq_zero.1 hnull
  · refine ⟨hfin, hsum, ?_⟩
    classical
    obtain ⟨S₀, hS₀⟩ : ∃ S₀ : Finset (HeightOneSpectrum (𝓞 F)), minf = 0 ∨ ∃ v ∈ S₀, m v = 0 := by
      rcases hz with hz | ⟨v, hv⟩
      · exact ⟨∅, Or.inl hz⟩
      · exact ⟨{v}, Or.inr ⟨v, by simp, hv⟩⟩
    refine ⟨S₀, fun S hS φinf φ _ _ => ?_⟩
    rcases hS₀ with hz | ⟨v, hv, hmv⟩
    · simp [hz]
    · rw [Finset.prod_eq_zero (hS hv) (by simp [hmv])]
      simp
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleHaarPiRestrictedProduct
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.AfBox

theorem eq_of_invariant_of_open {G : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (μ ν : Measure G) [ν.IsAddHaarMeasure] [μ.IsAddLeftInvariant] {C : Set G} (hC : IsOpen C)
    (h0 : (0 : G) ∈ C) (hμ : μ C = 1) (hν : ν C = 1) : μ = ν := by
  haveI : IsFiniteMeasureOnCompacts μ := by
    refine ⟨fun K hK => ?_⟩
    have hU : ∀ k : G, IsOpen ((fun x => -k + x) ⁻¹' C) := fun k =>
      hC.preimage (continuous_const.add continuous_id)
    obtain ⟨t, -, ht⟩ := hK.elim_nhds_subcover (fun k => (fun x => -k + x) ⁻¹' C)
      (fun k _ => (hU k).mem_nhds (by simpa using h0))
    have hm : ∀ k : G, μ ((fun x => -k + x) ⁻¹' C) = 1 := fun k => by
      rw [measure_preimage_add, hμ]
    calc μ K ≤ μ (⋃ k ∈ t, (fun x => -k + x) ⁻¹' C) := measure_mono ht
      _ ≤ ∑ k ∈ t, μ ((fun x => -k + x) ⁻¹' C) := measure_biUnion_finset_le _ _
      _ = t.card := by simp [hm]
      _ < ⊤ := by simp
  have h := Measure.isAddLeftInvariant_eq_smul μ ν
  have hc : Measure.addHaarScalarFactor μ ν = 1 := by
    have h2 : μ C = (Measure.addHaarScalarFactor μ ν • ν) C := by rw [← h]
    rw [Measure.smul_apply, hμ, hν] at h2
    simpa [ENNReal.smul_def, eq_comm] using h2
  rw [hc, one_smul] at h
  exact h

theorem map_restrict_invariant {G T : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    [AddCommGroup T] [MeasurableSpace T] [MeasurableAdd T]
    (m : Measure G) [m.IsAddLeftInvariant] (H : AddSubgroup G) (hH : MeasurableSet (H : Set G))
    (ρ : G →+ T) (hρ : Measurable ρ) (hs : ∀ t, ∃ h ∈ H, ρ h = t) :
    ((m.restrict H).map ρ).IsAddLeftInvariant := by
  constructor
  intro g
  obtain ⟨h, hh, rfl⟩ := hs g
  have e : (m.restrict H).map (fun x => h + x) = m.restrict H := by
    have hp : (fun x => h + x) ⁻¹' (H : Set G) = H := by
      ext x
      simp [H.add_mem_cancel_left hh]
    have := Measure.restrict_map (μ := m) (measurable_const_add h) hH
    rw [map_add_left_eq_self, hp] at this
    exact this.symm
  rw [Measure.map_map (measurable_const_add _) hρ]
  have hc : (fun x => ρ h + x) ∘ ρ = ρ ∘ (fun x => h + x) := by
    ext x
    simp
  rw [hc, ← Measure.map_map hρ (measurable_const_add _), e]

theorem measure_inter_preimage {G T : Type} [AddCommGroup G] [MeasurableSpace G] [MeasurableAdd G]
    [AddCommGroup T] [TopologicalSpace T] [IsTopologicalAddGroup T] [LocallyCompactSpace T]
    [SecondCountableTopology T] [MeasurableSpace T] [BorelSpace T]
    (m : Measure G) [m.IsAddLeftInvariant] (H : AddSubgroup G) (hH : MeasurableSet (H : Set G))
    (ρ : G →+ T) (hρ : Measurable ρ) (hs : ∀ t, ∃ h ∈ H, ρ h = t)
    (ν : Measure T) [ν.IsAddHaarMeasure] {C : Set T} (hC : IsOpen C) (h0 : (0 : T) ∈ C)
    (hm : m ((H : Set G) ∩ ρ ⁻¹' C) = 1) (hν : ν C = 1) {B : Set T} (hB : MeasurableSet B) :
    m ((H : Set G) ∩ ρ ⁻¹' B) = ν B := by
  haveI := map_restrict_invariant m H hH ρ hρ hs
  have hmap : ∀ D : Set T, MeasurableSet D → ((m.restrict H).map ρ) D = m ((H : Set G) ∩ ρ ⁻¹' D) := by
    intro D hD
    rw [Measure.map_apply hρ hD, Measure.restrict_apply (hρ hD), Set.inter_comm]
  have he := eq_of_invariant_of_open ((m.restrict H).map ρ) ν hC h0
    (by rw [hmap C hC.measurableSet, hm]) hν
  rw [← he, hmap B hB]

variable {F : Type} [Field F] [NumberField F]

def offS (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) : AddSubgroup (ι → Af F) where
  carrier := {x | ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F}
  add_mem' := fun {a b} ha hb v hv i => by
    simpa using add_mem (ha v hv i) (hb v hv i)
  zero_mem' := fun v _ i => by simp
  neg_mem' := fun {a} ha v hv i => by
    simpa using neg_mem (ha v hv i)

def compS (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    (ι → Af F) →+ ∀ v : S, ι → Fv F v.1 where
  toFun x := fun v i => evalV F v.1 (x i)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem continuous_compS (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (compS (F := F) ι S) :=
  continuous_pi fun v => continuous_pi fun i =>
    (RestrictedProduct.continuous_eval v.1).comp (continuous_apply i)

open Classical in

def liftS {S : Finset (HeightOneSpectrum (𝓞 F))} (t : ∀ v : S, Fv F v.1) : Af F :=
  ⟨fun w => if hw : w ∈ S then t ⟨w, hw⟩ else (0 : Fv F w), by
    filter_upwards [S.finite_toSet.compl_mem_cofinite] with w hw
    have : w ∉ S := by simpa using hw
    simp [this]⟩

open Classical in
theorem evalV_liftS_of_mem {S : Finset (HeightOneSpectrum (𝓞 F))} (t : ∀ v : S, Fv F v.1) (v : S) :
    evalV F v.1 (liftS t) = t v := by
  have : evalV F v.1 (liftS t) = dite (v.1 ∈ S) (fun hw => t ⟨v.1, hw⟩) (fun _ => (0 : Fv F v.1)) := rfl
  rw [this, dif_pos v.2]

open Classical in
theorem evalV_liftS_of_notMem {S : Finset (HeightOneSpectrum (𝓞 F))} (t : ∀ v : S, Fv F v.1)
    {v : HeightOneSpectrum (𝓞 F)} (hv : v ∉ S) : evalV F v (liftS t) = 0 := by
  have : evalV F v (liftS t) = dite (v ∈ S) (fun hw => t ⟨v, hw⟩) (fun _ => (0 : Fv F v)) := rfl
  rw [this, dif_neg hv]

theorem exists_offS_compS (ι : Type) (S : Finset (HeightOneSpectrum (𝓞 F)))
    (t : ∀ v : S, ι → Fv F v.1) : ∃ h ∈ offS (F := F) ι S, compS ι S h = t := by
  refine ⟨fun i => liftS fun v => t v i, fun v hv i => ?_, ?_⟩
  · rw [evalV_liftS_of_notMem _ hv]
    exact zero_mem (v.adicCompletionIntegers F)
  · funext v i
    exact evalV_liftS_of_mem (fun v => t v i) v

theorem isOpen_integral : IsOpen {x : Af F | ∀ v, x v ∈ v.adicCompletionIntegers F} :=
  RestrictedProduct.isOpen_forall_mem (fun v => Valued.isOpen_valuationSubring _)

theorem isOpen_offS (ι : Type) [Finite ι] (S : Finset (HeightOneSpectrum (𝓞 F))) :
    IsOpen (offS (F := F) ι S : Set (ι → Af F)) := by
  refine AddSubgroup.isOpen_of_mem_nhds _ (g := 0) ?_
  have ho : IsOpen (Set.pi Set.univ fun _ : ι => {x : Af F | ∀ v, x v ∈ v.adicCompletionIntegers F}) :=
    isOpen_set_pi Set.finite_univ fun _ _ => isOpen_integral
  refine Filter.mem_of_superset (ho.mem_nhds ?_) ?_
  · intro i _ v
    exact zero_mem (v.adicCompletionIntegers F)
  · intro x hx v _ i
    exact hx i (Set.mem_univ i) v

theorem pi_box : ∀ (F : Type) [Field F] [NumberField F] (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), (∀ v, IsStdV v (lam v)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → lf {x | ∀ v, x v ∈ v.adicCompletionIntegers F} = 1 → ∀ (ι : Type) [Fintype ι] (S : Finset (HeightOneSpectrum (𝓞 F))) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (ι → Fv F v)), (∀ v, MeasurableSet (A v)) → (Measure.pi fun _ : ι => lf) {x | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A v) ∧ ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} = ∏ v ∈ S, (Measure.pi fun _ : ι => lam v) (A v) := by
  intro F _ _ lam hlam lf hlf h1 ι _ S A hA
  obtain ⟨-, hAfLC, hAfSC, hAfT2⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  have hloc := fun v => GlobalTheory.T.completion_is_local_ring F v
  haveI : ∀ v, IsTopologicalRing (Fv F v) := fun v => (hloc v).1
  haveI : ∀ v, LocallyCompactSpace (Fv F v) := fun v => (hloc v).2.1
  haveI : ∀ v, SecondCountableTopology (Fv F v) := fun v => (hloc v).2.2.1
  haveI : ∀ v, BorelSpace (Fv F v) := fun v => ⟨rfl⟩
  haveI : ∀ v, (lam v).IsAddHaarMeasure := fun v => (hlam v).1
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  let ν : Measure (∀ v : S, ι → Fv F v.1) := Measure.pi fun v : S => Measure.pi fun _ : ι => lam v.1
  let O : Set (∀ v : S, ι → Fv F v.1) :=
    Set.pi Set.univ fun v : S => Set.pi Set.univ fun _ : ι => (v.1.adicCompletionIntegers F : Set (Fv F v.1))
  have hOo : IsOpen O := isOpen_set_pi Set.finite_univ fun v _ =>
    isOpen_set_pi Set.finite_univ fun _ _ => Valued.isOpen_valuationSubring _
  have hO0 : (0 : ∀ v : S, ι → Fv F v.1) ∈ O := fun v _ i _ => zero_mem (v.1.adicCompletionIntegers F)
  have hνO : ν O = 1 := by
    simp only [ν, O]
    rw [Measure.pi_pi]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [Measure.pi_pi]
    exact Finset.prod_eq_one fun _ _ => (hlam v.1).2
  have hmO : (Measure.pi fun _ : ι => lf) ((offS (F := F) ι S : Set (ι → Af F)) ∩ compS ι S ⁻¹' O) = 1 := by
    have : ((offS (F := F) ι S : Set (ι → Af F)) ∩ compS ι S ⁻¹' O) =
        Set.pi Set.univ fun _ : ι => {x : Af F | ∀ v, x v ∈ v.adicCompletionIntegers F} := by
      ext x
      constructor
      · rintro ⟨hx1, hx2⟩ i _ v
        by_cases hv : v ∈ S
        · exact hx2 ⟨v, hv⟩ (Set.mem_univ _) i (Set.mem_univ _)
        · exact hx1 v hv i
      · intro hx
        exact ⟨fun v _ i => hx i (Set.mem_univ i) v, fun v _ i _ => hx i (Set.mem_univ i) v.1⟩
    rw [this, Measure.pi_pi]
    exact Finset.prod_eq_one fun _ _ => h1
  have hset : {x : ι → Af F | (∀ v ∈ S, (fun i => evalV F v (x i)) ∈ A v) ∧ ∀ v, v ∉ S → ∀ i, evalV F v (x i) ∈ v.adicCompletionIntegers F} =
      (offS (F := F) ι S : Set (ι → Af F)) ∩ compS ι S ⁻¹' (Set.pi Set.univ fun v : S => A v.1) := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      exact ⟨hx2, fun v _ => hx1 v.1 v.2⟩
    · rintro ⟨hx1, hx2⟩
      exact ⟨fun v hv => hx2 ⟨v, hv⟩ (Set.mem_univ _), hx1⟩
  rw [hset, measure_inter_preimage (Measure.pi fun _ : ι => lf) (offS (F := F) ι S)
    (isOpen_offS ι S).measurableSet (compS ι S) (continuous_compS ι S).measurable
    (exists_offS_compS ι S) ν hOo hO0 hmO hνO (MeasurableSet.univ_pi fun v => hA v.1)]
  simp only [ν]
  rw [Measure.pi_pi]
  exact Finset.prod_coe_sort S fun v => (Measure.pi fun _ : ι => lam v) (A v)

end GlobalTheory.CompanionTheory.SW.AfBox
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdeleTopology
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups

namespace GlobalTheory.CompanionTheory.SW.Core.AfTop

variable (F : Type) [Field F] [NumberField F]

theorem isCompact_Oh : IsCompact (Oh F) :=
  (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).1

theorem isOpen_Oh : IsOpen (Oh F) := by
  haveI : Fact (∀ v : HeightOneSpectrum (𝓞 F),
      IsOpen (v.adicCompletionIntegers F : Set (v.adicCompletion F))) :=
    ⟨fun _ ↦ Valued.isOpen_valuationSubring _⟩
  exact RestrictedProduct.isOpen_forall_mem
    (R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F)
    (A := fun v => (v.adicCompletionIntegers F : Set (v.adicCompletion F))) Fact.out

theorem natCast_mul_mem_Oh (N : ℕ) {x : A F} (hx : x ∈ Oh F) : (N : A F) * x ∈ Oh F := by
  induction N with
  | zero =>
    intro v
    rw [Nat.cast_zero, zero_mul]
    exact zero_mem (v.adicCompletionIntegers F)
  | succ n ih =>
    intro v
    rw [Nat.cast_succ, add_mul, one_mul]
    exact add_mem (ih v) (hx v)

theorem algebraMap_mem_Oh_iff (b : F) : algebraMap F (A F) b ∈ Oh F ↔ ∃ r : 𝓞 F, (r : F) = b := by
  constructor
  · intro h
    obtain ⟨y, hy⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.1 b h
    exact ⟨y, hy.symm⟩
  · rintro ⟨r, rfl⟩ v
    exact HeightOneSpectrum.coe_mem_adicCompletionIntegers v r

theorem exists_mul_Oh_subset (U : Set (A F)) (hU : U ∈ 𝓝 (0 : A F)) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, (N : A F) * x ∈ U := by
  obtain ⟨h1, h2, h3, -⟩ := GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F
  let V : ℕ+ → Set (A F) := fun N => {a | ∃ c ∈ Oh F, a = ((N : ℕ) : A F) * c}
  have hV : Directed (· ⊇ ·) V := by
    intro M N
    refine ⟨M * N, ?_, ?_⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact ⟨_, natCast_mul_mem_Oh F N hc, by push_cast; ring⟩
    · rintro _ ⟨c, hc, rfl⟩
      exact ⟨_, natCast_mul_mem_Oh F M hc, by push_cast; ring⟩
  have hc : ∀ N, IsCompact (V N) := by
    intro N
    have : V N = (fun c => ((N : ℕ) : A F) * c) '' Oh F := by
      ext a
      simp only [V, Set.mem_setOf_eq, Set.mem_image, eq_comm]
    rw [this]
    exact (isCompact_Oh F).image (continuous_const.mul continuous_id)
  obtain ⟨N, hN⟩ := exists_subset_nhds_of_isCompact' hV hc (fun N => h2 N N.pos) (U := U) (by
    intro x hx
    have : x = 0 := h3 x fun M hM => Set.mem_iInter.1 hx ⟨M, hM⟩
    rwa [this])
  exact ⟨N, N.pos, fun x hx => hN ⟨x, hx, rfl⟩⟩

theorem exists_mul_mem_Oh_of_isCompact (K : Set (A F)) (hK : IsCompact K) :
    ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, (N : A F) * x ∈ Oh F := by
  let V : ℕ+ → Set (A F) := fun N => {a | ((N : ℕ) : A F) * a ∈ Oh F}
  have hV : Directed (· ⊆ ·) V := by
    intro M N
    refine ⟨M * N, fun a ha => ?_, fun a ha => ?_⟩
    · have := natCast_mul_mem_Oh F N ha
      show (((M * N : ℕ+) : ℕ) : A F) * a ∈ Oh F
      convert this using 1
      push_cast; ring
    · have := natCast_mul_mem_Oh F M ha
      show (((M * N : ℕ+) : ℕ) : A F) * a ∈ Oh F
      convert this using 1
      push_cast; ring
  obtain ⟨N, hN⟩ := hK.elim_directed_cover V
    (fun N => (isOpen_Oh F).preimage (continuous_const.mul continuous_id)) (fun a _ => by
      obtain ⟨M, hM, h⟩ := (GlobalTheory.IntegralFinAdele.integral_finiteAdele_properties F).2.2.2.2.1 a
      exact Set.mem_iUnion.2 ⟨⟨M, hM⟩, h⟩) hV
  exact ⟨N, N.pos, fun x hx => hN hx⟩

theorem isOpen_mul_Oh (N : ℕ) (hN : 0 < N) :
    IsOpen {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have h1 : (N : A F) * algebraMap F (A F) (N : F)⁻¹ = 1 := by
    rw [← map_natCast (algebraMap F (A F)), ← map_mul, mul_inv_cancel₀ hN', map_one]
  have : {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} =
      (fun x => algebraMap F (A F) (N : F)⁻¹ * x) ⁻¹' Oh F := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      show _ * (_ * y) ∈ Oh F
      rwa [← mul_assoc, mul_comm _ (N : A F), h1, one_mul]
    · intro hx
      exact ⟨_, hx, by rw [← mul_assoc, h1, one_mul]⟩
  rw [this]
  exact (isOpen_Oh F).preimage (continuous_const.mul continuous_id)

theorem denseRange_algebraMap : DenseRange (algebraMap F (A F)) := by
  intro y
  rw [mem_closure_iff_nhds]
  intro U hU
  have hc : Continuous fun z : A F => y - z := continuous_const.sub continuous_id
  have hU' : (fun z : A F => y - z) ⁻¹' U ∈ 𝓝 (0 : A F) :=
    hc.continuousAt.preimage_mem_nhds (by simpa using hU)
  obtain ⟨N, hN, h⟩ := exists_mul_Oh_subset F _ hU'
  obtain ⟨x, a, ha, hy⟩ := (GlobalTheory.AdLat.strong_approximation_mod_nat F N hN).1 y
  refine ⟨algebraMap F (A F) x, ?_, x, rfl⟩
  have h2 : y - (N : A F) * a ∈ U := h a ha
  have h3 : y - (N : A F) * a = algebraMap F (A F) x := by
    rw [sub_eq_iff_eq_add, ← nsmul_eq_mul]
    exact hy
  rwa [h3] at h2

theorem finiteAdele_topology : ∀ (F : Type) [Field F] [NumberField F], LocallyCompactSpace (A F) ∧ SecondCountableTopology (A F) ∧ T2Space (A F) ∧ IsCompact (Oh F) ∧ IsOpen (Oh F) ∧ DenseRange (algebraMap F (A F)) ∧ (∀ b : F, algebraMap F (A F) b ∈ Oh F ↔ ∃ r : 𝓞 F, (r : F) = b) ∧ (∀ U ∈ 𝓝 (0 : A F), ∃ N : ℕ, 0 < N ∧ ∀ x ∈ Oh F, (N : A F) * x ∈ U) ∧ (∀ K : Set (A F), IsCompact K → ∃ N : ℕ, 0 < N ∧ ∀ x ∈ K, (N : A F) * x ∈ Oh F) ∧ ∀ N : ℕ, 0 < N → IsOpen {x : A F | ∃ y ∈ Oh F, x = (N : A F) * y} :=
  fun F _ _ => ⟨GlobalTheory.AdelicUnitaryTop.locallyCompact_finiteAdele F,
    GlobalTheory.AdelicUnitaryTop.secondCountable_finiteAdele F, GlobalTheory.AdelicUnitaryTop.t2Space_finiteAdeleRing_of_numberField F,
    isCompact_Oh F, isOpen_Oh F, denseRange_algebraMap F, algebraMap_mem_Oh_iff F,
    exists_mul_Oh_subset F, exists_mul_mem_Oh_of_isCompact F, isOpen_mul_Oh F⟩

end GlobalTheory.CompanionTheory.SW.Core.AfTop
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FiniteAdelicTraceFormCoordinates
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.BB NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.BB

theorem finDensity_coord : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (B : Matrix (Fin M × Fin d) (Fin M × Fin d) F), (∀ x y : Fin M → Af F ⊗[F] E, Algebra.trace (Af F) (Af F ⊗[F] E) (hR (Af F) σ J x y) = cv (Af F) b x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ cv (Af F) b y)) → ∀ (lf : Measure (Af F)), lf.IsAddHaarMeasure → ∀ (a : ℕ) (U : Set (Af F)), coordW (Af F) b lf 1 M {X | (∀ v, projV v X ∈ {X : (Fin 1 → Fin M → Fv F v ⊗[F] E) | (fun p i => (a : Fv F v ⊗[F] E) * X p i) ∈ latV b v}) ∧ algebraMap F (Af F) (1 / 2) * Algebra.trace (Af F) (Af F ⊗[F] E) (gramR (Af F) σ J X 0 0) ∈ U} = (Measure.pi fun _ : Fin M × Fin d => lf) {x | (∀ i v, ((a : Af F) * x i) v ∈ v.adicCompletionIntegers F) ∧ algebraMap F (Af F) (1 / 2) * (x ⬝ᵥ (B.map (algebraMap F (Af F)) *ᵥ x)) ∈ U} := by
  intro F E _ _ _ _ _ σ hCM M J hJ d b B hB lf hlf a U
  obtain ⟨-, h1, h2, h3⟩ := GlobalTheory.T.adeles_locally_compact_second_countable F
  haveI : BorelSpace (Af F) := ⟨rfl⟩
  obtain ⟨-, hme, hmap⟩ := GlobalTheory.T.coordinate_homeomorph_rank_one_tuples F E σ hCM (Af F) d b lf hlf M
  rw [← hmap, hme.map_apply]
  congr 1
  ext X
  simp only [Set.mem_preimage, Set.mem_setOf_eq]
  have hl := GlobalTheory.T.finite_adelic_lattice_membership_iff F E d M b a X
  have ht : gramR (Af F) σ J X 0 0 = hR (Af F) σ J (X 0) (X 0) := rfl
  rw [ht, hB, ← hl]

end GlobalTheory.CompanionTheory.SW.BB
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainExistsUnitaryStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haar_fundamental_domain_exists_unitary : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → (∃ μ, IsHaarH F E σ M J μ) ∧ ∀ μ, IsHaarH F E σ M J μ → (∃ 𝓕, IsFDH F E σ M J μ 𝓕) ∧ (∃ 𝓕, MeasurableSet 𝓕 ∧ IsFDH F E σ M J μ 𝓕 ∧ ∀ h : HA (AF F) σ J, ∃ γ : HA (AF F) σ J, HA.mat (AF F) σ J γ ∈ HFin (AF F) σ J ∧ γ * h ∈ 𝓕) ∧ ∀ 𝓕, IsFDH F E σ M J μ 𝓕 → μ 𝓕 ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.SW.haar_fundamental_exist | exact GlobalTheory.CompanionTheory.SW.haar_fundamental_exist | (intros; apply GlobalTheory.CompanionTheory.SW.haar_fundamental_exist <;> assumption)
end

