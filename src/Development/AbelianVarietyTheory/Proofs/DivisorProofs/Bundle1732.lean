import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactSpaceAxis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1704
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0196
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1701
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1696
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulRightInvariantHaarAdelicUnitaryGroupHermiti
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1090
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0101
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemidirectAverageIndicatorLowerBound
section
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal Pointwise

namespace GlobalTheory.ResLine.LowerAverage

theorem countable_subgroupOf {G : Type} [Group G] (Λ N : Subgroup G) [Countable Λ] :
    Countable (Λ.subgroupOf N) := by
  refine Function.Injective.countable
    (f := fun x : Λ.subgroupOf N => (⟨x.1.1, Subgroup.mem_subgroupOf.1 x.2⟩ : Λ)) ?_
  intro x y h
  exact Subtype.ext (Subtype.ext (congrArg (fun z : Λ => (z : G)) h))

theorem right_of_closed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (N Λ : Subgroup G) [Countable Λ] (hN : IsClosed (N : Set G)) (ν : Measure N)
    (hν : ν.IsHaarMeasure) (D : Set N) (hD : IsFundamentalDomain (Λ.subgroupOf N) D ν)
    (hfin : ν D ≠ ⊤) : ν.IsMulRightInvariant := by
  haveI : BorelSpace N := Subtype.borelSpace (N : Set G)
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI := countable_subgroupOf Λ N
  exact RightUnfold.isMulRightInvariant_of_lattice ν (Λ.subgroupOf N) D hD hfin

theorem average_lower : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (N M Λ : Subgroup G) [Countable Λ] (ν : Measure N) (π : Measure M) (DN : Set N) (DM : Set M), SemiLat N M Λ ν π DN DM → ∀ (μ : Measure G), μ.IsHaarMeasure → ∀ C : Set G, IsCompact C → ∃ (U : Set G) (c : ℝ≥0∞), IsOpen U ∧ μ U ≠ ⊤ ∧ c ≠ 0 ∧ ∀ u₀ ∈ N, ∀ m₀ ∈ M, ∀ y ∈ C, c ≤ ∫⁻ m : M, ∫⁻ u : N, U.indicator 1 ((u : G) * m * (u₀ * m₀ * y)) ∂ν ∂π := by
  intro G _ _ _ _ _ _ _ _ N M Λ _ ν π DN DM H μ hμ C hC
  haveI : BorelSpace N := Subtype.borelSpace (N : Set G)
  haveI : BorelSpace M := Subtype.borelSpace (M : Set G)
  haveI := H.haarN
  haveI := H.haarM
  haveI := right_of_closed N Λ H.closedN ν H.haarN DN H.domN H.finN
  haveI := right_of_closed M Λ H.closedM π H.haarM DM H.domM H.finM
  obtain ⟨K, hK, hCK⟩ := exists_compact_superset hC
  obtain ⟨W, hW, hWC⟩ := compact_open_separated_mul_left hC isOpen_interior hCK
  obtain ⟨V, hVo, hV1, hVW⟩ := exists_open_nhds_one_mul_subset hW
  have hVN : IsOpen ((↑) ⁻¹' V : Set N) := hVo.preimage continuous_subtype_val
  have hVM : IsOpen ((↑) ⁻¹' V : Set M) := hVo.preimage continuous_subtype_val
  refine ⟨interior K, ν ((↑) ⁻¹' V) * π ((↑) ⁻¹' V), isOpen_interior,
    ((measure_mono interior_subset).trans_lt hK.measure_lt_top).ne,
    mul_ne_zero (hVN.measure_ne_zero ν ⟨1, hV1⟩) (hVM.measure_ne_zero π ⟨1, hV1⟩), ?_⟩
  intro u₀ hu₀ m₀ hm₀ y hy
  have h1 : ∀ m : M, ∫⁻ u : N, (interior K).indicator (1 : G → ℝ≥0∞) ((u : G) * m * (u₀ * m₀ * y)) ∂ν
      = ∫⁻ u : N, (interior K).indicator (1 : G → ℝ≥0∞)
        ((u : G) * ((m * ⟨m₀, hm₀⟩ : M) : G) * y) ∂ν := by
    intro m
    rw [← lintegral_mul_right_eq_self (fun u : N => (interior K).indicator (1 : G → ℝ≥0∞)
        ((u : G) * ((m * ⟨m₀, hm₀⟩ : M) : G) * y)) ⟨m * u₀ * (m : G)⁻¹, H.norm m m.2 u₀ hu₀⟩]
    refine lintegral_congr fun u => ?_
    congr 1
    simp only [Subgroup.coe_mul]
    group
  simp_rw [h1]
  rw [lintegral_mul_right_eq_self (fun m : M => ∫⁻ u : N, (interior K).indicator (1 : G → ℝ≥0∞)
        ((u : G) * (m : G) * y) ∂ν) ⟨m₀, hm₀⟩, ← lintegral_indicator_const hVM.measurableSet]
  refine lintegral_mono fun m => ?_
  by_cases hm : m ∈ ((↑) ⁻¹' V : Set M)
  swap
  · rw [Set.indicator_of_notMem hm]
    exact bot_le
  rw [Set.indicator_of_mem hm]
  rw [← lintegral_indicator_one hVN.measurableSet]
  refine lintegral_mono fun u => ?_
  by_cases hu : u ∈ ((↑) ⁻¹' V : Set N)
  swap
  · rw [Set.indicator_of_notMem hu]
    exact bot_le
  rw [Set.indicator_of_mem hu]
  have : (u : G) * m * y ∈ interior K :=
    hWC (Set.mul_mem_mul (hVW (Set.mul_mem_mul hu hm)) hy)
  rw [Set.indicator_of_mem this]
  exact le_rfl

end GlobalTheory.ResLine.LowerAverage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetIntegralEqOfSetLIntegralEq
section
open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CovolIndep
variable {S X : Type} [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X]
  [MeasurableSMul₂ S X]

theorem measure_mul_setLIntegral_eq [MeasurableInv S] (ν : Measure S) [SFinite ν] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] (D : Set X) (hD : MeasurableSet D) (E : Set S)
    (hE : MeasurableSet E) (ψ : X → ℝ≥0∞) (hψ : Measurable ψ)
    (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ν E * ∫⁻ x in D, ψ x ∂μ = ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D}) ∂μ :=
  GlobalTheory.T.lintegral_mul_measure_inter_smul_preimage_of_invariant S X ν μ D hD E hE ψ hψ hinv

theorem lintegral_unfold_eq [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S) [SFinite ν]
    [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ]
    (Γ : Subgroup S) [Countable Γ] (D₁ D₂ : Set X) (hD₁ : MeasurableSet D₁)
    (hD₂ : IsFundamentalDomain Γ D₂ μ) (E : Set S) (hE : MeasurableSet E)
    (hEf : IsFundamentalDomain Γ E ν) (ψ : X → ℝ≥0∞) (hψ : Measurable ψ)
    (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ∫⁻ y, ψ y * ν (E ∩ {s | s⁻¹ • y ∈ D₁}) ∂μ = ∫⁻ y in D₂, ψ y * ν {s | s⁻¹ • y ∈ D₁} ∂μ :=
  GlobalTheory.T.lintegral_fundamentalDomain_unfold_refold_measure S X ν μ Γ D₁ D₂ hD₁ hD₂ E hE hEf ψ hψ hinv

theorem ae_measure_setOf_smul_mem_eq [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S) [SFinite ν]
    [ν.IsMulLeftInvariant] (μ : Measure X) [SFinite μ] [SMulInvariantMeasure S X μ]
    (Γ : Subgroup S) [Countable Γ] (D : Set X) (hD : MeasurableSet D)
    (hDf : IsFundamentalDomain Γ D μ) (E : Set S) (hE : IsFundamentalDomain Γ E ν) :
    ∀ᵐ y ∂μ, ν {s | s • y ∈ D} = ν E :=
  GlobalTheory.T.ae_measure_smul_preimage_fundamentalDomain_eq S X ν μ Γ D hD hDf E hE

theorem lintegral_mul_eq_of_measurable [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S)
    [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsInvInvariant] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] (Γ₁ Γ₂ : Subgroup S) [Countable Γ₁] [Countable Γ₂]
    (D₁ D₂ : Set X) (E₁ E₂ : Set S) (hD₁m : MeasurableSet D₁) (hD₂m : MeasurableSet D₂)
    (hE₂m : MeasurableSet E₂)
    (hD₁ : IsFundamentalDomain Γ₁ D₁ μ) (hD₂ : IsFundamentalDomain Γ₂ D₂ μ)
    (hE₁ : IsFundamentalDomain Γ₁ E₁ ν) (hE₂ : IsFundamentalDomain Γ₂ E₂ ν)
    (ψ : X → ℝ≥0∞) (hψ : Measurable ψ) (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ν E₂ * ∫⁻ x in D₁, ψ x ∂μ = ν E₁ * ∫⁻ x in D₂, ψ x ∂μ := by
  rw [measure_mul_setLIntegral_eq ν μ D₁ hD₁m E₂ hE₂m ψ hψ hinv,
    lintegral_unfold_eq ν μ Γ₂ D₁ D₂ hD₁m hD₂ E₂ hE₂m hE₂ ψ hψ hinv, ← lintegral_const_mul _ hψ]
  refine lintegral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [ae_measure_setOf_smul_mem_eq ν μ Γ₁ D₁ hD₁m hD₁ E₁ hE₁] with y hy
  have : ν {s : S | s⁻¹ • y ∈ D₁} = ν {s : S | s • y ∈ D₁} := by
    change ν ({s : S | s • y ∈ D₁}⁻¹) = _
    exact Measure.measure_inv (μ := ν) _
  rw [this, hy, mul_comm]
end GlobalTheory.CovolIndep

namespace GlobalTheory.CovolIndep
variable {S X : Type} [Group S] [MeasurableSpace S] [MeasurableSpace X] [MulAction S X]
  [MeasurableSMul₂ S X]

theorem lintegral_mul_eq [MeasurableMul₂ S] [MeasurableInv S] (ν : Measure S)
    [SFinite ν] [ν.IsMulLeftInvariant] [ν.IsInvInvariant] (μ : Measure X) [SFinite μ]
    [SMulInvariantMeasure S X μ] (Γ₁ Γ₂ : Subgroup S) [Countable Γ₁] [Countable Γ₂]
    (D₁ D₂ : Set X) (E₁ E₂ : Set S)
    (hD₁ : IsFundamentalDomain Γ₁ D₁ μ) (hD₂ : IsFundamentalDomain Γ₂ D₂ μ)
    (hE₁ : IsFundamentalDomain Γ₁ E₁ ν) (hE₂ : IsFundamentalDomain Γ₂ E₂ ν)
    (ψ : X → ℝ≥0∞) (hψ : Measurable ψ) (hinv : ∀ (s : S) (x : X), ψ (s • x) = ψ x) :
    ν E₂ * ∫⁻ x in D₁, ψ x ∂μ = ν E₁ * ∫⁻ x in D₂, ψ x ∂μ := by
  have a₁ := hD₁.nullMeasurableSet.toMeasurable_ae_eq
  have a₂ := hD₂.nullMeasurableSet.toMeasurable_ae_eq
  have b₂ := hE₂.nullMeasurableSet.toMeasurable_ae_eq
  have key := lintegral_mul_eq_of_measurable ν μ Γ₁ Γ₂ (toMeasurable μ D₁) (toMeasurable μ D₂)
    E₁ (toMeasurable ν E₂) (measurableSet_toMeasurable _ _) (measurableSet_toMeasurable _ _)
    (measurableSet_toMeasurable _ _) (isFundamentalDomain_of_ae_eq hD₁ a₁)
    (isFundamentalDomain_of_ae_eq hD₂ a₂) hE₁ (isFundamentalDomain_of_ae_eq hE₂ b₂) ψ hψ hinv
  rwa [measure_toMeasurable, setLIntegral_congr a₁, setLIntegral_congr a₂] at key

end GlobalTheory.CovolIndep

namespace GlobalTheory

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SetLIntegralTsumUnfoldOfCosetRepresentativesStatement
section
open MeasureTheory Filter Topology GlobalTheory.ResLine
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.setLIntegral_tsum_unfold_of_cosetRepresentatives : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G) (Γ Λ : Subgroup G) [Countable Γ] (T : Set Γ) (𝓕 D : Set G), μ.IsHaarMeasure → Λ ≤ Γ → (∀ γ : Γ, ∃! t, t ∈ T ∧ ((γ * t⁻¹ : Γ) : G) ∈ Λ) → IsFundamentalDomain Γ 𝓕 μ → IsFundamentalDomain Λ D μ → ∀ f : G → ℝ≥0∞, Measurable f → (∀ γ ∈ Λ, ∀ g, f (γ * g) = f g) → ∫⁻ g in 𝓕, ∑' t : T, f (t.1.1 * g) ∂μ = ∫⁻ g in D, f g ∂μ := by
  first | exact @GlobalTheory.ResLine.setLIntegral_tsum_unfold | exact GlobalTheory.ResLine.setLIntegral_tsum_unfold | (intros; apply GlobalTheory.ResLine.setLIntegral_tsum_unfold <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteCombinationMulLiftByDegree
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
namespace GlobalTheory.SmallRoute

theorem setIntegral_mul_right_of_left_inv {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H] (Γ : Subgroup H) [Countable Γ] (ν : Measure H)
    [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] {fd : Set H} (hfd : IsFundamentalDomain Γ fd ν) {φ : H → ℂ}
    (hφ : ∀ γ ∈ Γ, ∀ u, φ (γ * u) = φ u) (hi : IntegrableOn φ fd ν) (k : H) :
    IntegrableOn (fun u => φ (u * k)) fd ν ∧ ∫ u in fd, φ (u * k) ∂ν = ∫ u in fd, φ u ∂ν := by
  have hmp : MeasurePreserving (· * k) ν ν := measurePreserving_mul_right ν k
  have hme : MeasurableEmbedding (· * k) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have hfd' : IsFundamentalDomain Γ ((· * k⁻¹) ⁻¹' fd) ν := by
    refine hfd.preimage_of_equiv (measurePreserving_mul_right ν k⁻¹).quasiMeasurePreserving (e := id)
      Function.bijective_id ?_
    intro g x
    simp only [id, Subgroup.smul_def, smul_eq_mul, mul_assoc]
  have hinv : ∀ g : Γ, ∀ x, φ (g • x) = φ x := fun g x => hφ g g.2 x
  have hpre : (· * k) ⁻¹' ((· * k⁻¹) ⁻¹' fd) = fd := by
    ext u; simp
  refine ⟨?_, ?_⟩
  · have h1 : IntegrableOn φ ((· * k⁻¹) ⁻¹' fd) ν := (hfd'.integrableOn_iff hfd hinv).2 hi
    have h2 := (hmp.integrableOn_comp_preimage hme (f := φ) (s := (· * k⁻¹) ⁻¹' fd)).2 h1
    rw [hpre] at h2
    exact h2
  · have h3 := hmp.setIntegral_preimage_emb hme φ ((· * k⁻¹) ⁻¹' fd)
    rw [hpre] at h3
    rw [h3]
    exact hfd'.setIntegral_eq hfd hinv

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem mem_support_tensT (W : G.Weil) {X Y : Node} {p : Path T X Y} {τi : PolT G p →₀ ℂ} {τf : TotT G p} {d : PureT G p}
    (hd : d ∈ (tensT W τi τf).support) :
    ∃ d₀ ∈ τf.support, ∃ P, d = Path.Fam.zip (fun a (f : Sch G a) Q => W.fock a.pair f Q) d₀ P := by
  classical
  unfold tensT at hd
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d₀, hd₀, h⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  exact ⟨d₀, hd₀, P, Finset.mem_singleton.1 (Finsupp.support_single_subset h)⟩

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem theta_of_matched {W : G.Weil} {B : Frames G} {ρ : RealMatch W} {t : T} {i j : Fin D.R.m}
    {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)} (hΘ : IsMatched B t ρ i j Θ Θ')
    {d : PureT G (routeSmall t i j)} (hd : d ∈ Θ'.support) :
    IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2 ∧
      IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 := by
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, hloc, -⟩, -⟩, -, rfl⟩ := hΘ
  obtain ⟨d₀, hd₀, P, rfl⟩ := mem_support_tensT W hd
  obtain ⟨h1, h2⟩ := hloc d₀ hd₀
  have v1 := ρ.vT_is t i j i.2.le j.2
  have v2 := ρ.vX_is i j i.2 j.2.le
  have t1 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h1.2 v1.2.theta
  have t2 := GlobalTheory.VecTheta.isThetaFunO_of_thetaAt W.ψ_std W.θ_is h2.2 v2.2.theta
  exact ⟨GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t2 _,
    GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ t1 _⟩

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem outer_left (W : G.Weil) (M : Vol G) {t : T} {i j : Fin D.R.m} {d : PureT G (routeSmall t i j)}
    (h2 : IsThetaFunO W.ψ (G.pS (.chi i j)) (G.pT (.chi i j)) d.2)
    (h1 : IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2) (F : Fn G (.grid i (j + 1)))
    (g₁ : GA D (G.V (.grid (i + 1) j))) {γ : GA D (G.V (.grid i j))} (hγ : γ ∈ GQ (G.V (.grid i j)))
    (u : GA D (G.V (.grid i j))) : outer W M d F g₁ (γ * u) = outer W M d F g₁ u := by
  have hc := W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩
  have hm := W.om_is (.mu t (i : ℕ) j) ⟨i.2.le, j.2⟩
  unfold outer
  congr 1
  · show thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) (γ * u) d.2 = thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) u d.2
    unfold thetaKO
    have e : ((negGA _ g₁, γ * u) : GA D (G.pS (.chi (i : ℕ) j)) × GA D (G.pT (.chi (i : ℕ) j))) =
        (1, γ) * (negGA _ g₁, u) := by simp
    rw [e, map_mul, Module.End.mul_apply]
    exact hc.om_aut 1 (one_mem _) γ hγ _ (hc.om_pres _ _ h2)
  · refine integral_congr_ae (.of_forall fun g => ?_)
    show thetaKO (W.om (.mu t (i : ℕ) j)) (γ * u) g d.1.2 * F g = thetaKO (W.om (.mu t (i : ℕ) j)) u g d.1.2 * F g
    unfold thetaKO
    have e : ((γ * u, g) : GA D (G.pS (.mu t (i : ℕ) j)) × GA D (G.pT (.mu t (i : ℕ) j))) = (γ, 1) * (u, g) := by simp
    rw [e, map_mul, Module.End.mul_apply, hm.om_aut γ hγ 1 (one_mem _) _ (hm.om_pres _ _ h1)]

end GlobalTheory.SmallRoute

namespace GlobalTheory.SmallRoute

theorem zdeg_mul_liftT : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (B : Frames G) (ρ : RealMatch W) (t : T) (i j : Fin D.R.m)
    (M : Vol G) (hM : M.Is t) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j)) (hΘ : IsMatched B t ρ i j Θ Θ')
    (F : Fn G (.grid i (j + 1))) (hF : IsAutFunSm W.θ _ F) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j)))
    (z : GA D (G.V (.grid i j)) →₀ ℂ),
    (∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => GlobalTheory.SmallRoute.outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j))) ∧
    zdeg z * liftT W M (routeSmall t i j) Θ' F g₁ =
      Θ'.sum fun d c => c * ∫ u in M.fd (.grid i j), translates z (GlobalTheory.SmallRoute.outer W M d F g₁) u ∂M.ν (.grid i j) := by
  intro D T L sc G μ₀ hL W B ρ t i j M hM Θ Θ' hΘ F hF hB g₁ z
  obtain ⟨hH, hfd⟩ := (hM.vtx (.grid i j) ⟨i.2.le, j.2.le⟩).haar_fund
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (G.V (.grid i j))
  haveI := hH
  haveI := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D _ (M.ν (.grid i j)) hH
  have key : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j)) ∧
      ∫ u in M.fd (.grid i j), outer W M d F g₁ (u * k) ∂M.ν (.grid i j) =
        ∫ u in M.fd (.grid i j), outer W M d F g₁ u ∂M.ν (.grid i j) := fun d hd k => by
    obtain ⟨h2, h1⟩ := theta_of_matched hΘ hd
    refine setIntegral_mul_right_of_left_inv (GQ (G.V (.grid i j))) (M.ν (.grid i j)) hfd
      (fun γ hγ u => outer_left W M h2 h1 F g₁ hγ u) ?_ k
    exact (hB d hd).2 g₁
  refine ⟨fun d hd k => (key d hd k).1, ?_⟩
  rw [liftT_routeSmall, Finsupp.sum, Finsupp.sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have e : ∫ u in M.fd (.grid i j), translates z (outer W M d F g₁) u ∂M.ν (.grid i j) =
      zdeg z * ∫ u in M.fd (.grid i j), outer W M d F g₁ u ∂M.ν (.grid i j) := by
    unfold translates zdeg
    simp only [Finsupp.sum]
    rw [integral_finset_sum _ fun k _ => ((key d hd k).1.integrable.const_mul _),
      Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, (key d hd k).2]
  rw [e]
  ring

end GlobalTheory.SmallRoute
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteKernelLeftInvariantRationalUnitary
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ZConvLeft

theorem isThetaFunO_down {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) {Θ : TotT G (routeBig t i j)} {Θ' : TotT G (routeSmall t i j)}
    (hΘ : IsMatched B t ρ i j Θ Θ') :
    ∀ d ∈ Θ'.support, IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) d.1.2 := by
  classical
  obtain ⟨a, b, τ, τ', n, Φ, -, -, ⟨e, -, ⟨φ₁, φ₂, h1, -⟩, -⟩, -, rfl⟩ := hΘ
  intro d hd
  obtain ⟨P, -, hP⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hd)
  obtain ⟨d', hd', hd''⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hP)
  have hdd := Finsupp.support_single_subset hd''
  rw [Finset.mem_singleton] at hdd
  subst hdd
  have h0 : IsThetaFunO W.ψ (G.pS (.mu t i j)) (G.pT (.mu t i j)) (ρ.vT i j) :=
    (ρ.vT_is t i j i.2.le j.2).2.2
  have hf := GlobalTheory.GalLift.Vec.theta_of_thetaAt W.ψ_std W.θ_is (h1 d' hd').1.2 h0
  exact GlobalTheory.GalLift.Vec.theta_pureTensorO W.ψ_std W.θ_is _ _ _ _ hf _

theorem kerSmall_rat_left : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (hΘ : IsMatched B t ρ i j Θ Θ') (g₁ : GA D (G.V (.grid (i + 1) j))),
    ∀ γ ∈ GQ (G.V (.grid i (j + 1))), ∀ g u, kerSmall W Θ' (γ * g) g₁ u = kerSmall W Θ' g g₁ u := by
  intro D T L sc G μ₀ hL W B ρ t i j Θ Θ' hΘ g₁ γ hγ g u
  have hω := W.om_is (.mu t i j) ⟨i.2.le, j.2⟩
  have hth := isThetaFunO_down W B ρ t i j hΘ
  unfold kerSmall
  refine Finsupp.sum_congr fun d hd => ?_
  congr 2
  show thetaKO (W.om (.mu t i j)) u (γ * g) d.1.2 = thetaKO (W.om (.mu t i j)) u g d.1.2
  unfold thetaKO
  have e : ((u, γ * g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (1, γ) * (u, g) := by simp
  rw [e, map_mul]
  exact hω.om_aut 1 (one_mem _) γ hγ _ (hω.om_pres _ _ (hth d hd))

end GlobalTheory.ZConvLeft
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallRouteSumTranslatedOuterIntegralsEq
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallRoute

theorem sum_integral_translates_outer_eq : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T} (hL : L.Is μ₀)
    (W : G.Weil) (t : T) (i j : Fin D.R.m) (M : Vol G) (hM : M.Is t) (Θ' : TotT G (routeSmall t i j))
    (F : Fn G (.grid i (j + 1))) (hB : TotConv W M _ Θ' F) (g₁ : GA D (G.V (.grid (i + 1) j))) (z : GA D (G.V (.grid i j)) →₀ ℂ)
    (hI : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun u => GlobalTheory.SmallRoute.outer W M d F g₁ (u * k)) (M.fd (.grid i j)) (M.ν (.grid i j)))
    (hJ : Integrable (fun p : GA D (G.V (.grid i (j + 1))) × GA D (G.V (.grid i j)) => F p.1 * translates z (kerSmall W Θ' p.1 g₁) p.2)
      (((M.ν (.grid i (j + 1))).restrict (M.fd (.grid i (j + 1)))).prod ((M.ν (.grid i j)).restrict (M.fd (.grid i j))))),
    (Θ'.sum fun d c => c * ∫ u in M.fd (.grid i j), translates z (GlobalTheory.SmallRoute.outer W M d F g₁) u ∂M.ν (.grid i j)) =
      ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid i j),
        translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j) ∂M.ν (.grid i (j + 1)) := by
  intro D T L sc G μ₀ hL W t i j M hM Θ' F hB g₁ z hI hJ
  classical
  have hσ : ∀ X : Node, X.InRange D.R.m → SigmaFinite (M.ν X) := fun X hX => by
    obtain ⟨h1, h2, -⟩ := GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D (G.V X)
    haveI := (hM.vtx X hX).haar_fund.1
    infer_instance
  haveI := hσ (.grid i (j + 1)) ⟨i.2.le, j.2⟩
  haveI := hσ (.grid i j) ⟨i.2.le, j.2.le⟩
  have hpt : ∀ u, ∫ g in M.fd (.grid i (j + 1)), F g * translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i (j + 1)) =
      Θ'.sum fun d c => c * translates z (outer W M d F g₁) u := by
    intro u
    have hint : ∀ d ∈ Θ'.support, ∀ k, IntegrableOn (fun g => W.kerA (.down t i j) d.1.2 g (u * k) * F g)
        (M.fd (.grid i (j + 1))) (M.ν (.grid i (j + 1))) := fun d hd k => (hB d hd).1.2 (u * k)
    have e : ∀ g, F g * translates z (kerSmall W Θ' g g₁) u = ∑ k ∈ z.support, ∑ d ∈ Θ'.support,
        z k * (Θ' d * (W.kerA (.right i j) d.2 (u * k) g₁ * (W.kerA (.down t i j) d.1.2 g (u * k) * F g))) := by
      intro g
      simp only [translates, kerSmall, Finsupp.sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun d _ => by ring
    simp_rw [e]
    rw [integral_finset_sum _ fun k _ => integrable_finset_sum _ fun d hd =>
      (((hint d hd k).const_mul _).const_mul _).const_mul _]
    simp_rw [integral_finset_sum _ fun d hd => (((hint d hd _).const_mul _).const_mul _).const_mul _]
    simp only [integral_const_mul, translates, outer, Finsupp.sum, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun k _ => by ring
  have hint2 : ∀ d ∈ Θ'.support, Integrable (translates z (outer W M d F g₁))
      ((M.ν (.grid i j)).restrict (M.fd (.grid i j))) := fun d hd =>
    integrable_finset_sum _ fun k _ => (hI d hd k).const_mul _
  symm
  calc ∫ g in M.fd (.grid i (j + 1)), F g * ∫ u in M.fd (.grid i j), translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j)
        ∂M.ν (.grid i (j + 1))
      = ∫ g in M.fd (.grid i (j + 1)), ∫ u in M.fd (.grid i j), F g * translates z (kerSmall W Θ' g g₁) u ∂M.ν (.grid i j)
        ∂M.ν (.grid i (j + 1)) := by simp_rw [integral_const_mul]
    _ = ∫ u in M.fd (.grid i j), ∫ g in M.fd (.grid i (j + 1)), F g * translates z (kerSmall W Θ' g g₁) u
        ∂M.ν (.grid i (j + 1)) ∂M.ν (.grid i j) := integral_integral_swap hJ
    _ = ∫ u in M.fd (.grid i j), (Θ'.sum fun d c => c * translates z (outer W M d F g₁) u) ∂M.ν (.grid i j) := by
        simp_rw [hpt]
    _ = _ := by
        simp only [Finsupp.sum]
        rw [integral_finset_sum _ fun d hd => (hint2 d hd).const_mul _]
        simp_rw [integral_const_mul]

end GlobalTheory.SmallRoute

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitTorusRationalSquaringPathsRigidCharZeroStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitTorus_rationalSquaringPathsRigid_charZero : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (X : Type) [AddCommGroup X], RatRigid (splitTorus (Sp Ω) X) (𝟙 (Sp Ω)) := by
  first | exact @GlobalTheory.Nef.splitTorus_ratRigid | exact GlobalTheory.Nef.splitTorus_ratRigid | (intros; apply GlobalTheory.Nef.splitTorus_ratRigid <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuInvHasInfinityTypeCmTypeStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareNu_inv_hasInfinityType_cmType : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m), (nuH G μ₀ i j)⁻¹.HasInf (Formalism.L2.Host.embTau D) (fun τ => 2 * ((GlobalTheory.ChiGrid.num D sc.cGap τ).e (j + 1) + GlobalTheory.ChiGrid.cen D sc.cGap τ (D.R.m - i))) := by
  first | exact @GlobalTheory.FunObj.SqNum.nuH_inv_hasInf | exact GlobalTheory.FunObj.SqNum.nuH_inv_hasInf | (intros; apply GlobalTheory.FunObj.SqNum.nuH_inv_hasInf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareNuInvUnramifiedOverInertPrimeStatement
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareNu_inv_unramified_over_inert_prime : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m) (P : HeightOneSpectrum (𝓞 D.host.E)), (∃ q : ℕ, q.Prime ∧ InertQ D q ∧ ((q : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) → (nuH G μ₀ i j)⁻¹.UnrAt P := by
  first | exact @GlobalTheory.FunObj.SqNum.nuH_inv_unrAt_of_inertQ | exact GlobalTheory.FunObj.SqNum.nuH_inv_unrAt_of_inertQ | (intros; apply GlobalTheory.FunObj.SqNum.nuH_inv_unrAt_of_inertQ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumWedgePrimitiveOneFormsEqZeroAbelianSchemeStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_wedge_primitive_oneForms_eq_zero_abelianScheme : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (n : ℕ) (u v : Fin n → GlobForm A.hom), wsum (OAff (A ⊗ A).hom) (fun k ↦ pF μ[A] (u k)) (fun k ↦ pF μ[A] (v k)) = wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (fst A A) (u k)) (fun k ↦ pF (fst A A) (v k)) + wsum (OAff (A ⊗ A).hom) (fun k ↦ pF (snd A A) (u k)) (fun k ↦ pF (snd A A) (v k)) → wsum (OAff A.hom) u v = 0 := by
  first | exact @GlobalTheory.AbCoh.wsum_eq_zero_of_mul | exact GlobalTheory.AbCoh.wsum_eq_zero_of_mul | (intros; apply GlobalTheory.AbCoh.wsum_eq_zero_of_mul <;> assumption)
end

