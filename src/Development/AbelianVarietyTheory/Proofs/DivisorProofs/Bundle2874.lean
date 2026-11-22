import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2467
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2822
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2781
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2855
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2644
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0296
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2785
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2574
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2782
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2773
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2631
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CrossRelationGivesConvolutionRelation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0023
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchIntegrableRegularVariety
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory Set Filter Topology Metric
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ChartGlue
open scoped ENNReal

namespace GlobalTheory.LogNormInt

theorem integrableOn_of_chart {M : Type} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M] {n : ℕ}
    (e : OpenPartialHomeomorph M (V n)) {μ : Measure M} {ρ : V n → ℝ≥0∞}
    (hμ : ∀ A, MeasurableSet A → A ⊆ e.source → μ A = ∫⁻ v in e '' A, ρ v)
    {A : Set M} (hA : MeasurableSet A) (hAs : A ⊆ e.source) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hρ : ∀ v ∈ e '' A, ρ v ≤ C) {f : M → ℝ} (hf : ContinuousOn f A)
    (hi : IntegrableOn (f ∘ e.symm) (e '' A)) : IntegrableOn f A μ := by
  have hm := measurableSet_image e hA hAs
  have hsub : e '' A ⊆ e.target := fun _ ⟨y, hy, h⟩ => h ▸ e.map_source (hAs hy)
  have hs : AEMeasurable e.symm (volume.restrict (e '' A)) :=
    (e.continuousOn_symm.mono hsub).aemeasurable hm
  have hle : μ.restrict A ≤ C • Measure.map e.symm (volume.restrict (e '' A)) := by
    refine Measure.le_iff.2 fun B hB => ?_
    have hBA := hB.inter hA
    have hm' := measurableSet_image e hBA (inter_subset_right.trans hAs)
    rw [Measure.restrict_apply hB, hμ _ hBA (inter_subset_right.trans hAs), Measure.smul_apply,
      Measure.map_apply_of_aemeasurable hs hB, Measure.restrict_apply' hm, smul_eq_mul]
    refine (setLIntegral_mono' hm' fun v hv => hρ v (image_mono inter_subset_right hv)).trans ?_
    rw [setLIntegral_const]
    gcongr
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨by rw [mem_preimage, e.left_inv (hAs hy.2)]; exact hy.1, mem_image_of_mem _ hy.2⟩
  refine ⟨hf.aestronglyMeasurable hA, ?_⟩
  refine (lintegral_mono' hle le_rfl).trans_lt ?_
  rw [lintegral_smul_measure, smul_eq_mul]
  exact ENNReal.mul_lt_top hC.lt_top ((lintegral_map_le _ _).trans_lt hi.2)

variable {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {σ : k →+* ℂ} {D : ℕ}

theorem continuousAt_ratVal {f : X.functionField} {y : CxPts p σ} (hf : RegAt (under y) f) :
    ContinuousAt (fun z : CxPts p σ => ratVal f z) y := by
  obtain ⟨U, hU, a, rfl⟩ := hf.exists_fnOf
  have hn := (isOpen_ptsIn (p := p) (σ := σ) U).mem_nhds (mem_ptsIn.2 hU)
  refine ((continuousOn_ev a).continuousAt hn).congr ?_
  filter_upwards [hn] with z hz
  exact (ratVal_fnOf hz _ a).symm

theorem frequently_ne_zero (hσ : Function.Injective σ) (c : AlgChart p σ D) {U : X.Opens}
    {a : Γ(X, U)} (ha : a ≠ 0) {y : CxPts p σ} (hy : y ∈ c.e.source) (hU : y ∈ ptsIn p σ U) :
    ∃ᶠ v in 𝓝 (c.e y), (ev p σ U a ∘ c.e.symm) v ≠ 0 := by
  have : IsDomain k := hσ.isDomain σ
  have hg := gen_mem (mem_ptsIn.1 hU)
  have hb : genericPoint X ∈ X.basicOpen a := (unitAt_fnOf_iff hg hg a).1
    (unitAt_genericPoint ((map_ne_zero_iff _ (fnOf_injective U hg)).2 ha))
  have h := Measure.dense_of_ae (SemiPosBir.ae_mem hσ c (U := X.basicOpen a) ⟨_, hb⟩)
  have h₁ := mem_closure_iff_frequently.1 (h (c.e y))
  refine (h₁.and_eventually ((isOpen_over c.e (isOpen_ptsIn U)).mem_nhds (mem_over c.e hy hU))).mono ?_
  rintro v ⟨h₂, h₃⟩
  exact (mem_ptsIn_basicOpen h₃.2 a).1 (h₂ h₃.1)

theorem exists_integrableOn [SecondCountableTopology (CxPts p σ)] (hσ : Function.Injective σ)
    {A B : LB X} {ψ : Weight p σ A} (hψ : ψ.IsCInf) {φ : Weight p σ B} (hφ : φ.IsCInf)
    {r : B.ι → X.functionFieldˣ} (hr : IsRatSec B r) (ε : ℤˣ) (c : AlgChart p σ D) {y : CxPts p σ}
    (hy : y ∈ c.e.source) : ∃ O ∈ 𝓝 y, IntegrableOn (logNorm φ r)
      (offSupp p σ (divOfRatSec φ.isLB hr) ∩ O) (ψ.chernPart D ε) := by
  set i := pick φ.isLB y
  have hi : y ∈ ptsIn p σ (B.U i) := mem_pick _ y
  have hyU := c.source_subset hy
  have hg := gen_mem (mem_ptsIn.1 hyU)
  have : Nonempty c.U := ⟨⟨_, hg⟩⟩
  have := functionField_isFractionRing_of_isAffineOpen X c.U c.affine
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective (A := Γ(X, c.U)) (r i : X.functionField)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  change fnOf c.U hg a / fnOf c.U hg b = _ at hab
  have hb1 : fnOf c.U hg b ≠ 0 := (map_ne_zero_iff _ (fnOf_injective _ hg)).2 hb0
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_div] at hab
    exact (r i).ne_zero hab.symm
  have hT := (isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) c.U)).mem_nhds (mem_over c.e hy hyU)
  have hd (s : Γ(X, c.U)) : ∀ᶠ v in 𝓝 (c.e y), DifferentiableAt ℂ (ev p σ c.U s ∘ c.e.symm) v :=
    (c.holo _ s).eventually_differentiableAt hT
  obtain ⟨δ, hδ, hae, hint⟩ := exists_integrableOn_log_norm_div volume (hd a) (hd b)
    (frequently_ne_zero hσ c ha0 hy hyU) (frequently_ne_zero hσ c hb0 hy hyU)
  have hT' := (isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (B.U i))).mem_nhds (mem_over c.e hy hi)
  obtain ⟨η, hη, hηs⟩ := nhds_basis_closedBall.mem_iff.1 (inter_mem hT' (ball_mem_nhds _ hδ))
  have hcont : ContinuousOn (fun v => c.chernDens ψ (c.e.symm v)) c.e.target :=
    continuousOn_const.mul (Complex.continuous_re.comp_continuousOn
      ((Continuous.matrix_det continuous_id).comp_continuousOn
        ((GlobalTheory.MixDens.chernMat_isForm k X p σ D _ ψ hψ).2.1 c)))
  obtain ⟨C, hC⟩ := (isCompact_closedBall (c.e y) η).exists_bound_of_continuousOn
    (hcont.mono fun v hv => (hηs hv).1.1)
  set O := c.e.source ∩ c.e ⁻¹' ball (c.e y) η
  have hO : IsOpen O := c.e.continuousOn.isOpen_inter_preimage c.e.open_source isOpen_ball
  set S := offSupp p σ (divOfRatSec φ.isLB hr) ∩ O
  have hS : IsOpen S := (isOpen_offSupp _).inter hO
  have hSs : S ⊆ c.e.source := fun z hz => hz.2.1
  have him : c.e '' S ⊆ closedBall (c.e y) η := by
    rintro _ ⟨z, hz, rfl⟩
    exact ball_subset_closedBall hz.2.2
  have hSi (z) (hz : z ∈ S) : z ∈ ptsIn p σ (B.U i) := by
    have := (hηs (him (mem_image_of_mem _ hz))).1.2
    rwa [mem_preimage, c.e.left_inv (hSs hz)] at this
  have hm := measurableSet_image c.e hS.measurableSet hSs
  refine ⟨O, hO.mem_nhds ⟨hy, mem_ball_self hη⟩, integrableOn_of_chart c.e
    (fun A hA hAs => Weight.chernPart_apply hψ ε c hA hAs) hS.measurableSet hSs
    (C := ENNReal.ofReal C) ENNReal.ofReal_ne_top (fun v hv => ENNReal.ofReal_le_ofReal ?_) ?_ ?_⟩
  · have h := hC v (him hv)
    rw [Real.norm_eq_abs, abs_le] at h
    rcases Int.units_eq_one_or ε with rfl | rfl
    · simpa using h.2
    · simpa [neg_le] using h.1
  · refine ContinuousOn.congr (f := fun z => Real.log ‖ratVal (r i : X.functionField) z‖ - φ.φ i z / 2)
      (fun z hz => ContinuousAt.continuousWithinAt ?_) fun z hz => logNorm_eq φ hr hz.1 (hSi z hz)
    have hu := hr.unitAt φ.isLB hz.1 (hSi z hz)
    exact ((continuousAt_ratVal hu.regAt).norm.log (norm_ne_zero_iff.2 (ratVal_ne_zero hu))).sub
      ((hφ i z (hSi z hz)).continuousAt.div_const 2)
  · have hsub : c.e '' S ⊆ ball (c.e y) δ := fun v hv => (hηs (him hv)).2
    have h₁ : IntegrableOn (fun v => (φ.φ i ∘ c.e.symm) v / 2) (c.e '' S) :=
      (((((contDiffOn_chart (hφ i) c).continuousOn.mono fun v hv => (hηs hv).1).div_const
        2).integrableOn_compact (isCompact_closedBall _ _)).mono_set him)
    refine ((hint.mono_set hsub).sub h₁).congr ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hae, ae_restrict_mem hm] with v hv hv'
    obtain ⟨z, hz, rfl⟩ := hv'
    have hzU := c.source_subset (hSs hz)
    have hu := hr.unitAt φ.isLB hz.1 (hSi z hz)
    have e := ratVal_mul hu.regAt (regAt_fnOf (mem_ptsIn.1 hzU) hg b)
    rw [← hab, div_mul_cancel₀ _ hb1, hab, ratVal_fnOf hzU, ratVal_fnOf hzU] at e
    simp only [Function.comp_apply, Pi.sub_apply, c.e.left_inv (hSs hz)] at hv ⊢
    rw [logNorm_eq φ hr hz.1 (hSi z hz), e, mul_div_cancel_right₀ _ hv.2]

theorem archIntegrable : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {D : ℕ}, GlobalTheory.CxForm.IsRegVar p D → ∀ (M N : HermLB p) {r : N.B.ι → X.functionFieldˣ} (hr : IsRatSec N.B r),
      M.ArchIntegrable N D hr := by
  intro k _ X _ p D hX M N r hr σ
  have := hX.toIsArithVar.compactSpace σ
  have := CxPts.secondCountableTopology_of_isProjOver σ hX.isProjOver
  obtain ⟨R⟩ := RegGenSmooth.genSmooth hX.toIsArithVar hX.regular σ
  have hσ : Function.Injective σ := ChernNull.injective_of_arithVar hX.toIsArithVar σ
  have key (ε : ℤˣ) : IntegrableOn (logNorm (N.φ σ) r) (offSupp p σ (N.div hr))
      ((M.φ σ).chernPart D ε) := by
    have h (y : CxPts p σ) : ∃ O ∈ 𝓝 y, IntegrableOn (logNorm (N.φ σ) r)
        (offSupp p σ (N.div hr) ∩ O) ((M.φ σ).chernPart D ε) :=
      have ⟨_, hi⟩ := R.cover y
      exists_integrableOn hσ (M.cInf σ) (N.cInf σ) hr ε _ hi
    choose O hO hint using h
    obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover O fun y _ => hO y
    refine ((integrableOn_finset_iUnion (s := t)).2 fun y _ => hint y).mono_set fun z hz => ?_
    obtain ⟨y, hy, hz'⟩ := mem_iUnion₂.1 (ht (mem_univ z))
    exact mem_iUnion₂.2 ⟨y, hy, hz, hz'⟩
  exact ⟨key 1, key (-1)⟩

end GlobalTheory.LogNormInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AxesVanishingDegreeOneExtension
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem axesE1_of_axesO1 : AxesVanishingStructureSheafDegOne → AxesVanishingExtendedDegOne := by
  intro hO R₀ R₁ _ _ _ q hq A _ g hab hsm c h₁ h₂
  obtain ⟨B, hB, pr, pr', habB, hsmB, hp, hp', -, -, -, hl, hr⟩ :=
    GlobalTheory.T.exists_abelianScheme_baseChange_and_square R₀ R₁ A g hab hsm
  letI : GrpObj B := hB
  obtain ⟨e, he⟩ := GlobalTheory.T.h1_structure_base_change_extension R₀ R₁ q hq
  set c₁ := (e _ _ _ _ _ hp').symm c with hc₁
  have hc : e _ _ _ _ _ hp' c₁ = c := by simp [hc₁]
  have hl' : IsPullO (overW (lift (𝟙 B) 1)) c₁ 0 := by
    refine he _ _ _ _ _ hp' _ _ _ _ _ hp _ _ (overW (lift (𝟙 A) 1)) (overW (lift (𝟙 B) 1)) hl c₁ 0 ?_
    rw [hc, map_zero]; exact h₁
  have hr' : IsPullO (overW (lift 1 (𝟙 B))) c₁ 0 := by
    refine he _ _ _ _ _ hp' _ _ _ _ _ hp _ _ (overW (lift 1 (𝟙 A))) (overW (lift 1 (𝟙 B))) hr c₁ 0 ?_
    rw [hc, map_zero]; exact h₂
  have h0 : c₁ = 0 := hO R₁ B g habB hsmB c₁ hl' hr'
  rw [← hc, h0, map_zero]

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSendsClosedFibreGenericPointDvrStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_sends_closedFibre_genericPoint_dvr : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → π y' = y := by
  first | exact @GlobalTheory.Desc.GaussBC.apply_eq_of_closedFibre_dim_one | exact GlobalTheory.Desc.GaussBC.apply_eq_of_closedFibre_dim_one | (intros; apply GlobalTheory.Desc.GaussBC.apply_eq_of_closedFibre_dim_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BertiniCoordinateStrataEtaleChartCotangent
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
namespace GlobalTheory.StrataBertini

theorem isLocalization_atPrime_quotient {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]
    (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime S p] (I : Ideal A) (hI : I ≤ p)
    [(p.map (Ideal.Quotient.mk I)).IsPrime] :
    IsLocalization.AtPrime (S ⧸ I.map (algebraMap A S)) (p.map (Ideal.Quotient.mk I)) := by
  constructor
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨x, hx⟩
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    have ha : a ∉ p := fun h => hx (Ideal.mem_map_of_mem _ h)
    simp only [Ideal.Quotient.algebraMap_quotient_map_quotient]
    exact (IsLocalization.map_units S (⟨a, ha⟩ : p.primeCompl)).map _
  · intro z
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj p.primeCompl w
    refine ⟨⟨Ideal.Quotient.mk I a, ⟨Ideal.Quotient.mk I s, ?_⟩⟩, ?_⟩
    · exact fun hs => s.2 ((Ideal.mem_quotient_iff_mem hI).1 hs)
    · simp only [Ideal.Quotient.algebraMap_quotient_map_quotient]
      rw [← map_mul, h]
  · intro x y hxy
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    simp only [Ideal.Quotient.algebraMap_quotient_map_quotient, Ideal.Quotient.eq, ← map_sub] at hxy
    rw [IsLocalization.mem_map_algebraMap_iff p.primeCompl S] at hxy
    obtain ⟨⟨⟨i, hi⟩, m⟩, hm⟩ := hxy
    rw [← map_mul, IsLocalization.eq_iff_exists p.primeCompl S] at hm
    obtain ⟨c, hc⟩ := hm
    refine ⟨⟨Ideal.Quotient.mk I (c * m), ?_⟩, ?_⟩
    · exact fun hs => (p.primeCompl.mul_mem c.2 m.2) ((Ideal.mem_quotient_iff_mem hI).1 hs)
    · show Ideal.Quotient.mk I (↑c * ↑m) * Ideal.Quotient.mk I a = Ideal.Quotient.mk I (↑c * ↑m) * Ideal.Quotient.mk I b
      rw [← sub_eq_zero, ← mul_sub, ← map_sub, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      have : (↑c * ↑m * (a - b) : A) = ↑c * i := by linear_combination hc
      rw [this]
      exact I.mul_mem_left _ hi

end GlobalTheory.StrataBertini

namespace GlobalTheory.StrataBertini

open IsLocalRing in
theorem linearIndependent_option_cotangent {S : Type*} [CommRing S] [IsLocalRing S] {J : Type*}
    [Fintype J] (w : Option J → S) (hw : ∀ j, w j ∈ maximalIdeal S)
    (hind : LinearIndependent (ResidueField S)
      (fun j : J => ((maximalIdeal S).toCotangent ⟨w (some j), hw (some j)⟩ : CotangentSpace S)))
    (hnot : w none ∉ maximalIdeal S ^ 2 ⊔ Ideal.span (Set.range (fun j : J => w (some j)))) :
    LinearIndependent (ResidueField S)
      (fun j : Option J => ((maximalIdeal S).toCotangent ⟨w j, hw j⟩ : CotangentSpace S)) := by
  rw [linearIndependent_option]
  refine ⟨hind, fun hmem => hnot ?_⟩
  rw [Submodule.mem_span_range_iff_exists_fun] at hmem
  obtain ⟨c, hc⟩ := hmem
  choose b hb using fun j => IsLocalRing.residue_surjective (c j)
  have hc' : ∑ j, b j • (maximalIdeal S).toCotangent ⟨w (some j), hw (some j)⟩ =
      (maximalIdeal S).toCotangent ⟨w none, hw none⟩ := by
    rw [← hc]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Function.comp_apply, ← hb j, ← IsLocalRing.ResidueField.algebraMap_eq, algebraMap_smul]
  have h0 : (maximalIdeal S).toCotangent
      (⟨w none, hw none⟩ - ∑ j, b j • ⟨w (some j), hw (some j)⟩) = 0 := by
    rw [map_sub, map_sum]
    simp only [map_smul]
    rw [hc', sub_self]
  rw [Ideal.toCotangent_eq_zero] at h0
  have h1 : w none = (w none - ∑ j, b j * w (some j)) + ∑ j, b j * w (some j) := by ring
  rw [h1]
  refine Submodule.add_mem_sup ?_ ?_
  · simpa using h0
  · exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)

end GlobalTheory.StrataBertini

namespace GlobalTheory.StrataBertini

open IsLocalRing in
theorem key (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ)
    [SmoothOfRelativeDimension n q] (U : Y.Opens) (z : Fin n → Γ(Y, U)) (hfr : IsFrame (dOn q z))
    (ι : Type) [Fintype ι] (f : ι → Γ(Y, U)) (J : Finset (Fin n)) :
    ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 →
      ∀ (y : Y) (hy : y ∈ U), (∃ i, y ∈ Y.basicOpen (f i)) →
      (∀ j : J, Y.presheaf.germ U y hy (z j) ∈ maximalIdeal (Y.presheaf.stalk y)) →
      Y.presheaf.germ U y hy (∑ i, algX q U (u i) * f i) ∈ maximalIdeal (Y.presheaf.stalk y) →
      Y.presheaf.germ U y hy (∑ i, algX q U (u i) * f i) ∉
        maximalIdeal (Y.presheaf.stalk y) ^ 2 ⊔
          Ideal.span (Set.range (fun j : J => Y.presheaf.germ U y hy (z j))) := by
  have hU : IsAffineOpen U := hfr.affine
  set I : Ideal Γ(Y, U) := Ideal.span (z '' (J : Set (Fin n))) with hIdef
  letI : Algebra ℂ (Γ(Y, U) ⧸ I) := ((Ideal.Quotient.mk I).comp (algX q U)).toAlgebra
  haveI : Algebra.Smooth ℂ (Γ(Y, U) ⧸ I) := GlobalTheory.T.smooth_coordinateStratum_etaleChart Y q n U z hfr J
  obtain ⟨Q1, hQ1, hQ1u⟩ :=
    GlobalTheory.bertini_cotangent_independent ℂ (Γ(Y, U) ⧸ I) (fun i => Ideal.Quotient.mk I (f i)) 1
  have hinj : Function.Injective (Prod.snd : Fin 1 × ι → ι) :=
    fun a b h => Prod.ext (Subsingleton.elim _ _) h
  refine ⟨MvPolynomial.rename Prod.snd Q1, fun h0 => hQ1 (MvPolynomial.rename_injective _ hinj
    (by rw [h0, map_zero])), ?_⟩
  intro u hu y hy hf hz ht
  have hu' : MvPolynomial.eval (u ∘ Prod.snd) Q1 ≠ 0 := by rwa [MvPolynomial.eval_rename] at hu
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) :=
    TopCat.Presheaf.algebra_section_stalk Y.presheaf ⟨y, hy⟩
  set p := (hU.primeIdealOf ⟨y, hy⟩).asIdeal with hpdef
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) p := hU.isLocalization_stalk ⟨y, hy⟩
  have hgerm : ∀ a, algebraMap Γ(Y, U) (Y.presheaf.stalk y) a = Y.presheaf.germ U y hy a :=
    fun a => rfl
  have hpm : ∀ a, a ∈ p ↔ Y.presheaf.germ U y hy a ∈ maximalIdeal (Y.presheaf.stalk y) := by
    intro a
    rw [← IsLocalization.AtPrime.comap_maximalIdeal (Y.presheaf.stalk y) p, ← hgerm]
    rfl
  have hIp : I ≤ p := Ideal.span_le.2 (by
    rintro _ ⟨j, hj, rfl⟩
    exact (hpm _).2 (hz ⟨j, hj⟩))
  haveI : (p.map (Ideal.Quotient.mk I)).IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rw [Ideal.mk_ker]; exact hIp)
  set IS := I.map (algebraMap Γ(Y, U) (Y.presheaf.stalk y)) with hISdef
  have hISm : IS ≤ maximalIdeal (Y.presheaf.stalk y) :=
    Ideal.map_le_iff_le_comap.2 (fun a ha => (hpm a).1 (hIp ha))
  haveI : Nontrivial (Y.presheaf.stalk y ⧸ IS) :=
    Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hISm)
  haveI : IsLocalRing (Y.presheaf.stalk y ⧸ IS) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk IS) Ideal.Quotient.mk_surjective
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y ⧸ IS) (p.map (Ideal.Quotient.mk I)) :=
    isLocalization_atPrime_quotient p I hIp
  have hmk : ∀ a ∈ maximalIdeal (Y.presheaf.stalk y),
      Ideal.Quotient.mk IS a ∈ maximalIdeal (Y.presheaf.stalk y ⧸ IS) := by
    intro a ha
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hun
    obtain ⟨c, hc⟩ := hun.exists_right_inv
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    rw [← map_mul, ← map_one (Ideal.Quotient.mk IS), Ideal.Quotient.eq] at hc
    have h1 : a * c' ∈ maximalIdeal (Y.presheaf.stalk y) := Ideal.mul_mem_right _ _ ha
    have h2 := Ideal.sub_mem _ h1 (hISm hc)
    rw [sub_sub_cancel] at h2
    exact (maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h2)
  have hfi : ∃ i, Ideal.Quotient.mk I (f i) ∉ p.map (Ideal.Quotient.mk I) := by
    obtain ⟨i, hi⟩ := hf
    refine ⟨i, ?_⟩
    rw [Ideal.mem_quotient_iff_mem hIp, hpm]
    exact fun h => ((IsLocalRing.mem_maximalIdeal _).1 h) ((Y.mem_basicOpen _ _ hy).1 hi)
  have htR : algebraMap (Γ(Y, U) ⧸ I) (Y.presheaf.stalk y ⧸ IS)
      (∑ i, (u ∘ Prod.snd) ((0 : Fin 1), i) • Ideal.Quotient.mk I (f i)) =
      Ideal.Quotient.mk IS (Y.presheaf.germ U y hy (∑ i, algX q U (u i) * f i)) := by
    rw [← hgerm, map_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.smul_def, map_mul, map_mul, map_mul]
    rfl
  have hli := hQ1u (u ∘ Prod.snd) hu' (p.map (Ideal.Quotient.mk I)) (Y.presheaf.stalk y ⧸ IS) hfi
  have hmemR : algebraMap (Γ(Y, U) ⧸ I) (Y.presheaf.stalk y ⧸ IS)
      (∑ i, (u ∘ Prod.snd) ((0 : Fin 1), i) • Ideal.Quotient.mk I (f i)) ∈
      maximalIdeal (Y.presheaf.stalk y ⧸ IS) := by
    rw [htR]; exact hmk _ ht
  have hne := hli.ne_zero ⟨0, hmemR⟩
  rw [Ne, Ideal.toCotangent_eq_zero] at hne
  intro hmem2
  apply hne
  show algebraMap (Γ(Y, U) ⧸ I) (Y.presheaf.stalk y ⧸ IS)
      (∑ i, (u ∘ Prod.snd) ((0 : Fin 1), i) • Ideal.Quotient.mk I (f i)) ∈ _
  rw [htR]
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hmem2
  have hbI : b ∈ IS := by
    refine (Ideal.span_le.2 ?_) hb
    rintro _ ⟨j, rfl⟩
    exact Ideal.mem_map_of_mem (algebraMap Γ(Y, U) (Y.presheaf.stalk y)) (Ideal.subset_span ⟨j, j.2, rfl⟩)
  rw [← hab, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hbI, add_zero]
  have hma : Ideal.Quotient.mk IS a ∈ (maximalIdeal (Y.presheaf.stalk y)).map (Ideal.Quotient.mk IS) ^ 2 := by
    rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ ha
  exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.2 hmk) 2 hma

end GlobalTheory.StrataBertini

namespace GlobalTheory.StrataBertini

theorem bertini_strata_cotangent : ∀ (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp ℂ) (n : ℕ) [SmoothOfRelativeDimension n q], ∀ (U : Y.Opens) (z : Fin n → Γ(Y, U)), IsFrame (dOn q z) → ∀ (ι : Type) [Fintype ι] (f : ι → Γ(Y, U)), ∃ Q : MvPolynomial ι ℂ, Q ≠ 0 ∧ ∀ u : ι → ℂ, MvPolynomial.eval u Q ≠ 0 → ∀ (y : Y) (hy : y ∈ U), (∃ i, y ∈ Y.basicOpen (f i)) → ∀ (J : Finset (Fin n)) (h : ∀ j : Option J, Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j) ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)), LinearIndependent (IsLocalRing.ResidueField (Y.presheaf.stalk y)) (fun j : Option J => ((IsLocalRing.maximalIdeal (Y.presheaf.stalk y)).toCotangent ⟨(fun j : Option J => Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j)) j, h j⟩ : IsLocalRing.CotangentSpace (Y.presheaf.stalk y))) := by
  intro Y _ _ q n _ U z hfr ι _ f
  choose Q hQ0 hQ using fun J : Finset (Fin n) => key Y q n U z hfr ι f J
  refine ⟨∏ J, Q J, Finset.prod_ne_zero_iff.2 fun J _ => hQ0 J, fun u hu y hy hf J h => ?_⟩
  rw [map_prod] at hu
  have huJ := Finset.prod_ne_zero_iff.1 hu J (Finset.mem_univ _)
  exact linearIndependent_option_cotangent
    (fun j : Option J => Y.presheaf.germ U y hy (j.elim (∑ i, algX q U (u i) * f i) fun j => z j)) h
    (GlobalTheory.T.linearIndependent_cotangent_of_isTopFormFrame_of_vanishing Y q n U z hfr y hy J (fun j => h (some j)))
    (hQ J u huJ y hy hf (fun j => h (some j)) (h none))

end GlobalTheory.StrataBertini
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgebraPullbackTwoVariablesResCocycleEq
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

theorem Dat.fv_add_h_res {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {p : ℕ} {G : PDivGroup p R}
    {t : G.TorsionTower A} {c : primDR A} (d : Dat t c) (n : ℕ) (D : Type) [CommRing D] [Algebra R D]
    (φ : G.A n →ₐ[R] D) :
    fv d.f (G.A (n + 1)) D (φ.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) (t.y (n + 1)) +
      (φ.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) (d.h (n + 1)) = fv d.f (G.A n) D φ (t.y n) + φ (d.h n) := by
  have hc := (_root_.GlobalTheory.T.crystallineCocycleOnPoints_isCocycle_and_eval_eq R A d.f).1 (G.A (n + 1)) (G.A n) D
    (G.res n : G.A (n + 1) →ₐ[R] G.A n) φ (t.y (n + 1)) (sm_whole _)
  rw [hc, t.res n, d.res n, AlgHom.comp_apply, map_sub]
  simp only [BialgHom.coe_toAlgHom]
  abel

theorem Dat.pullTwo_res_coc (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (p : ℕ) (G : PDivGroup p R)
    (t : G.TorsionTower A) (c : primDR A) (d : Dat t c) (n : ℕ) :
    pullbackTwo (G.res n) (d.coc (n + 1)) = d.coc n := by

  let L : G.A n →ₐ[R] G.A n ⊗[R] G.A n := Algebra.TensorProduct.includeLeft
  let Rt : G.A n →ₐ[R] G.A n ⊗[R] G.A n := Algebra.TensorProduct.includeRight
  have hres : ∀ u : G.A (n + 1) ⊗[R] G.A (n + 1), pullbackTwo (G.res n) u =
      Algebra.TensorProduct.lift (L.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n))
        (Rt.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) (fun _ _ ↦ Commute.all _ _) u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [L, Rt]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hid : ∀ u : G.A n ⊗[R] G.A n,
      Algebra.TensorProduct.lift L Rt (fun _ _ ↦ Commute.all _ _) u = u := by
    intro u
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp [L, Rt]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hmul : (toConv (L.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n)) *
      toConv (Rt.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n))).ofConv =
      (toConv L * toConv Rt).ofConv.comp (G.res n : G.A (n + 1) →ₐ[R] G.A n) :=
    (AlgHom.convMul_comp_bialgHom_distrib (toConv L) (toConv Rt) (G.res n)).symm
  rw [hres, _root_.GlobalTheory.T.cocycle_tensorLift_apply_eq_twoPointValue, hmul, d.fv_add_h_res n, d.fv_add_h_res n, d.fv_add_h_res n]
  conv_rhs => rw [← hid (d.coc n), _root_.GlobalTheory.T.cocycle_tensorLift_apply_eq_twoPointValue]
  simp only [← spOver_comp, Category.assoc, t.res]

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedFlagTriangularFrameStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical
open GlobalTheory.FlagCell GlobalTheory.FlagConnect

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carried_flag_triangular_frame : ∀ (B Y T : Scheme.{0}) (π : Y ⟶ B) (ι : Type) (r : ι → ℕ) (E : ι → B.Modules) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (r a)), Carries π E r fl g' g w fl' → ∀ (U : B.Opens) (a : ι) (e : Fin (r a) → Γ(E a, U)) (V : Y.Opens) (hV : V ≤ π ⁻¹ᵁ U) (M : Matrix (Fin (r a)) (Fin (r a)) Γ(Y, V)) (V' : T.Opens) (h : V' ≤ g' ⁻¹ᵁ V) (h' : V' ≤ g ⁻¹ᵁ U), Spans (fl a) V (pullCol π e hV M) → Spans (fl' a) V' (pullCol g e h' (M.map (g'.appLE V V' h).hom)) := by
  first | exact @GlobalTheory.FlagCell.spans_pullCol_of_carries | exact GlobalTheory.FlagCell.spans_pullCol_of_carries | (intros; apply GlobalTheory.FlagCell.spans_pullCol_of_carries <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CarriedSectionsCrossRelationOfHomStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two GlobalTheory.FieldBaseChange
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.carriedSections_crossRelation_of_hom : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ D₂ : DegData R I) (A₁ A₂ : PolAV (Sp (FractionRing R))) (G₁ G₂ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (a : G₁ ⟶ G₂) (c : A₁.A ⟶ A₂.A), Gen₀ U₁ U₂ a c → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (w₁ : W0 U₁) (w₂ : W0 U₂), w₁.IsGen → w₂.IsGen → ∀ (j j' : ℕ) (t₁ t₂ : SecA A₂ F j) (t₁' t₂' : SecA A₁ F j') (σ₁ σ₂ : U₂.SecGF F j) (σ₁' σ₂' : U₁.SecGF F j'), MixedConv.Carried w₂ j t₁ σ₁ → MixedConv.Carried w₂ j t₂ σ₂ → MixedConv.Carried w₁ j' t₁' σ₁' → MixedConv.Carried w₁ j' t₂' σ₂' → CrossH c t₁ t₂ t₁' t₂' → ∀ (y : (UnifPre.GF (G := G₁) F).left) (J₁ J₂), Good U₁.LG.L y J₁ → Good U₂.LG.L y J₂ → sval σ₁ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y J₂ * sval σ₂' (𝟙 _) y J₁ = sval σ₂ (TFK (R := R) F ◁ (Over.pullback (jK R)).map a).left y J₂ * sval σ₁' (𝟙 _) y J₁ := by
  first | exact @GlobalTheory.Mum.Two.carried_cross_of_hom | exact GlobalTheory.Mum.Two.carried_cross_of_hom | (intros; apply GlobalTheory.Mum.Two.carried_cross_of_hom <;> assumption)
end

