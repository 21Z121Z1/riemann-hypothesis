import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0337
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0347
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0274
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralConjInnerMulInnerOfIsEmptyEquiv
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0858
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0991
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0989
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0988
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0990
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1260
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0223
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1263
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1248
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankOfMulEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1265
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantPositivePeterssonForm
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU
open MeasureTheory

namespace GlobalTheory.DefU.Petersson

theorem topology_facts (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    T2Space (UA E n) ∧ LocallyCompactSpace (UA E n) ∧ SecondCountableTopology (UA E n) ∧ DiscreteTopology (ratU E n) := by
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E n
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL (E := E) (a := n)
  refine ⟨inferInstance, (GlobalTheory.DefU.LocAdm.isClosed_UA (E := E) (n := n)).isClosedEmbedding_subtypeVal.locallyCompactSpace,
    (Topology.IsEmbedding.subtypeVal (p := fun g : GA E n => g ∈ UA E n)).secondCountableTopology, ?_⟩
  have hm : ∀ x : ratU E n, ((x : UA E n) : GA E n) ∈ latticeGL E n := fun x => by
    obtain ⟨δ, hδ⟩ := x.2
    have h := GlobalTheory.CuspRep.CuspidalL2GL.ratGL_mem_latticeGL (E := E) δ
    rw [hδ] at h
    exact h
  let f : ratU E n → latticeGL E n := fun x => ⟨_, hm x⟩
  have hf : Continuous f := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  have hi : Function.Injective f := fun x y h =>
    Subtype.ext (Subtype.ext (congrArg (fun z : latticeGL E n => (z : GA E n)) h))
  exact DiscreteTopology.of_continuous_injective hf hi

theorem exists_isOpen_isCompact_finU (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    ∃ K : Subgroup (finU E n), IsOpen (K : Set (finU E n)) ∧ IsCompact (K : Set (finU E n)) := by
  haveI := GlobalTheory.DefU.LocAdm.t2Space_adelicGL_cmField (E := E) (n := n)
  obtain ⟨U0, hU0o, hU0c⟩ := GlobalTheory.GLIntegral.exists_isOpen_isCompact E n
  let p : finU E n →* GL (Fin n) (Af E) :=
    (GeneralLinearGroup.map (pFin E)).comp ((UA E n).subtype.comp (finU E n).subtype)
  have hp : Continuous p := continuous_map_pFin.comp (continuous_subtype_val.comp continuous_subtype_val)
  have hKo : IsOpen (U0.comap p : Set (finU E n)) := hU0o.preimage hp
  have hfin : ∀ x : UA E n, x ∈ finU E n ↔
      finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n) := by
    intro x
    constructor
    · intro hx
      have h1 : GeneralLinearGroup.map (pInf E) (x : GA E n) = 1 := hx
      exact ga_ext (by rw [pInf_finGL, h1]) (by rw [pFin_finGL])
    · intro hx
      change GeneralLinearGroup.map (pInf E) (x : GA E n) = 1
      rw [← hx, pInf_finGL]
  have hc : IsClosed ((finU E n : Subgroup (UA E n)) : Set (UA E n)) := by
    have e : ((finU E n : Subgroup (UA E n)) : Set (UA E n)) =
        {x : UA E n | finGL E n (GeneralLinearGroup.map (pFin E) (x : GA E n)) = (x : GA E n)} :=
      Set.ext hfin
    rw [e]
    exact isClosed_eq (GlobalTheory.DefU.LocAdm.continuous_finGL.comp (continuous_map_pFin.comp continuous_subtype_val))
      continuous_subtype_val
  have hι : Topology.IsClosedEmbedding (fun x : finU E n => ((x : UA E n) : GA E n)) :=
    GlobalTheory.DefU.LocAdm.isClosed_UA.isClosedEmbedding_subtypeVal.comp hc.isClosedEmbedding_subtypeVal
  exact ⟨U0.comap p, hKo, IsCompact.of_isClosed_subset
    (hι.isCompact_preimage (hU0c.image GlobalTheory.DefU.LocAdm.continuous_finGL))
    (Subgroup.isClosed_of_isOpen _ hKo) fun x hx => ⟨p x, hx, (hfin x).1 x.2⟩⟩

theorem exists_compact_cover (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) :
    ∃ C : Set (UA E n), IsCompact C ∧ ∀ g, ∃ γ ∈ ratU E n, ∃ c ∈ C, g = γ * c := by
  classical
  obtain ⟨K, hKo, hKc⟩ := exists_isOpen_isCompact_finU E n
  obtain ⟨S, hS⟩ := GlobalTheory.T.definiteUnitary_classSet_finite E n K hKo
  haveI : CompactSpace (Matrix.unitaryGroup (Fin n) ℂ) := GlobalTheory.compactSpace_unitaryGroup (Fin n) ℂ
  haveI : ∀ v : InfinitePlace E, CompactSpace (embU n v.embedding) := fun v => by
    obtain ⟨e, -⟩ := GlobalTheory.T.archimedeanUnitaryPoints_equiv_unitaryGroup E n v.embedding
    exact e.toHomeomorph.symm.compactSpace
  let P : (∀ v : InfinitePlace E, embU n v.embedding) → UA E n :=
    fun y => (Finset.univ.toList.map fun v => (y v : UA E n)).prod
  have hP : Continuous P :=
    continuous_list_prod _ fun v _ => continuous_subtype_val.comp (continuous_apply v)
  have hPc : IsCompact (Set.range P) := isCompact_range hP
  have hKc' : IsCompact (Subtype.val '' (K : Set (finU E n))) := hKc.image continuous_subtype_val
  refine ⟨_, (S.finite_toSet.isCompact.mul hPc).mul hKc', fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, x, hx, k, hk, e⟩ := hS g
  obtain ⟨y, hy, -, hyx⟩ := GlobalTheory.T.definiteUnitaryInfinitePoint_eq_list_prod_placeParts E n x hx
  refine ⟨γ, hγ, s * x * k, Set.mul_mem_mul (Set.mul_mem_mul hs ⟨fun v => ⟨y v, hy v⟩, hyx⟩) ⟨k, hk, rfl⟩, ?_⟩
  rw [e, mul_assoc, mul_assoc, mul_assoc]

end GlobalTheory.DefU.Petersson

namespace GlobalTheory.DefU.Petersson

set_option maxHeartbeats 1600000 in

theorem exists_invariant_pos_form : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ),
    ∃ B : GlobalTheory.DefU.autU E n →ₗ⋆[ℂ] GlobalTheory.DefU.autU E n →ₗ[ℂ] ℂ, (∀ u v, star (B u v) = B v u) ∧ (∀ v, 0 ≤ (B v v).re) ∧
      (∀ v, B v v = 0 → v = 0) ∧ ∀ g u v, B (GlobalTheory.DefU.autRep E n g u) (GlobalTheory.DefU.autRep E n g v) = B u v := by
  intro E _ _ _ n
  classical
  obtain ⟨h1, h2, h3, h4⟩ := topology_facts E n
  obtain ⟨C, hC, hcov⟩ := exists_compact_cover E n
  letI : MeasurableSpace (UA E n) := borel _
  haveI : BorelSpace (UA E n) := ⟨rfl⟩
  haveI : SecondCountableTopology (ratU E n) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : TopologicalSpace.SeparableSpace (ratU E n) := inferInstance
  haveI : Countable (ratU E n) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (UA E n), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨𝓕, -, h𝓕'⟩ := Formalism.IndefR.Eqv.G5.fdom_exists_all (ratU E n)
  have h𝓕 := h𝓕' μ
  have hfin : μ 𝓕 < ⊤ := by
    refine lt_of_le_of_lt ?_ (hC.measure_lt_top (μ := μ))
    rw [h𝓕.measure_eq_tsum C]
    refine le_trans (measure_mono ?_) (measure_iUnion_le _)
    intro g hg
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    exact Set.mem_iUnion.2 ⟨⟨γ, hγ⟩, ⟨c, hc, rfl⟩, hg⟩
  haveI hR : μ.IsMulRightInvariant :=
    GlobalTheory.unimodular_of_isFundamentalDomain_finite _ (ratU E n) μ 𝓕 hμ h𝓕 hfin.ne
  have hl : ∀ u : autU E n, ∀ γ ∈ ratU E n, ∀ g, u.1 (γ * g) = u.1 g := fun u γ hγ g => u.2.left γ hγ g
  have hI : ∀ u v : autU E n, IntegrableOn (fun g => star (u.1 g) * v.1 g) 𝓕 μ := by
    intro u v
    have hc : Continuous (fun g => star (u.1 g) * v.1 g) := u.2.cont.star.mul v.2.cont
    obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
    refine Measure.integrableOn_of_bounded (M := M) hfin.ne hc.aestronglyMeasurable (ae_of_all _ fun g => ?_)
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov g
    simp only [hl u γ hγ, hl v γ hγ]
    exact hM c hc
  have hright : ∀ (y : UA E n) (f : UA E n → ℂ), (∀ γ ∈ ratU E n, ∀ h, f (γ * h) = f h) →
      ∫ h in 𝓕, f (h * y) ∂μ = ∫ h in 𝓕, f h ∂μ := by
    intro y f hf
    have h' : IsFundamentalDomain (ratU E n) ((fun h => h * y) '' 𝓕) μ := by
      refine h𝓕.image_of_equiv (Equiv.mulRight y) ?_ (Equiv.refl _) ?_
      · exact (measurePreserving_mul_right μ y⁻¹).quasiMeasurePreserving
      · intro γ h
        simp [Subgroup.smul_def, mul_assoc]
    rw [h𝓕.setIntegral_eq h' (f := f) (fun γ h => hf γ γ.2 h)]
    exact ((measurePreserving_mul_right μ y).setIntegral_image_emb
      (measurableEmbedding_mulRight y) f 𝓕).symm
  let F : autU E n → autU E n → ℂ := fun u v => ∫ g in 𝓕, star (u.1 g) * v.1 g ∂μ
  let B : autU E n →ₗ⋆[ℂ] autU E n →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) F
    (fun x x' y => by
      simp only [F]
      rw [← integral_add (hI x y) (hI x' y)]
      congr 1
      funext g
      simp only [Submodule.coe_add, Pi.add_apply, star_add, add_mul])
    (fun c x y => by
      simp only [F, smul_eq_mul]
      rw [← integral_const_mul]
      congr 1
      funext g
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, star_mul', starRingEnd_apply]
      ring)
    (fun x y y' => by
      simp only [F]
      rw [← integral_add (hI x y) (hI x y')]
      congr 1
      funext g
      simp only [Submodule.coe_add, Pi.add_apply, mul_add])
    (fun c x y => by
      simp only [F, smul_eq_mul, RingHom.id_apply]
      rw [← integral_const_mul]
      congr 1
      funext g
      simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul]
      ring)
  have hB : ∀ u v, B u v = ∫ g in 𝓕, star (u.1 g) * v.1 g ∂μ := fun _ _ => rfl
  have hre : ∀ v, B v v = ((∫ g in 𝓕, ‖v.1 g‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro v
    rw [hB, ← integral_complex_ofReal]
    congr 1
    funext g
    rw [Complex.star_def, Complex.conj_mul']
    push_cast
    rfl
  refine ⟨B, fun u v => ?_, fun v => ?_, fun v h0 => ?_, fun k u v => ?_⟩
  · rw [hB, hB, Complex.star_def, ← integral_conj]
    congr 1
    funext g
    simp only [map_mul, Complex.conj_conj]
    ring
  · rw [hre, Complex.ofReal_re]
    exact integral_nonneg fun g => by positivity
  · rw [hre, Complex.ofReal_eq_zero] at h0
    have hi : IntegrableOn (fun g => ‖v.1 g‖ ^ 2) 𝓕 μ := by
      have := (hI v v).norm
      have e2 : (fun g => ‖star (v.1 g) * v.1 g‖) = fun g => ‖v.1 g‖ ^ 2 := by
        funext g
        rw [norm_mul, norm_star, sq]
      rw [e2] at this
      exact this
    have hae := (integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi).1 h0
    have := GlobalTheory.eq_zero_of_ae_fundamentalDomain_of_leftInvariant (ratU E n) μ 𝓕 h𝓕 v.1 v.2.cont (hl v) (by
      filter_upwards [hae] with g hg
      simpa using hg)
    exact Subtype.ext (funext this)
  · rw [hB, hB]
    exact hright k (fun g => star (u.1 g) * v.1 g) fun γ hγ g => by simp only [hl u γ hγ, hl v γ hγ]

end GlobalTheory.DefU.Petersson
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenCoveringChartsGenericallyFiniteField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false
noncomputable section
open scoped Classical
open GlobalTheory.ChartGlue

namespace GlobalTheory.CoverDegField

theorem exists_open_covering_charts : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → SmoothOfRelativeDimension D p → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∃ U : X.Opens, genericPoint X ∈ U ∧ (∀ y ∈ ptsIn p σ U, (PtsOver.map π hπ (spMap σ) ⁻¹' {y}).encard = (π.residueDegree (genericPoint Y) : ℕ∞)) ∧ (∀ y ∈ ptsIn p σ U, ∃ c : AlgChart p σ D, y ∈ c.e.source) ∧ (∀ z : CxPts q σ, PtsOver.map π hπ (spMap σ) z ∈ ptsIn p σ U → ∀ c : AlgChart p σ D, PtsOver.map π hπ (spMap σ) z ∈ c.e.source → ∃ c' : AlgChart q σ D, z ∈ c'.e.source ∧ ∀ w ∈ c'.e.source, PtsOver.map π hπ (spMap σ) w ∈ c.e.source ∧ c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) := by
  intro k _ X Y _ _ p q σ D hpP hqP hsm π hπ hη hδ
  haveI : SmoothOfRelativeDimension D p := hsm
  haveI : CharZero k := RingHom.charZero σ
  obtain ⟨U₁, t₁, hU₁, hx₁, ht⟩ := GlobalTheory.AlgChart.exists_etale_coords (p := p) (D := D) (genericPoint X)
  obtain ⟨U₂, hU₂, hx₂, hV₂, he₂, hf₂, hr₂⟩ := GlobalTheory.T.exists_affine_etale_finite_free_nbhd k X Y p q hpP hqP π hπ hη hδ
  obtain ⟨U, hxU, hG⟩ := GlobalTheory.CoverDeg.exists_goodCover_of_coords_of_cover p π D _ _ U₁ U₂ hU₁ hx₁ ⟨t₁, ht⟩ hU₂ hx₂ hV₂ he₂ hf₂ hr₂
  refine ⟨U, hxU, fun y hy => ?_, fun y hy => ?_, fun z hz c hc => ?_⟩
  · rw [GlobalTheory.encard_fibre_eq_encard_ringHom π hπ U hG.1 hG.2.1 σ y hy]
    exact GlobalTheory.EtaleComplexPoints.encard_complexPoints_eq_rank (π.app U).hom _ hG.2.2.2.1 hG.2.2.2.2.1 hG.2.2.2.2.2 _
  · obtain ⟨t, ht⟩ := hG.2.2.1
    obtain ⟨c, hc, -⟩ := AlgChart.exists_of_etale hG.1 t ht hy
    exact ⟨c, hc⟩
  · set y := PtsOver.map π hπ (spMap σ) z with hy
    have hyc : y ∈ ptsIn p σ c.U := c.source_subset hc
    have hpt : ∀ W : X.Opens, y ∈ ptsIn p σ W → π (z.1 (IsLocalRing.closedPoint ℂ)) ∈ W := by
      intro W hW
      have := mem_ptsIn.1 hW
      exact this
    obtain ⟨V, hV, hzV, h, hVe⟩ := GlobalTheory.CoverDeg.etale_pullback_coords π hπ D _ U hG c.U c.x c.affine c.etale _ (hpt U hz) (hpt c.U hyc)
    obtain ⟨c'', hc'', hU'', hx''⟩ := AlgChart.exists_of_etale (σ := σ) hV _ hVe (mem_ptsIn.2 hzV)
    have key : ∀ w ∈ c''.e.source, w ∈ ptsIn q σ V ∧
        ∀ a, c''.e w a = ev q σ V ((π.appLE c.U V h).hom (c.x a)) w := by
      rcases c'' with ⟨e, U', aff, x', et, ss, ae, ho⟩
      dsimp only at hU'' hx'' ⊢
      subst hU''
      have hx : x' = fun a => (π.appLE c.U U' h).hom (c.x a) := hx''
      subst hx
      exact fun w hw => ⟨ss hw, ae w hw⟩
    have hS : IsOpen (c''.e.source ∩ PtsOver.map π hπ (spMap σ) ⁻¹' c.e.source) :=
      (PtsOver.continuous_map π hπ (spMap σ)).continuousOn.isOpen_inter_preimage c''.e.open_source
        c.e.open_source
    refine ⟨c''.restr _ hS, ⟨hc'', hc'', hc⟩, fun w hw => ⟨hw.2.2, ?_⟩⟩
    have hw' : w ∈ c''.e.source := hw.1
    obtain ⟨hwV, hwe⟩ := key w hw'
    ext a
    change c''.e w a = c.e (PtsOver.map π hπ (spMap σ) w) a
    rw [hwe a, c.apply_eq _ hw.2.2 a]
    exact valR_appLE w.1 π h hwV _

end GlobalTheory.CoverDegField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfPrincipalUnitIdeleNormOne
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitTorsion

theorem principal_unit_idele_torsion : ∀ (E : Type) [Field E] [NumberField E] (t : Eˣ), Neutral.B1.diagUnits E t ∈ GlobalTheory.Mem.Chr.unitIdl E →
    (∀ φ : E →+* ℂ, ‖φ (t : E)‖ = 1) → ∃ n : ℕ, 0 < n ∧ t ^ n = 1 := by
  intro E _ _ t ht hnorm
  have hv : ∀ v : HeightOneSpectrum (𝓞 E), v.valuation E (t : E) ≤ 1 := by
    intro v
    have h1 := ht v
    have h2 : ((Neutral.B1.diagUnits E t : AdeleRing (𝓞 E) E)).2 v = ((t : E) : v.adicCompletion E) := rfl
    rw [h2, HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h1
    exact h1.le
  obtain ⟨y, hy⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one E (t : E) hv
  have hint : IsIntegral ℤ (t : E) := by
    rw [← hy]; exact y.isIntegral_coe
  obtain ⟨n, hn, hpow⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one E ℂ hint hnorm
  exact ⟨n, hn, Units.ext (by simpa using hpow)⟩

end GlobalTheory.UnitTorsion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealOneParamProductChartAdelicUnitary
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct ContDiff Topology

noncomputable section

namespace GlobalTheory.UnitChart

open GlobalTheory.Orb (archMat)

def lieU {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {X | Xᴴ * H + H * X = 0}
  add_mem' := by
    intro X Y hX hY
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hX, hY, add_zero]
  zero_mem' := by simp
  smul_mem' := by
    intro c X hX
    simp only [Set.mem_setOf_eq] at *
    rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, hX, smul_zero]

theorem exists_realLines_chart : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∃ (d : ℕ) (δ : Fin d → ℝ → GAd σ J), (∀ a, IsRealLine σ J (δ a)) ∧
      ∀ U ∈ 𝓝 (1 : GAd σ J), ∃ W ∈ 𝓝 (1 : GAd σ J), ∃ s : GAd σ J → (Fin d → ℝ), ContinuousAt s 1 ∧
        ∀ y ∈ W, ∃ u ∈ U, u ∈ finPts σ J ∧ y = (List.ofFn fun a => δ a (s y a)).prod * u := by
  intro F E _ _ _ _ _ σ h n J hJ
  classical
  let τ : ∀ w : InfinitePlace F, EmbOver E w := fun w => Classical.choice inferInstance
  let H : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ := fun w => J.map (τ w).1
  have hHu : ∀ w, IsUnit (H w).det := fun w => by
    show IsUnit (J.map (τ w).1).det
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (IsUnit.mk0 _ hJ.2).map _
  have hHh : ∀ w, (H w)ᴴ = H w := fun w => by
    ext i k
    simp only [H, conjTranspose_apply, map_apply]
    rw [← h.2.2.2, hJ.1 i k]
  let e : InfinitePlace F → ℕ := fun w => Module.finrank ℝ (lieU (H w))
  let b : ∀ w, Module.Basis (Fin (e w)) ℝ (lieU (H w)) := fun w => Module.finBasis ℝ _
  let q : (Σ w : InfinitePlace F, Fin (e w)) ≃ Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) :=
    Fintype.equivFin _
  let Zg : Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) → Matrix (Fin n) (Fin n) ℂ :=
    fun a => (b (q.symm a).1 (q.symm a).2 : Matrix (Fin n) (Fin n) ℂ)
  have hZg : ∀ a, (Zg a)ᴴ * H (q.symm a).1 + H (q.symm a).1 * Zg a = 0 := fun a => (b (q.symm a).1 (q.symm a).2).2
  have hy : ∀ a (t : ℝ), ∃ y : GArch σ J (q.symm a).1,
      archMat σ J (τ (q.symm a).1) y = NormedSpace.exp (t • Zg a) := fun a t => by
    obtain ⟨u, hu⟩ := Matrix.isUnit_exp (t • Zg a)
    have h1 := GlobalTheory.SmoothForms.exp_mem_UH (hHu (q.symm a).1) (X := t • Zg a) ((lieU (H (q.symm a).1)).smul_mem t (hZg a))
    refine ⟨(archEquiv J h (τ (q.symm a).1)).symm ⟨u, show _ * _ * _ = _ from hu ▸ h1⟩, ?_⟩
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h, MulEquiv.apply_symm_apply]
    exact hu
  choose y hy using hy
  let δ : Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) → ℝ → GAd σ J :=
    fun a t => embArch σ J (q.symm a).1 (y a t)
  let Zw : InfinitePlace F → Fin (Fintype.card (Σ w : InfinitePlace F, Fin (e w))) → Matrix (Fin n) (Fin n) ℂ :=
    fun w a => if (q.symm a).1 = w then Zg a else 0
  have hK : ∀ w a (t : ℝ), archMat σ J (τ w) (projArch σ J w (δ a t)) = NormedSpace.exp (t • Zw w a) := by
    intro w a t
    by_cases hw : (q.symm a).1 = w
    · subst hw
      simp only [δ, Zw, if_pos rfl, projArch_embArch_self, hy]
    · simp only [δ, Zw, if_neg hw, smul_zero, NormedSpace.exp_zero, projArch_embArch_ne σ J (Ne.symm hw), map_one]
  have hunit : ∀ w (g : GArch σ J w), (archMat σ J (τ w) g)ᴴ * H w * archMat σ J (τ w) g = H w := fun w g => by
    rw [GlobalTheory.Orb.archMat_eq_archEquiv J h]
    exact (archEquiv J h (τ w) g).2
  have hinj : ∀ w, Function.Injective (archMat σ J (τ w)) := fun w g g' hg =>
    (archEquiv J h (τ w)).injective (Subtype.ext (Units.ext (by
      rwa [GlobalTheory.Orb.archMat_eq_archEquiv J h, GlobalTheory.Orb.archMat_eq_archEquiv J h] at hg)))
  have hloc : ∀ w, ∃ V ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ), ∃ s : Matrix (Fin n) (Fin n) ℂ → (Fin _ → ℝ),
      ContinuousAt s 1 ∧ ∀ g ∈ V, gᴴ * H w * g = H w → g = (List.ofFn fun a => NormedSpace.exp (s g a • Zw w a)).prod := by
    intro w
    have hj : Function.Injective fun i : Fin (e w) => q ⟨w, i⟩ := fun i i' hi => by
      simpa using q.injective hi
    have hZj : ∀ i, Zw w (q ⟨w, i⟩) = (b w i : Matrix (Fin n) (Fin n) ℂ) := fun i => by
      show (if (q.symm (q ⟨w, i⟩)).1 = w then Zg (q ⟨w, i⟩) else 0) = _
      rw [if_pos (by simp)]
      show ((b (q.symm (q ⟨w, i⟩)).1 (q.symm (q ⟨w, i⟩)).2 : Matrix (Fin n) (Fin n) ℂ)) = _
      rw [q.symm_apply_apply]
    refine GlobalTheory.T.hermitian_unitary_group_one_parameter_chart n (H w) (hHh w) (hHu w) _ (e w) (Zw w) (fun i => q ⟨w, i⟩) hj ?_ ?_ ?_ ?_
    · intro a ha
      simp only [Zw]
      rw [if_neg]
      intro hw
      apply ha
      rcases hqa : q.symm a with ⟨w', i⟩
      rw [hqa] at hw
      subst hw
      have h2 := congrArg q hqa
      rw [Equiv.apply_symm_apply] at h2
      exact ⟨i, h2.symm⟩
    · intro a
      simp only [Zw]
      split_ifs with hw
      · subst hw; exact hZg a
      · simp
    · simp only [hZj]
      refine Fintype.linearIndependent_iff.2 fun c hc i => ?_
      refine Fintype.linearIndependent_iff.1 (b w).linearIndependent c (Subtype.ext ?_) i
      simpa using hc
    · intro X hX
      simp only [hZj]
      have e1 := congrArg Subtype.val ((b w).sum_repr ⟨X, hX⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at e1
      rw [← e1]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose V hV sw hsw hdec using hloc
  let gw : InfinitePlace F → GAd σ J → Matrix (Fin n) (Fin n) ℂ := fun w x => archMat σ J (τ w) (projArch σ J w x)
  have hgc : ∀ w, Continuous (gw w) := fun w =>
    (GlobalTheory.Orb.continuous_archMat σ J (τ w)).comp (continuous_projArch σ J w)
  have hg1 : ∀ w, gw w 1 = 1 := fun w => by simp [gw]
  refine ⟨_, δ, fun a => ⟨(q.symm a).1, τ _, Zg a, hZg a, fun t => ⟨y a t, rfl, hy a t⟩⟩, fun U hU => ?_⟩
  have hfc : Continuous fun x => ofFin σ J (projFin σ J x) := (continuous_ofFin σ J).comp (continuous_projFin σ J)
  refine ⟨{x | ∀ w, gw w x ∈ V w} ∩ {x | ofFin σ J (projFin σ J x) ∈ U}, ?_,
    fun x a => sw (q.symm a).1 (gw (q.symm a).1 x) a, ?_, ?_⟩
  · refine Filter.inter_mem (Filter.eventually_all.2 fun w => (hgc w).continuousAt.preimage_mem_nhds ?_)
      (hfc.continuousAt.preimage_mem_nhds ?_)
    · rw [hg1]; exact hV w
    · simpa using hU
  · exact continuousAt_pi.2 fun a =>
      (continuous_apply a).continuousAt.comp ((hsw _).comp_of_eq (hgc _).continuousAt (hg1 _))
  · intro x hx
    refine ⟨ofFin σ J (projFin σ J x), hx.2, mem_finPts.2 (projInf_ofFin _ _ _), ?_⟩
    conv_lhs => rw [← ofInf_projInf_mul_ofFin_projFin σ J x]
    congr 1
    apply GAd_ext σ J
    · intro w
      apply hinj w
      rw [projArch_ofInf, projInfArch_projInf, map_list_prod, map_list_prod, List.map_ofFn, List.map_ofFn]
      have e2 : (⇑(archMat σ J (τ w)) ∘ ⇑(projArch σ J w) ∘ fun a => δ a (sw (q.symm a).1 (gw (q.symm a).1 x) a)) =
          fun a => NormedSpace.exp (sw w (gw w x) a • Zw w a) := funext fun a => by
        simp only [Function.comp_apply]
        rw [hK]
        by_cases hw : (q.symm a).1 = w
        · subst hw; rfl
        · simp [Zw, hw]
      rw [e2]
      exact hdec w _ (hx.1 w) (hunit w _)
    · intro v
      rw [proj_ofInf, map_list_prod, List.map_ofFn]
      have e3 : (⇑(proj σ J v) ∘ fun a => δ a (sw (q.symm a).1 (gw (q.symm a).1 x) a)) = fun _ => 1 :=
        funext fun a => by simp [δ]
      rw [e3]
      simp

end GlobalTheory.UnitChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmallAmpleThroughOffStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_small_ample_through_off' : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (x z : X) (ε : ℚ), IsAmpleLB N → ¬ z ⤳ x → 0 < ε → ∃ (b : ℚ) (A : X → ℚ), 0 ≤ b ∧ b ≤ ε ∧ QNum p N b A ∧ Off A x ∧ ¬ Off A z := by
  first | exact @GlobalTheory.PairStep.exists_small_ample_through_off | exact GlobalTheory.PairStep.exists_small_ample_through_off | (intros; apply GlobalTheory.PairStep.exists_small_ample_through_off <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryCommutingOfMemNormOneTorusStatement
section
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat GlobalTheory.KapOrb
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_commuting_of_mem_normOneTorus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A) (n : ℕ) (γ : GLw n w) (ψ : B.A ≃+ (Fin n → w.adicCompletion E)), IsModelMap w e B u x γ ψ → ∀ s ∈ B.T, ∃ h : GLw n w, h ∈ UL n w ∧ h * γ = γ * h ∧ ∀ y, ψ ((s : B.A) * y) = h.val *ᵥ ψ y := by
  first | exact @GlobalTheory.KapOrb.exists_unitary_of_torus | exact GlobalTheory.KapOrb.exists_unitary_of_torus | (intros; apply GlobalTheory.KapOrb.exists_unitary_of_torus <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPieceBoundedWeightsOfQuadraticStatement
section
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_piece_bounded_weights_of_quadratic : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (s : ι → Bool) (α β α' β' : ℂ), ∃ R : ℝ, ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (F : ι → ι → Module.End ℂ M), Nontrivial M → IsGl F → (∀ a b, qop F α β a b = 0) → (∀ a b, qop (negT F) α' β' a b = 0) → LocU s F → ∃ U : Submodule ℂ M, U ≠ ⊥ ∧ UnitOn s F U ∧ ∀ a, ∀ u ∈ U, u ≠ 0 → ∀ m : ℂ, F a a u = m • u → |m.re| ≤ R := by
  first | exact @GlobalTheory.HoweR.exists_unitOn_diag_bounded | exact GlobalTheory.HoweR.exists_unitOn_diag_bounded | (intros; apply GlobalTheory.HoweR.exists_unitOn_diag_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWachModuleMapMatrixReductionCommStatement
section
open NumberField PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors Formalism.CohomologicalDescent.FrobeniusPeriodChange IsLocalRing GlobalTheory.WachPlace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_wachModule_map_matrix_reduction_comm : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (K LL : FinExt l) (hA : CaseA K LL) (T T' : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (n n' : ℕ) (γ : (H.W K 1 LL hA.2.2).Gam) (b : Module.Basis (Fin n) (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T)) (b' : Module.Basis (Fin n') (LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K))) ↥((H.W K 1 LL hA.2.2).N T')) (N : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n ↥(OL LL)) (N' : Lat (ZMod (Module.finrank ℚ_[l] ↥(K0 K))) n' ↥(OL LL)) (u : ℤ_[l]) (un : PowerSeries ↥(OL LL)) (g : LatHom T.L T'.L), IsCrys (P.PD K) T.ρ → IsCrys (P.PD K) T'.ρ → IsFrame (H.W K 1 LL hA.2.2) T γ b N → IsFrame (H.W K 1 LL hA.2.2) T' γ b' N' → ((H.W K 1 LL hA.2.2).χΓ γ : ↥(OL LL)) = algebraMap ℤ_[l] ↥(OL LL) u → IsUn l ↥(OL LL) u un → ∃ A : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Mx (PowerSeries ↥(OL LL)) n' n, IsMapMat (H.W K 1 LL hA.2.2) g b b' A ∧ ∀ i, RedHom l ((PowerSeries.map (residue ↥(OL LL))) un) ((N.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.P i).map (PowerSeries.map (residue ↥(OL LL)))) ((N'.D i).map (PowerSeries.map (residue ↥(OL LL)))) ((A i).map (PowerSeries.map (residue ↥(OL LL)))) ((A (i - 1)).map (PowerSeries.map (residue ↥(OL LL)))) := by
  first | exact @GlobalTheory.WachMap.exists_mapMat_redHom | exact GlobalTheory.WachMap.exists_mapMat_redHom | (intros; apply GlobalTheory.WachMap.exists_mapMat_redHom <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalVectorMatrixCoeffHolomorphicTypeStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extremalVector_matrixCoeff_holomorphicType : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (w : D.what₂.Tau → Fin V.rank → ℤ) (v : M.Vec), IsInfFam θ → HolShape M → WtIs M w → IsExtVec M v → HolFn (gramAt D V) (fun τ => nNeg (M.ε τ)) (x0Mat M) w (fun u => ∏ τ, ⟪(v τ : M.H τ), M.rep τ (u τ) (v τ : M.H τ)⟫_ℂ) ∧ ∀ s τ, M.rep τ (torEl (x0Mat M) s τ) (v τ : M.H τ) = (∏ a, Complex.exp ((s τ a : ℂ) * Complex.I) ^ w τ a) • (v τ : M.H τ) := by
  first | exact @GlobalTheory.HolDict.holFn_coef_extVec | exact GlobalTheory.HolDict.holFn_coef_extVec | (intros; apply GlobalTheory.HolDict.holFn_coef_extVec <;> assumption)
end

