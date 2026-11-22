import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2869
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3113
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3060
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3129
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1654
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3109
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3082
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2565
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2840
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2713
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3130
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3100
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3043
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureMapPullbackGenericallyFinite
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

theorem GlobalTheory.Mix.map_part_pull_of_genFinite : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D : ℕ), IsProjOver p → topologicalKrullDim X = (D : ℕ) → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (L : Fin D → MLine p σ) (ε : ℤˣ), Measure.map (ptMap π hπ σ) (part (fun i => (L i).pull π hπ) ε) = (π.residueDegree (genericPoint Y) : ENNReal) • part L ε := by
  intro F _ X Y _ _ p q σ D hp hD hq π hπ hgen hdeg L ε
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hp
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ hq
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hp
  haveI := CxPts.secondCountableTopology_of_isProjOver σ hq
  haveI : IsLocallyNoetherian X := by
    obtain ⟨N, i, _, rfl⟩ := hp
    have := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str F N
    exact LocallyOfFiniteType.isLocallyNoetherian (i ≫ PSpace.str F N)
  obtain ⟨U, hU, hfibU, hchU⟩ := GlobalTheory.T.exists_open_complexPoints_covering_generic_degree F X Y p q σ D hp hq π hπ hgen hdeg
  obtain ⟨U', hU', hcharts⟩ := GlobalTheory.T.exists_holomorphic_charts_genericPoint_projective F X p σ D hp hD
  set m := ptMap π hπ σ with hm_def
  set Z : Set X := ((U ⊓ U' : X.Opens) : Set X)ᶜ with hZ_def
  have hZ : IsClosed Z := (U ⊓ U').isOpen.isClosed_compl
  have hgZ : genericPoint X ∉ Z := fun h => h ⟨hU, hU'⟩
  set T : Set (CxPts p σ) := (ptsIn p σ (U ⊓ U'))ᶜ with hT_def
  have hTset : T = {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} := by
    ext y
    simp only [hT_def, hZ_def, mem_compl_iff, mem_setOf_eq, mem_ptsIn]
    rfl
  have hmT : m ⁻¹' T = {z : CxPts q σ | z.1 (IsLocalRing.closedPoint ℂ) ∈ π ⁻¹' Z} := by
    rw [hTset]
    ext z
    simp only [mem_preimage, mem_setOf_eq, hm_def, ptMap, PtsOver.map_val]
    rfl
  have hZ' : IsClosed (π ⁻¹' Z : Set Y) := hZ.preimage π.continuous
  have hgZ' : genericPoint Y ∉ (π ⁻¹' Z : Set Y) := by
    simp only [mem_preimage, hgen]
    exact hgZ
  have hm : Continuous m := PtsOver.continuous_map π hπ (spMap σ)
  refine GlobalTheory.GlueCoverNull.map_glueMeas_of_cover D (CxPts p σ) (CxPts q σ) (AlgChart p σ D) (AlgChart q σ D)
    (fun c => c.e) (fun c y => ENNReal.ofReal ((ε : ℤ) * dens L c y))
    (fun c => c.e) (fun c y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y))
    (fun i j => i.holo_trans j) ?_ (fun i j => i.holo_trans j) ?_ m hm T
    (isOpen_ptsIn _).isClosed_compl ?_ ?_ _ ?_ ?_
  · intro i j y hi hj
    rw [GlobalTheory.T.mixedChernFormDensity_change_of_chart F X p σ D L i j y hi hj, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  · intro i j y hi hj
    rw [GlobalTheory.T.mixedChernFormDensity_change_of_chart F Y q σ D _ i j y hi hj, ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  · intro c
    rw [hTset]
    exact GlobalTheory.ChernNull.chart_null_field F X p σ D Z hZ hgZ c
  · intro c
    rw [hmT]
    exact GlobalTheory.ChernNull.chart_null_field F Y q σ D _ hZ' hgZ' c
  · intro x hx
    have hx' : x ∈ ptsIn p σ (U ⊓ U') := not_not.1 hx
    exact hfibU x (mem_ptsIn_inf.1 hx').1
  · intro z hz
    have hz' := mem_ptsIn_inf.1 (not_not.1 hz : m z ∈ ptsIn p σ (U ⊓ U'))
    obtain ⟨c, hc⟩ := hcharts (m z) hz'.2
    obtain ⟨c', hzc', hw⟩ := hchU z hz'.1 c hc
    refine ⟨c, c', hzc', hc, fun w hwc' _ => ⟨(hw w hwc').2, ?_⟩⟩
    rw [GlobalTheory.T.mixedChernFormDensity_pullback_matching_charts F X Y p q σ D π hπ L c c' hw w hwc']
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasurePullbackEqZeroOfLtDim
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.MixDrop

theorem part_pull_eq_zero : ∀ (F : Type) [Field F] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp F) (q : Y ⟶ Sp F) (σ : F →+* ℂ) (D D' : ℕ), D' < D → IsProjOver p → topologicalKrullDim X = (D' : ℕ) → IsProjOver q → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → ∀ (L : Fin D → MLine p σ) (ε : ℤˣ), part (fun i => (L i).pull π hπ) ε = 0 := by
  intro F _ X Y _ _ p q σ D D' hD hp hX hq π hπ hgen L ε
  have hLN : IsLocallyNoetherian X := by
    obtain ⟨N, ι, _, h⟩ := hp
    have : LocallyOfFiniteType p := h ▸ inferInstance
    exact LocallyOfFiniteType.isLocallyNoetherian p
  obtain ⟨U, hU, hch⟩ := GlobalTheory.GenericCharts.exists_generic_charts F X p σ D' hp hX
  have hgU : genericPoint Y ∈ π ⁻¹ᵁ U := by
    show π (genericPoint Y) ∈ U
    rw [hgen]; exact hU
  have hnull := GlobalTheory.MixNull.part_compl_null F Y q σ σ.injective hq D (fun i => (L i).pull π hπ) ε (π ⁻¹ᵁ U) hgU
  have hz : ∀ (c : AlgChart q σ D) (w : CxPts q σ), w ∈ c.e.source → w ∈ ptsIn q σ (π ⁻¹ᵁ U) →
      dens (fun i => (L i).pull π hπ) c w = 0 := by
    intro c w hw hwU
    have hm : ptMap π hπ σ w ∈ ptsIn p σ U := by
      rw [mem_ptsIn] at hwU ⊢
      exact hwU
    obtain ⟨c0, hc0⟩ := hch _ hm
    obtain ⟨ξ, hξ, hker⟩ := GlobalTheory.T.exists_common_kernel_hessians_pullback_smaller_chart F X Y p q σ D D' hD π hπ c0 c w hw hc0
    have hdet : ∀ τ : Equiv.Perm (Fin D), (Matrix.of fun j l =>
        c.hess ((L (τ l)).pull π hπ).φ (pick ((L (τ l)).pull π hπ).φ.isLB w) w j l).det = 0 := by
      intro τ
      refine (Matrix.exists_vecMul_eq_zero_iff).1 ⟨ξ, hξ, funext fun l => ?_⟩
      have h1 := congrFun (hker (L (τ l)) (pick ((L (τ l)).pull π hπ).φ.isLB w) (mem_pick _ w)) l
      simpa [Matrix.vecMul, dotProduct] using h1
    unfold dens
    simp only [hdet, Finset.sum_const_zero, Complex.zero_re, mul_zero]
  have hc : ∀ c : AlgChart q σ D, chartMeas c.e
      (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y)) = 0 := by
    intro c
    set S := ptsIn q σ (π ⁻¹ᵁ U) with hSdef
    have hS : MeasurableSet S := (isOpen_ptsIn _).measurableSet
    have h1 : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y)) S = 0 := by
      rw [chartMeas_apply c.e _ hS]
      refine (setLIntegral_congr_fun (measurableSet_image _ (c.e.open_source.measurableSet.inter hS)
        inter_subset_left) ?_).trans lintegral_zero
      rintro _ ⟨y, hy, rfl⟩
      show ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c (c.e.symm (c.e y))) = 0
      rw [c.e.left_inv hy.1, hz c y hy.1 hy.2, mul_zero, ENNReal.ofReal_zero]
    have hle : chartMeas c.e (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y)) ≤
        part (fun i => (L i).pull π hπ) ε :=
      le_iSup (fun c : AlgChart q σ D => chartMeas c.e
        (fun y => ENNReal.ofReal ((ε : ℤ) * dens (fun i => (L i).pull π hπ) c y))) c
    have h2 := (Measure.le_iff'.1 hle Sᶜ).trans_eq hnull
    refine Measure.measure_univ_eq_zero.1 (le_antisymm ?_ bot_le)
    calc _ ≤ _ := measure_mono (show univ ⊆ S ∪ Sᶜ by simp)
      _ ≤ _ := measure_union_le _ _
      _ ≤ 0 := by rw [h1, zero_add]; exact h2
  show glueMeas _ _ = 0
  unfold glueMeas
  simp only [hc]
  exact le_antisymm (iSup_le fun _ => le_rfl) (Measure.zero_le _)

end GlobalTheory.MixDrop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulDescendsNearClosedFibreOfEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Near.law_of_emb : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → N.Law := by
  intro R _ _ _ hR M G' _ _ _ E N fU l hl1 hl2
  obtain ⟨hNoeth, -, hIC, -⟩ := hR
  obtain ⟨hbij, hsurj⟩ := GlobalTheory.T.appTop_bijective_and_surjective_normalDomain R M
  haveI := M.proper
  haveI := M.integral
  haveI := N.smooth
  obtain ⟨O, h, hfib, hover, hpt⟩ := GlobalTheory.T.exists_open_mul_point_on_pullback_containing_closedFibre R M G' N
  have hconst := GlobalTheory.T.closedFibre_productCoord_constant_on_projectionFibres R M G' E N fU l hl1 hl2 hsurj O h hpt
  have hflat : Flat (N.U ⊗ N.U).hom := by
    rw [Over.tensorObj_hom]; infer_instance
  have hPB : IsPullback (pullback.fst (N.U ⊗ N.U).hom M.π) (pullback.snd (N.U ⊗ N.U).hom M.π) (N.U ⊗ N.U).hom M.π :=
    IsPullback.of_hasPullback _ _
  have hpsurj : Surjective (pullback.fst (N.U ⊗ N.U).hom M.π) := by
    haveI : Surjective M.π := hsurj
    infer_instance
  have key : ∀ i : {y₀ : (N.U ⊗ N.U).left // (N.U ⊗ N.U).hom y₀ = closedPoint R},
      ∃ (V : (N.U ⊗ N.U).left.Opens) (hV : pullback.fst (N.U ⊗ N.U).hom M.π ⁻¹ᵁ V ≤ O) (h₀ : V.toScheme ⟶ N.U.left),
        i.1 ∈ V ∧ (pullback.fst (N.U ⊗ N.U).hom M.π ∣_ V) ≫ h₀ = (pullback (N.U ⊗ N.U).hom M.π).homOfLE hV ≫ h := by
    rintro ⟨y₀, hy₀⟩
    obtain ⟨z, hz⟩ := hpsurj.surj y₀
    have hzO : z ∈ O := hfib z (by rw [hz]; exact hy₀)
    exact GlobalTheory.T.morphism_descends_near_fibre_rigidity R M.S _ _ N.U.left M.π _ _ _ M.proper hsurj hbij hflat hPB O h y₀ (h ⟨z, hzO⟩)
      (fun z' hz' => hfib z' (by rw [hz']; exact hy₀))
      (fun z' hz' => hconst z' ⟨z, hzO⟩ (by rw [hz']; exact hz.symm) (by rw [hz']; exact hy₀))
  choose V hV h₀ hmem hcomm using key
  obtain ⟨hV', m, hm, huniq⟩ := GlobalTheory.T.morphism_local_descents_glue_union R M.S _ _ N.U.left M.π _ _ _ M.proper hsurj M.integral hflat hPB O h _ V hV h₀ hcomm
  refine ⟨⨆ i, V i, m, fun z hz => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hmem _⟩, ?_, ?_⟩
  · apply huniq
    simp only [reassoc_of% hm, hover, Scheme.homOfLE_ι_assoc, morphismRestrict_ι_assoc]
  · intro T v s x y hx hy
    have hc : (v ≫ (⨆ i, V i).ι) ≫ (N.U ⊗ N.U).hom = s ≫ M.π := by
      obtain ⟨x₀, h1, h2, -⟩ := hx
      have e1 : (fst N.U N.U).left ≫ N.U.hom = (N.U ⊗ N.U).hom := Over.w _
      simp only [← e1, ← h2, Category.assoc, ← pullback.condition]
      rw [reassoc_of% h1]
    let z : T ⟶ pullback (N.U ⊗ N.U).hom M.π := pullback.lift (v ≫ (⨆ i, V i).ι) s hc
    let z₁ := (isPullback_morphismRestrict (pullback.fst (N.U ⊗ N.U).hom M.π) (⨆ i, V i)).lift v z (pullback.lift_fst _ _ _).symm
    have hz₁a : z₁ ≫ (pullback.fst (N.U ⊗ N.U).hom M.π ∣_ ⨆ i, V i) = v := IsPullback.lift_fst _ _ _ _
    have hz₁b : z₁ ≫ (pullback.fst (N.U ⊗ N.U).hom M.π ⁻¹ᵁ ⨆ i, V i).ι = z := IsPullback.lift_snd _ _ _ _
    let t := z₁ ≫ (pullback (N.U ⊗ N.U).hom M.π).homOfLE hV'
    have ht : t ≫ O.ι = z := by
      simp only [t, Category.assoc, Scheme.homOfLE_ι, hz₁b]
    have hvm : v ≫ m = t ≫ h := by rw [← hz₁a, Category.assoc, hm, Category.assoc]
    rw [hvm]
    refine hpt T t s x y (by rw [reassoc_of% ht, pullback.lift_snd]) ?_ ?_
    · rw [reassoc_of% ht, pullback.lift_fst_assoc]; exact hx
    · rw [reassoc_of% ht, pullback.lift_fst_assoc]; exact hy

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoAdditiveCubicalStructure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem lamVal_add_cub : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (Z : Over (Sp V)) (x x' y : Z ⟶ D.P.A) (x₀ x₀' y₀ : Over.mk (Z.hom ≫ spMap ω) ⟶ T.B), x.left ≫ β = x₀.left → x'.left ≫ β = x₀'.left → y.left ≫ β = y₀.left → ∀ (z : Z.left) J J', Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (x * x') y).left z J J' * cubV D.cub z J' x x' y = lamVal w (lift x y).left z J J' * lamVal w (lift x' y).left z J J' * @id (Z.left.presheaf.stalk z)ˣ (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J x₀ x₀' y₀) ∧ lamVal w (lift y (x * x')).left z J J' * cubV D.cub z J' y x x' = lamVal w (lift y x).left z J J' * lamVal w (lift y x').left z J J' * @id (Z.left.presheaf.stalk z)ˣ (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J y₀ x₀ x₀') := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hτ hF Z x x' y x₀ x₀' y₀ hx hx' hy z J J' hJ hJ'
  have hn : ∀ (T' : Over (Sp V)) (z : T'.left) (J : (T'.left ⟶ T.B.left) → T.M.L.ι)
      (J' : (T'.left ⟶ D.P.A.left) → D.P.L.ι), Good T.M.L z J → Good D.P.L z J' →
      lamVal w (lift (1 : T' ⟶ D.P.A) (1 : T' ⟶ D.P.A)).left z J J' = 1 := fun T' z J J' hJ hJ' =>
    (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D ω s e β ββ w hτ hF T' 1 z J J' hJ hJ').1
  have L := GlobalTheory.LamRigid.lam_iso_laws (Sp W) (Sp V) T.B D.P.A T.M _ T.cub D.cub (spMap ω) β ββ w hF.1 D.P.isAb
    hF.2.1 hF.2.2.1 hn
  have C₁ : IsCub (cubV D.cub z J') := isCub_cubV D.cub hJ'
  have C₀ : IsCub (cubV T.cub (T := Over.mk (Z.hom ≫ spMap ω)) z J) := isCub_cubV T.cub hJ
  have A₁ := (L Z x x' y z J J' hJ hJ').2 x₀ x₀' y₀ hx.symm hx'.symm hy.symm
  refine ⟨?_, ?_⟩
  · rw [A₁]; simp only [id]; ac_rfl
  · rw [(L Z y y (x * x') z J J' hJ hJ').1, (L Z y y x z J J' hJ hJ').1, (L Z y y x' z J J' hJ hJ').1,
      C₁.s01 y x x', C₁.s12 x y x', C₀.s01 y₀ x₀ x₀', C₀.s12 x₀ y₀ x₀', A₁]
    simp only [id]; ac_rfl

end GlobalTheory.TInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoComparisonNormalisedGenerator
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

namespace GlobalTheory.TInj

theorem lamVal_cmp : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (ω : W →+* V) (D₁ D₂ : DegPre V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A), D₁.TauBimult → D₂.TauBimult → From T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → IsMonHom b → b.left ≫ β₂ = β₁ → ∀ (χ₁ : D₁.X) (χ₂ : D₂.X), e₁ χ₁ = e₂ χ₂ → ∀ u : LB.Gen (CmpLB D₁ D₂ b χ₁ χ₂), Nrm u → ∀ (Z : Over (Sp V)) (x : Z ⟶ D₁.P.A) (z : Z.left) (J : (Z.left ⟶ (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0})) → (JN D₁ D₂).ι) J₀, Good (JN D₁ D₂) z J → Good T.M.L z J₀ → lamVal w₂ (lift (toUnit Z ≫ D₂.c χ₂) (x ≫ b)).left z J₀ (rr J) = lamVal w₁ (lift (toUnit Z ≫ D₁.c χ₁) x).left z J₀ (rl J) * val u x.left z J := by
  intro o W _ _ _ T I _ ε n V _ _ ω D₁ D₂ s₁ e₁ β₁ ββ₁ w₁ s₂ e₂ β₂ ββ₂ w₂ b hB₁ hB₂ hF₁ hF₂ hb hbβ χ₁ χ₂ hχ u hu Z x z J J₀ hJ hJ₀
  haveI : Nonempty D₁.P.A.left := nonempty_av D₁.P
  haveI : Nonempty D₂.P.A.left := nonempty_av D₂.P
  haveI : Nonempty (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0}) :=
    ⟨(coprod.inl : D₁.P.A.left ⟶ (D₁.P.A.left ⨿ D₂.P.A.left : Scheme.{0})) (Classical.arbitrary _)⟩
  haveI : Nonempty T.B.left := ⟨β₁ (Classical.arbitrary _)⟩
  have hJN : (JN D₁ D₂).IsLB := jn_isLB D₁ D₂
  have hN : (join (JN D₁ D₂) T.M.L).IsLB := join_isLB hJN T.M.isLB
  have pJ := isPart_inl (JN D₁ D₂) T.M.L
  have pT := isPart_inr (JN D₁ D₂) T.M.L
  have p₁ := pJ.trans (isPart_inl D₁.P.L D₂.P.L)
  have p₂ := pJ.trans (isPart_inr D₁.P.L D₂.P.L)
  obtain ⟨t₁, ht₁, ht₁v⟩ := exists_gen_of_iso pT p₁ w₁ hF₁.2.2.1
  obtain ⟨t₂, ht₂, ht₂v⟩ := exists_gen_of_iso pT p₂ w₂ hF₂.2.2.1
  let m₁ : D₁.P.A.left ⟶ (G2 D₁.P.A).left := (lift (toUnit _ ≫ D₁.c χ₁) (𝟙 _)).left
  let m₂ : D₁.P.A.left ⟶ (G2 D₂.P.A).left := (lift (toUnit _ ≫ D₂.c χ₂) b).left
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨J', hJ', eJl, eJr⟩ := exists_good_join hJN T.M.isLB hJ hJ₀
  have key := gen_unique' hN (u := LB.pullGen _ _ _ t₂ m₂)
    (u' := LB.mulGen _ _ _ _ _ (LB.pullGen _ _ _ t₁ m₁) (pJ.gen u)) ?fe D₁.P.A.hom (eSec D₁.P.A) (Over.w η[D₁.P.A])
    (hG _ _ D₁.P.isAb).2 (DVR.pullGen_isGen _ _ _ _ ht₂ m₂)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht₁ m₁) (pJ.gen_isGen hu.1)) ?ev Z.left x.left z J' hJ'
  · rw [val_pull hJ', ht₂v _ _ z J' hJ', val_mul hJ', val_pull hJ', ht₁v _ _ z J' hJ', pJ.val_gen _ _ z hJ'] at key
    have e₁ : x.left ≫ m₁ = (lift (toUnit Z ≫ D₁.c χ₁) x).left := by
      rw [← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit Z)]
    have e₂ : x.left ≫ m₂ = (lift (toUnit Z ≫ D₂.c χ₂) (x ≫ b)).left := by
      rw [← Over.comp_left, comp_lift, ← Category.assoc, toUnit_unique (x ≫ toUnit _) (toUnit Z)]
    have r₁ : rs (M := D₁.P.L) (coprod.inl ≫ coprod.inl) (Prod.fst ∘ Prod.fst) J' = rl J := by
      rw [← eJl]; funext ψ
      show Prod.fst (Prod.fst (J' (ψ ≫ coprod.inl ≫ coprod.inl))) = Prod.fst (Prod.fst (J' ((ψ ≫ coprod.inl) ≫ coprod.inl)))
      rw [Category.assoc]
    have r₂ : rs (M := D₂.P.L) (coprod.inr ≫ coprod.inl) (Prod.snd ∘ Prod.fst) J' = rr J := by
      rw [← eJl]; funext ψ
      show Prod.snd (Prod.fst (J' (ψ ≫ coprod.inr ≫ coprod.inl))) = Prod.snd (Prod.fst (J' ((ψ ≫ coprod.inr) ≫ coprod.inl)))
      rw [Category.assoc]
    rw [e₁, e₂] at key
    convert key using 3 <;> first | exact r₁.symm | exact r₂.symm | exact eJl.symm | exact eJr.symm | exact congrArg₂ (isoVal w₂ _ z) eJr.symm r₂.symm | exact congrArg₂ (isoVal w₁ _ z) eJr.symm r₁.symm
  case fe =>
    have g2 : ∀ {a c : D₁.P.A.left ⟶ (G2 T.B).left}, a ≫ (fst T.B T.B).left = c ≫ (fst T.B T.B).left →
        a ≫ (snd T.B T.B).left = c ≫ (snd T.B T.B).left → a = c := fun h1 h2 => pullback.hom_ext h1 h2
    have hT0 : (lift (toUnit _ ≫ D₁.c χ₁) (𝟙 _)).left ≫ ββ₁ = (lift (toUnit _ ≫ D₂.c χ₂) b).left ≫ ββ₂ := by
      refine g2 ?_ ?_
      · rw [Category.assoc, Category.assoc, hF₁.2.1.1, hF₂.2.1.1, ← Category.assoc, ← Category.assoc,
          ← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst, Over.comp_left, Over.comp_left, Category.assoc,
          Category.assoc, hF₁.2.2.2.1, hF₂.2.2.2.1, hχ]
      · rw [Category.assoc, Category.assoc, hF₁.2.1.2, hF₂.2.1.2, ← Category.assoc, ← Category.assoc,
          ← Over.comp_left, ← Over.comp_left, lift_snd, lift_snd, Over.id_left, Category.id_comp, hbβ]
    have hT : m₁ ≫ ββ₁ = m₂ ≫ ββ₂ := hT0
    have eT : ∀ (X : Scheme.{0}) (g : (G2 T.B).left ⟶ X), m₁ ≫ ββ₁ ≫ g = m₂ ≫ ββ₂ ≫ g := fun _ g => by
      rw [← Category.assoc, hT, Category.assoc]
    intro U _ h
    rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
    simp only [Sum.elim_inl, Sum.elim_inr, eT]
    letI := D₁.P.isAb.comm
    letI := D₂.P.isAb.comm
    have hc₁ : (toUnit D₁.P.A ≫ D₁.c χ₁) * 𝟙 D₁.P.A = 𝟙 D₁.P.A * (toUnit D₁.P.A ≫ D₁.c χ₁) := mul_comm _ _
    have hc₂ : (toUnit D₁.P.A ≫ D₂.c χ₂) * b = b * (toUnit D₁.P.A ≫ D₂.c χ₂) := mul_comm _ _
    have A1 : ∏ a₂ : ULift.{0} (Finset (Fin 2)),
        h (m₁ ≫ (psum D₁.P.A (x2 D₁.P.A) a₂.down).left ≫ coprod.inl ≫ coprod.inl) ^ (-(-1 : ℤ) ^ (2 - a₂.down.card)) =
        (h ((𝟙 D₁.P.A * (toUnit _ ≫ D₁.c χ₁)).left ≫ coprod.inl ≫ coprod.inl) *
          (h ((toUnit _ ≫ D₁.c χ₁).left ≫ coprod.inl ≫ coprod.inl))⁻¹ *
          (h ((𝟙 D₁.P.A : D₁.P.A ⟶ D₁.P.A).left ≫ coprod.inl ≫ coprod.inl))⁻¹ *
          h ((1 : D₁.P.A ⟶ D₁.P.A).left ≫ coprod.inl ≫ coprod.inl))⁻¹ := by
      rw [← hc₁, ← GlobalTheory.PrimCocycle.prod_lam (toUnit _ ≫ D₁.c χ₁) (𝟙 _) (fun g => h (g ≫ coprod.inl ≫ coprod.inl)),
        ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg, ← Category.assoc]
    have A2 : ∏ a₂ : ULift.{0} (Finset (Fin 2)),
        h (m₂ ≫ (psum D₂.P.A (x2 D₂.P.A) a₂.down).left ≫ coprod.inr ≫ coprod.inl) ^ (-(-1 : ℤ) ^ (2 - a₂.down.card)) =
        (h ((b * (toUnit _ ≫ D₂.c χ₂)).left ≫ coprod.inr ≫ coprod.inl) *
          (h ((toUnit _ ≫ D₂.c χ₂).left ≫ coprod.inr ≫ coprod.inl))⁻¹ *
          (h (b.left ≫ coprod.inr ≫ coprod.inl))⁻¹ *
          h ((1 : D₁.P.A ⟶ D₂.P.A).left ≫ coprod.inr ≫ coprod.inl))⁻¹ := by
      rw [← hc₂, ← GlobalTheory.PrimCocycle.prod_lam (toUnit _ ≫ D₂.c χ₂) b (fun g => h (g ≫ coprod.inr ≫ coprod.inl)),
        ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun k _ => ?_
      rw [zpow_neg, ← Category.assoc]
    rw [A1, A2, Fin.prod_univ_four, Fin.prod_univ_four]
    have pm : ∀ {X Y : Over (Sp V)} [GrpObj Y] (a c : X ⟶ Y), padd Y a c = a * c := fun _ _ => rfl
    simp only [DegPre.Oφ, Oε, Oinvε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, pm, ← Hom.one_def, Category.assoc]
    simp only [zpow_one, zpow_neg]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  case ev =>
    intro y I hI
    haveI := hb
    rw [val_pull hI, ht₂v _ _ y I hI, val_mul hI, val_pull hI, ht₁v _ _ y I hI, pJ.val_gen _ _ y hI]
    have o₁ : (1 : 𝟙_ (Over (Sp V)) ⟶ D₁.P.A) = η[D₁.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have o₂ : (1 : 𝟙_ (Over (Sp V)) ⟶ D₂.P.A) = η[D₂.P.A] := by
      rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
    have f₁ : eSec D₁.P.A ≫ m₁ = (lift (toUnit (𝟙_ (Over (Sp V))) ≫ D₁.c χ₁) (1 : 𝟙_ _ ⟶ D₁.P.A)).left := by
      rw [eSec, ← Over.comp_left, comp_lift, Category.comp_id, ← Category.assoc,
        toUnit_unique (η[D₁.P.A] ≫ toUnit _) (toUnit _), o₁]
    have f₂ : eSec D₁.P.A ≫ m₂ = (lift (toUnit (𝟙_ (Over (Sp V))) ≫ D₂.c χ₂) (1 : 𝟙_ _ ⟶ D₂.P.A)).left := by
      have hbη : η[D₁.P.A] ≫ b = η[D₂.P.A] := IsMonHom.one_hom b
      rw [eSec, ← Over.comp_left, comp_lift, hbη, ← Category.assoc,
        toUnit_unique (η[D₁.P.A] ≫ toUnit _) (toUnit _), o₂]
    rw [f₁, f₂]
    have a₂ := (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D₂ ω s₂ e₂ β₂ ββ₂ w₂ hB₂ hF₂ (𝟙_ _) (toUnit _ ≫ D₂.c χ₂) y _ _ (pT.good hI)
      (p₂.good hI)).2
    have a₁ := (GlobalTheory.T.mumford_bundle_iso_eq_one_along_axes T ε n V D₁ ω s₁ e₁ β₁ ββ₁ w₁ hB₁ hF₁ (𝟙_ _) (toUnit _ ≫ D₁.c χ₁) y _ _ (pT.good hI)
      (p₁.good hI)).2
    have c := hu.2 (𝟙_ (Over (Sp V))).left (𝟙 _) y _ (pJ.good hI)
    rw [Category.id_comp] at c
    refine a₂.trans (Eq.symm ?_)
    exact (congrArg₂ (· * ·) a₁ c).trans (_root_.mul_one 1)

end GlobalTheory.TInj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordClassSymmetricPullbackQuadratic
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem pull_zsmul_of_symm : ∀ (K : Type) [Field K] (B A : AbVar K) (c : Pic A.X.left), CechPic.pull (Hom.hom (-(𝟙 A))).left c = c → ∀ (f : B ⟶ A) (n : ℤ), AbVar.lam c f.hom f.hom = 2 • CechPic.pull f.hom.left c ∧ CechPic.pull (Hom.hom (n • f)).left c = (n ^ 2) • CechPic.pull f.hom.left c := by
  intro K _ B A c hc f n
  have bil := GlobalTheory.T.abelianVarietyMumfordClass_bilinear K A c B.X

  have h1 : CechPic.pull (1 : B.X ⟶ A.X).left c = 0 := by
    have e := (bil 1 1 1 0).2.1
    simp only [AbVar.lam, _root_.mul_one, sub_self, zero_sub, neg_eq_zero] at e
    exact e

  have hinv : ∀ y : B.X ⟶ A.X, CechPic.pull (y⁻¹).left c = CechPic.pull y.left c := by
    intro y
    have hc' : CechPic.pull ((𝟙 A.X)⁻¹).left c = c := hc
    rw [show y⁻¹ = y ≫ (𝟙 A.X)⁻¹ by rw [GrpObj.comp_inv, Category.comp_id], Over.comp_left, pull_comp, hc']

  have hmul : ∀ y z : B.X ⟶ A.X, CechPic.pull (y * z).left c =
      AbVar.lam c y z + CechPic.pull y.left c + CechPic.pull z.left c := by
    intro y z
    simp only [AbVar.lam]
    abel
  set x := f.hom with hx
  have key : AbVar.lam c x x = 2 • CechPic.pull x.left c := by
    have e := (bil x x 1 (-1)).2.2.2.2
    rw [zpow_neg_one] at e
    have e2 := hmul x x⁻¹
    rw [_root_.mul_inv_cancel, h1, hinv, e] at e2
    have e3 : AbVar.lam c x x - 2 • CechPic.pull x.left c =
        -((-1 : ℤ) • AbVar.lam c x x + CechPic.pull x.left c + CechPic.pull x.left c) := by module
    rw [← sub_eq_zero, e3, ← e2, neg_zero]
  refine ⟨key, ?_⟩
  have step : ∀ m : ℤ, CechPic.pull (x ^ (m + 1)).left c =
      CechPic.pull (x ^ m).left c + (2 * m + 1) • CechPic.pull x.left c := by
    intro m
    rw [zpow_add_one, hmul, (bil x x 1 m).2.2.2.1, key]
    module
  change CechPic.pull (x ^ n).left c = (n ^ 2) • CechPic.pull x.left c
  induction n using Int.induction_on with
  | zero => rw [zpow_zero, h1]; simp
  | succ m ih =>
    rw [step, ih]
    module
  | pred m ih =>
    have e := step (-(m : ℤ) - 1)
    rw [show -(m : ℤ) - 1 + 1 = -(m : ℤ) by ring, ih] at e
    rw [eq_sub_of_add_eq e.symm]
    module

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvPowerSeriesAlgHomExtOfIsNilpotentX
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem mvPowerSeries_algHom_ext_of_isNilpotent :
    ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (A : Type) [CommRing A] [Algebra k A],
      ∀ φ ψ : MvPowerSeries σ k →ₐ[k] A, (∀ i, IsNilpotent (φ (X i))) →
        (∀ i, φ (X i) = ψ (X i)) → φ = ψ := by
  intro k _ σ _ A _ _ φ ψ hφ h
  classical
  obtain ⟨N₁, h₁⟩ := GlobalTheory.mvPowerSeries_algHom_kill_high_order k σ A φ hφ
  obtain ⟨N₂, h₂⟩ := GlobalTheory.mvPowerSeries_algHom_kill_high_order k σ A ψ (fun i => h i ▸ hφ i)
  have hp : φ.comp (MvPolynomial.coeToMvPowerSeries.algHom k) =
      ψ.comp (MvPolynomial.coeToMvPowerSeries.algHom k) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [h i]
  have hm : ∀ (α : σ →₀ ℕ) (c : k), φ (monomial α c) = ψ (monomial α c) := by
    intro α c
    have := DFunLike.congr_fun hp (MvPolynomial.monomial α c)
    simpa [MvPolynomial.coe_monomial] using this
  have hfin : {α : σ →₀ ℕ | α.degree ≤ N₁ + N₂}.Finite := Finsupp.finite_of_degree_le _
  apply AlgHom.ext
  intro f
  set p : MvPowerSeries σ k := ∑ α ∈ hfin.toFinset, monomial α (coeff α f) with hpdef
  have hc : ∀ α : σ →₀ ℕ, α.degree ≤ N₁ + N₂ → coeff α (f - p) = 0 := by
    intro α hα
    rw [map_sub, hpdef, map_sum, Finset.sum_eq_single α]
    · simp
    · intro β _ hβ
      rw [coeff_monomial_ne hβ.symm]
    · intro hn
      exact absurd (by simpa using hα) hn
  have e₁ : φ (f - p) = 0 := h₁ _ (fun α hα => hc α (by omega))
  have e₂ : ψ (f - p) = 0 := h₂ _ (fun α hα => hc α (by omega))
  have e₃ : φ p = ψ p := by
    rw [hpdef, map_sum, map_sum]
    exact Finset.sum_congr rfl (fun α _ => hm _ _)
  rw [map_sub, sub_eq_zero] at e₁ e₂
  rw [e₁, e₂, e₃]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowFinrankCotangentLeFinrankFrobeniusKernelQuotiStatement
section
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_finrank_cotangent_le_finrank_frobeniusKernelQuotient : ∀ (p : ℕ) [Fact p.Prime] (k H : Type) [Field k] [CharP k p] [CommRing H] [HopfAlgebra k H] [Module.Finite k H], p ^ Module.finrank k (Cot k H) ≤ Module.finrank k (H ⧸ frobKerIdeal p k H) := by
  first | exact @GlobalTheory.PDiv.FrobKerOrder.pow_finrank_cot_le | exact GlobalTheory.PDiv.FrobKerOrder.pow_finrank_cot_le | (intros; apply GlobalTheory.PDiv.FrobKerOrder.pow_finrank_cot_le <;> assumption)
end

