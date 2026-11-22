import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0021
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0703
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0144
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0610
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0606
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0602
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0592
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0633
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0599
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0867
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0872
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0873
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0580
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0615
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0722
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0651
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0680
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0676
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0628
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0617
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0666
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0638
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplication
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.Bundle0008
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteUnitaryMultiplication
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.MatchLM
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LeviMatchingWords.SplitPlaceGeneratorPowers
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0855

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanIntegrableOn
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.ArchI

theorem exists_modif (hK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement) (m : ℕ) (n : Fin (m + 1) → ℕ) (X : Scheme.{0})
    [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (D : ℕ) (hX : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) D) :
    ∃ (T : Type) (_ : TopologicalSpace T) (_ : CompactSpace T) (_ : T2Space T) (A : FinHolAtlas D T)
      (F : T → GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Z : Set (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)),
      Continuous F ∧
      (∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ W) (ev (i ≫ mpStr ℤ m n) σ₀ W f ∘ F)) ∧
      MeasurableSet Z ∧ (∀ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0) ∧
      (∀ y, y ∉ Z → ∃ x, F x = y) ∧ (∀ x x', F x ∉ Z → F x = F x' → x = x') := by
  have hC := hX.charZero
  obtain ⟨-, hp₃, hp₄, -⟩ := GlobalTheory.T.mixed_cycle_point_dictionary m n X i (D + 1) hX.dim_eq
  have hP := hp₄ (hp₃.2 hC)
  obtain ⟨J, ⟨R⟩⟩ := ReciprocityTheory.ChartRestriction.G.Geo.exists_anLogRes (GlobalTheory.T.resolution_exists_of_resolution_statement hK) hP
  obtain ⟨S, hS, hJ⟩ := R.homog
  obtain ⟨f, hfS, hfP⟩ : ∃ f ∈ S, f ∉ ptIdeal (i (genericPoint X)) := by
    by_contra h
    push_neg at h
    exact R.nondeg (hJ ▸ Ideal.span_le.2 h)
  obtain ⟨a, ha⟩ := hS f hfS
  have hfJ : f ∈ J := hJ ▸ Ideal.subset_span hfS
  have hJz : ∀ z ∈ mcPts J, eval z (map (Int.castRingHom ℂ) f) = 0 := fun z hz => hz.2 f hfJ
  choose F hF' using fun x => GlobalTheory.T.multicone_point_descends_to_subvariety m n X i (R.lift x x) (R.mem x x (R.mem_U x))
  have hU : ∀ x, ∀ y ∈ R.U x, IsUnder (PtsOver.map i rfl _ (F y)) (R.lift x y) := fun x y hy =>
    GlobalTheory.T.isUnder_of_same_orbit m n _ _ _ (hF' y) (R.compat x y y ⟨hy, R.mem_U y⟩)
  have key (x : R.X) (j : Fin R.A.n) := GlobalTheory.T.holomorphic_lift_gives_holomorphic_section m n X i D
    ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) (fun v => R.lift x ((R.A.chart j).symm v))
    (F ∘ (R.A.chart j).symm) ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x))
    (fun u hu => (ReciprocityTheory.ChartRestriction.G.Geo.analyticAt_lift_chart R x j hu).differentiableAt.differentiableWithinAt)
    (fun v hv => hU x _ hv.2)
  have hO (x : R.X) (j : Fin R.A.n) := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)
  have hFc : Continuous F := continuous_iff_continuousAt.2 fun x => by
    obtain ⟨j, hj⟩ := R.A.cover x
    have hm : R.A.chart j x ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
      ⟨(R.A.chart j).map_source hj, by
        simpa only [Set.mem_preimage, (R.A.chart j).left_inv hj] using R.mem_U x⟩
    have h₁ := ((key x j).1.continuousAt ((hO x j).mem_nhds hm)).comp
      (f := R.A.chart j) (x := x) ((R.A.chart j).continuousAt hj)
    refine h₁.congr ?_
    filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with w hw
    simp only [Function.comp_apply, (R.A.chart j).left_inv hw]
  refine ⟨R.X, inferInstance, inferInstance, inferInstance, R.A, F,
    {y | ∃ z, IsUnder (PtsOver.map i rfl _ y) z ∧ eval z (map (Int.castRingHom ℂ) f) = 0}, hFc, ?_,
    (GlobalTheory.T.hypersurface_complex_points_measurable_null m n X i D f a ha hfP).1, (GlobalTheory.T.hypersurface_complex_points_measurable_null m n X i D f a ha hfP).2, ?_, ?_⟩
  · intro W g j v hv
    set x := (R.A.chart j).symm v with hx
    have hvO : v ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x := ⟨hv.1, R.mem_U x⟩
    have hcont := (key x j).1
    have hO' : IsOpen (((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x) ∩
        (F ∘ (R.A.chart j).symm) ⁻¹' ptsIn (i ≫ mpStr ℤ m n) σ₀ W) :=
      hcont.isOpen_inter_preimage (hO x j) (isOpen_ptsIn W)
    have hd := (key x j).2 W g
    exact (SCV.analyticOnNhd_iff_differentiableOn hO').2 hd v ⟨hvO, hv.2⟩
  · intro y hy
    obtain ⟨z, hz, hyz⟩ := GlobalTheory.T.complex_point_lifts_to_multicone m n X i y
    have hzJ : z ∉ mcPts J := fun h => hy ⟨z, hyz, hJz z h⟩
    obtain ⟨x, hx⟩ := R.surj z hz hzJ
    exact ⟨x, (GlobalTheory.T.points_eq_iff_same_torus_orbit m n X i _ _ _ _ (hF' x) hyz).2 hx⟩
  · intro x x' hx e
    refine R.inj x x' (fun h => hx ⟨_, hF' x, hJz _ h⟩) ?_
    exact (GlobalTheory.T.points_eq_iff_same_torus_orbit m n X i _ _ _ _ (hF' x) (hF' x')).1 e

theorem integrableOn_of_modif {X : Scheme.{0}} [IsIntegral X] {q : X ⟶ Sp ℤ} {σ : ℤ →+* ℂ} {D : ℕ}
    [CompactSpace (GlobalTheory.CxPts q σ)] {T : Type} [TopologicalSpace T] [CompactSpace T] [T2Space T]
    (A : FinHolAtlas D T) (F : T → GlobalTheory.CxPts q σ) (hF : Continuous F)
    (H : ∀ (W : X.Opens) (f : Γ(X, W)), A.HoloOn (F ⁻¹' ptsIn q σ W) (ev q σ W f ∘ F))
    (Z : Set (GlobalTheory.CxPts q σ)) (hZ : MeasurableSet Z)
    (hZ0 : ∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z) = 0)
    (hs : ∀ y, y ∉ Z → ∃ x, F x = y) (hi : ∀ x x', F x ∉ Z → F x = F x' → x = x')
    {B C : LB X} (φ : GlobalTheory.Weight q σ B) (hφ : φ.IsCInf) (ψ : GlobalTheory.Weight q σ C) (hψ : ψ.IsCInf)
    {r : C.ι → X.functionFieldˣ} (hr : IsRatSec C r) (ε : ℤˣ) :
    IntegrableOn (GlobalTheory.Cartier.logNorm ψ r) (offSupp q σ (divOfRatSec ψ.isLB hr)) (φ.chernPart D ε) := by
  classical
  obtain ⟨N, W, b, a, d, hcov, hWb, hd, hf⟩ := GlobalTheory.T.rational_section_finite_open_cover ψ hr
  set S := offSupp q σ (divOfRatSec ψ.isLB hr) with hSdef
  have hSo : IsOpen S := isOpen_offSupp _
  have hgc := GlobalTheory.T.log_norm_continuous_off_divisor ψ hψ hr
  set g := GlobalTheory.Cartier.logNorm ψ r with hgdef
  set Z' : Set (GlobalTheory.CxPts q σ) := Z ∪ ⋃ l, {y | y ∈ ptsIn q σ (W l) ∧ ev q σ (W l) (d l) y = 0} with hZ'def
  have hpiece (l : Fin N) : MeasurableSet {y | y ∈ ptsIn q σ (W l) ∧ ev q σ (W l) (d l) y = 0} := by
    have ho : IsOpen (ptsIn q σ (W l) ∩ ev q σ (W l) (d l) ⁻¹' {0}ᶜ) :=
      (continuousOn_ev (d l)).isOpen_inter_preimage (isOpen_ptsIn _) isOpen_compl_singleton
    have e : {y | y ∈ ptsIn q σ (W l) ∧ ev q σ (W l) (d l) y = 0} =
        ptsIn q σ (W l) \ (ptsIn q σ (W l) ∩ ev q σ (W l) (d l) ⁻¹' {0}ᶜ) := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_diff, Set.mem_inter_iff, Set.mem_preimage, Set.mem_compl_iff,
        Set.mem_singleton_iff, not_and, not_not]
      exact ⟨fun h => ⟨h.1, fun _ => h.2⟩, fun h => ⟨h.1, h.2 h.1⟩⟩
    rw [e]
    exact (isOpen_ptsIn _).measurableSet.diff ho.measurableSet
  have hZ'm : MeasurableSet Z' := hZ.union (MeasurableSet.iUnion hpiece)
  have hZ'0 : ∀ c : GlobalTheory.AlgChart q σ D, volume (c.e.target ∩ c.e.symm ⁻¹' Z') = 0 := fun c => by
    rw [hZ'def, Set.preimage_union, Set.inter_union_distrib_left, Set.preimage_iUnion, Set.inter_iUnion]
    refine measure_union_null (hZ0 c) (measure_iUnion_null fun l => ?_)
    obtain ⟨h, hne⟩ := hd l
    exact GlobalTheory.T.zero_locus_regular_function_null X q σ D c (W l) h (d l) hne
  have hne : Nonempty (ChartPartition A) := existsPartition A
  set Pt := hne.some
  have hKK (j : Fin A.n) := image_closed_compact (A.chart j) (isClosed_tsupport (Pt.χ j)) (Pt.tsupport_subset j)
  have hcovK : ∀ x, ∃ j, ∃ u ∈ (A.chart j) '' tsupport (Pt.χ j), (A.chart j).symm u = x := fun x => by
    obtain ⟨j, hj⟩ : ∃ j, Pt.χ j x ≠ 0 := by
      by_contra h
      push_neg at h
      have := Pt.sum_eq_one x
      simp [h] at this
    have hx : x ∈ tsupport (Pt.χ j) := subset_tsupport _ hj
    exact ⟨j, _, ⟨x, hx, rfl⟩, (A.chart j).left_inv (Pt.tsupport_subset j hx)⟩
  have hle := GlobalTheory.T.measure_zero_set_avoided_by_holomorphic_map A F hF H Z' hZ'm hZ'0 (fun y hy => hs y fun h => hy (Or.inl h))
    (fun x x' hx => hi x x' fun h => hx (Or.inl h)) φ hφ ε (fun j => (A.chart j) '' tsupport (Pt.χ j))
    (fun j => (hKK j).1) (fun j => (hKK j).2) hcovK
  have hfin (j : Fin A.n) := GlobalTheory.T.lintegral_indicator_mul_locDens_pullback_lt_top A F hF H φ hφ ψ hψ g S Z' W b a d hcov hWb
    (fun l y hy hyS hyZ => hf l y hy hyS fun h0 => hyZ (Or.inr (Set.mem_iUnion.2 ⟨l, hy, h0⟩))) hSo hgc hZ'm j
    _ (hKK j).2 (hKK j).1
  refine ⟨hgc.aestronglyMeasurable hSo.measurableSet, ?_⟩
  set h : GlobalTheory.CxPts q σ → ENNReal := S.indicator fun y => ‖g y‖ₑ with hh
  have hhm : Measurable h := by
    have := (hgc.enorm).measurable_piecewise (continuousOn_const (c := (0 : ENNReal)) (s := Sᶜ)) hSo.measurableSet
    rwa [show S.piecewise (fun y => ‖g y‖ₑ) (fun _ => (0 : ENNReal)) = h from Set.piecewise_eq_indicator] at this
  show ∫⁻ y, ‖g y‖ₑ ∂(φ.chernPart D ε).restrict S < ⊤
  rw [← lintegral_indicator hSo.measurableSet]
  refine (lintegral_mono' hle le_rfl).trans_lt ?_
  rw [lintegral_finset_sum_measure]
  refine ENNReal.sum_lt_top.2 fun j _ => ?_
  have hT := (A.chart j).open_target.measurableSet
  have hc : ContinuousOn (F ∘ (A.chart j).symm) (A.chart j).target :=
    hF.comp_continuousOn (A.chart j).continuousOn_symm
  have hsub : (A.chart j) '' tsupport (Pt.χ j) \ (F ∘ (A.chart j).symm) ⁻¹' Z' ⊆ (A.chart j).target :=
    Set.diff_subset.trans (hKK j).2
  have hm₀ : AEMeasurable (F ∘ (A.chart j).symm)
      (volume.restrict ((A.chart j) '' tsupport (Pt.χ j) \ (F ∘ (A.chart j).symm) ⁻¹' Z')) :=
    (hc.aemeasurable hT).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hdc := locDensCont A (fun _ => φ.locPot.pullback F hF)
    (fun _ => GlobalTheory.T.smooth_weight_pullback_is_potential A F hF H φ hφ) j
  have hρ : AEMeasurable (fun u => ENNReal.ofReal |locDens A (fun _ => φ.locPot.pullback F hF) j u|)
      (volume.restrict ((A.chart j) '' tsupport (Pt.χ j) \ (F ∘ (A.chart j).symm) ⁻¹' Z')) :=
    ((ENNReal.continuous_ofReal.comp_continuousOn hdc.abs).aemeasurable hT).mono_measure
      (Measure.restrict_mono hsub le_rfl)
  rw [lintegral_map' hhm.aemeasurable (hm₀.mono_ac (withDensity_absolutelyContinuous _ _))]
  change ∫⁻ u, (h ∘ F ∘ (A.chart j).symm) u ∂_ < ⊤
  rw [lintegral_withDensity_eq_lintegral_mul₀ hρ (hhm.comp_aemeasurable hm₀)]
  refine lt_of_eq_of_lt (lintegral_congr fun u => ?_) (hfin j)
  simp only [Pi.mul_apply, Function.comp_apply, hh]
  exact mul_comm _ _

end GlobalTheory.CompanionTheory.ArchI

namespace GlobalTheory.CompanionTheory.MixZ

open GlobalTheory.CompanionTheory.ArchI in

theorem archIntegrableOn_of_resK : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ArchIntegrableOn := by
  intro hK m n N M X _ i _ D hX r hr σ
  obtain rfl : σ = σ₀ := Subsingleton.elim _ _
  obtain ⟨T, _, _, _, A, F, Z, hF, H, hZ, hZ0, hs, hi⟩ := exists_modif hK m n X i D hX
  have := hX.compactSpace σ₀
  exact ⟨integrableOn_of_modif A F hF H Z hZ hZ0 hs hi _ ((N.restr i).cInf σ₀) _ ((M.restr i).cInf σ₀) hr 1,
    integrableOn_of_modif A F hF H Z hZ hZ0 hs hi _ ((N.restr i).cInf σ₀) _ ((M.restr i).cInf σ₀) hr (-1)⟩

end GlobalTheory.CompanionTheory.MixZ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanIntegralEq
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit segre fibre IsGoodProj IsSheet HermLine IsSmoothHerm sheetDensity maDensity ptsIntegral ptsIntegralAt pot)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat)

noncomputable section
namespace GlobalTheory.CompanionTheory.MixZ.ArchEq

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {D : ℕ}

theorem ae_cover {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    [SecondCountableTopology (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀)]
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (ptIdeal (i (genericPoint X))) (D + 1)) (Ψ : LinProj n D)
    (hΨ : IsGoodProj (ptIdeal (i (genericPoint X))) Ψ) (N : Pol n) (a : Fin (m + 1) → ℕ) (hN : IsMultiHomog N a)
    (hNP : N ∉ ptIdeal (i (genericPoint X)))
    (hcov : ∀ y z, Over i y z → eval z (map (Int.castRingHom ℂ) N) ≠ 0 →
      ∃ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, y ∈ c.e.source) :
    ∀ᵐ v : Fin D → ℂ, ∀ z ∈ mcPts (ptIdeal (i (genericPoint X))), Ψ (segre z) = Fin.cons 1 v →
      ∃ y, Over i y z ∧ y ∈ pieceSet i Ψ N := by
  classical
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D => c.e.source) (fun c => c.e.open_source)
  have h1 := ReciprocityTheory.ChartRestriction.G.Geo.projB_null (J := Ideal.span {N}) Ψ hP hΨ
    ⟨{N}, by rintro f rfl; exact ⟨a, hN⟩, rfl⟩ (fun h => hNP (h (Ideal.subset_span rfl)))
  have h2 : volume (⋃ c ∈ T, projCoord i Ψ '' {y | y ∈ c.e.source ∧
      (∃ z, Over i y z ∧ Ψ (segre z) 0 ≠ 0) ∧ ¬ IsRegAt i Ψ c y}) = 0 :=
    (measure_biUnion_null_iff hTc).2 fun c _ => GlobalTheory.T.irregular_projection_image_null m n X i D Ψ c
  have h3 := measure_union_null h1 h2
  refine ae_iff.2 (measure_mono_null ?_ h3)
  intro v hv
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨z, hz, hzv, hno⟩ := hv
  by_cases hNz : eval z (map (Int.castRingHom ℂ) N) = 0
  · refine Or.inl ⟨z, hz, ⟨hz.1, fun g hg => ?_⟩, hzv⟩
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hg
    simp [hNz]
  · obtain ⟨y, hy⟩ := GlobalTheory.T.multicone_point_descends_to_subvariety m n X i z hz
    obtain ⟨c₀, hc₀⟩ := hcov y z hy hNz
    have hyU : y ∈ ⋃ c ∈ T, c.e.source := by
      rw [hTU]
      exact Set.mem_iUnion.2 ⟨c₀, hc₀⟩
    obtain ⟨c, hcT, hyc⟩ := Set.mem_iUnion₂.1 hyU
    have h0 : Ψ (segre z) 0 ≠ 0 := by simp [hzv]
    by_cases hreg : IsRegAt i Ψ c y
    · exact absurd ⟨y, hy, GlobalTheory.T.projection_regular_on_nonvanishing_chart m n X i D Ψ N a hN c y z hyc hy hNz h0 hreg⟩ hno
    · refine Or.inr (Set.mem_iUnion₂.2 ⟨c, hcT, y, ⟨hyc, ⟨z, hy, h0⟩, hreg⟩, ?_⟩)
      have hl : Over i y (liftOf i y) := by
        have hex : ∃ z, Over i y z := ⟨z, hy⟩
        simp only [liftOf, dif_pos hex]
        exact hex.choose_spec
      have ho : SameOrbit (liftOf i y) z := (GlobalTheory.T.points_eq_iff_same_torus_orbit m n X i y y _ _ hl hy).1 rfl
      rw [projCoord, ratios_eq_of_sameOrbit Ψ ho h0, ratios_of_proj Ψ hzv]

theorem exists_form_chart {X : Scheme.{0}} [IsIntegral X] (i : X ⟶ MP ℤ m n) [IsClosedImmersion i]
    (hX : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) D) :
    ∃ (j : Pol n) (a : Fin (m + 1) → ℕ), IsMultiHomog j a ∧ j ∉ ptIdeal (i (genericPoint X)) ∧
      ∀ y z, Over i y z → eval z (map (Int.castRingHom ℂ) j) ≠ 0 →
        ∃ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, y ∈ c.e.source := by
  obtain ⟨U, x, hU, hg, hx⟩ := GlobalTheory.T.arithmetic_variety_generically_etale_coordinates X (i ≫ mpStr ℤ m n) D hX
  obtain ⟨j, a, hj, hjP, hjU⟩ := GlobalTheory.T.exists_form_nonvanishing_on_chart m n X i U hg
  refine ⟨j, a, hj, hjP, fun y z hyz hz => ?_⟩
  obtain ⟨c, hc, -⟩ := GlobalTheory.AlgChart.exists_of_etale hU x hx (hjU y z hyz hz)
  exact ⟨c, hc⟩

end GlobalTheory.CompanionTheory.MixZ.ArchEq

namespace GlobalTheory.CompanionTheory.MixZ

open ArchEq in

theorem archIntEq_of_integrable : ArchIntegrableOn → ArchIntEq := by
  intro hI m n Nh M B A hB hA X _ i _ D hX sB sA r hr f g hfg hrat
  classical
  have hC := hX.charZero
  obtain ⟨-, hp₃, hp₄, -⟩ := GlobalTheory.T.mixed_cycle_point_dictionary m n X i (D + 1) hX.dim_eq
  have hP := hp₄ (hp₃.2 hC)
  have hPp : (ptIdeal (i (genericPoint X))).IsPrime := hP.2.1.1
  have hex : ∃ Ψ : LinProj n D, IsGoodProj (ptIdeal (i (genericPoint X))) Ψ :=
    ReciprocityTheory.ChartRestriction.G.Geo.goodProjExists _ _ _ D hP
  haveI hsc : SecondCountableTopology (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) := GlobalTheory.T.complex_points_second_countable m n X i D hX
  unfold ptsIntegral
  rw [dif_pos hex]
  set Ψ : LinProj n D := hex.choose with hΨdef
  have hΨ : IsGoodProj (ptIdeal (i (genericPoint X))) Ψ := hex.choose_spec
  obtain ⟨j, aj, hj, hjP, hjc⟩ := exists_form_chart i hX
  have hfg' := hfg
  obtain ⟨α, β, hα, hβ, hfP, hgP, -⟩ := hfg'
  set N : Pol n := j * f * g with hNdef
  have hNh : IsMultiHomog N (aj + α + β) := homog_mul (homog_mul hj hα) hβ
  have hNP : N ∉ ptIdeal (i (genericPoint X)) := fun h => by
    rcases hPp.mem_or_mem h with h | h
    · rcases hPp.mem_or_mem h with h | h
      · exact hjP h
      · exact hfP h
    · exact hgP h
  have hNe : ∀ z : (Σ k, Bk n k) → ℂ, eval z (map (Int.castRingHom ℂ) N) ≠ 0 →
      eval z (map (Int.castRingHom ℂ) j) ≠ 0 ∧ eval z (map (Int.castRingHom ℂ) f) ≠ 0 ∧
        eval z (map (Int.castRingHom ℂ) g) ≠ 0 := fun z h => by
    simp only [hNdef, map_mul, mul_ne_zero_iff] at h
    exact ⟨h.1.1, h.1.2, h.2⟩
  have hcov : ∀ y z, Over i y z → eval z (map (Int.castRingHom ℂ) N) ≠ 0 →
      ∃ c : GlobalTheory.AlgChart (i ≫ mpStr ℤ m n) σ₀ D, y ∈ c.e.source := fun y z h h' => hjc y z h (hNe z h').1

  have hL : (Nh.restr i).archInt (M.restr i) D hr =
      ((Nh.restr i).φ σ₀).chernInt D (offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr))
        (GlobalTheory.Cartier.logNorm ((M.restr i).φ σ₀) r) :=
    finsum_eq_single _ σ₀ fun σ hσ => absurd (Subsingleton.elim σ σ₀) hσ
  rw [hL]
  set S₀ := offSupp (i ≫ mpStr ℤ m n) σ₀ ((M.restr i).div hr) with hS₀
  set F := GlobalTheory.Cartier.logNorm ((M.restr i).φ σ₀) r with hF
  set μ : ℤˣ → Measure (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) := fun ε => ((Nh.restr i).φ σ₀).chernPart D ε with hμ
  set G := pieceSet i Ψ N with hG
  have hGo : IsOpen G := isOpen_pieceSet i Ψ N
  have hGS : G ⊆ S₀ := by
    rintro y ⟨e, Γ, hp, hy⟩
    have hv := hp.2.2 (e y) (e.map_source hy)
    rw [e.left_inv hy] at hv
    exact (GlobalTheory.T.rational_section_log_norm_on_sheet m n M A X i r hr f g hfg hrat y _ hv.1 (hNe _ hv.2.2.2).2.1 (hNe _ hv.2.2.2).2.2).1
  have hnull : ∀ ε, μ ε Gᶜ = 0 := fun ε => by
    refine GlobalTheory.T.chern_part_null_set_zero _ ε _ hGo.measurableSet.compl fun c => ?_
    have hsub : c.e.target ∩ c.e.symm ⁻¹' Gᶜ ⊆
        (c.e.target ∩ c.e.symm ⁻¹' {y | (∃ z, Over i y z ∧ Ψ (ReciprocityTheory.ChartRestriction.G.Geo.segre z) 0 = 0) ∨ ¬ IsRegAt i Ψ c y}) ∪
        (c.e.target ∩ c.e.symm ⁻¹' {y | ∃ z, IsUnder (PtsOver.map i rfl _ y) z ∧ eval z (map (Int.castRingHom ℂ) N) = 0}) := by
      rintro v ⟨hv, hvG⟩
      obtain ⟨z, -, hz⟩ := GlobalTheory.T.complex_point_lifts_to_multicone m n X i (c.e.symm v)
      by_cases hNz : eval z (map (Int.castRingHom ℂ) N) = 0
      · exact Or.inr ⟨hv, z, hz, hNz⟩
      · refine Or.inl ⟨hv, ?_⟩
        by_cases h0 : Ψ (ReciprocityTheory.ChartRestriction.G.Geo.segre z) 0 = 0
        · exact Or.inl ⟨z, hz, h0⟩
        · exact Or.inr fun hreg => hvG (GlobalTheory.T.projection_regular_on_nonvanishing_chart m n X i D Ψ N _ hNh c _ z (c.e.map_target hv) hz hNz h0 hreg)
    exact measure_mono_null hsub (measure_union_null (GlobalTheory.T.bad_projection_locus_null m n X i D hX Ψ hΨ c)
      ((GlobalTheory.T.hypersurface_complex_points_measurable_null m n X i D N _ hNh hNP).2 c))

  let J := {p : OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ) ×
    ((Fin D → ℂ) → (Σ k, Bk n k) → ℂ) // IsPiece i Ψ N p.1 p.2}
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable (fun p : J => p.1.1.source)
    (fun p => p.1.1.open_source)
  haveI : Countable T := hTc.to_subtype
  let e : T → OpenPartialHomeomorph (GlobalTheory.CxPts (i ≫ mpStr ℤ m n) σ₀) (Fin D → ℂ) := fun l => l.1.1.1
  let Γ : T → (Fin D → ℂ) → (Σ k, Bk n k) → ℂ := fun l => l.1.1.2
  have hpc : ∀ l, IsPiece i Ψ N (e l) (Γ l) := fun l => l.1.2
  let ρ : T → (Fin D → ℂ) → ℝ := fun l => maDensity (fun _ y' => Real.log (B.h (Γ l y')))
  have hd := fun l => GlobalTheory.T.local_chart_sheet_decomposition m n Nh B hB sB X i D Ψ N (e l) (Γ l) (hpc l)
  have hcovG : G ⊆ ⋃ l, (e l).source := by
    rintro y ⟨e', Γ', hp, hy⟩
    have hmem : y ∈ ⋃ p : J, p.1.1.source := Set.mem_iUnion.2 ⟨⟨(e', Γ'), hp⟩, hy⟩
    rw [← hTU] at hmem
    obtain ⟨p, hp, hy⟩ := Set.mem_iUnion₂.1 hmem
    exact Set.mem_iUnion.2 ⟨⟨p, hp⟩, hy⟩
  have hIS := hI m n Nh M X i D hX r hr σ₀
  have hIG : ∀ ε, IntegrableOn F G (μ ε) := fun ε => by
    rcases Int.units_eq_one_or ε with rfl | rfl
    · exact hIS.1.mono_set hGS
    · exact hIS.2.mono_set hGS
  obtain ⟨S, hSm, hSs, hSd, hSU, hSI⟩ := GlobalTheory.T.density_chart_integral_formula μ e ρ (fun l => (hd l).1) (fun l ε => (hd l).2 ε) G
    hGo.measurableSet hcovG F hIG
  have hae : ∀ ε, S₀ =ᵐ[μ ε] G := fun ε => by
    refine (ae_eq_set.2 ⟨measure_mono_null (fun y hy => hy.2) (hnull ε), ?_⟩)
    rw [Set.diff_eq_empty.2 hGS, measure_empty]
  have hchern : ((Nh.restr i).φ σ₀).chernInt D S₀ F = ∫ y in G, F y ∂μ 1 - ∫ y in G, F y ∂μ (-1) := by
    rw [GlobalTheory.Weight.chernInt, setIntegral_congr_set (hae 1), setIntegral_congr_set (hae (-1))]
  rw [hchern, hSI, ReciprocityTheory.ChartRestriction.G.Geo.ptsIntegralAt]
  refine integral_congr_ae ?_
  filter_upwards [ae_cover i hP Ψ hΨ N _ hNh hNP hcov, GlobalTheory.T.sheet_density_log_norm_formula m n _ D Ψ B A f g hP hΨ sB hfg] with v h1 h2
  have h3 : ∀ z ∈ mcPts (ptIdeal (i (genericPoint X))), Ψ (ReciprocityTheory.ChartRestriction.G.Geo.segre z) = Fin.cons 1 v →
      ∃ y, Over i y z ∧ y ∈ ⋃ l, S l := fun z hz hzv => by
    rw [hSU]
    exact h1 z hz hzv
  have h4 := GlobalTheory.T.sheet_integral_projection_formula m n X i D Ψ N hP hΨ e Γ S hpc hSs hSd v h3
    (fun w => sheetDensity (ptIdeal (i (genericPoint X))) Ψ (pot fun _ : Fin D => B) (logNormRat A f g) v w)
    (fun l => F ((e l).symm v) * ρ l v) (fun l hl => by
      obtain ⟨y, hyS, rfl⟩ := hl
      have hvt := (e l).map_source (hSs l hyS)
      have hv := (hpc l).2.2 _ hvt
      have hs : IsSheet (ptIdeal (i (genericPoint X))) Ψ (e l y) (ReciprocityTheory.ChartRestriction.G.Geo.segre (Γ l (e l y))) (Γ l) := by
        refine ⟨rfl, ?_⟩
        filter_upwards [(e l).open_target.mem_nhds hvt] with v' hv'
        have hv2 := (hpc l).2.2 v' hv'
        exact ⟨(hpc l).2.1.differentiableAt ((e l).open_target.mem_nhds hv'), hv2.2.1, hv2.2.2.1⟩
      rw [h2 _ _ hs]
      congr 1
      exact (GlobalTheory.T.rational_section_log_norm_on_sheet m n M A X i r hr f g hfg hrat _ _ hv.1 (hNe _ hv.2.2.2).2.1 (hNe _ hv.2.2.2).2.2).2.symm)
  exact h4.symm

end GlobalTheory.CompanionTheory.MixZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DoubleCosetMultiplicationStatement
section
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.double_coset_multiplication : DcosMul := by
  first | exact @GlobalTheory.CompanionTheory.DcosProduct.dcosMul | exact GlobalTheory.CompanionTheory.DcosProduct.dcosMul | (intros; apply GlobalTheory.CompanionTheory.DcosProduct.dcosMul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteUnitaryMultiplicationStatement
section
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_unitary_multiplication : FUMul := by
  first | exact @GlobalTheory.CompanionTheory.FUMulPf.fuMul | exact GlobalTheory.CompanionTheory.FUMulPf.fuMul | (intros; apply GlobalTheory.CompanionTheory.FUMulPf.fuMul <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriDoubleCosetFiniteStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwahori_double_coset_finite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (a : ℕ) (t : GLw a w), (Function.support fun q : GLw a w ⧸ iwGL a w => dcos a w t q.out).Finite ∧ IsOpen (iwGL a w : Set (GLw a w)) ∧ IsCompact (iwGL a w : Set (GLw a w)) ∧ iwGL a w ≤ GlobalTheory.LFun.KGL w a ∧ (iwGL a w).relIndex (GlobalTheory.LFun.KGL w a) ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.IwDcosFin.dcos_finite_support_iwGL | exact GlobalTheory.CompanionTheory.IwDcosFin.dcos_finite_support_iwGL | (intros; apply GlobalTheory.CompanionTheory.IwDcosFin.dcos_finite_support_iwGL <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingTransferOfStatement
section
open GlobalTheory.BCT GlobalTheory.UnitaryBC PositivityTheory.Rg.Bc.ArchbcB.B PositivityTheory.Rg.BcB.F.MT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matching_transfer_of : MatchTOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchPow.matchTOf | exact GlobalTheory.CompanionTheory.MatchPow.matchTOf | (intros; apply GlobalTheory.CompanionTheory.MatchPow.matchTOf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MatchingUnitOfStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.matching_unit_of : PositivityTheory.Rg.BcB.F.MLM.MatchLMUnitOf := by
  first | exact @GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf | exact GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf | (intros; apply GlobalTheory.CompanionTheory.MatchUnit.matchLMUnitOf <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityInert
section
noncomputable section

open NumberField IsDedekindDomain Polynomial
open GlobalTheory.BCT GlobalTheory.UnitaryBC

namespace GlobalTheory.CompanionTheory.MuInertPlace

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem delta_indep {w : Pl E} (hw : ¬ IsSplitAt w) (μ μ' : (w.adicCompletion E)ˣ →* ℂˣ)
    (Q₁ Q₂ : (w.adicCompletion E)[X]) : delta w μ Q₁ Q₂ = delta w μ' Q₁ Q₂ := by
  simp only [delta, hw, if_false]

theorem match_indep {n a b : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w) (μ μ' : (w.adicCompletion E)ˣ →* ℂˣ)
    (f : UL n w → ℂ) (φ : GLw a w × GLw b w → ℂ) : Match n a b w μ f φ ↔ Match n a b w μ' f φ := by
  unfold Match
  simp only [delta_indep hw μ μ']

theorem muInert : PositivityTheory.Rg.BcB.F.MLM.MuInert := by
  intro E _ _ _ n a b w hw μ μ' f φ
  exact match_indep hw μ μ' f φ

end GlobalTheory.CompanionTheory.MuInertPlace
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialLocusLocalToGlobalStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_locus_local_to_global : ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ N : LB (A ⊗ Y).left, N.IsLB →
    Triv (ev N (1 : Y ⟶ A) (𝟙 Y)) → ∀ (T : Scheme.{0}) (t : T ⟶ Y.left),
    (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ Locus N (W.ι ≫ t)) → Locus N t := by
  first | exact @GlobalTheory.CompanionTheory.TrivLoc.locus_of_locally | exact GlobalTheory.CompanionTheory.TrivLoc.locus_of_locally | (intros; apply GlobalTheory.CompanionTheory.TrivLoc.locus_of_locally <;> assumption)
end

