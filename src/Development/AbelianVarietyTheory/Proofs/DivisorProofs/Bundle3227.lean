import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1663
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2776
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3211
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0798
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0568
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SupremumOnGoodPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3200
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineDegreeIdentity
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineCos

theorem map_cosSq_part_le : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ α : (hY.atlas σ).Fld, (hY.atlas σ).IsForm α → ∀ ε : ℤˣ,
      ∃ C : ENNReal, C ≠ ⊤ ∧ Measure.map v ((hY.atlas σ).part α ε) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv α hα ε
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  have loc : ∀ y : CxPts p σ, ∃ W : Set (CxPts p σ), IsOpen W ∧ y ∈ W ∧ ContinuousOn v W ∧ ∃ C : ENNReal, C ≠ ⊤ ∧
      Measure.map v (((hY.atlas σ).part α ε).restrict W) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
    intro y
    obtain ⟨c, G, s, O, hy, hO, hcy, hOt, hG, hGp⟩ := GlobalTheory.T.flag_bundle_curvature_at_point k B Y q p d hB hY π w E h H flB fl hfl σ v hv y
    have hρ : ContinuousOn (fun z => ((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α c z) O :=
      (continuousOn_const.mul ((hY.atlas σ).continuousOn_reDens hα c)).mono hOt
    obtain ⟨N, hN, hzN, hNO, C, hC, hle⟩ :=
      GlobalTheory.T.local_density_bound_near_point d O (fun z => ((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α c z) G s (c.e y) hO hcy hρ hG fun z hz => (hGp z hz).1
    have hWo : IsOpen (c.e.source ∩ c.e ⁻¹' N) := c.e.isOpen_inter_preimage hN
    have hWc : ContinuousOn v (c.e.source ∩ c.e ⁻¹' N) := by
      have hF := GlobalTheory.LineCos.continuousOn_cosSq s hG fun z hz => (hGp z hz).1
      have : ContinuousOn (fun y => GlobalTheory.LineCos.cosSq s (G (GlobalTheory.LineCos.base (c.e y))) (GlobalTheory.LineCos.fib (c.e y)))
          (c.e.source ∩ c.e ⁻¹' N) :=
        hF.comp (c.e.continuousOn.mono Set.inter_subset_left) fun y hy => hNO hy.2
      refine this.congr fun y' hy' => ?_
      have := (hGp (c.e y') (hNO hy'.2)).2
      rwa [c.e.left_inv hy'.1] at this
    refine ⟨_, hWo, ⟨hy, hzN⟩, hWc, C, hC, ?_⟩
    set W := c.e.source ∩ c.e ⁻¹' N with hWdef
    have hWm : MeasurableSet W := hWo.measurableSet
    have hNt : N ⊆ c.e.target := hNO.trans hOt
    set ν := (volume.restrict N).withDensity fun z => ENNReal.ofReal (((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α c z) with hνdef
    have haem : AEMeasurable c.e.symm ν :=
      ((c.e.continuousOn_symm.mono hNt).aemeasurable hN.measurableSet).mono_ac (withDensity_absolutelyContinuous _ _)
    have hcompat : ∀ (i j : (hY.atlas σ).ι) (y : CxPts p σ), y ∈ ((hY.atlas σ).e i).source → y ∈ ((hY.atlas σ).e j).source →
        ENNReal.ofReal (((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α i ((hY.atlas σ).e i y)) =
          ENNReal.ofReal (‖ChartGlue.transDet ((hY.atlas σ).e i) ((hY.atlas σ).e j) y‖ ^ 2) *
            ENNReal.ofReal (((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α j ((hY.atlas σ).e j y)) :=
      (hY.atlas σ).ofReal_compat (fun i v => ((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α i v)
        (fun i j y hi hj => by rw [(hY.atlas σ).reDens_compat hα i j y hi hj]; ring)
    have hrest : ((hY.atlas σ).part α ε).restrict W = Measure.map c.e.symm ν := by
      ext A hA
      have hAW : MeasurableSet (A ∩ W) := hA.inter hWm
      have hsub : A ∩ W ⊆ c.e.source := fun y hy => hy.2.1
      have hp : (hY.atlas σ).part α ε = ChartGlue.glueMeas (hY.atlas σ).e
          (fun i y => ENNReal.ofReal (((ε : ℤ) : ℝ) * (hY.atlas σ).reDens α i ((hY.atlas σ).e i y))) := rfl
      rw [Measure.restrict_apply hA, Measure.map_apply_of_aemeasurable haem hA, hp,
        ChartGlue.glueMeas_apply _ _ (hY.atlas σ).holo hcompat c hAW hsub,
        ChartGlue.chartMeas_apply_of_subset ((hY.atlas σ).e c) _ hAW hsub, hνdef, withDensity_apply' _ _,
        Measure.restrict_restrict' hN.measurableSet]
      have himg : (c.e '' (A ∩ W)) = c.e.symm ⁻¹' A ∩ N := by
        ext z
        constructor
        · rintro ⟨y', ⟨hyA, hys, hyN⟩, rfl⟩
          exact ⟨by simpa [c.e.left_inv hys] using hyA, hyN⟩
        · rintro ⟨hzA, hzN'⟩
          exact ⟨c.e.symm z, ⟨hzA, c.e.map_target (hNt hzN'), by simpa [c.e.right_inv (hNt hzN')] using hzN'⟩,
            c.e.right_inv (hNt hzN')⟩
      change ∫⁻ v in c.e '' (A ∩ W), ENNReal.ofReal (((ε : ℤ) : ℝ) *
          (hY.atlas σ).reDens α c (c.e (c.e.symm v))) = _
      rw [himg]
      refine setLIntegral_congr_fun (himg ▸ ChartGlue.measurableSet_image _ hAW hsub) fun z hz => ?_
      rw [c.e.right_inv (hNt hz.2)]
    have hvae : AEMeasurable v (Measure.map c.e.symm ν) := by
      rw [← hrest]
      exact hWc.aemeasurable hWm
    rw [hrest, AEMeasurable.map_map_of_aemeasurable hvae haem]
    refine le_of_eq_of_le (Measure.map_congr ?_) hle
    refine (withDensity_absolutelyContinuous _ _).ae_le ((ae_restrict_iff' hN.measurableSet).2
      (Filter.Eventually.of_forall fun z hz => (hGp z (hNO hz)).2))

  choose W hWo hyW hWc C hC hle using loc
  have hvc : Continuous v :=
    continuous_iff_continuousAt.2 fun y => (hWc y).continuousAt ((hWo y).mem_nhds (hyW y))
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo fun y _ => Set.mem_iUnion.2 ⟨y, hyW y⟩
  refine ⟨∑ y ∈ t, C y, ENNReal.sum_ne_top.2 fun y _ => hC y, Measure.le_iff.2 fun S hS => ?_⟩
  have hsub : v ⁻¹' S ⊆ ⋃ y ∈ t, (v ⁻¹' S ∩ W y) := fun x hx => by
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact Set.mem_iUnion₂.2 ⟨y, hy, hx, hxy⟩
  calc Measure.map v ((hY.atlas σ).part α ε) S = (hY.atlas σ).part α ε (v ⁻¹' S) :=
        Measure.map_apply hvc.measurable hS
    _ ≤ ∑ y ∈ t, (hY.atlas σ).part α ε (v ⁻¹' S ∩ W y) :=
        (measure_mono hsub).trans (measure_biUnion_finset_le t _)
    _ = ∑ y ∈ t, Measure.map v (((hY.atlas σ).part α ε).restrict (W y)) S := by
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Measure.map_apply hvc.measurable hS, Measure.restrict_apply (hvc.measurable hS)]
    _ ≤ ∑ y ∈ t, C y * volume.restrict (Set.Icc (0 : ℝ) 1) S :=
        Finset.sum_le_sum fun y _ => Measure.le_iff.1 (hle y) S hS
    _ = ((∑ y ∈ t, C y) • volume.restrict (Set.Icc (0 : ℝ) 1)) S := by
        rw [Measure.smul_apply, smul_eq_mul, Finset.sum_mul]

end GlobalTheory.LineCos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleOverFieldIrreducible
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits

namespace GlobalTheory.FlagIrrFld

theorem isPreirreducible_of_connect {Y : Scheme.{0}}
    (h : ∀ y₁ y₂ : Y, ∃ (T : Scheme.{0}) (f : T ⟶ Y), IrreducibleSpace T ∧ y₁ ∈ Set.range f ∧ y₂ ∈ Set.range f) :
    IsPreirreducible (Set.univ : Set Y) := by
  rintro u v hu hv ⟨y₁, -, hy₁⟩ ⟨y₂, -, hy₂⟩
  obtain ⟨T, f, hT, ⟨t₁, rfl⟩, ⟨t₂, rfl⟩⟩ := h y₁ y₂
  obtain ⟨t, -, ht⟩ := (IrreducibleSpace.isIrreducible_univ T).isPreirreducible _ _
    (hu.preimage f.continuous) (hv.preimage f.continuous) ⟨t₁, trivial, hy₁⟩ ⟨t₂, trivial, hy₂⟩
  exact ⟨f t, trivial, ht⟩

theorem nonempty_of_field (K : Type) [Field K] (Y : Scheme.{0}) (π : Y ⟶ Spec (CommRingCat.of K)) (ι : Type)
    [Fintype ι] (E : ι → (Spec (CommRingCat.of K)).Modules) (r : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)) (hE : ∀ a, GlobalTheory.VB.IsVB (E a) (r a))
    (hF : IsFlagBundle π E r fl) : Nonempty Y := by
  have fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback (𝟙 (Spec (CommRingCat.of K)))).obj (E a)) (r a) :=
    fun a => (GlobalTheory.T.vector_bundle_over_field_has_flag K _ (r a) ((hE a).pullback _)).some
  obtain ⟨g', -, -⟩ := hF _ (𝟙 _) fl'
  obtain ⟨x⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  exact ⟨g' x⟩

theorem irreducibleSpace_of_isFlagBundle : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (π : Y ⟶ Spec (CommRingCat.of K)) (ι : Type) [Fintype ι]
    (E : ι → (Spec (CommRingCat.of K)).Modules) (r : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)),
    (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → IrreducibleSpace Y := by
  intro K _ Y π ι _ E r fl hE hF
  haveI := nonempty_of_field K Y π ι E r fl hE hF
  refine { isPreirreducible_univ := isPreirreducible_of_connect fun y₁ y₂ => ?_, toNonempty := inferInstance }
  set p₁ := Y.fromSpecResidueField y₁
  set p₂ := Y.fromSpecResidueField y₂
  obtain ⟨x₁⟩ : Nonempty (Spec (Y.residueField y₁)) := inferInstance
  obtain ⟨x₂⟩ : Nonempty (Spec (Y.residueField y₂)) := inferInstance
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p₁ ≫ π) (g := p₂ ≫ π) x₁ x₂
    (Subsingleton.elim _ _)
  set P := pullback (p₁ ≫ π) (p₂ ≫ π)
  let L : Type := P.residueField z
  let u : Spec (CommRingCat.of L) ⟶ P := P.fromSpecResidueField z
  have hq : (u ≫ pullback.fst _ _ ≫ p₁) ≫ π = (u ≫ pullback.snd _ _ ≫ p₂) ≫ π := by
    simp only [Category.assoc]
    exact congrArg (u ≫ ·) pullback.condition
  obtain ⟨T, t₁, t₂, f, hT, h₁, h₂⟩ := GlobalTheory.T.flag_bundle_points_irreducible_connected _ Y π ι E r fl hE hF L _ _ hq
  obtain ⟨w⟩ : Nonempty (Spec (CommRingCat.of L)) := inferInstance
  have m₁ : p₁ ((pullback.fst (p₁ ≫ π) (p₂ ≫ π)) (u w)) = y₁ := by
    have := Scheme.range_fromSpecResidueField y₁ ▸ Set.mem_range_self (f := p₁) ((pullback.fst (p₁ ≫ π) (p₂ ≫ π)) (u w))
    exact this
  have m₂ : p₂ ((pullback.snd (p₁ ≫ π) (p₂ ≫ π)) (u w)) = y₂ := by
    have := Scheme.range_fromSpecResidueField y₂ ▸ Set.mem_range_self (f := p₂) ((pullback.snd (p₁ ≫ π) (p₂ ≫ π)) (u w))
    exact this
  refine ⟨T, f, hT, ⟨t₁ w, ?_⟩, ⟨t₂ w, ?_⟩⟩
  · rw [← m₁, ← Scheme.Hom.comp_apply, h₁]; rfl
  · rw [← m₂, ← Scheme.Hom.comp_apply, h₂]; rfl

end GlobalTheory.FlagIrrFld
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFrameCoverTangentCompat
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HtGen.CoverChart

theorem pairDet_tri {R J : Type} [CommRing R] {m g k : ℕ} (h : J → Fin g → R) (a b : Fin m → Fin g → R)
    (T : Fin m → Fin m → R) (hT : ∀ i l, i < l → T i l = 0) (hb : ∀ i, b i = ∑ l, T i l • a l) (hk : k ≤ m)
    (σ : Fin k → J) :
    pairDet h b hk σ = (∏ l : Fin k, T (Fin.castLE hk l) (Fin.castLE hk l)) * pairDet h a hk σ := by
  have e : ∀ c : Fin m → Fin g → R, pairDet h c hk σ = minor (fun l r => ∑ i, h (σ r) i * c l i) hk id := fun c =>
    (Matrix.det_transpose _).symm
  rw [e, e]
  refine Chart.minor_tri _ _ T hT (fun i => funext fun r => ?_) hk id
  simp only [hb, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => by ring

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := (Spec.map_comp _ _)

variable {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y)

theorem gen_eq' {G : Scheme.{0}} [IsIntegral G] (z : G) :
    spMap (algebraMap (G.presheaf.stalk z) G.functionField) ≫ G.fromSpecStalk z = G.fromSpecStalk (genericPoint G) :=
  Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes z)

theorem stalk_eq (z : V.G) :
    spMap (V.π.stalkMap z).hom ≫ Y.X.fromSpecStalk (V.π z) = V.G.fromSpecStalk z ≫ V.π :=
  Scheme.SpecMap_stalkMap_fromSpecStalk V.π

theorem alg_comp_stalkMap (z : V.G) :
    (algebraMap (V.G.presheaf.stalk z) V.G.functionField).comp (V.π.stalkMap z).hom =
      V.φ.comp (algebraMap (Y.X.presheaf.stalk (V.π z)) Y.X.functionField) := by
  have h : spMap ((algebraMap (V.G.presheaf.stalk z) V.G.functionField).comp (V.π.stalkMap z).hom) ≫
        Y.X.fromSpecStalk (V.π z) =
      spMap (V.φ.comp (algebraMap (Y.X.presheaf.stalk (V.π z)) Y.X.functionField)) ≫ Y.X.fromSpecStalk (V.π z) := by
    rw [sp_comp, sp_comp, Category.assoc, Category.assoc, stalk_eq, gen_eq', ← Category.assoc, gen_eq', V.φ_spec]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono _).1 h))

end GlobalTheory.HtGen.CoverChart

open GlobalTheory.HtGen.CoverChart GlobalTheory.LineNorm.Chart GlobalTheory.LieMet in

theorem GlobalTheory.HtGen.CoverChart.pairDet_div_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (m : ℕ) (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left)) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d : Y.X → Fin m → Y.Fnˣ), IsFlagFrame t ρ u₀ f d → ∀ (U : V.X.Opens) (hU : IsAffineOpen U) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)), IsTanBasis t (hU.fromSpec ≫ ρ') e → ∀ (J : Type) (h : J → Fin g → Γ(V.X, U)) (k : ℕ) (hk : k ≤ m), ∃ s : (Fin k → J) → V.G.functionField, ∀ z : V.G, V.j z ∈ U → ∃ (α : Γ(V.X, U) →+* V.G.presheaf.stalk z) (a : Fin m → Fin g → V.G.presheaf.stalk z), spMap α ≫ hU.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧ (∀ l, IsCombAtG t (spMap α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l) (spMap (dualMap (V.π.stalkMap z).hom) ≫ f (V.π z) l)) ∧ ∀ σ, s σ / V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn) = algebraMap (V.G.presheaf.stalk z) V.G.functionField (pairDet (fun j i => α (h j i)) a hk σ) := by
  intro E _ _ _ H X t F _ _ Y V ρ' ρ hρ m u₀ f d hf U hU g e he J h k hk
  by_cases hgen : V.j (genericPoint V.G) ∈ U
  swap
  · exact ⟨fun _ => 0, fun z hz => absurd
      (((genericPoint_specializes z).map V.j.continuous).mem_open U.isOpen hz) hgen⟩
  choose α hα using fun (z : V.G) (hz : V.j z ∈ U) => exists_stalkHom hU V.j z hz
  have hα' : ∀ z hz, spMap (α z hz) ≫ hU.fromSpec ≫ ρ' = V.G.fromSpecStalk z ≫ V.π ≫ ρ := fun z hz => by
    rw [← Category.assoc, hα, Category.assoc, hρ]
  let ι₀ : Γ(V.X, U) →+* V.G.functionField := α _ hgen
  have hι : spMap ι₀ ≫ hU.fromSpec ≫ ρ' = spMap V.φ ≫ GlobalTheory.ShFam.genericPt Y ≫ ρ :=
    (hα' _ hgen).trans (by rw [← Category.assoc, V.φ_spec, Category.assoc]; rfl)
  have hαι : ∀ z hz, (algebraMap (V.G.presheaf.stalk z) V.G.functionField).comp (α z hz) = ι₀ := fun z hz =>
    ringHom_ext hU (by
      rw [sp_comp, Category.assoc, hα, ← Category.assoc, gen_eq']
      exact (hα _ hgen).symm)
  have ha : ∀ z (hz : V.j z ∈ U) l, ∃ a, IsCombAtG t (spMap (α z hz) ≫ hU.fromSpec ≫ ρ')
      (fun i => spMap (dualMap (α z hz)) ≫ e i) a (spMap (dualMap (V.π.stalkMap z).hom) ≫ f (V.π z) l) := fun z hz l =>
    (he.2 _ (α z hz) _ (isTan_map _ (by
      rw [hα', ← Category.assoc, ← Category.assoc, ← stalk_eq]; rfl) (hf.tan (V.π z) l))).exists
  choose a ha using ha
  have key : ∀ z (hz : V.j z ∈ U) i, ∃ cf : Fin m → Y.Fn, cf i = d (V.π z) i ∧ (∀ k, i < k → cf k = 0) ∧
      IsCombAtG t (spMap ι₀ ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap ι₀) ≫ e i)
        (∑ l, V.φ (cf l) • fun j => algebraMap (V.G.presheaf.stalk z) V.G.functionField (a z hz l j))
        (spMap (dualMap V.φ) ≫ u₀ i) := by
    intro z hz i
    obtain ⟨cf, h1, h2, h3⟩ := hf.tri (V.π z) i
    have h4 := GlobalTheory.LatDRFree.comb_map t V.φ h3
    refine ⟨cf, h1, h2, comb_comb (fun j => isTan_map _ rfl (he.1 j)) (fun l => ?_) (hι ▸ h4)⟩
    have := coord_map _ (algebraMap (V.G.presheaf.stalk z) V.G.functionField) (ha z hz l)
    rw [hαι, dual_comp, alg_comp_stalkMap] at this
    rw [dual_comp]
    exact this
  choose T hT1 hT2 hT3 using key
  have hA₀ : ∀ i, ∃ b, IsCombAtG t (spMap ι₀ ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap ι₀) ≫ e i) b
      (spMap (dualMap V.φ) ≫ u₀ i) := fun i => ⟨_, hT3 _ hgen i⟩
  choose A₀ hA₀ using hA₀
  have hA : ∀ z hz i, A₀ i = ∑ l, V.φ (T z hz i l) • fun j => algebraMap _ V.G.functionField (a z hz l j) := fun z hz i =>
    (he.2 _ ι₀ _ (comb_tan (fun j => isTan_map _ rfl (he.1 j)) (hT3 z hz i))).unique (hA₀ i) (hT3 z hz i)
  refine ⟨fun σ => pairDet (fun j i => ι₀ (h j i)) A₀ hk σ, fun z hz => ⟨α z hz, a z hz, hα z hz, ha z hz, fun σ => ?_⟩⟩
  have hne : V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn) ≠ 0 :=
    (_root_.map_ne_zero V.φ).2 (Units.ne_zero _)
  beta_reduce
  rw [div_eq_iff hne, map_pairDet, pairDet_tri _ _ A₀ (fun i l => V.φ (T z hz i l))
    (fun i l hl => by simp only [hT2 z hz i l hl, map_zero]) (hA z hz), mul_comm, Units.coe_prod, map_prod, ← hαι z hz]
  simp only [hT1]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFramePrimeTangentCompat
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.HtGen.FlagPoint

open GlobalTheory.LineNorm.Chart GlobalTheory.LieMet

theorem residueCharacteristic_eq {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) {q : ℕ} (hq : q.Prime)
    (hv : (q : 𝓞 F) ∈ v.asIdeal) : resP v = q := by
  refine (Nat.prime_dvd_prime_iff_eq (residueCharacteristic_prime v) hq).1 (ringChar.dvd ?_)
  rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  exact hv

theorem chart {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
    {t : SAB H X} {S G : Scheme.{0}} (j : G ⟶ S) (ρ' : S ⟶ X) {K : Type} [Field K] (O : ValuationSubring K)
    {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C] (io : K →+* C) (ioO : O →+* intO C)
    (hio : (intO C).subtype.comp ioO = io.comp O.subtype) (z : Sp K ⟶ G) (yt : Sp O ⟶ S)
    (hyt : spMap O.subtype ≫ yt = z ≫ j) {U : S.Opens} (hU : IsAffineOpen U) (hin : ⊤ ≤ yt ⁻¹ᵁ U) {g m : ℕ}
    (e : Fin g → (Sp (DualNumber Γ(S, U)) ⟶ t.G.left)) (α : Γ(S, U) →+* G.presheaf.stalk (below z))
    (hα : spMap α ≫ hU.fromSpec = G.fromSpecStalk (below z) ≫ j) (a : Fin m → Fin g → G.presheaf.stalk (below z))
    (w : Fin m → (Sp (DualNumber (G.presheaf.stalk (below z))) ⟶ t.G.left))
    (ha : ∀ l, IsCombAtG t (spMap α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l) (w l))
    (ψ : G.presheaf.stalk (below z) →+* C) (hψ : ψ = io.comp (Scheme.stalkClosedPointTo z).hom) :
    ∃ β : Γ(S, U) →+* intO C, spMap β ≫ hU.fromSpec = spMap ioO ≫ yt ∧ (∀ r, ψ (α r) = β r) ∧
      ∀ l, IsCombAtG t (spMap (intO C).subtype ≫ (spMap ioO ≫ yt) ≫ ρ')
        (fun i => spMap (dualMap (intO C).subtype) ≫ spMap (dualMap β) ≫ e i) (fun i => ψ (a l i))
        (spMap (dualMap ψ) ≫ w l) := by
  obtain ⟨β, hβ⟩ := exists_ringHom hU yt hin
  obtain ⟨σ, hσ₀⟩ : ∃ σ : G.presheaf.stalk (below z) →+* K, σ = (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  have hσ : σ.comp α = O.subtype.comp β := ringHom_ext hU (by
    rw [← spMap_comp', ← spMap_comp', Category.assoc, Category.assoc, hα, hβ, hyt, ← Category.assoc, hσ₀]
    exact congrArg (· ≫ j) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z))
  have h1 : spMap (ioO.comp β) ≫ hU.fromSpec = spMap ioO ≫ yt := by
    rw [← spMap_comp', Category.assoc, hβ]
  have h2 : ψ.comp α = (intO C).subtype.comp (ioO.comp β) := by
    rw [hψ, ← hσ₀, RingHom.comp_assoc, hσ, ← RingHom.comp_assoc, ← hio, RingHom.comp_assoc]
  refine ⟨ioO.comp β, h1, fun r => congrArg (fun φ => φ r) h2, fun l => ?_⟩
  have := coord_map α ψ (ha l)
  rw [h2, ← spMap_comp', Category.assoc, ← Category.assoc (spMap (ioO.comp β)), h1] at this
  simpa only [dual_comp] using this

theorem pairDet_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H
    : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) [IsLocallyNoetherian
    X] (t : SAB H X), X.IsSeparated → ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V
    : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (q : ℕ) [Fact q.Prime] (m
    : ℕ) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d
    : Y.X → Fin m → Y.Fnˣ), (∀ y l, IsTanAtG t (GlobalTheory.ShFam.stalkPt Y y ≫ ρ) (f y
    l)) → (∀ y (K : Type) [Field K] (ψ : Y.X.presheaf.stalk y →+* K), IsIndep t (spMap ψ ≫
    GlobalTheory.ShFam.stalkPt Y y ≫ ρ) (fun l => spMap (dualMap ψ) ≫ f y l)) → ∀ (k : ℕ) (hk
    : k ≤ m) (N : ℕ) (c : Fin N → ∀ y : Sp ↥(intO ℂ_[q]) ⟶ V.X, TorsChar t (y ≫ ρ') (q ^
    2)), (∀ y (c' : TorsChar t (y ≫ ρ') (q ^ 2)), ∃ j, Agree c' (c j y)) → ∀ (U U' : V.X.Opens) (hU
    : IsAffineOpen U) (hU' : IsAffineOpen U') (g g' : ℕ) (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶
    t.G.left)) (e' : Fin g' → (Sp (DualNumber Γ(V.X, U')) ⟶ t.G.left)) (h : Fin N → Fin g → Γ(V.X,
    U)) (h' : Fin N → Fin g' → Γ(V.X, U')), IsTanBasis t (hU.fromSpec ≫
    ρ') e → IsTanBasis t (hU'.fromSpec ≫ ρ') e' → (∀ (x : Γ(V.X, U) →+* ↥(intO ℂ_[q])) (y
    : Sp ↥(intO ℂ_[q]) ⟶ V.X), spMap x ≫ hU.fromSpec = y → ∀ j, DlogIs t q 2 (c j
    y) (fun i => spMap (dualMap x) ≫ e i) (fun i => x (h j i))) → (∀ (x : Γ(V.X, U') →+* ↥(intO
    ℂ_[q])) (y : Sp ↥(intO ℂ_[q]) ⟶ V.X), spMap x ≫ hU'.fromSpec = y → ∀ j, DlogIs t q 2 (c j
    y) (fun i => spMap (dualMap x) ≫ e' i) (fun i => x (h' j i))) → ∀ (s s' : (Fin k → Fin
    N) → V.G.functionField), (∀ z : V.G, V.j z ∈ U → ∃ (α : Γ(V.X, U) →+* V.G.presheaf.stalk z) (a
    : Fin m → Fin g → V.G.presheaf.stalk z), spMap α ≫ hU.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧ (∀ l, IsCombAtG t (spMap
    α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l) (spMap (dualMap (V.π.stalkMap
    z).hom) ≫ f (V.π z) l)) ∧ ∀ σ, s σ / V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ)
    : Y.Fn) = algebraMap (V.G.presheaf.stalk z) V.G.functionField (pairDet (fun j i => α (h j i)) a
    hk σ)) → (∀ z : V.G, V.j z ∈ U' → ∃ (α : Γ(V.X, U') →+* V.G.presheaf.stalk z) (a
    : Fin m → Fin g' → V.G.presheaf.stalk z), spMap α ≫ hU'.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧ (∀ l, IsCombAtG t (spMap
    α ≫ hU'.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e' i) (a l) (spMap (dualMap (V.π.stalkMap
    z).hom) ≫ f (V.π z) l)) ∧ ∀ σ, s' σ / V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ)
    : Y.Fn) = algebraMap (V.G.presheaf.stalk z) V.G.functionField (pairDet (fun j i => α (h' j i)) a
    hk σ)) → ∀ (v : HeightOneSpectrum (𝓞 F)) (ε : GlobalTheory.TrueGeo.Ext v) (y : AlgPt Y) (z
    : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp ε.O ⟶ V.X), (q
    : 𝓞 F) ∈ v.asIdeal → z ≫ V.π = y.1 → spMap ε.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → ⊤ ≤ yt ⁻¹ᵁ U' → ∀ [Fact
    (resP v).Prime], (∀ l, 0 < GlobalTheory.ShFam.Pad.grNorm t (spMap ((ioOf (resP v) ε).comp
    (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (lat t
    (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫
    GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v = q))) (fun l => spMap (dualMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk
    l)) ∧ (∀ σ, ‖ioOf (resP v) ε (TrueGeo.valAt z (s σ / V.φ ((∏ l : Fin k, d (below
    y.1) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn)))‖ ≤ ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y
    (below y.1) ≫ ρ) (lat t (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v =
    q))) (fun l => spMap (dualMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk l)) ∧ (∃ σ, ‖ioOf (resP v) ε (TrueGeo.valAt z (s σ
    / V.φ ((∏ l : Fin k, d (below y.1) (Fin.castLE hk l) : Y.Fnˣ)
    : Y.Fn)))‖ = ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap ((ioOf (resP v) ε).comp
    (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (lat t
    (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫
    GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v = q))) (fun l => spMap (dualMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk
    l)) ∧ ∀ σ, ‖ioOf (resP v) ε (TrueGeo.valAt z ((s σ - s' σ) / V.φ ((∏ l : Fin k, d (below
    y.1) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn)))‖ < ∏ l : Fin k, GlobalTheory.ShFam.Pad.grNorm t (spMap
    ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y
    (below y.1) ≫ ρ) (lat t (resP v) (spMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom) ≫ GlobalTheory.ShFam.stalkPt Y (below y.1) ≫ ρ) (decide (resP v =
    q))) (fun l => spMap (dualMap ((ioOf (resP v) ε).comp (Scheme.stalkClosedPointTo
    y.1).hom)) ≫ f (below y.1) l) (Fin.castLE hk l) := by
  intro E _ _ _ H X _ t hX F _ _ Y V ρ' ρ hρ q hq m f d hf hind k hk N c hc U U' hU hU' g g' e e' h h' he he' hd hd'
    s s' hs hs' v ε y z yt hv hz hyt hin hin' hp
  obtain rfl : resP v = q := residueCharacteristic_eq v hq.out hv
  obtain rfl : hq = hp := rfl
  obtain ⟨y, hy⟩ := y
  dsimp only at hz ⊢
  subst hz
  have h1 := ioOf_le_one_iff (resP v) hv ε
  generalize ioOf (resP v) ε = io at h1 ⊢
  let ioO : ε.O →+* intO ℂ_[resP v] := (io.comp ε.O.subtype).codRestrict _ fun b => (h1 b).2 b.2
  have hio : (intO ℂ_[resP v]).subtype.comp ioO = io.comp ε.O.subtype := rfl
  have hmem : ∀ W : V.X.Opens, ⊤ ≤ yt ⁻¹ᵁ W → V.j (below z) ∈ W := fun W hW => by
    have : (spMap ε.O.subtype ≫ yt) (IsLocalRing.closedPoint _) ∈ W := hW (Set.mem_univ _)
    rwa [hyt] at this
  obtain ⟨α, a, hα, ha, hsα⟩ := hs _ (hmem U hin)
  obtain ⟨α', a', hα', ha', hsα'⟩ := hs' _ (hmem U' hin')
  obtain ⟨ψ, hψ⟩ : ∃ ψ : V.G.presheaf.stalk (below z) →+* ℂ_[resP v],
    ψ = io.comp (Scheme.stalkClosedPointTo z).hom := ⟨_, rfl⟩
  obtain ⟨β, hβ, hβα, hb⟩ := chart V.j ρ' ε.O io ioO hio z yt hyt hU hin e α hα a _ ha ψ hψ
  obtain ⟨β', hβ', hβα', hb'⟩ := chart V.j ρ' ε.O io ioO hio z yt hyt hU' hin' e' α' hα' a' _ ha' ψ hψ
  obtain ⟨φ, hφ⟩ : ∃ φ : Y.X.presheaf.stalk (V.π (below z)) →+* ℂ_[resP v],
    φ = io.comp (Scheme.stalkClosedPointTo (z ≫ V.π)).hom := ⟨_, rfl⟩
  have hφψ : ψ.comp (V.π.stalkMap (below z)).hom = φ := by
    rw [hφ, hψ, Scheme.stalkClosedPointTo_comp]; rfl
  simp only [dual_comp _ ψ, hφψ] at hb hb'
  have hx : spMap φ ≫ GlobalTheory.ShFam.stalkPt Y (V.π (below z)) ≫ ρ =
      spMap (intO ℂ_[resP v]).subtype ≫ (spMap ioO ≫ yt) ≫ ρ' := by
    have e1 : spMap (Scheme.stalkClosedPointTo z).hom ≫ V.G.fromSpecStalk (below z) = z :=
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk z
    have e2 : spMap (V.π.stalkMap (below z)).hom ≫ GlobalTheory.ShFam.stalkPt Y (V.π (below z)) =
        V.G.fromSpecStalk (below z) ≫ V.π := Scheme.SpecMap_stalkMap_fromSpecStalk V.π
    rw [← hφψ, ← spMap_comp', Category.assoc, ← Category.assoc _ _ ρ, e2, Category.assoc, ← hρ, hψ, ← spMap_comp',
      Category.assoc, ← Category.assoc _ (V.G.fromSpecStalk _), e1, Category.assoc,
      ← Category.assoc (spMap (intO ℂ_[resP v]).subtype), spMap_comp', hio, ← spMap_comp', Category.assoc,
      ← Category.assoc _ yt, hyt, Category.assoc]
  have hB := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t β he
  have hB' := GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t β' he'
  rw [← Category.assoc, hβ] at hB
  rw [← Category.assoc, hβ'] at hB'
  have hli : LinearIndependent ℂ_[resP v] fun l i => ψ (a l i) :=
    linInd (GlobalTheory.LineNorm.WedgeMax.isTanBasis_map t _ hB).1 hb (hx ▸ hind _ _ φ)
  obtain ⟨k1, k2, k3, k4⟩ := GlobalTheory.T.pairDet_norm_le_attained_and_sub_norm_lt E H X t hX (resP v) _ g g' _ _ hB hB' N (fun j => c j (spMap ioO ≫ yt)) _ _
    (hc _) (hd β _ hβ) (hd' β' _ hβ') m k hk _ _ _ hli hb hb' _ rfl
  rw [← hx] at k1 k2 k3 k4
  have hval : ∀ r, io (TrueGeo.valAt z (algebraMap (V.G.presheaf.stalk (below z)) V.G.functionField r)) = ψ r :=
    fun r => by rw [hψ, Base.valAt_stalk]; rfl
  have hv1 : ∀ σ, ψ (pairDet (fun j i => α (h j i)) a hk σ) =
      pairDet (fun j i => (β (h j i) : ℂ_[resP v])) (fun l i => ψ (a l i)) hk σ := fun σ => by
    simp only [map_pairDet, hβα]
  have hv2 : ∀ σ, ψ (pairDet (fun j i => α' (h' j i)) a' hk σ) =
      pairDet (fun j i => (β' (h' j i) : ℂ_[resP v])) (fun l i => ψ (a' l i)) hk σ := fun σ => by
    simp only [map_pairDet, hβα']
  rw [decide_eq_true rfl]
  subst hφ
  refine ⟨fun l => k1 _, fun σ => ?_, ?_, fun σ => ?_⟩
  · exact (congrArg norm (((congrArg (fun r => io (TrueGeo.valAt z r)) (hsα σ)).trans (hval _)).trans (hv1 σ))).trans_le
      (k2 σ)
  · obtain ⟨σ, hσ⟩ := k3
    exact ⟨σ, (congrArg norm (((congrArg (fun r => io (TrueGeo.valAt z r)) (hsα σ)).trans (hval _)).trans
      (hv1 σ))).trans hσ⟩
  · have e1 := (sub_div _ _ _).trans ((congrArg₂ (· - ·) (hsα σ) (hsα' σ)).trans (map_sub _ _ _).symm)
    refine (congrArg norm (((congrArg (fun r => io (TrueGeo.valAt z r)) e1).trans (hval _)).trans ?_)).trans_lt (k4 σ)
    rw [map_sub, hv1, hv2]

end GlobalTheory.HtGen.FlagPoint
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineThetaRootTwistTwistingSectionStatement
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatLine_thetaRoot_twist_twistingSection : GlobalTheory.Published.AbelianDeRham → ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (V : (c.F →+* ℂ) → HSp D) (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r), IsComplexData U V dict → FnAlgClosed Xo c → 1 ≤ Dw.p + Dw.q → (∀ p : ℕ, p.Prime → l.GoodAt p) → FlatExists U (xiR D) → UnramPts Xo c (badPrimes H l) → ∀ (w : Psi H → ℤ) (m : ℕ), (∀ Z : Comp Xo c, ∃ t : TwSec U (xiR D) Z (wtOf Dw (parWt Dw w) m), IntOff (badPrimes H l) t.lo ∧ (∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) ≤ t.degLo) ∧ ∀ (u : Weight Dw) (n : ℤ), (∀ Z : Comp Xo c, GoodOn U (xiR D) V dict Z (wtOf Dw u n) → GoodOn U (xiR D) V dict Z (wtOf Dw (u + parWt Dw w) (n + m)) ∧ rankOn U Z (wtOf Dw (u + parWt Dw w) (n + m)) = rankOn U Z (wtOf Dw u n) ∧ degOn U (xiR D) V dict Z (wtOf Dw u n) + (rankOn U Z (wtOf Dw u n) : ℝ) * ((∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) - logSum (badPrimes H l)) ≤ degOn U (xiR D) V dict Z (wtOf Dw (u + parWt Dw w) (n + m))) ∧ (GoodW U (xiR D) V dict (wtOf Dw u n) → GoodW U (xiR D) V dict (wtOf Dw (u + parWt Dw w) (n + m)) ∧ rankW U (wtOf Dw (u + parWt Dw w) (n + m)) = rankW U (wtOf Dw u n) ∧ degW U (xiR D) V dict (wtOf Dw u n) + (rankW U (wtOf Dw u n) : ℝ) * ((∑ τ, (w τ : ℝ) * c1 U (xiR D) τ) - (Dw.q : ℝ) * lrd D.host.E * (∑ τ, |(w τ : ℝ)|) - (m : ℝ) * ((Module.finrank ℚ D.host.E / 2 * (Dw.p + Dw.q) : ℕ) : ℝ) * (Real.log (2 * Real.pi) / 2 + lrd D.host.E) - logSum (badPrimes H l)) ≤ degW U (xiR D) V dict (wtOf Dw (u + parWt Dw w) (n + m))) := by
  first | exact @GlobalTheory.FlatRootTwist.flat_root_twist | exact GlobalTheory.FlatRootTwist.flat_root_twist | (intros; apply GlobalTheory.FlatRootTwist.flat_root_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FubiniStudyPullbackChernMassEqDegreeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernInt_pull_fubiniStudy_eq_topSelf : ∀ (Y : Var ℂ) (π : Y.X ⟶ PSpace ℂ Y.dim) (hπ : π ≫ PSpace.str ℂ Y.dim = Y.str), Weight.chernInt (((ProjSpace.hermitianTwistingSheaf ℂ Y.dim).φ (RingHom.id ℂ)).pull π hπ) Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ ((ProjSpace.O1 ℂ Y.dim).pull π) Y.dim : ℝ) := by
  first | exact @GlobalTheory.FubiniStudyPull.fubiniStudy_pullback_chern_mass_eq_degree | exact GlobalTheory.FubiniStudyPull.fubiniStudy_pullback_chern_mass_eq_degree | (intros; apply GlobalTheory.FubiniStudyPull.fubiniStudy_pullback_chern_mass_eq_degree <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLocalOfKernelAtPointStatement
section
open GlobalTheory.FlatModel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_tate_local_of_kernel_at_point : GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel.HodgeTateKernelAtPoint → HTLocSt := by
  first | exact @GlobalTheory.FlatModel.htLocSt_of_hodgeTateKernel | exact GlobalTheory.FlatModel.htLocSt_of_hodgeTateKernel | (intros; apply GlobalTheory.FlatModel.htLocSt_of_hodgeTateKernel <;> assumption)
end

