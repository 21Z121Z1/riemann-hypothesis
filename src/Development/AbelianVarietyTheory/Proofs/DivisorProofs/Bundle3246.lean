import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3226
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3069
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3234
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3163
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3135
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3227
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2668
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3211
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentSectionsOnNormalModel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0798
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2973
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3043
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3199
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3230
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3228
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDominantOfSection
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2811
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2956
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2925
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3221
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3213
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3098
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3124

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormOfWeightIsFormDbarEqZeroStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.firstChernFormOfWeight_isForm_dbar_eq_zero : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (L : LB X.X) (ψ : Weight X.str σ L), ψ.IsCInf → (atlas X σ).IsForm (fld (atlas X σ) (c1W ψ)) ∧ (atlas X σ).dbar (fld (atlas X σ) (c1W ψ)) = 0 := by
  first | exact @GlobalTheory.ChernCalc.FirstChernW.c1W_isForm_and_dbar_eq_zero | exact GlobalTheory.ChernCalc.FirstChernW.c1W_isForm_and_dbar_eq_zero | (intros; apply GlobalTheory.ChernCalc.FirstChernW.c1W_isForm_and_dbar_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernFormProperties
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.LineForm

theorem basicForms : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ) (hX : IsRegVar p D) (σ : k →+* ℂ),
    (∀ L M : HermLB p, (hX.atlas σ).IsRealForm 1 (fld _ (c1F hX σ L)) ∧ (hX.atlas σ).del (fld _ (c1F hX σ L)) = 0 ∧
      (hX.atlas σ).dbar (fld _ (c1F hX σ L)) = 0 ∧ c1F hX σ (L.tens M) = c1F hX σ L + c1F hX σ M ∧ c1F hX σ L.dual = -c1F hX σ L ∧
      (L.Isometric M → c1F hX σ L = c1F hX σ M)) ∧
    (∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl fl' : Vert.Flag E 2),
      (hX.atlas σ).IsRealForm 1 (fld _ (omF hX σ h fl)) ∧ (hX.atlas σ).IsRealForm 2 (fld _ (c2F hX σ h fl)) ∧
      (hX.atlas σ).del (fld _ (c2F hX σ h fl)) = 0 ∧ (hX.atlas σ).dbar (fld _ (c2F hX σ h fl)) = 0 ∧
      c2F hX σ h fl = c2F hX σ h fl' ∧ omF hX σ h fl * omF hX σ h fl = 0 ∧
      c1F hX σ (VMetric.grLB fl 0 H) + c1F hX σ (VMetric.grLB fl 1 H) = c1F hX σ (VMetric.grLB fl' 0 H) + c1F hX σ (VMetric.grLB fl' 1 H) ∧
      (hX.atlas σ).ddc (fld _ (omF hX σ h fl)) =
        fld _ (c2F hX σ h fl - c1F hX σ (VMetric.grLB fl 0 H) * c1F hX σ (VMetric.grLB fl 1 H))) ∧
    ∀ (Y : Scheme.{0}) (p' : Y ⟶ Sp k) (D' : ℕ) (hY : IsRegVar p' D') (π : Y ⟶ X) (w : π ≫ p = p'),
      (hX.atlas σ).IsHolo (hY.atlas σ) (GlobalTheory.Points.PtsOver.map π w _) ∧
      (∀ L : HermLB p, fld _ (c1F hY σ (L.pull π w)) = pullF hX hY σ π w (fld _ (c1F hX σ L))) ∧
      ∀ (E : X.Modules) (h : VMetric p E 2) (H : h.IsCInf) (fl : Vert.Flag E 2) (fl' : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
        fld _ (c2F hY σ (h.pull π w) fl') = pullF hX hY σ π w (fld _ (c2F hX σ h fl)) ∧
        c1F hY σ (VMetric.grLB fl' 0 (H.pull π w)) + c1F hY σ (VMetric.grLB fl' 1 (H.pull π w)) =
          c1F hY σ ((VMetric.grLB fl 0 H).pull π w) + c1F hY σ ((VMetric.grLB fl 1 H).pull π w) := by
  intro k _ X _ p D hX σ
  refine ⟨fun L M => ⟨(GlobalTheory.T.firstChern_real_closed k X p D hX σ L).1, (GlobalTheory.T.firstChern_real_closed k X p D hX σ L).2.1, (GlobalTheory.T.firstChern_real_closed k X p D hX σ L).2.2,
    GlobalTheory.T.firstChern_tensor_add k X p D hX σ L M, GlobalTheory.T.firstChern_dual_neg k X p D hX σ L, GlobalTheory.T.firstChern_isometric_eq k X p D hX σ L M⟩,
    fun E h H fl fl' => ⟨GlobalTheory.T.flag_omega_form_real k X p D hX σ E h H fl, (GlobalTheory.T.secondChern_real_closed k X p D hX σ E h H fl).1, (GlobalTheory.T.secondChern_real_closed k X p D hX σ E h H fl).2.1,
      (GlobalTheory.T.secondChern_real_closed k X p D hX σ E h H fl).2.2, GlobalTheory.T.secondChern_flag_independent k X p D hX σ E h H fl fl', GlobalTheory.T.flag_omega_form_sq_zero k X p D hX σ E h H fl,
      GlobalTheory.T.graded_first_chern_sum_indep k X p D hX σ E h H fl fl', GlobalTheory.T.ddc_omega_form_eq_c2_sub_c1_product k X p D hX σ E h H fl⟩,
    fun Y p' D' hY π w => ⟨GlobalTheory.T.points_map_holomorphic k X p D hX σ Y p' D' hY π w, GlobalTheory.T.first_chern_form_pullback k X p D hX σ Y p' D' hY π w,
      fun E h H fl fl' => ⟨GlobalTheory.T.second_chern_form_pullback k X p D hX σ Y p' D' hY π w E h H fl fl', GlobalTheory.T.sum_first_chern_graded_pullback k X p D hX σ Y p' D' hY π w E h H fl fl'⟩⟩⟩

end GlobalTheory.LineForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralRankTwoStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_chern_integral_rank_two : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ Φ : (hY.atlas σ).Fld, (hY.atlas σ).IsForm Φ → (∀ x : (hY.atlas σ).Pt, v x.pt = 1 → dens (Φ x) = 0) →
      Filter.Tendsto (fun t : ℝ => (hY.atlas σ).integral ((hY.atlas σ).fn (fun y => t / (1 - v y + t) ^ 2) * Φ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  first | exact @GlobalTheory.LineCos.tendsto_integral_kernel_mul | exact GlobalTheory.LineCos.tendsto_integral_kernel_mul | (intros; apply GlobalTheory.LineCos.tendsto_integral_kernel_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineDegreeIdentityStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_hermitian_line_degree_identity : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ α : (hY.atlas σ).Fld, (hY.atlas σ).IsForm α → ∀ ε : ℤˣ,
      ∃ C : ENNReal, C ≠ ⊤ ∧ Measure.map v ((hY.atlas σ).part α ε) ≤ C • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  first | exact @GlobalTheory.LineCos.map_cosSq_part_le | exact GlobalTheory.LineCos.map_cosSq_part_le | (intros; apply GlobalTheory.LineCos.map_cosSq_part_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleOverFieldIrreducibleStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
open CategoryTheory.Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_over_field_irreducible : ∀ (K : Type) [Field K] (Y : Scheme.{0}) (π : Y ⟶ Spec (CommRingCat.of K)) (ι : Type) [Fintype ι] (E : ι → (Spec (CommRingCat.of K)).Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → IrreducibleSpace Y := by
  first | exact @GlobalTheory.FlagIrrFld.irreducibleSpace_of_isFlagBundle | exact GlobalTheory.FlagIrrFld.irreducibleSpace_of_isFlagBundle | (intros; apply GlobalTheory.FlagIrrFld.irreducibleSpace_of_isFlagBundle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagCellCoordsBijectiveOntoChartProd
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagCell2

theorem pt_bsL_fb {n d : ℕ} {J : Type} (ε : Fin n ≃ Fin d ⊕ J) (w : V n) : pt ε (bsL ε w) (fb ε w) = w := by
  ext a
  obtain ⟨x, rfl⟩ := ε.symm.surjective a
  rcases x with b | j <;> simp [pt, bsL_apply, fb]

theorem cellMap_image_eq : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (u : Cell m → Y.Fn), InCell E E' φ f A u (genericPoint Y.X) → ∀ (n : ℕ) (ε : Fin n ≃ Fin X.dim ⊕ Cell m), IsOpen (cellSet E E' φ f hf c A u) ∧ Set.InjOn (cellMap ε f hf c u) (cellSet E E' φ f hf c A u) ∧ ∀ T : Set (CxPts X.str σ), T ⊆ c.e.source → (∀ x ∈ T, A ∈ E.S (under x)) → cellMap ε f hf c u '' (ptMap σ f hf ⁻¹' T ∩ cellSet E E' φ f hf c A u) = bsL ε ⁻¹' (c.e '' T) := by
  intro F _ σ X Y ι _ m E E' φ f hf hR c A u hgen n ε
  have hO := GlobalTheory.T.isOpen_flagBundleCell_and_coords_regular F X Y ι m E E' φ f hR A u
  have hP := GlobalTheory.T.flag_cell_points_existsUnique_unitriangular F X Y ι m E E' φ f hR A u hgen
  have hval : ∀ y : CxPts Y.str σ, InCell E E' φ f A u (under y) → ∀ j,
      ratVal (u j) y = (ratOf Y).val y.1 (u j) :=
    fun y hy j => ratVal_eq_val_ratOf y (mem_O_ratOf.2 (hO.2 _ hy j))
  refine ⟨?_, ?_, ?_⟩
  · let W : Y.X.Opens := ⟨{y | InCell E E' φ f A u y}, hO.1⟩
    have e : cellSet E E' φ f hf c A u = ptsIn Y.str σ W ∩ ptMap σ f hf ⁻¹' c.e.source := by
      ext y
      simp only [cellSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, mem_ptsIn]
      rfl
    rw [e]
    exact (isOpen_ptsIn W).inter (c.e.open_source.preimage (Points.PtsOver.continuous_map f hf _))
  · intro y hy y' hy' h
    have h1 := congrArg (bsL ε) h
    have h2 := congrArg (fb ε) h
    simp only [cellMap, bsL_pt, fb_pt] at h1 h2
    have hx : ptMap σ f hf y = ptMap σ f hf y' := c.e.injOn hy.2 hy'.2 h1
    have hA : A ∈ E.S ((ptMap σ f hf y).1 (IsLocalRing.closedPoint ℂ)) := hy.1.1
    apply Subtype.ext
    exact (hP ℂ (ptMap σ f hf y).1 hA (fun j => ratVal (u j) y)).unique
      ⟨rfl, hy.1, fun j => (hval y hy.1 j).symm⟩
      ⟨congrArg Subtype.val hx.symm, hy'.1, fun j => (hval y' hy'.1 j).symm.trans (congrFun h2 j).symm⟩
  · intro S hS hA
    ext w
    constructor
    · rintro ⟨y, ⟨hyS, -⟩, rfl⟩
      exact ⟨ptMap σ f hf y, hyS, by simp only [cellMap, bsL_pt]⟩
    · rintro ⟨x, hxS, hxw⟩
      obtain ⟨p, ⟨hpf, hpc, hpv⟩, -⟩ := hP ℂ x.1 (hA x hxS) (fb ε w)
      have hps : p ≫ Y.str = spMap σ := by rw [← hf, ← Category.assoc, hpf, x.2]
      let y : CxPts Y.str σ := ⟨p, hps⟩
      have hyx : ptMap σ f hf y = x := Subtype.ext hpf
      refine ⟨y, ⟨by rw [Set.mem_preimage, hyx]; exact hxS, hpc, by rw [hyx]; exact hS hxS⟩, ?_⟩
      have hv : (fun j => ratVal (u j) y) = fb ε w := funext fun j => (hval y hpc j).trans (hpv j)
      simp only [cellMap, hyx, hxw, hv]
      exact pt_bsL_fb ε w

end GlobalTheory.FlagCell2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFrameCoverTangentCompatStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_frame_cover_tangent_compat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (m : ℕ) (u₀ : Fin m → (Sp (DualNumber Y.Fn) ⟶ t.G.left)) (f : ∀ y : Y.X, Fin m → (Sp (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d : Y.X → Fin m → Y.Fnˣ), IsFlagFrame t ρ u₀ f d → ∀ (U : V.X.Opens) (hU : IsAffineOpen U) (g : ℕ) (e : Fin g → (Sp (DualNumber Γ(V.X, U)) ⟶ t.G.left)), IsTanBasis t (hU.fromSpec ≫ ρ') e → ∀ (J : Type) (h : J → Fin g → Γ(V.X, U)) (k : ℕ) (hk : k ≤ m), ∃ s : (Fin k → J) → V.G.functionField, ∀ z : V.G, V.j z ∈ U → ∃ (α : Γ(V.X, U) →+* V.G.presheaf.stalk z) (a : Fin m → Fin g → V.G.presheaf.stalk z), spMap α ≫ hU.fromSpec = V.G.fromSpecStalk z ≫ V.j ∧ (∀ l, IsCombAtG t (spMap α ≫ hU.fromSpec ≫ ρ') (fun i => spMap (dualMap α) ≫ e i) (a l) (spMap (dualMap (V.π.stalkMap z).hom) ≫ f (V.π z) l)) ∧ ∀ σ, s σ / V.φ ((∏ l : Fin k, d (V.π z) (Fin.castLE hk l) : Y.Fnˣ) : Y.Fn) = algebraMap (V.G.presheaf.stalk z) V.G.functionField (pairDet (fun j i => α (h j i)) a hk σ) := by
  first | exact @GlobalTheory.HtGen.CoverChart.pairDet_div_eq | exact GlobalTheory.HtGen.CoverChart.pairDet_div_eq | (intros; apply GlobalTheory.HtGen.CoverChart.pairDet_div_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagFramePrimeTangentCompatStatement
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj
open GlobalTheory GlobalTheory.ArInt GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.Mean4O GlobalTheory.LineNorm GlobalTheory.CoverNorm GlobalTheory.VertForm GlobalTheory.HtGen
open Formalism.MainNotions.DIV.Cons (intO)
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_frame_prime_tangent_compat : ∀ (E : Type) [Field E] [NumberField
    E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X
    : Scheme.{0}) [IsLocallyNoetherian X] (t : SAB H X), X.IsSeparated → ∀ (F : Type) [Field
    F] [NumberField F] (Y : Var F) (V : Cover Y) (ρ' : V.X ⟶ X) (ρ
    : Y.X ⟶ X), V.j ≫ ρ' = V.π ≫ ρ → ∀ (q : ℕ) [Fact q.Prime] (m : ℕ) (f : ∀ y : Y.X, Fin m → (Sp
    (DualNumber (Y.X.presheaf.stalk y)) ⟶ t.G.left)) (d
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
  first | exact @GlobalTheory.HtGen.FlagPoint.pairDet_values | exact GlobalTheory.HtGen.FlagPoint.pairDet_values | (intros; apply GlobalTheory.HtGen.FlagPoint.pairDet_values <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagGradedMetricsWeightsOnLineBundles
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem graded_weight : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Finite ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m m) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ) (gr : Root m → X.Dv), IsGraded E gr →
    IsMetricFr E H → ∀ x : Root m, ∃ (L : LB X.X) (r : L.ι → X.Fnˣ) (ψ : Weight X.str σ L),
      Presents (gr x) L r ∧ ψ.IsCInf ∧ c1W ψ = grF E H x := by
  intro F _ σ X ι _ m E H gr hG hH x
  obtain ⟨B, hB, hgr⟩ := hG
  have hunit : ∀ (z : X.X) (A : Mat m X.Fn), A ∈ E.S z → ∀ f : X.Fnˣ, (gr x).IsEqn z f →
      UnitAt z ((B * A⁻¹) x.1 x.2 x.2 / f) := by
    intro z A hA f hf
    obtain ⟨A₀, hA₀, t, ht, he⟩ := hgr z x
    obtain ⟨hu, hd⟩ := GlobalTheory.T.adaptedFullFlag_frame_change_diagonal_units F X ι m E B hB z A₀ A hA₀ hA x
    have htf : UnitAt z ((t : X.Fn) / f) := (hf.iff_unitAt).1 he
    have hne : (A * A₀⁻¹) x.1 x.2 x.2 ≠ 0 := fun h0 => by
      obtain ⟨a, ha, h⟩ := hu
      rw [h0] at h
      exact (ha.map (algebraMap _ X.Fn)).ne_zero h
    have e : (B * A⁻¹) x.1 x.2 x.2 / f = ((t : X.Fn) / f) * ((A * A₀⁻¹) x.1 x.2 x.2)⁻¹ := by
      rw [← ht, hd]; field_simp
    rw [e]; exact htf.mul hu.inv

  let Ach : CxPts X.str σ → Mat m X.Fn := fun y => (E.nonempty (under y)).choose
  have hAch : ∀ y, Ach y ∈ E.S (under y) := fun y => (E.nonempty (under y)).choose_spec
  let val : Mat m X.Fn → CxPts X.str σ → X.Fn → ℝ := fun A y f =>
    -Real.log (‖ratVal ((B * A⁻¹) x.1 x.2 x.2 / f) y‖ ^ 2) - Real.log (grD (H A y x.1) x.2)
  let D := gr x
  have hP := presents_toLB D
  have heq : ∀ (i : (toLB D).ι) (y : CxPts X.str σ), y ∈ ptsIn X.str σ ((toLB D).U i) →
      D.IsEqn (under y) (i.1.2) := fun i y hy => i.2.2 _ (mem_ptsIn.1 hy)
  have hindep : ∀ (i : (toLB D).ι) (y : CxPts X.str σ), y ∈ ptsIn X.str σ ((toLB D).U i) →
      ∀ A ∈ E.S (under y), val (Ach y) y i.1.2 = val A y i.1.2 := fun i y hy A hA =>
    GlobalTheory.T.flaggedBundleMetric_graded_weight_frame_independent F σ X ι m E H hH B hB y (Ach y) (hAch y) A hA x _ (hunit _ A hA _ (heq i y hy))
  let ψ : Weight X.str σ (toLB D) :=
    { isLB := isLB_toLB D
      φ := fun i y => val (Ach y) y i.1.2
      trans := by
        intro i j y hi hj
        have hu1 := hunit _ _ (hAch y) _ (heq i y hi)
        have hu2 : UnitAt (under y) ((i.1.2 : X.Fn) / (j.1.2 : X.Fn)) := ((heq j y hj).iff_unitAt).1 (heq i y hi)
        have hg : gv X.str σ (toLB D) i j y = ratVal ((i.1.2 : X.Fn) / (j.1.2 : X.Fn)) y := by
          have hgen : genericPoint X.X ∈ (toLB D).U i ⊓ (toLB D).U j := ⟨i.2.1, j.2.1⟩
          rw [← fnOf_toLB_g i j hgen, ratVal_fnOf (mem_ptsIn_inf.2 ⟨hi, hj⟩) hgen]
          rfl
        have hi0 := (i.1.2).ne_zero
        have hj0 := (j.1.2).ne_zero
        have e : (B * (Ach y)⁻¹) x.1 x.2 x.2 / (j.1.2 : X.Fn) =
            ((B * (Ach y)⁻¹) x.1 x.2 x.2 / i.1.2) * ((i.1.2 : X.Fn) / (j.1.2 : X.Fn)) := by
          field_simp
        show val (Ach y) y j.1.2 = val (Ach y) y i.1.2 - _
        simp only [val]
        rw [e, ratVal_mul hu1.regAt hu2.regAt, log_normSq_mul (ratVal_ne_zero hu1) (ratVal_ne_zero hu2), hg]
        ring }
  refine ⟨toLB D, fun i => i.1.2, ψ, hP, ?_, ?_⟩
  · intro i y hy
    have hu := hunit _ _ (hAch y) _ (heq i y hy)
    refine (GlobalTheory.T.complexPointsSmoothAt_log_unit_add_graded_length F σ X ι m m E H hH y (Ach y) (hAch y) _ hu x.1 x.2).congr ?_
    filter_upwards [frame_eventually_near F σ X ι m m E y (Ach y) (hAch y), (isOpen_ptsIn _).mem_nhds hy] with z hz hzi
    exact hindep i z hzi (Ach y) hz
  · funext p
    obtain ⟨⟨c, y⟩, hy⟩ := p
    have hy' : y ∈ c.e.source := hy
    have ha : y ∈ ptsIn X.str σ ((toLB D).U (pick ψ.isLB y)) := mem_pick ψ.isLB y
    have hu := hunit _ _ (hAch y) _ (heq _ y ha)
    have hnear : ∀ᶠ z in 𝓝 y, z ∈ ptsIn X.str σ ((toLB D).U (pick ψ.isLB y)) ∧ Ach y ∈ E.S (under z) :=
      Filter.Eventually.and ((isOpen_ptsIn _).mem_nhds ha) (frame_eventually_near F σ X ι m m E y (Ach y) (hAch y))
    have hnear' : ∀ᶠ v in 𝓝 (c.e y), c.e.symm v ∈ ptsIn X.str σ ((toLB D).U (pick ψ.isLB y)) ∧
        Ach y ∈ E.S (under (c.e.symm v)) := by
      have hc := c.e.continuousAt_symm (c.e.map_source hy')
      rw [ContinuousAt, c.e.left_inv hy'] at hc
      exact hc.eventually hnear
    have key : leviForm (fun v => ψ.φ (pick ψ.isLB y) (c.e.symm v)) (c.e y) =
        leviForm (fun v => -Real.log (grD (H (Ach y) (c.e.symm v) x.1) x.2)) (c.e y) := by
      rw [leviForm_congr (u' := fun v => val (Ach y) (c.e.symm v) (pick ψ.isLB y).1.2)]
      · exact GlobalTheory.T.leviForm_graded_length_sub_log_unit_normSq F σ X ι m m E H hH y (Ach y) (hAch y) _ hu x.1 x.2 c hy'
      · filter_upwards [hnear'] with v hv
        exact hindep _ _ hv.1 (Ach y) hv.2
    have e1 : c1W ψ ⟨(c, y), hy⟩ =
        ofValues (HermFrame.ddc (fun v => ψ.φ (pick ψ.isLB y) (c.e.symm v)) (c.e y)) := rfl
    have e2 : grF E H x ⟨(c, y), hy⟩ =
        ofValues (HermFrame.ddc (fun v => -Real.log (grD (H (Ach y) (c.e.symm v) x.1) x.2)) (c.e y)) := rfl
    rw [e1, e2]
    unfold HermFrame.ddc
    rw [key]

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceIntersectionNumberAdjacentSwapNegStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZH GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.FlagPush
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flagSpace_intersectionNumber_adjacent_swap_neg : ∀ (F : Type) [Field F] (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X), Refines E E' φ f → ∀ (gr : Root m → Y.Dv), IsGraded E' gr → ∀ (τ : ι) (a b : Fin (m τ)), (b : ℕ) = a + 1 → ∀ Q : MvPolynomial (Root m) ℝ, Y.interPoly gr (rename (Equiv.swap (⟨τ, a⟩ : Root m) ⟨τ, b⟩) Q) = - Y.interPoly gr Q := by
  first | exact @GlobalTheory.FlagPush.interPoly_swap_adjacent | exact GlobalTheory.FlagPush.interPoly_swap_adjacent | (intros; apply GlobalTheory.FlagPush.interPoly_swap_adjacent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalChartPresentsLevelsModIdealStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalChart_presents_levels_mod_ideal : ∀ (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (I : Ideal O) (m : ℕ), (p : O) ^ m ∈ I → ∃ hx : ∀ n i, IsNilpotent ((1 : O ⧸ I) ⊗ₜ[O] c.x n i), (∀ n f, evA (O ⧸ I) (fun i => (1 : O ⧸ I) ⊗ₜ[O] c.x n i) (hx n) (map (Ideal.Quotient.mk I) f) = 1 ⊗ₜ[O] c.ev n f) ∧ Presents (O ⧸ I) (B := fun n => (O ⧸ I) ⊗[O] G.A n) (fun n i => 1 ⊗ₜ[O] c.x n i) hx := by
  first | exact @GlobalTheory.QLog.Chart.presents_quotient | exact GlobalTheory.QLog.Chart.presents_quotient | (intros; apply GlobalTheory.QLog.Chart.presents_quotient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionTorusExtensionRespectCubical
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors

namespace GlobalTheory.Poinc.Sep.LiesCube

theorem alternating_alg {M : Type} [CommGroup M] (u e w f t : Finset (Fin 3) → M) (a b c : M)
    (v : ∀ S, u S * e S * w S = f S * t S)
    (c₁ : f {0, 1, 2} * f {0} * f {1} * f {2} * (t {0, 1, 2} * t {0} * t {1} * t {2}) * b =
      a * (f {0, 1} * f {0, 2} * f {1, 2} * f ∅) * (t {0, 1} * t {0, 2} * t {1, 2} * t ∅))
    (c₂ : u {0, 1, 2} * u {0} * u {1} * u {2} * c = a * (u {0, 1} * u {0, 2} * u {1, 2} * u ∅)) :
    e {0, 1, 2} * e {0} * e {1} * e {2} * (w {0, 1, 2} * w {0} * w {1} * w {2}) * b =
      c * (e {0, 1} * e {0, 2} * e {1, 2} * e ∅) * (w {0, 1} * w {0, 2} * w {1, 2} * w ∅) := by
  have E := fun {p q : M} (e : p = q) => congrArg Additive.ofMul e
  have v₀ := E (v ∅); have v₁ := E (v {0}); have v₂ := E (v {1}); have v₃ := E (v {2})
  have v₄ := E (v {0, 1}); have v₅ := E (v {0, 2}); have v₆ := E (v {1, 2}); have v₇ := E (v {0, 1, 2})
  have d₁ := E c₁; have d₂ := E c₂
  apply Additive.ofMul.injective
  simp only [ofMul_mul] at *
  linear_combination (norm := abel) v₁ + v₂ + v₃ + v₇ - v₀ - v₄ - v₅ - v₆ + d₁ - d₂

theorem cube_of_liesOver : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G) (w₀ : W0 U.toUnifPre), w₀.IsGen → ∀ N : ℕ, 1 ≤ N → ∀ (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) (c : CubicalStr A.A ⟨A.L, ρ, A.isLB, hρ⟩) (g : Finset (Fin 3) → GtPtF D.toPre (FractionRing V)) (w : ∀ S, Frm D.toPre (FractionRing V) 1 (g S).b) (x : Finset (Fin 3) → (TFK (R := V) (FractionRing V) ⟶ A.A)) (e : ∀ S, FrAt (x S)), x ∅ = 1 → x {0, 1} = x {0} * x {1} → x {0, 2} = x {0} * x {2} → x {1, 2} = x {1} * x {2} → x {0, 1, 2} = x {0} * x {1} * x {2} → (∀ S, (∃ o, GtPtF.IsNsmul N (g S) o ∧ o.IsZero) ∧ (w S).IsGen ∧ (e S).IsGen ∧ LiesOver U.toUnifPre w₀ (g S) (w S) (x S) (e S)) → ∀ (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ A.A.left) → A.L.ι) (JB : ((TF (R := V) (FractionRing V)).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Good A.L z JA → Good D.toPre.P.L z JB → @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 1, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {1}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {2}) (𝟙 _) z JA) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 1, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {1}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {2}) (𝟙 _) z JB)) * cubV D.toPre.cub z JB (g {0}).b (g {1}).b (g {2}).b = @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x {0}) (x {1}) (x {2})) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 1}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {0, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e {1, 2}) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (e ∅) (𝟙 _) z JA)) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 1}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {0, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w {1, 2}) (𝟙 _) z JB) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (w ∅) (𝟙 _) z JB)) := by
  intro V _ _ _ hV D A G _ _ hG U w₀ hw₀ N hN ρ hρ c g w x e hx₀ hx₁ hx₂ hx₃ hx₄ hS z JA JB hJA hJB
  choose h g' f t hF hE hP hf ht hT using fun S => GlobalTheory.T.exists_integral_data_framed_torsion_point_torus_ext V hV D A G hG U w₀ hw₀ N hN (g S) (w S) (x S) (e S)
    (hS S).1 (hS S).2.1 (hS S).2.2.1 (hS S).2.2.2
  have hm : ∀ S T S', x S' = x S * x T → h S' = h S * h T ∧ (g' S').b = (g' S).b * (g' T).b := fun S T S' hx => by
    have a := GlobalTheory.T.uniformisation_sections_extending_points_multiply V hV D A G hG U (x S) (x T) (h S) (h T) (h S') (hE S) (hE T) (hx ▸ hE S')
    exact ⟨a, GlobalTheory.T.formal_points_abelian_parts_multiply V hV D A G hG U (h S) (h T) (g' S) (g' T) (g' S') (hF S) (hF T) (a ▸ hF S')⟩
  have m₀ := hm ∅ ∅ ∅ (by rw [hx₀, _root_.mul_one])
  have m₁ := hm _ _ _ hx₁
  have m₂ := hm _ _ _ hx₂
  have m₃ := hm _ _ _ hx₃
  have m₄ := hm {0, 1} {2} {0, 1, 2} (by rw [hx₄, hx₁])
  have a₀ : h ∅ = 1 := mul_eq_left.1 m₀.1.symm
  have b₀ : (g' ∅).b = 1 := mul_eq_left.1 m₀.2.symm
  have a₄ : h {0, 1, 2} = h {0} * h {1} * h {2} := m₄.1.trans (by rw [m₁.1])
  have b₄ : (g' {0, 1, 2}).b = (g' {0}).b * (g' {1}).b * (g' {2}).b := m₄.2.trans (by rw [m₁.2])
  obtain ⟨JG, hJG⟩ : ∃ J, Good U.LG.L z J := by
    choose I hI using fun χ : _ ⟶ G.left => exists_chart U.LG.isLB (χ z)
    exact ⟨I, hI⟩
  have v := fun S => GlobalTheory.T.torsionPointFrame_mul_eq_integralGenerators V hV D A G hG U w₀ hw₀ N hN (g S) (w S) (x S) (e S)
    (hS S).1 (hS S).2.1 (hS S).2.2.1 (hS S).2.2.2 (h S) (g' S) (f S) (t S) (hF S) (hE S) (hP S) (hf S) (ht S) (hT S)
    z JA JG JB hJA hJG hJB
  have c₁ := GlobalTheory.T.integral_frames_respect_cubical_structures V hV D A G hG U h g' f t a₀ m₁.1 m₂.1 m₃.1 a₄ b₀ m₁.2 m₂.2 m₃.2 b₄ hF hf ht hT z JG JB hJG hJB
  have c₂ := GlobalTheory.T.uniformisation_cubical_structure_generic_fibre V hV D A G hG U w₀ hw₀ ρ hρ c x h hx₀ hx₁ hx₂ hx₃ hx₄ a₀ m₁.1 m₂.1 m₃.1 a₄ hE z JA JG hJA hJG
  have hb : ∀ S, toUnit (TF (R := V) (FractionRing V)) ≫ (g' S).b = (g S).b := fun S =>
    Over.OverMorphism.ext (hP S).1.symm
  rw [hb, hb, hb] at c₁
  exact alternating_alg (M := ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ) _
    (fun S => val (Z := (TF (R := V) (FractionRing V)).left) (e S) (𝟙 _) z JA) (fun S => val (w S) (𝟙 _) z JB)
    (fun S => val (f S) (toUnit (TF (R := V) (FractionRing V))).left z JG)
    (fun S => val (t S) (toUnit (TF (R := V) (FractionRing V))).left z JB) _ _ _ v c₁ c₂

end GlobalTheory.Poinc.Sep.LiesCube
end

