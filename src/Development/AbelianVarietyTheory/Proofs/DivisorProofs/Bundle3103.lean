import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1622
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1660
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1325
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2877
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3095
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3047
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0042
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernFormsFrameIndependentClosed
section
set_option autoImplicit false

noncomputable section

open Set Matrix Filter Topology MeasureTheory
open GlobalTheory.HermFrame GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec chernPoly curvPoly)
open scoped ContDiff ComplexOrder

namespace GlobalTheory.ChernFrame

theorem chernAt_congr {n : ℕ} {r : Type} [Fintype r] [DecidableEq r] {H K : V n → Matrix r r ℂ} {v : V n}
    (h : H =ᶠ[𝓝 v] K) (j : ℕ) : chernAt H v j = chernAt K v j := by
  unfold chernAt chernPoly curvPoly
  simp only [curv_congr h]

theorem delAt_congr {n : ℕ} {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) : delAt α v = delAt β v := by
  unfold delAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  exact congrArg (fun L => L (coordVec a) • bas n S)
    (GlobalTheory.del_congr (f := fun x => (bas n).repr (α x) S) (g := fun x => (bas n).repr (β x) S)
      (h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx))

theorem dbarAt_congr {n : ℕ} {α β : V n → Alt n} {v : V n} (h : α =ᶠ[𝓝 v] β) : dbarAt α v = dbarAt β v := by
  unfold dbarAt coefwise
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun S _ => ?_
  exact congrArg (fun L => L (coordVec a) • bas n S)
    (GlobalTheory.dbar_congr (f := fun x => (bas n).repr (α x) S) (g := fun x => (bas n).repr (β x) S)
      (h.mono fun x hx => congrArg (fun y => (bas n).repr y S) hx))

theorem chern_frame_closed : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {ι : Type} [Fintype ι] [DecidableEq ι] {κ : Type} (U : κ → Set M),
    (∀ a, IsOpen (U a)) → (∀ y, ∃ a, y ∈ U a) → ∀ (g : κ → κ → M → Matrix ι ι ℂ),
    (∀ a b i j, A.HolOn (U a ∩ U b) fun y => g a b y i j) → ∀ (G : κ → M → Matrix ι ι ℂ),
    (∀ a i j, A.SmoothOn (U a) fun y => G a y i j) → (∀ a, ∀ y ∈ U a, (G a y).PosDef) →
    (∀ a b, ∀ y ∈ U a ∩ U b, G b y = chg (g a b y) (G a y)) → ∀ (j : ℕ),
    (∀ a b (x : A.Pt), x.pt ∈ U a → x.pt ∈ U b → A.chern (G a) j x = A.chern (G b) j x) ∧
    ∀ P : A.Fld, (∀ a (x : A.Pt), x.pt ∈ U a → P x = (A.chern (G a) j x : GlobalTheory.CxForm.Alt n)) →
      A.IsForm P ∧ A.del P = 0 ∧ A.dbar P = 0 := by
  intro M _ n A ι _ _ κ U hUo hUc g hg G hGs hGp hGt j
  have hop : ∀ i a, IsOpen ((A.e i).target ∩ (A.e i).symm ⁻¹' U a) := fun i a =>
    (A.e i).isOpen_inter_preimage_symm (hUo a)
  have hsm : ∀ i a p q, ContDiffOn ℝ ∞ (fun v => G a ((A.e i).symm v) p q)
      ((A.e i).target ∩ (A.e i).symm ⁻¹' U a) := fun i a p q => hGs a p q i
  have hun : ∀ i a, ∀ v ∈ (A.e i).target ∩ (A.e i).symm ⁻¹' U a, IsUnit (G a ((A.e i).symm v)).det :=
    fun i a v hv => (isUnit_iff_isUnit_det _).1 (hGp a _ hv.2).isUnit
  have hpt : ∀ (x : A.Pt) a, x.pt ∈ U a → x.crd ∈ (A.e x.1.1).target ∩ (A.e x.1.1).symm ⁻¹' U a :=
    fun x a ha => ⟨x.ch.map_source x.2, by simp only [mem_preimage]; rw [x.ch.left_inv x.2]; exact ha⟩
  have hfr : ∀ a b (x : A.Pt), x.pt ∈ U a → x.pt ∈ U b → A.chern (G a) j x = A.chern (G b) j x := by
    intro a b x ha hb
    have hN : IsOpen ((A.e x.1.1).target ∩ (A.e x.1.1).symm ⁻¹' (U a ∩ U b)) :=
      (A.e x.1.1).isOpen_inter_preimage_symm ((hUo a).inter (hUo b))
    have hsym : (A.e x.1.1).symm x.crd = x.pt := x.ch.left_inv x.2
    have hx : x.crd ∈ (A.e x.1.1).target ∩ (A.e x.1.1).symm ⁻¹' (U a ∩ U b) :=
      ⟨x.ch.map_source x.2, by simp only [mem_preimage]; rw [hsym]; exact ⟨ha, hb⟩⟩
    have hK : MContDiffAt 2 (fun v => G a ((A.e x.1.1).symm v)) x.crd := fun p q =>
      ((hsm x.1.1 a p q).contDiffAt ((hop x.1.1 a).mem_nhds (hpt x a ha))).of_le (by norm_cast)
    have hKu : IsUnit (G a ((A.e x.1.1).symm x.crd)).det := hun x.1.1 a _ (hpt x a ha)
    have hA : ∀ p q, AnalyticAt ℂ (fun w => g a b ((A.e x.1.1).symm w) p q) x.crd := fun p q =>
      GlobalTheory.SCV.analyticAt_of_differentiableOn (hg a b p q x.1.1) (hN.mem_nhds hx)
    have hAu : IsUnit (g a b ((A.e x.1.1).symm x.crd)).det := by
      rw [hsym]
      have h2 := (isUnit_iff_isUnit_det _).1 (hGp b _ hb).isUnit
      rw [hGt a b x.pt ⟨ha, hb⟩, chg, det_mul, det_mul] at h2
      simpa using isUnit_of_mul_isUnit_left (isUnit_of_mul_isUnit_left h2)
    have hev : (fun v => G b ((A.e x.1.1).symm v)) =ᶠ[𝓝 x.crd]
        fun v => chg (g a b ((A.e x.1.1).symm v)) (G a ((A.e x.1.1).symm v)) :=
      Filter.eventually_of_mem (hN.mem_nhds hx) fun v hv => hGt a b _ hv.2
    exact (GlobalTheory.T.chernFormOfGramMatrixAt_holomorphic_frameChange _ _ _ _ hK hKu hA hAu hev j).symm
  refine ⟨hfr, fun P hP => ?_⟩
  have hloc : ∀ i a, ∀ v ∈ (A.e i).target ∩ (A.e i).symm ⁻¹' U a,
      A.loc P i v = (chernAt (fun w => G a ((A.e i).symm w)) v j : Alt n) := by
    intro i a v hv
    rw [HolAtlas.loc, dif_pos hv.1, hP a ⟨(i, (A.e i).symm v), (A.e i).map_target hv.1⟩ hv.2]
    show ((chernAt (fun w => G a ((A.e i).symm w)) ((A.e i) ((A.e i).symm v)) j : Ev n) : Alt n) = _
    rw [(A.e i).right_inv hv.1]
  have hgerm : ∀ i a v, v ∈ (A.e i).target ∩ (A.e i).symm ⁻¹' U a →
      A.loc P i =ᶠ[𝓝 v] fun w => (chernAt (fun w' => G a ((A.e i).symm w')) w j : Alt n) :=
    fun i a v hv => Filter.eventually_of_mem ((hop i a).mem_nhds hv) (hloc i a)
  refine ⟨⟨fun i S => ?_, fun x x' hxx => ?_⟩, ?_, ?_⟩
  · refine contDiffOn_of_locally_contDiffOn fun v hv => ?_
    obtain ⟨a, ha⟩ := hUc ((A.e i).symm v)
    refine ⟨_, hop i a, ⟨hv, ha⟩, ?_⟩
    refine ((GlobalTheory.T.contDiffOn_chernFormOfGramMatrixAt_coefficients _ _ (hop i a) (hsm i a) (hun i a) j S).mono inter_subset_right).congr fun w hw => ?_
    rw [hloc i a w hw.2]
  · obtain ⟨a, ha⟩ := hUc x.pt
    have ha' : x'.pt ∈ U a := hxx ▸ ha
    rw [hP a x ha, hP a x' ha']
    have hW : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
      x.ch.isOpen_inter_preimage_symm x'.ch.open_source
    have hxW : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source :=
      ⟨x.ch.map_source x.2, by simp only [mem_preimage]; rw [x.ch.left_inv x.2]; show x.pt ∈ _; rw [hxx]; exact x'.2⟩
    have hφ : AnalyticAt ℂ (x'.ch ∘ x.ch.symm) x.crd := GlobalTheory.SCV.analyticAt_of_differentiableOn (A.holo x.1.1 x'.1.1) (hW.mem_nhds hxW)
    have hφv : (x'.ch ∘ x.ch.symm) x.crd = x'.crd := by
      simp only [Function.comp_apply]; rw [x.ch.left_inv x.2]; show x'.ch x.pt = x'.ch x'.pt; rw [hxx]
    have hH2 : MContDiffAt 2 (fun v => G a (x'.ch.symm v)) ((x'.ch ∘ x.ch.symm) x.crd) := by
      rw [hφv]
      exact fun p q => ((hsm x'.1.1 a p q).contDiffAt ((hop x'.1.1 a).mem_nhds (hpt x' a ha'))).of_le
        (by norm_cast)
    have hHu : IsUnit (G a (x'.ch.symm ((x'.ch ∘ x.ch.symm) x.crd))).det := by
      rw [hφv]; exact hun x'.1.1 a _ (hpt x' a ha')
    have key := GlobalTheory.T.chernFormOfGramMatrixAt_comp_holomorphic (fun v => G a (x'.ch.symm v)) (x'.ch ∘ x.ch.symm) x.crd hφ hH2 hHu j
    rw [hφv] at key
    have hge : (fun v => G a (x.ch.symm v)) =ᶠ[𝓝 x.crd] fun w => G a (x'.ch.symm ((x'.ch ∘ x.ch.symm) w)) :=
      Filter.eventually_of_mem (hW.mem_nhds hxW) fun w hw => by
        simp only [Function.comp_apply]; rw [x'.ch.left_inv hw.2]
    show ((chernAt (fun v => G a (x.ch.symm v)) x.crd j : Ev n) : Alt n) = _
    rw [chernAt_congr hge j, key]
    rfl
  · funext x
    obtain ⟨a, ha⟩ := hUc x.pt
    show delAt (A.loc P x.1.1) x.crd = 0
    rw [delAt_congr (hgerm _ a _ (hpt x a ha))]
    exact GlobalTheory.T.holomorphicDel_chernFormOfGramMatrix_eq_zero _ _ (hop _ a) (hsm _ a) (hun _ a) j _ (hpt x a ha)
  · funext x
    obtain ⟨a, ha⟩ := hUc x.pt
    show dbarAt (A.loc P x.1.1) x.crd = 0
    rw [dbarAt_congr (hgerm _ a _ (hpt x a ha))]
    exact GlobalTheory.T.antiholomorphicDbar_chernFormOfGramMatrix_eq_zero _ _ (hop _ a) (hsm _ a) (hun _ a) j _ (hpt x a ha)

end GlobalTheory.ChernFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassPullMulDegreeField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

namespace GlobalTheory.ChernMassPull

theorem mass : ∀ (k : Type) [Field k] (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → IsProjOver q → SmoothOfRelativeDimension D p → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), π (genericPoint Y) = genericPoint X → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → ∀ ε : ℤˣ, (φ.pull π hπ).chernPart D ε Set.univ = (π.residueDegree (genericPoint Y) : ENNReal) * φ.chernPart D ε Set.univ := by
  intro k _ X Y _ _ p q σ D hX hY hsm π hπ hη hδ B φ hφ ε
  obtain ⟨U, hUη, hcard, hchart, hlift⟩ := GlobalTheory.T.exists_open_covering_charts_generically_finite_field k X Y p q σ D hX hY hsm π hπ hη hδ
  have hpre : PtsOver.map π hπ (spMap σ) ⁻¹' ptsIn p σ U = ptsIn q σ (π ⁻¹ᵁ U) := by
    ext z
    simp only [Set.mem_preimage, mem_ptsIn]
    rfl
  have h0Y := GlobalTheory.T.chernPart_complement_dense_open_null_field k Y q σ D hY (π ⁻¹ᵁ U) (by simp [hη, hUη]) _ (φ.pull π hπ) ε
  have h0X := GlobalTheory.T.chernPart_complement_dense_open_null_field k X p σ D hX U hUη B φ ε
  have h3 := GlobalTheory.T.chernMeasurePart_preimage_covering_field k X Y p q σ D hX hY π hπ B φ hφ ε (ptsIn p σ U) (isOpen_ptsIn U) _
    hcard hchart hlift
  rw [hpre] at h3
  rw [← measure_add_measure_compl (isOpen_ptsIn (π ⁻¹ᵁ U)).measurableSet, h0Y, add_zero, h3,
    ← measure_add_measure_compl (isOpen_ptsIn (p := p) (σ := σ) U).measurableSet, h0X, add_zero]

end GlobalTheory.ChernMassPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopDensityEqPolarisedTopChern
section
set_option autoImplicit false

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem chernTop_eq_mixTop {n m : ℕ} (G : V n → Mat (fun _ : Unit => m) ℂ) (v : V n) :
    chernTop (MvPolynomial.X ((), n)) G v =
      (Real.pi ^ n)⁻¹ * (mixTop fun _ => curvAt (fun u => G u ()) v).re := by
  rw [chernTop, MvPolynomial.aeval_X, GlobalTheory.T.topDegreeFormCoeff_chernPoly_eq_polarised]

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTransgressionFormsFrameInvariantStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernTransgression_forms_frame_invariant : ∀ (n : ℕ) (r : Type) [Fintype r] [DecidableEq r] (G G' G₂ G₂' T K K' : V n → Matrix r r ℂ) (v : V n), MContDiffAt ∞ G v → IsUnit (G v).det → MContDiffAt ∞ G' v → IsUnit (G' v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => T u a b) x) → IsUnit (T v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => K u a b) x) → IsUnit (K v).det → (∀ a b, ∀ᶠ x in 𝓝 v, DifferentiableAt ℂ (fun u => K' u a b) x) → IsUnit (K' v).det → (∀ᶠ x in 𝓝 v, G₂ x = T x * G x * (K x)ᴴ ∧ G₂' x = T x * G' x * (K' x)ᴴ) → ∀ k, powAt G₂ v k = powAt G v k ∧ chernAt G₂ v k = chernAt G v k ∧ transAt G₂ G₂' v k = transAt G G' v k := by
  first | exact @GlobalTheory.ChernCalc.FrameInv.pow_chern_trans_frame | exact GlobalTheory.ChernCalc.FrameInv.pow_chern_trans_frame | (intros; apply GlobalTheory.ChernCalc.FrameInv.pow_chern_trans_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmDefiniteLieIndexIdealEqNormIdealStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmDefinite_lieIndex_ideal_eq_norm_ideal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0) (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
    GlobalTheory.FlatCM.IsGram X gP gQ →
    ∃ 𝔫 : Ideal (𝓞 E), 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det} ∧
      ∀ (FP : GlobalTheory.CM.GenFib (X.A true).pol) (FB : GlobalTheory.CM.GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))),
        (∀ a, FP.IsDiffOf FB (GlobalTheory.FlatCM.phiP X a) (MP a)) →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ →
          GlobalTheory.FlatCM.idx K p (FB.eigLat X.B.t.act τ) (GlobalTheory.FlatCM.subP FP FB MP τ) = 𝔫.map τ := by
  first | exact @GlobalTheory.FlatCM.IdealZero.idealSt_zero | exact GlobalTheory.FlatCM.IdealZero.idealSt_zero | (intros; apply GlobalTheory.FlatCM.IdealZero.idealSt_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoheightAddPointClosureDimEqDimStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coheight_add_pointClosureDim_eq_dim : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k), IsAmb q → ∀ d : ℕ, topologicalKrullDim Y = d → ∀ (z : Y) (e : ℕ), HasDim z e → Order.coheight z + (e : ℕ∞) = d := by
  first | exact @GlobalTheory.DimCoheight.coheight_add_eq | exact GlobalTheory.DimCoheight.coheight_add_eq | (intros; apply GlobalTheory.DimCoheight.coheight_add_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMapEqSelfOfInjectiveFiniteHopf
section
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup Coalgebra Bialgebra

namespace GlobalTheory.PDiv

theorem faithfullyFlat_range_of_hopf_finite (k A B : Type) [Field k] [CommRing A] [CommRing B]
    [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A) :
    Module.FaithfullyFlat (AlgHom.range (f : B →ₐ[k] A)) A := by
  obtain ⟨e⟩ := GlobalTheory.HopfShear.shear k A B f
  haveI : Module.Finite k (AlgHom.range (f : B →ₐ[k] A)) :=
    Module.Finite.of_injective (AlgHom.range (f : B →ₐ[k] A)).val.toLinearMap
      Subtype.val_injective
  haveI : Module.Finite (AlgHom.range (f : B →ₐ[k] A)) A :=
    Module.Finite.of_restrictScalars_finite k _ A
  haveI : IsArtinianRing (AlgHom.range (f : B →ₐ[k] A)) := IsArtinianRing.of_finite k _
  obtain ⟨b⟩ := GlobalTheory.nonempty_basis_of_basis_baseChange (B := AlgHom.range (f : B →ₐ[k] A))
    (A := A) (M := A) Subtype.val_injective (((Module.finBasis k _).baseChange A).map e.symm)
  haveI := Module.Free.of_basis b
  haveI : Nontrivial A := (counitAlgHom k A).domain_nontrivial
  infer_instance

theorem comap_map_eq_self_of_hopf_injective : ∀ (k A B : Type) [Field k] [CommRing A] [CommRing B] [HopfAlgebra k A] [HopfAlgebra k B] [Module.Finite k A] (f : B →ₐc[k] A), Function.Injective f → ∀ J : Ideal B, Ideal.comap (f : B →ₐ[k] A) (Ideal.map (f : B →ₐ[k] A) J) = J := by
  intro k A B _ _ _ _ _ _ f hf J
  haveI := faithfullyFlat_range_of_hopf_finite k A B f
  let g : B →+* AlgHom.range (f : B →ₐ[k] A) := (f : B →ₐ[k] A).rangeRestrict.toRingHom
  have hg : Function.Bijective g :=
    ⟨fun x y h => hf (congrArg Subtype.val h), (f : B →ₐ[k] A).rangeRestrict_surjective⟩
  have h := Ideal.comap_map_eq_self_of_faithfullyFlat (B := A) (Ideal.map g J)
  rw [Ideal.map_map] at h
  have h2 := congrArg (Ideal.comap g) h
  rw [Ideal.comap_comap, Ideal.comap_map_of_bijective g hg] at h2
  exact h2

end GlobalTheory.PDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingDiagonalMumfordBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutator_pairing_diagonal_mumford_bundle : ∀ (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (M : LB A.left) (u : HolUnif A M g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), M.IsLB → GlobalTheory.TorusRM.IsFactorAH u Hm χ → ∀ (N : LB A.left), N.IsLB → LBIso N (cubeLB A ![𝟙 A, 𝟙 A] M) → Out.RelAmple A N → ∀ (k : ℕ) (a b : Fin g → ℂ) (c : ℂˣ), 0 < k → a ∈ u.Λ → b ∈ u.Λ → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (((2 * (hermForm Hm a b).im : ℝ)) : ℂ) / k) → Out.WeilIs A N k (u.ex ((k : ℂ)⁻¹ • a)) (u.ex ((k : ℂ)⁻¹ • b)) (unitOn c) := by
  first | exact @GlobalTheory.DiagWeil.weilIs_diag_lam | exact GlobalTheory.DiagWeil.weilIs_diag_lam | (intros; apply GlobalTheory.DiagWeil.weilIs_diag_lam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingEqOfMumfordBundleIsoStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.commutator_pairing_eq_of_mumford_bundle_iso : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P₀ P₁ P₂ : PolAV S) (f₁ g₁ : P₀.A ⟶ P₁.A) (f₂ g₂ : P₀.A ⟶ P₂.A), IsMonHom f₁ → IsMonHom g₁ → IsMonHom f₂ → IsMonHom g₂ → LBIso (cubeLB P₁.A ![fst P₀.A P₀.A ≫ f₁, snd P₀.A P₀.A ≫ g₁] P₁.L) (cubeLB P₂.A ![fst P₀.A P₀.A ≫ f₂, snd P₀.A P₀.A ≫ g₂] P₂.L) → ∀ (F : Type) [Field F] (p : Sp F ⟶ S) (k : ℕ) (x y : Over.mk p ⟶ P₀.A), x ^ k = 1 → y ^ k = 1 → ∀ c, WeilIs P₁.A P₁.L k (x ≫ f₁) (y ≫ g₁) c ↔ WeilIs P₂.A P₂.L k (x ≫ f₂) (y ≫ g₂) c := by
  first | exact @GlobalTheory.Mum.Two.weilIs_iff_of_lbIso | exact GlobalTheory.Mum.Two.weilIs_iff_of_lbIso | (intros; apply GlobalTheory.Mum.Two.weilIs_iff_of_lbIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactificationComponentIntegralSmoothProjectivStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compactificationComponent_integral_smooth_projective : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed Xo c → ∃ _ : IsIntegral (X₀ TF.Y Z), SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z) ∧ IsProjOver (s₀ TF.Y Z) ∧ GeometricallyConnected (s₀ TF.Y Z) ∧ Surjective (π₀ TF.X Z) ∧ GlobalTheory.IsNormalScheme (V₀ TF.Y Z) ∧ ∀ v : V₀ TF.Y Z, i₀ TF.Y Z v = genPt Z → j₀ TF.Y Z v = genericPoint (X₀ TF.Y Z) := by
  first | exact @GlobalTheory.BaseVar.isVariety_barComp | exact GlobalTheory.BaseVar.isVariety_barComp | (intros; apply GlobalTheory.BaseVar.isVariety_barComp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatBox
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

noncomputable section

namespace GlobalTheory.ProdUnif

open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.UnifPullRig

theorem compat_box₂ : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → ∀ (we : LB.Iso (L.pull f) (M.pull p)), BoxSq wM wL we we₁ we₂ h₁ h₂ → ∀ {T' T₁' T₂' : Scheme.{0}} {p' : T' ⟶ B} {f' : T' ⟶ G} {p₁' : T₁' ⟶ B₁} {f₁' : T₁' ⟶ G₁} {p₂' : T₂' ⟶ B₂} {f₂' : T₂' ⟶ G₂} {h₁' : T' ⟶ T₁'} {h₂' : T' ⟶ T₂'} (we' : LB.Iso (L.pull f') (M.pull p')) (we₁' : LB.Iso (L₁.pull f₁') (M₁.pull p₁')) (we₂' : LB.Iso (L₂.pull f₂') (M₂.pull p₂')), BoxSq wM wL we' we₁' we₂' h₁' h₂' → ∀ (m : T ⟶ T') (m₁ : T₁ ⟶ T₁') (m₂ : T₂ ⟶ T₂'), m ≫ h₁' = h₁ ≫ m₁ → m ≫ h₂' = h₂ ≫ m₂ → m ≫ f' = f → m ≫ p' = p → m₁ ≫ f₁' = f₁ → m₁ ≫ p₁' = p₁ → m₂ ≫ f₂' = f₂ → m₂ ≫ p₂' = p₂ → GlobalTheory.UnifPullRig.CompatAlong we₁' we₁ m₁ → GlobalTheory.UnifPullRig.CompatAlong we₂' we₂ m₂ → GlobalTheory.UnifPullRig.CompatAlong we' we m := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂ hM hM₁ hM₂ hL hL₁ hL₂
    ep₁ ep₂ ef₁ ef₂ we Q T' T₁' T₂' p' f' p₁' f₁' p₂' f₂' h₁' h₂' we' we₁' we₂' Q' m m₁ m₂ hm₁ hm₂ hmf hmp hm₁f hm₁p
    hm₂f hm₂p H₁ H₂
  rintro ⟨qM, qL⟩ V a₁ a₂
  refine unit_ext fun y hy => ?_
  have bM : p y ∈ M.U (qM ⟨⟩) := mem_pull.1 (a₂ hy).1
  have bL : f y ∈ L.U (qL ⟨⟩) := mem_pull.1 (a₂ hy).2
  obtain ⟨J, hJ, eJ⟩ := exists_good M hM y (K := PUnit) (fun _ => p) (fun _ => qM ⟨⟩) (fun _ _ _ => rfl)
    (fun _ => bM)
  obtain ⟨N, hN, eN⟩ := exists_good L hL y (K := PUnit) (fun _ => f) (fun _ => qL ⟨⟩) (fun _ _ _ => rfl)
    (fun _ => bL)
  obtain ⟨J₁, hJ₁⟩ := exists_good_at hM₁ y
  obtain ⟨J₂, hJ₂⟩ := exists_good_at hM₂ y
  obtain ⟨N₁, hN₁⟩ := exists_good_at hL₁ y
  obtain ⟨N₂, hN₂⟩ := exists_good_at hL₂ y
  have e₀ := Q T (𝟙 T) y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
  have e₁ := Q' T m y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
  have c₁ := H₁.stalk hm₁f hm₁p h₁ y (J₁ (p ≫ b₁)) (N₁ (f ≫ g₁))
    ((pt_of_eq ep₁ y) ▸ hJ₁ (p ≫ b₁)) ((pt_of_eq ef₁ y) ▸ hN₁ (f ≫ g₁))
  have c₂ := H₂.stalk hm₂f hm₂p h₂ y (J₂ (p ≫ b₂)) (N₂ (f ≫ g₂))
    ((pt_of_eq ep₂ y) ▸ hJ₂ (p ≫ b₂)) ((pt_of_eq ef₂ y) ▸ hN₂ (f ≫ g₂))
  simp only [Category.id_comp] at e₀
  rw [hmp, hmf, hm₁, hm₂, c₁, c₂, ← e₀] at e₁
  have e := mul_left_cancel e₁
  rw [eJ ⟨⟩, eN ⟨⟩] at e
  exact (gm_res_pull _ m y a₁ hy _).trans ((Category.id_comp m).symm ▸ e.trans (gm_res _ y a₂ hy _).symm)

end GlobalTheory.ProdUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsOverRingHomIsHomeomorphBaseChangeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexPointsOverRingHom_isHomeomorph_baseChange : ∀ (k K : Type) [CommRing k] [CommRing K] (ρ : k →+* K) (X G : Scheme.{0}) (p : X ⟶ Sp k) (q : G ⟶ Sp K) (j : G ⟶ X) (hp : IsPullback j q p (spMap ρ)) (τ : K →+* ℂ), IsHomeomorph (bcPt hp.w τ) := by
  first | exact @GlobalTheory.Mix.isHomeomorph_bcPt | exact GlobalTheory.Mix.isHomeomorph_bcPt | (intros; apply GlobalTheory.Mix.isHomeomorph_bcPt <;> assumption)
end

