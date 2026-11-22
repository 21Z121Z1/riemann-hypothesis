import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2877
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PairingMulFirstChern
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2872
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2640
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0777
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2763
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2878
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2744
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2762
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2879
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2813
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPointHodgePeriodFormula
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2371
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0546
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2818
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0100

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernIntegrableOnDescendGenericallyFiniteStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernIntegrableOn_descend_genericallyFinite : ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] (q : Y ⟶ Sp k) (e : ℕ), IsArithVar q e → ∀ (Y' : Scheme.{0}) [IsIntegral Y'] (ρ : Y' ⟶ Y), IsArithVar (ρ ≫ q) e → ρ (genericPoint Y') = genericPoint Y → ρ.residueDegree (genericPoint Y') ≠ 0 → ∀ (N : HermLB q) (σ : k →+* ℂ) (U : Y.Opens) (f : CxPts q σ → ℝ), ContinuousOn f (ptsIn q σ U) → ((N.restr ρ).φ σ).ChernIntegrableOn e (ptsIn (ρ ≫ q) σ (ρ ⁻¹ᵁ U)) (fun y => f (PtsOver.map ρ rfl _ y)) → (N.φ σ).ChernIntegrableOn e (ptsIn q σ U) f := by
  first | exact @GlobalTheory.ChernDescend.chernIntegrableOn_descend | exact GlobalTheory.ChernDescend.chernIntegrableOn_descend | (intros; apply GlobalTheory.ChernDescend.chernIntegrableOn_descend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartCombinationPowerStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_part_combination_power : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} (hX : IsRegVar p D) (σ : k →+* ℂ)
    {ι : Type} [Fintype ι] (L : ι → HermLB p) (n : ι → ℤ) (ε : ℤˣ),
    ((comb L n).φ σ).chernPart D ε = (hX.atlas σ).part (evalF (hX.atlas σ) (fun i => c1F hX σ (L i)) (lin (fun i => (n i : ℝ)) ^ D)) ε := by
  first | exact @GlobalTheory.ChernTop.chernPart_comb_eq_part | exact GlobalTheory.ChernTop.chernPart_comb_eq_part | (intros; apply GlobalTheory.ChernTop.chernPart_comb_eq_part <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartComplementDenseOpenNullField
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ChernNullField

theorem chernPart_compl_null : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (σ : k →+* ℂ) (D : ℕ), IsProjOver p → ∀ U : X.Opens, genericPoint X ∈ U → ∀ (B : LB X) (φ : Weight p σ B) (ε : ℤˣ), φ.chernPart D ε (ptsIn p σ U)ᶜ = 0 := by
  intro k _ X _ p σ D _ U hU B φ ε
  have hcX : (ptsIn p σ U)ᶜ =
      {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ ((U : X.Opens) : Set X)ᶜ} := by
    ext y
    simp [mem_ptsIn]
  have hA : MeasurableSet (ptsIn p σ U)ᶜ := (isOpen_ptsIn U).measurableSet.compl
  refine GlueCoverNull.glueMeas_null _ _ hA fun c => ?_
  rw [hcX]
  exact GlobalTheory.T.volume_complexPoints_properClosed_chart_field k X p σ D _ U.isOpen.isClosed_compl (by simpa using hU) c

end GlobalTheory.ChernNullField

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopChartIndependent
section
open NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ChernWeilLine
open ReciprocityTheory.L2DbarEstimates (V)
open scoped Classical

open Filter Topology AlgebraicGeometry CategoryTheory
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.ChernWeilLine

theorem cInfAt_eventually {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}
    {f : CxPts p σ → ℝ} {y : CxPts p σ} (h : CInfAt f y) : ∀ᶠ z in 𝓝 y, CInfAt f z := by
  obtain ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have hW := (isOpen_ptsIn (p := p) (σ := σ) W).mem_nhds h₁
  have hc : ContinuousAt (fun z a => ev p σ W (g a) z) y :=
    continuousAt_pi.2 fun a => (continuousOn_ev (g a)).continuousAt hW
  filter_upwards [hW, hc.preimage_mem_nhds (h₂.mem_nhds h₃), h₅.eventuallyEq_nhds] with z hz hzO hz5
  exact ⟨W, ι, i, g, F, O, hz, h₂, hzO, h₄, hz5⟩

theorem chernTop_congr {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ)
    {G G' : V n → Mat m ℂ} {v : V n} (h : G =ᶠ[𝓝 v] G') : chernTop R G v = chernTop R G' v := by
  have hc : ∀ x : ι × ℕ, chernPoly (fun u => G u x.1) v x.2 = chernPoly (fun u => G' u x.1) v x.2 := by
    intro x
    unfold chernPoly curvPoly
    simp only [curv_congr (h.mono fun u hu => congrFun hu x.1)]
  simp only [chernTop, hc]

end GlobalTheory.ChernWeilLine

theorem GlobalTheory.ChernWeilLine.chernTop_lineGram_trans : ∀ {F : Type} [Field F] [NumberField F] {Y : Var F} {σ : F →+* ℂ} {ι : Type} [Fintype ι] {Δ : ι → Y.Dv} (m : ∀ i, (cxSt F).Met Y σ (Δ i)), IsMetricOn (ofDivisors Δ) ⊤ (lineGram (cxSt F) m) → ∀ (t : ι → ℝ) (c c' : GlobalTheory.AlgChart Y.str σ Y.dim) (y : Pts Y σ), y ∈ c.e.source → y ∈ c'.e.source → ∀ A ∈ (ofDivisors Δ).S (under y), chernTop ((∑ i, C (t i) * X (i, 1)) ^ Y.dim) (fun v => lineGram (cxSt F) m A (c.e.symm v)) (c.e y) = ‖transDet c.e c'.e y‖ ^ 2 * chernTop ((∑ i, C (t i) * X (i, 1)) ^ Y.dim) (fun v => lineGram (cxSt F) m A (c'.e.symm v)) (c'.e y) := by
  intro F _ _ Y σ ι _ Δ m hM t c c' y hy hy' A hA
  set R : MvPolynomial (ι × ℕ) ℝ := (∑ i, C (t i) * X (i, 1)) ^ Y.dim
  let K : V Y.dim → Mat (fun _ : ι => 1) ℂ := fun v => lineGram (cxSt F) m A (c'.e.symm v)
  have ho := isOpen_over c.e c'.e.open_source
  have hm := mem_over c.e hy hy'
  have hφ : AnalyticAt ℂ (c'.e ∘ c.e.symm) (c.e y) :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (c.holo_trans c') (ho.mem_nhds hm)
  have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
  have hy'' : c'.e.symm (c'.e y) = y := c'.e.left_inv hy'
  have hsm := hM.smooth y mem_ptsIn_top A hA
  have hK2 : ∀ τ, MContDiffAt 2 (fun u => K u τ) (c'.e y) := by
    intro τ a b
    have hre := GlobalTheory.ChernWeilLine.cInfAt_eventually (hsm τ a b).1
    have him := GlobalTheory.ChernWeilLine.cInfAt_eventually (hsm τ a b).2
    have hn : ∀ {f : Pts Y σ → ℝ}, (∀ᶠ z in 𝓝 y, CInfAt f z) → ContDiffAt ℝ 2 (f ∘ c'.e.symm) (c'.e y) := by
      intro f hf
      have hs : c'.e.target ∩ c'.e.symm ⁻¹' {z | CInfAt f z} ∈ 𝓝 (c'.e y) := by
        refine Filter.inter_mem (c'.e.open_target.mem_nhds (c'.e.map_source hy')) ?_
        exact (c'.e.continuousAt_symm (c'.e.map_source hy')).preimage_mem_nhds (hy''.symm ▸ hf)
      exact ((contDiffOn_chart (fun z hz => hz) c').contDiffAt hs).of_le (by norm_cast)
    have h1 := (Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn hre)).add
      ((Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hn him)).mul (contDiffAt_const (c := Complex.I)))
    refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
    simp only [Function.comp_apply, Complex.ofRealCLM_apply, K]
    exact (Complex.re_add_im _).symm
  have hKu : ∀ τ, IsUnit (K (c'.e y) τ).det := by
    intro τ
    have hp := hM.posDef y mem_ptsIn_top A hA τ
    simp only [K, hy'']
    exact (Matrix.isUnit_iff_isUnit_det _).1 hp.isUnit
  have key := GlobalTheory.ChernPull.chernTop_comp R K (c'.e ∘ c.e.symm) (c.e y) hφ (e₂ ▸ hK2) (e₂ ▸ hKu)
  have hg : (fun v => lineGram (cxSt F) m A (c.e.symm v)) =ᶠ[𝓝 (c.e y)] fun w => K ((c'.e ∘ c.e.symm) w) := by
    filter_upwards [ho.mem_nhds hm] with w hw
    simp only [K, Function.comp_apply, c'.e.left_inv hw.2]
  rw [GlobalTheory.ChernWeilLine.chernTop_congr R hg, key, e₂, transDet, Complex.sq_norm]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFibreProductCoordConstantOnProjectionFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem Near.closed_fibre_constant : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (M : Modif R) (G' : Over M.S) [GrpObj G'] (E : Emb M.π G') (N : Near M.π G') (fU : N.U.left ⟶ PSpace R E.N) (l : pullback N.U.hom M.π ⟶ E.H.toScheme), l ≫ E.H.ι = N.u → l ≫ E.f = pullback.fst _ _ ≫ fU → Surjective M.π → ∀ (O : (pullback (N.U ⊗ N.U).hom M.π).Opens) (h : O.toScheme ⟶ N.U.left), (∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (s : T ⟶ M.S) (x y : Over.mk s ⟶ G'), t ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π = s → N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (fst N.U N.U).left) x.left → N.Pt s (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π ≫ (snd N.U N.U).left) y.left → N.Pt s (t ≫ h) (x * y).left) → ∀ z z' : O.toScheme, pullback.fst (N.U ⊗ N.U).hom M.π (O.ι z) = pullback.fst (N.U ⊗ N.U).hom M.π (O.ι z') → (N.U ⊗ N.U).hom (pullback.fst (N.U ⊗ N.U).hom M.π (O.ι z)) = closedPoint R → h z = h z' := by
  intro R _ _ _ M G' _ E N fU l hl hf hπ O h hyp z z' hzz hcl
  have hzz' : (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) z = (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) z' := by
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]; exact hzz
  obtain ⟨w, hw, hw'⟩ := Scheme.Pullback.exists_preimage_pullback z z' hzz'
  let P := pullback (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π)
  let t : Sp (P.residueField w) ⟶ O.toScheme := P.fromSpecResidueField w ≫ pullback.fst _ _
  let t' : Sp (P.residueField w) ⟶ O.toScheme := P.fromSpecResidueField w ≫ pullback.snd _ _
  have ht : ∀ u, t u = z := fun u => by
    show (P.fromSpecResidueField w ≫ pullback.fst _ _) u = z
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]; exact hw
  have ht' : ∀ u, t' u = z' := fun u => by
    show (P.fromSpecResidueField w ≫ pullback.snd _ _) u = z'
    rw [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]; exact hw'
  have hc₀ : t' ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π = t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π := by
    show (P.fromSpecResidueField w ≫ pullback.snd _ _) ≫ (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) =
      (P.fromSpecResidueField w ≫ pullback.fst _ _) ≫ (O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π)
    rw [Category.assoc, Category.assoc, pullback.condition]
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_spMap_residueField_of_forall_eq_closedPoint R (P.residueField w)
    ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (N.U ⊗ N.U).hom) (fun u => by
      rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, ht]; exact hcl)
  have key : ∀ (t₁ : Sp (P.residueField w) ⟶ O.toScheme),
      t₁ ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π = t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π →
      ∃ (s : Sp (P.residueField w) ⟶ M.S) (x y : Over.mk s ⟶ G'), s ≫ M.π = spMap (κ.comp (residue R)) ∧
        N.Pt s ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (fst N.U N.U).left) x.left ∧
        N.Pt s ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (snd N.U N.U).left) y.left ∧
        N.Pt s (t₁ ≫ h) (x * y).left := by
    intro t₁ e
    have hs : (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ≫ M.π =
        (t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (N.U ⊗ N.U).hom := by
      rw [← e, Category.assoc, Category.assoc, Category.assoc, Category.assoc, pullback.condition]
    have ea : ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (fst N.U N.U).left) ≫ N.U.hom =
        (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ≫ M.π := by
      rw [hs, Category.assoc, Over.w]
    have eb : ((t ≫ O.ι ≫ pullback.fst (N.U ⊗ N.U).hom M.π) ≫ (snd N.U N.U).left) ≫ N.U.hom =
        (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ≫ M.π := by
      rw [hs, Category.assoc, Over.w]
    let x : Over.mk (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ⟶ G' :=
      Over.homMk (pullback.lift _ _ ea ≫ N.u) (by
        rw [Category.assoc, N.u_over, pullback.lift_snd]; rfl)
    let y : Over.mk (t₁ ≫ O.ι ≫ pullback.snd (N.U ⊗ N.U).hom M.π) ⟶ G' :=
      Over.homMk (pullback.lift _ _ eb ≫ N.u) (by
        rw [Category.assoc, N.u_over, pullback.lift_snd]; rfl)
    refine ⟨_, x, y, hs.trans hκ, ⟨pullback.lift _ _ ea, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩,
      ⟨pullback.lift _ _ eb, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, rfl⟩, hyp _ t₁ _ x y rfl ?_ ?_⟩
    · refine ⟨pullback.lift _ _ ea, ?_, pullback.lift_snd _ _ _, rfl⟩
      rw [pullback.lift_fst, ← e]; simp only [Category.assoc]
    · refine ⟨pullback.lift _ _ eb, ?_, pullback.lift_snd _ _ _, rfl⟩
      rw [pullback.lift_fst, ← e]; simp only [Category.assoc]
  obtain ⟨s, x, y, hs, hx, hy, hxy⟩ := key t rfl
  obtain ⟨s', x', y', hs', hx', hy', hxy'⟩ := key t' hc₀
  have e := GlobalTheory.T.closedFibre_product_coordinate_independent R M G' E N fU l hl hf hπ (P.residueField w) κ s s' _ _ (t ≫ h) (t' ≫ h) x y x' y'
    hs hs' hx hy hxy hx' hy' hxy'
  have := congrArg (fun g : Sp (P.residueField w) ⟶ N.U.left => g (IsLocalRing.closedPoint _)) e
  rw [← ht (IsLocalRing.closedPoint _), ← ht' (IsLocalRing.closedPoint _)]
  first
    | exact this
    | simpa only [Scheme.Hom.comp_apply] using this
    | simpa only [Scheme.comp_base_apply] using this

end GlobalTheory.Mum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedPointMemAbelianLocusOfFixedTorsionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedPoint_mem_abelianLocus_of_fixedTorsion : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → Unif (maximalIdeal R) D A G → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V), GlobalTheory.LN.CDvr V → Function.Injective φ → ∀ n : ℕ, 2 ≤ n → IsUnit (n : V) → (∀ j : ℕ, ∃ (T' : Subring (AlgebraicClosure (FractionRing V))) (_ : IsDiscreteValuationRing T') (f : V →+* T'), (∀ v : V, (f v : AlgebraicClosure (FractionRing V)) = algebraMap (FractionRing V) _ (algebraMap V _ v)) ∧ (∀ π, Irreducible π → Irreducible (f π)) ∧ ∀ σ : AlgebraicClosure (FractionRing V) ≃+* AlgebraicClosure (FractionRing V), (∀ z ∈ T', σ z = z) → ∀ x : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ (Over.pullback (spMap φ)).obj G, x ^ (n ^ j) = 1 → spMap σ.toRingHom ≫ x.left = x.left) → closedPoint V ∈ abLocus ((Over.pullback (spMap φ)).obj G) := by
  first | exact @GlobalTheory.FixedTorsionTrait.closedPoint_mem_abLocus_of_fixedTorsion | exact GlobalTheory.FixedTorsionTrait.closedPoint_mem_abLocus_of_fixedTorsion | (intros; apply GlobalTheory.FixedTorsionTrait.closedPoint_mem_abLocus_of_fixedTorsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAbelianVarietyPeriodNormalizationStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_abelian_variety_period_normalization : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
      ∀ (𝔠 : FracId (FR E)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice c y) 0 X),
      ∃ (X₀ : Obj (FR E) 𝔠 (Sp Qb)) (p : X.A.left ⟶ X₀.A.left), X.IsPullBy X₀ (spMap (algebraMap Qb ℂ)) p := by
  first | exact @GlobalTheory.CMModel.exists_model | exact GlobalTheory.CMModel.exists_model | (intros; apply GlobalTheory.CMModel.exists_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmAuxiliarySetLocalConditions
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct
set_option autoImplicit false

noncomputable section

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FilEig

theorem fil_baseChange_eq_iSup_eigK : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (n : ℕ) (eH : HdR X₀.A ≃ₗ[R] (Fin n → R)),
      (Submodule.map eH.toLinearMap (Fil X₀.A)).baseChange (FractionRing R) =
        ⨆ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK (eH.conjRingEquiv.toRingHom.comp (act (dp0 R) (𝟙 _) cm)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) := by
  intro hPC hDR hDC E _ _ _ _ I _ d φ hφ 𝔣 h𝔣 l _ Q hQ hQl y hy lam 𝔠 R _ hR X₀ X U p cm hpull hrm hα j hj φK hφK n eH
  choose α hαm hαp hαu using hα
  have hcm : ∀ a, IsMonHom (cm.act a) := cm.hom
  have hgrp : IsGrpPullback X.A X₀.A (spMap (algebraMap R ℂ)) p := hpull.grp
  obtain ⟨hbc, hF1⟩ := hDR.2.2.1 R X₀.A _ X₀.ab X₀.dim ℂ X.A p hgrp
  obtain ⟨hfin, hproj, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hDR.1 X₀.ab X₀.dim
  obtain ⟨-, hcompl, -⟩ := hDR.2.1 R X₀.A _ X₀.ab X₀.dim
  have hcorr : ∀ (h : HdR X₀.A) c, hbc.bcMap h ((GlobalTheory.Published.AbelianDeRham.bcMor hgrp).pull c) = algebraMap R ℂ (h c) :=
    fun h c ↦ (hbc.corr_iff.2 rfl) c
  let β : (Fin n → R) →ₛₗ[algebraMap R ℂ] HdR X.A := hbc.bcMap.comp eH.symm.toLinearMap
  have hc0 : condQ 𝔣 Q ≠ ⊥ := by
    rw [condQ, Ne, Ideal.mul_eq_bot, not_or]
    refine ⟨h𝔣.1, ?_⟩
    rw [← Ideal.zero_eq_bot, Finset.prod_eq_zero_iff]
    push_neg
    intro q _
    rw [Ideal.zero_eq_bot]
    exact q.ne_bot
  have hC := GlobalTheory.T.cm_order_uniformization_endomorphisms hPC hDR E I φ hφ.2.2.2.2.2.2.1 (condQ 𝔣 Q) hc0 𝔠 _ X U α hαu
  refine GlobalTheory.T.lattice_basis_fraction_field_independent j hj β ?_ _ (fun a ↦ push (dp0 ℂ) (𝟙 _) (α a)) ?_ _ (fun i ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φK i)) ?_
  · exact GlobalTheory.T.semilinear_dual_basis_base_change (GlobalTheory.Published.AbelianDeRham.bcMor hgrp).pull hbc eH _ (fun k c ↦ hcorr _ c)
  · intro a x
    have e := GrpMor.Corr.push (GlobalTheory.Published.AbelianDeRham.bcMor hgrp) (cm.act a) (α a)
      (hαp a).symm (hbc.corr_iff.2 rfl : (GlobalTheory.Published.AbelianDeRham.bcMor hgrp).Corr (eH.symm x) (hbc.bcMap (eH.symm x)))
    have e2 := hbc.corr_iff.1 e
    simp only [β, LinearMap.comp_apply, LinearEquiv.coe_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_comp,
      RingHom.coe_coe, Function.comp_apply]
    rw [act_apply]
    simpa [LinearEquiv.conjRingEquiv, LinearEquiv.conj_apply] using e2
  · have himg : β '' (Submodule.map eH.toLinearMap (Fil X₀.A) : Set (Fin n → R)) = hbc.bcMap '' (Fil X₀.A : Set (HdR X₀.A)) := by
      ext v
      simp [β]
    rw [himg, Fil, GlobalTheory.T.semilinear_filtration_base_change (GlobalTheory.Published.AbelianDeRham.bcMor hgrp).pull hbc _ hcompl _ hF1 hbc.bcMap hcorr]
    change Fil X.A = _
    rw [hC]
    congr 1
    ext i : 1
    congr 1
    ext a : 1
    congr 1
    show _ = j (φK i _)
    rw [← RingHom.comp_apply, hφK i]
    rfl

end GlobalTheory.FilEig
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmLatticeSpansRealSpaceStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_lattice_spans_real_space : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), 0 < d → δ ^ 2 = -(d : K) →
    ∀ g : ℂ ≃+* ℂ, (∀ x, g (io x) = io x) →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ),
      IsCMType φ → (∀ i, (φ i).comp (algebraMap K E) = io) →
      ∀ (n : ℕ) (e : Fin n ≃ I) (Λ : Submodule ℤ (Fin n → ℂ)) (L : Set E),
        Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ → (∀ w, w ∈ Λ ↔ ∃ x ∈ L, w = fun j ↦ g (φ (e j) x)) →
      ∀ (h : I → ℝ) (β : E), (∀ i, (h i : ℂ) = 2 * Complex.I * φ i β) → ∀ N : ℝ, 0 < N →
      ∀ Hm : Matrix (Fin n) (Fin n) ℂ, Hm.IsHermitian →
        (∀ x ∈ L, ∀ x' ∈ L, ((fun j ↦ g (φ (e j) x)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (e j) x'))).im =
          N⁻¹ * ∑ i, h i * (φ i x * starRingEnd ℂ (φ i x')).im) →
        ∃ h' : I → ℝ, Hm = Matrix.diagonal (fun j ↦ (h' (e j) : ℂ)) ∧
          ∀ i, g ((h i : ℂ) * (Real.sqrt d : ℝ)) = (N : ℂ) * ((h' i : ℂ) * (Real.sqrt d : ℝ)) := by
  first | exact @GlobalTheory.HermDiagCM.diagonal_of_conj_form | exact GlobalTheory.HermDiagCM.diagonal_of_conj_form | (intros; apply GlobalTheory.HermDiagCM.diagonal_of_conj_form <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmPointHodgePeriodFormulaStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_point_hodge_period_formula : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ → ∀ (𝔠 : FracId (FR E)) (T : CxPt 𝔠 φ (lattice c y)),
      ∃ β : E, ∀ i, (T.U.h i : ℂ) = 2 * Complex.I * φ i β := by
  first | exact @GlobalTheory.cmPoint_herm_eq | exact GlobalTheory.cmPoint_herm_eq | (intros; apply GlobalTheory.cmPoint_herm_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRiemannFormGaloisConjugateStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (upIdele IsLatOf)
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cm_riemann_form_galois_conjugate : ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (io : K →+* ℂ), Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∀ g : ℂ ≃+* ℂ, (∀ x, g (io x) = io x) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I]
    (φ : I → E →+* ℂ), (∀ i, (φ i).comp (algebraMap K E) = io) → ∀ (c : Ideal (OF E)) (y : (Af E)ˣ), c ≠ ⊥ →
    ∀ (n : ℕ) (e : Fin n ≃ I) (h : I → ℝ) (Hm : Matrix (Fin n) (Fin n) ℂ), 0 < n →
      (∀ z : Fin n → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ (Matrix.diagonal fun j ↦ (h (e j) : ℂ)).mulVec (star z)).re) → Hm.IsHermitian →
      (∀ z : Fin n → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm.mulVec (star z)).re) →
      ∃ u ∈ lattice c y, ∃ u' ∈ lattice c y, (∑ i, h i * (φ i u * starRingEnd ℂ (φ i u')).im) ≠ 0 ∧
        0 < (∑ i, h i * (φ i u * starRingEnd ℂ (φ i u')).im) * ((fun j ↦ g (φ (e j) u)) ⬝ᵥ Hm.mulVec (star fun j ↦ g (φ (e j) u'))).im := by
  first | exact @GlobalTheory.ConjRiemannPos.exists_pos_pair | exact GlobalTheory.ConjRiemannPos.exists_pos_pair | (intros; apply GlobalTheory.ConjRiemannPos.exists_pos_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpFormEqZeroOfPullbackVanishingStatement
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cmpForm_eq_zero_of_pullback_vanishing : ∀ (K : Type) [Field K] (X : Over (Sp K)), Smooth X.hom → ∀ f : Form (X.hom ≫ 𝟙 (Sp K)), (∀ (L : Type) [Field L] (σ : K →+* L), ∃ (X' : Over (Sp L)) (φ : X'.left ⟶ X.left) (m : IsMor (dp0 K) (X.hom ≫ 𝟙 (Sp K)) (dp0 L) (X'.hom ≫ 𝟙 (Sp L)) σ φ), IsPullback φ X'.hom X.hom (spMap σ) ∧ ∀ u : epsR L ⟶ X', tanVal u (m.pullForm f) = 0) → GlobalTheory.CechDR.cmpForm (X.hom ≫ 𝟙 (Sp K)) f = 0 := by
  first | exact @GlobalTheory.PtVanish.cmpForm_eq_zero_of_tanVal | exact GlobalTheory.PtVanish.cmpForm_eq_zero_of_tanVal | (intros; apply GlobalTheory.PtVanish.cmpForm_eq_zero_of_tanVal <;> assumption)
end

