import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTypeAllAddOfEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0242
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0070
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0086
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0017
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0016
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.MaxBoundPf
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0038
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0040
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0042
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0039
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0044
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0021
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0008
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0025
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0042
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0014
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0054
import Development.AbelianVarietyTheory.Proofs.HeightProofs.LeOfFiniteSplitNotSplitBauer
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0024

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.HasAllKTypesOfClosureDiscreteSeriesCoefficients
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ClosureSeries

open Formalism.REAL GlobalTheory.SmoothGlob GlobalTheory.TypeSum

theorem hasTypeAll_of_closure : GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CasselmanWallach →
    ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ), Formalism.QuantumDeterminants.IsHCParam lam →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)),
    IsDS ε lam σ → ∀ f : Matrix (Fin n) (Fin n) ℂ → ℂ, ContinuousOn f (UJset ε) → GlobalTheory.TypeSum.UMG ε f →
    (∀ C : Set (Matrix (Fin n) (Fin n) ℂ), IsCompact C → ∀ δ : ℝ, 0 < δ →
      ∃ (m : ℕ) (ℓ : Fin m → (H →ₗ[ℂ] ℂ)) (v : Fin m → H), (∀ j, Sobolev₂ (GlobalTheory.SmoothGlob.lieSet ε) σ (ℓ j)) ∧
        (∀ j, SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) σ (v j)) ∧
        ∀ y ∈ C, y ∈ UJset ε → ‖f y - ∑ j, ℓ j (σ y (v j))‖ < δ) →
    GlobalTheory.TypeSum.HasTypeAll (GlobalTheory.TypeSum.lieOf (Formalism.REAL.Jm ε)) (Formalism.QuantumDeterminants.UH (Formalism.REAL.Jm ε)) σ f := by
  intro hHC hCW n ε lam _ H _ _ σ hDS f hf hU happ
  haveI : CompleteSpace H := hDS.1
  have hstd : Std ε σ := std_of_isDS hHC hDS
  refine GlobalTheory.T.discreteSeriesCoeffSeries_of_kTypeProjections hHC hCW n ε H σ hstd f hf hU ?_
  intro e he hK
  obtain ⟨hc, hu⟩ := GlobalTheory.T.compactAverage_continuousOn_uniformModerateGrowth n ε f hf hU e he
  obtain ⟨d, w, hw, hap⟩ := GlobalTheory.T.kProjection_limit_discreteSeriesCoeffs n ε H σ hstd f hf happ e he hK
  obtain ⟨L, hL, heq⟩ := GlobalTheory.T.eq_matrixCoeff_of_locallyUniform_limit_kFinite hHC hCW n ε H σ hstd d w hw _ hc hu hap
  exact ⟨d, L, w, hL, hw, heq⟩

end GlobalTheory.ClosureSeries
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.PnContinuous
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.FrameNorm GlobalTheory.Reg

noncomputable section

namespace GlobalTheory.HeightDefinite.Generic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem frMap_comp {S T U : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T] [CommRing U]
    [Algebra c.F U] (φ : S →ₐ[c.F] T) (ψ : T →ₐ[c.F] U) {y : FrPt Xo c S} {z : FrPt Xo c T} {w : FrPt Xo c U}
    (h₁ : FrMap φ y z) (h₂ : FrMap ψ z w) : FrMap (ψ.comp φ) y w :=
  Formalism.L2.Pj.frMap_trans S T U φ ψ y z w h₁ h₂

theorem frBor_of_frMap {S T : Type} [CommRing S] [Algebra c.F S] [CommRing T] [Algebra c.F T]
    (φ : S →ₐ[c.F] T) {t : Ix Dw → Sˣ} {y y' : FrPt Xo c S} {z z' : FrPt Xo c T} (h : FrBor t y y')
    (hz : FrMap φ y z) (hz' : FrMap φ y' z') : FrBor (fun i => Units.map (φ : S →* T) (t i)) z z' := by
  obtain ⟨g, hg2, hg1, hg⟩ := (GlobalTheory.Frames.frBor_iff_frChg y y' t).1 h
  have hc := (GlobalTheory.Frames.ChgBC.frChg_baseChange E H Dw l Xo c S T φ y y' z z' g _ hg hz).1 hz'
  exact (GlobalTheory.Frames.frBor_iff_frChg z z' _).2
    ⟨fun τ => (g τ).map φ, fun τ i j hij => by simp [hg2 τ i j hij], fun τ i => by simp [hg1], hc⟩

theorem evR_of_frMap (hL : EvLaws Xo c) {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul Xo c} (hg : g ∈ sec Xo c a n)
    {S T : Type} [CommRing S] [IsReduced S] [Algebra c.F S] [CommRing T] [Algebra c.F T] (φ : S →ₐ[c.F] T)
    {y : FrPt Xo c S} {z : FrPt Xo c T} (hyz : FrMap φ y z) : evR Xo c g z = φ (evR Xo c g y) := by
  obtain ⟨q, χ, y₀, hy₀⟩ := hL.test S y
  rw [evR_eq_map_of_test_point hL hg q χ y₀ y hy₀,
    evR_eq_map_of_test_point hL hg q (φ.comp χ) y₀ z (frMap_comp χ φ hy₀ hyz)]
  rfl

theorem isFractionRing_chart {h : GenFrEx Xo c} (C : FChart h) : IsFractionRing C.R (Om C.Z) := by
  refine IsFractionRing.of_field _ _ fun x => ?_
  obtain ⟨a, ha, b, hb, hb0, e⟩ := C.frac x
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩, by
    change x = a / b
    rw [eq_div_iff hb0, e]⟩

theorem le_of_generic {h : GenFrEx Xo c} (C : FChart h) (σ : c.F →+* ℂ) (F : (C.R →ₐ[c.F] CAt σ) → ℝ)
    (hF : @Continuous _ _ (TopologicalSpace.induced (fun x (a : C.R) => Formalism.L2.PjFree.toC (x a)) inferInstance) _ F)
    (M : ℝ) (hM : ∀ (x : C.R →ₐ[c.F] CAt σ) (P : Om C.Z →+* ℂ), P ∈ T0.PT (Ω := Om C.Z) σ →
      (∀ a, Formalism.L2.PjFree.toC (x a) = P a) → F x ≤ M) (ψ : C.R →ₐ[c.F] CAt σ) : F ψ ≤ M := by
  letI : TopologicalSpace (C.R →ₐ[c.F] CAt σ) :=
    TopologicalSpace.induced (fun x (a : C.R) => Formalism.L2.PjFree.toC (x a)) inferInstance
  have hcl : IsClosed {x | F x ≤ M} := isClosed_le hF continuous_const
  refine hcl.closure_subset (mem_closure_iff_nhds.2 fun t ht => ?_)
  rw [nhds_induced, Filter.mem_comap] at ht
  obtain ⟨s, hs, hst⟩ := ht
  rw [nhds_pi, Filter.mem_pi'] at hs
  obtain ⟨I, u, hu, hIu⟩ := hs
  have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ∀ a ∈ I, Metric.ball (Formalism.L2.PjFree.toC (ψ a)) ε ⊆ u a := by
    rw [Filter.eventually_all_finset]
    intro a _
    obtain ⟨δ, hδ, hb⟩ := Metric.mem_nhds_iff.1 (hu a)
    filter_upwards [Ioo_mem_nhdsGT hδ] with ε hε
    exact (Metric.ball_subset_ball hε.2.le).trans hb
  obtain ⟨ε, hε, hε0⟩ := (hev.and self_mem_nhdsWithin).exists
  haveI := C.sm
  haveI := isFractionRing_chart C
  let φ : C.R →+* ℂ := ψ.toRingHom
  have hφ : φ.comp (algebraMap c.F C.R) = σ := RingHom.ext fun k => ψ.commutes k
  obtain ⟨P, hP, hPε⟩ := GlobalTheory.generic_points_dense GlobalTheory.exists_algIndep_tuple_near c.F C.R (Om C.Z) σ φ hφ I ε hε0
  let x : C.R →ₐ[c.F] CAt σ :=
    { (P.comp (algebraMap C.R (Om C.Z)) : C.R →+* ℂ) with
      commutes' := fun k => RingHom.congr_fun hP k }
  refine ⟨x, hst (hIu fun a ha => hε a ha ?_), hM x P hP fun a => rfl⟩
  rw [Metric.mem_ball, dist_eq_norm]
  exact hPε a ha

section Pin

variable {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r}
  (hU : ∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) {xR : ℝ}
  {fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ} (hx : 0 < xR) (hfn : FnPin U xR fn)
  {a : (E →+* ℂ) × ℕ → ℕ} {n : ℕ} {g : Rul Xo c}

abbrev pn (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (g : Rul Xo c) (y : FrPt Xo c (CAt σ)) : ℝ :=
  ptNorm (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) σ (fn σ) (ex Dw a n) g y

include hU hx hfn

theorem pn_frBor_good (hd : Dom a n) (hg : g ∈ sec Xo c a n) {σ : c.F →+* ℂ} (hσ : Formalism.L2.PjFree.GoodEmb c σ)
    {t : Ix Dw → (CAt σ)ˣ} {y y' : FrPt Xo c (CAt σ)} (hb : FrBor t y y') : pn fn σ a n g y' = pn fn σ a n g y := by
  obtain ⟨k, x, s, hs⟩ := (hU σ hσ).2.2.1 y
  have hs' := (GlobalTheory.Reg.BorelGroupoid.frBor_groupoid E H Dw l Xo c (CAt σ)).2.1 _ _ _ _ _ hs hb
  have T := (GlobalTheory.T.pointwise_norm_section_eq_flagDomain_norm E H Dw l Xo c r U hU xR fn hx hfn).2.1 σ hσ k x
  exact (T _ _ hs' a n hd g hg).trans (T _ _ hs a n hd g hg).symm

theorem pn_frBor (hd : Dom a n) (hg : g ∈ sec Xo c a n) {σ : c.F →+* ℂ}
    {t : Ix Dw → (CAt σ)ˣ} {y y' : FrPt Xo c (CAt σ)} (hb : FrBor t y y') : pn fn σ a n g y' = pn fn σ a n g y := by
  by_cases hσ : Formalism.L2.PjFree.GoodEmb c σ
  · exact pn_frBor_good hU hx hfn hd hg hσ hb
  · have hσ' : Formalism.L2.PjFree.GoodEmb c ((starRingEnd ℂ).comp σ) := by
      have := Formalism.L2.PjFree.goodEmb_goodOf c σ
      unfold Formalism.L2.PjFree.goodOf at this
      rwa [if_neg hσ] at this
    have hL := (GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c).1
    obtain ⟨z, hz⟩ := hL.bc _ _ (conjAlg σ) y
    obtain ⟨z', hz'⟩ := hL.bc _ _ (conjAlg σ) y'
    have T := (GlobalTheory.T.pointwise_norm_section_eq_flagDomain_norm E H Dw l Xo c r U hU xR fn hx hfn).2.2 σ
    exact ((T _ _ hz' a n g hg).symm.trans
      (pn_frBor_good hU hx hfn hd hg hσ' (frBor_of_frMap _ hb hz hz'))).trans (T _ _ hz a n g hg)

theorem pn_generic (hd : Dom a n) (hg : g ∈ sec Xo c a n) {h : GenFrEx Xo c}
    {yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))} (hyP : ∀ Z, CBase h Z (yP Z))
    (C : FChart h) {σ : c.F →+* ℂ} (x : C.R →ₐ[c.F] CAt σ) (P : Om C.Z →+* ℂ) (hP : P ∈ T0.PT (Ω := Om C.Z) σ)
    (hxP : ∀ b, Formalism.L2.PjFree.toC (x b) = P b) {z : FrPt Xo c (CAt σ)} (hz : FrMap x C.y z) :
    pn fn σ a n g z = nrmC fn (yP C.Z) (wtZ a n) (valC h a n g C.Z) P := by
  obtain rfl : sgOf P = σ := hP
  have hL := (GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c).1
  obtain ⟨w, hw⟩ := hL.bc _ _ (PAlg P) C.yg
  have h1 := frMap_comp _ _ C.gen hw
  obtain rfl : x = (PAlg P).comp C.R.val := AlgHom.ext hxP
  obtain rfl : z = w := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ _ C.y).1 _ _ hz h1
  rw [(GlobalTheory.T.frameNorm_conjugate_points_eq_pointwise E H Dw l Xo c r U hU xR fn hx hfn h yP hyP).2.2 C.Z P a n g hg]
  exact pn_frBor hU hx hfn hd hg (frBor_of_frMap _ C.bor (hyP C.Z P) hw)

theorem pn_continuous (hg : g ∈ sec Xo c a n) {h : GenFrEx Xo c} (C : FChart h) {σ : c.F →+* ℂ}
    (y : (C.R →ₐ[c.F] CAt σ) → FrPt Xo c (CAt σ)) (hy : ∀ x, FrMap x C.y (y x)) :
    @Continuous _ _ (TopologicalSpace.induced (fun x (b : C.R) => Formalism.L2.PjFree.toC (x b)) inferInstance) _
      fun x => pn fn σ a n g (y x) := by
  letI : TopologicalSpace (C.R →ₐ[c.F] CAt σ) :=
    TopologicalSpace.induced (fun x (b : C.R) => Formalism.L2.PjFree.toC (x b)) inferInstance
  haveI := C.sm
  have hL := (GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c).1
  have hc : ∀ b : C.R, Continuous fun x : C.R →ₐ[c.F] CAt σ => Formalism.L2.PjFree.toC (x b) := fun b =>
    (continuous_apply b).comp
      (continuous_induced_dom (f := fun (x : C.R →ₐ[c.F] CAt σ) (b : C.R) => Formalism.L2.PjFree.toC (x b)))
  have hf : ∀ i, Continuous fun x => |fn σ (y x) i| := fun i =>
    continuousOn_univ.1 (GlobalTheory.T.frameNorms_continuousOn_smoothChart E H Dw l Xo c r U hU xR fn hx hfn σ C.R C.y _ Set.univ (fun x => x) y
      (fun b => (hc b).continuousOn) (fun x _ => hy x) i)
  have hne := (GlobalTheory.T.pointwise_norm_section_eq_flagDomain_norm E H Dw l Xo c r U hU xR fn hx hfn).1
  have e : (fun x => pn fn σ a n g (y x)) =
      fun x => ‖Formalism.L2.PjFree.toC (x (evR Xo c g C.y))‖ * ∏ i, |fn σ (y x) i|⁻¹ ^ ex Dw a n i := by
    funext x
    rw [← evR_of_frMap hL hg x (hy x)]
    rfl
  rw [e]
  exact (hc _).norm.mul (continuous_finsetProd _ fun i _ =>
    ((hf i).inv₀ fun x => abs_ne_zero.2 (hne _ _ _)).pow _)

end Pin

theorem supC_le_iSup_generic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ∀ (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Formalism.L2.PjFree.Unf Xo c σ r), (∀ σ, Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf (U σ)) → ∀ (xR : ℝ) (fn : ∀ σ : c.F →+* ℂ, FrPt Xo c (CAt σ) → Ix Dw → ℝ), 0 < xR → FnPin U xR fn → ∀ (h : GenFrEx Xo c) (yP : ∀ Z : Comp Xo c, ∀ P : Om Z →+* ℂ, FrPt Xo c (CAt (sgOf P))), (∀ Z, CBase h Z (yP Z)) → ∀ a n, Dom a n → ∀ (Z : Comp Xo c), ∀ f ∈ Formalism.L2.PjFree.cusp Xo c U a n, ∀ g ∈ Formalism.L2.PjFree.cusp Xo c U a n, evC h Z g = evC h Z f → (∀ Z', Z' ≠ Z → evC h Z' g = 0) → ∀ σ : c.F →+* ℂ, BddAbove (Set.range fun P : T0.PT (Ω := Om Z) σ => nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P) ∧ Formalism.L2.PjFree.supC Xo c U xR (Formalism.L2.PjFree.goodOf c σ) a n g ≤ ⨆ P : T0.PT (Ω := Om Z) σ, nrmC fn (yP Z) (wtZ a n) (valC h a n f Z) P := by
  intro E _ _ _ H Dw l Xo c r U hU xR fn hx hfn h yP hyP a n hd Z f hf g hg hgf hg0 σ
  have hgs := Formalism.L2.PjFree.cusp_le_sec Xo c U a n hg
  obtain ⟨hB, hS⟩ := GlobalTheory.T.pointwiseNorm_bddAbove_iSup_eq_cuspForm_supNorm E H Dw l Xo c r U hU xR fn hx hfn a n hd g hg
  obtain ⟨hL, -, -, hA⟩ := GlobalTheory.T.evaluation_laws_generic_frames_atlas_hold E H Dw l Xo c
  have hv : valC h a n f Z = valC h a n g Z := by unfold valC; rw [hgf]
  rw [hv, ← hS σ]
  have hbdd : BddAbove (Set.range fun P : T0.PT (Ω := Om Z) σ => nrmC fn (yP Z) (wtZ a n) (valC h a n g Z) P) := by
    refine ⟨supR Xo c fn σ a n g, ?_⟩
    rintro _ ⟨⟨P, hP⟩, rfl⟩
    obtain rfl : sgOf P = σ := hP
    dsimp only
    rw [(GlobalTheory.T.frameNorm_conjugate_points_eq_pointwise E H Dw l Xo c r U hU xR fn hx hfn h yP hyP).2.2 Z P a n g hgs]
    exact le_ciSup (hB (sgOf P)) (yP Z P)
  have hnn : 0 ≤ ⨆ P : T0.PT (Ω := Om Z) σ, nrmC fn (yP Z) (wtZ a n) (valC h a n g Z) P :=
    Real.iSup_nonneg fun P => mul_nonneg (norm_nonneg _)
      (Finset.prod_nonneg fun i _ => zpow_nonneg (abs_nonneg _) _)
  refine ⟨hbdd, Real.iSup_le (fun y => ?_) hnn⟩
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  obtain ⟨C, ψ, z, t, hz, hb⟩ := hA h (CAt σ) y
  change pn fn σ a n g y ≤ _
  rw [pn_frBor hU hx hfn hd hgs hb]
  by_cases hZ : C.Z = Z
  · subst hZ
    choose w hw using fun x : C.R →ₐ[c.F] CAt σ => hL.bc _ _ x C.y
    obtain rfl : z = w ψ := (GlobalTheory.Frames.frMap_unique_refl_iff E H Dw l Xo c _ _ _ C.y).1 _ _ hz (hw ψ)
    refine le_of_generic C σ (fun x => pn fn σ a n g (w x)) (pn_continuous hU hx hfn hgs C w hw) _
      (fun x P hP hxP => ?_) ψ
    rw [pn_generic hU hx hfn hd hgs hyP C x P hP hxP (hw x)]
    exact le_ciSup hbdd ⟨P, hP⟩
  · have h1 : evR Xo c g C.yg = 0 := by
      rw [hL.wt a n g hgs _ C.t _ _ (hL.test _ _) (hL.test _ _) C.bor]
      have := hg0 C.Z hZ
      unfold evC at this
      rw [this, mul_zero]
    have h2 : evR Xo c g C.y = 0 := by
      rw [evR_of_frMap hL hgs C.R.val C.gen] at h1
      exact Subtype.ext h1
    have h3 : evR Xo c g z = 0 := by rw [evR_of_frMap hL hgs ψ hz, h2, map_zero]
    have h4 : pn fn σ a n g z = 0 := by
      change cabs (evR Xo c g z) * _ = 0
      rw [h3]
      exact mul_eq_zero_of_left (norm_zero (E := ℂ)) _
    rw [h4]
    exact hnn

end GlobalTheory.HeightDefinite.Generic
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetOfContainsRayFi
section
set_option autoImplicit false

open NumberField IsDedekindDomain GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.WeberIn

theorem finite_mem {K : Type} [Field K] [NumberField K] {a : 𝓞 K} (ha : a ≠ 0) :
    {𝔭 : HeightOneSpectrum (𝓞 K) | a ∈ 𝔭.asIdeal}.Finite := by
  have h : Ideal.span {a} ≠ (0 : Ideal (𝓞 K)) := by
    simpa [Ideal.span_singleton_eq_bot] using ha
  refine (Ideal.finite_factors h).subset ?_
  intro 𝔭 h𝔭
  exact Ideal.dvd_span_singleton.2 h𝔭

theorem finite_norm_mem {K : Type} [Field K] [NumberField K] (S : Finset ℕ) :
    {𝔭 : HeightOneSpectrum (𝓞 K) | Ideal.absNorm 𝔭.asIdeal ∈ S}.Finite := by
  have h : {I : Ideal (𝓞 K) | Ideal.absNorm I ≠ 0 ∧ Ideal.absNorm I ∈ S}.Finite := by
    refine (Ideal.finite_setOf_absNorm_le (S := 𝓞 K) (S.sup id)).subset ?_
    intro I hI
    exact Finset.le_sup (f := id) hI.2
  refine (h.preimage (f := fun 𝔭 : HeightOneSpectrum (𝓞 K) => 𝔭.asIdeal)
    (fun a _ b _ hab => HeightOneSpectrum.ext hab)).subset ?_
  intro 𝔭 h𝔭
  exact ⟨fun h0 => 𝔭.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0), h𝔭⟩

theorem numberField_adjoin (K L : IntermediateField ℚ ℂ) [NumberField L] (S : Set ℂ)
    [NumberField (IntermediateField.adjoin K S)] : NumberField (IntermediateField.adjoin L S) := by
  have h1 : FiniteDimensional ℚ ((IntermediateField.adjoin K S).restrictScalars ℚ) :=
    (inferInstance : FiniteDimensional ℚ (IntermediateField.adjoin K S))
  have hle : IntermediateField.adjoin ℚ S ≤ (IntermediateField.adjoin K S).restrictScalars ℚ :=
    IntermediateField.adjoin_le_iff.2 (IntermediateField.subset_adjoin K S)
  have h2 : FiniteDimensional ℚ (IntermediateField.adjoin ℚ S) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  have h3 : FiniteDimensional ℚ ((IntermediateField.adjoin L S).restrictScalars ℚ) := by
    have e := IntermediateField.restrictScalars_adjoin_eq_sup ℚ L S
    have h5 : FiniteDimensional ℚ (L ⊔ IntermediateField.adjoin ℚ S : IntermediateField ℚ ℂ) := inferInstance
    rw [← e] at h5
    exact h5
  have h4 : FiniteDimensional ℚ (IntermediateField.adjoin L S) := h3
  exact NumberField.mk

theorem weberSet_subset : ∀ (K L : IntermediateField ℚ ℂ) [NumberField K] [NumberField L] [IsTotallyComplex K] (h : K ≤ L), Module.finrank ℚ K = 2 → discr K < -4 → ∀ P : PeriodPair, (∀ z, z ∈ P.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, 3 ≤ n → GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (IntermediateField.inclusion h).toRingHom n → weberSet P n ⊆ L := by
  intro K L _ _ _ h h2 hd P hP n hn hR
  obtain ⟨inst, S, hS⟩ := GlobalTheory.T.principalRayPrimes_splitCompletely_weberValues K h2 hd P hP n hn
  haveI := numberField_adjoin K L (weberSet P n)
  have hn0 : (n : 𝓞 L) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  haveI : NumberField (⊥ : IntermediateField L ℂ) := NumberField.of_module_finite L _
  have hle : IntermediateField.adjoin L (weberSet P n) ≤ ⊥ := by
    refine GlobalTheory.Bauer.le_of_finite_split_not_split L ℂ ⊥ (IntermediateField.adjoin L (weberSet P n)) ?_
    refine ((finite_mem hn0).union (finite_norm_mem S)).subset ?_
    rintro 𝔓 ⟨hp, -, hnot⟩
    by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or] at hc
    obtain ⟨f, α, hN, hα, h1⟩ := hR 𝔓 hc.1
    have hf : f = 1 := by
      have hp' := hp
      rw [hN] at hp'
      exact hp'.eq_one_of_pow
    subst hf
    rw [pow_one] at hN hα
    have hne : 𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom) ≠ ⊥ := by
      intro h0
      rw [h0, Ideal.absNorm_bot] at hN
      exact hp.ne_zero hN
    haveI := 𝔓.isPrime
    let 𝔭 : HeightOneSpectrum (𝓞 K) :=
      ⟨𝔓.asIdeal.comap (RingOfIntegers.mapRingHom (IntermediateField.inclusion h).toRingHom),
        Ideal.comap_isPrime _ _, hne⟩
    apply hnot
    refine GlobalTheory.T.completeSplitting_compositum_degreeOnePrime K L h (weberSet P n) 𝔭 𝔓 rfl hN ?_
    have h𝔭 : 𝔭.asIdeal = Ideal.span {α} := hα
    rw [h𝔭]
    exact hS α _ hp hc.2 (by rw [← hα, ← hN]) (Ideal.mem_span_singleton.2 h1)
  intro x hx
  have hx' := hle (IntermediateField.subset_adjoin L _ hx)
  obtain ⟨y, rfl⟩ := IntermediateField.mem_bot.1 hx'
  exact y.2

end GlobalTheory.FieldSize.WeberIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberInvariantTorsionValuesSubsetRayClassField
section
set_option autoImplicit false

open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.FieldSize.InRayAny

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField in
private theorem weberSet_subset_of_isRay_span_natCast :
    ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
      discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) →
      ∀ n : ℕ, 3 ≤ n → ∀ (R : IntermediateField K ℂ) [NumberField R] [IsAbelianGalois K R],
      _root_.GlobalTheory.FieldSize.IsRay R (Ideal.span {(n : 𝓞 K)}) → _root_.GlobalTheory.FieldSize.weberSet L n ⊆ R := by
  intro K _ _ h2 hd L hL n hn R _ _ hR
  obtain ⟨hM, S, hS⟩ := _root_.GlobalTheory.WeberSplitAny.splits_completely_of_three_le K h2 hd L hL n hn
  have hn0 : 0 < n := by omega
  have hN : Ideal.absNorm (Ideal.span {(n : 𝓞 K)}) ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn0.ne'
  have hMR : IntermediateField.adjoin (↥K) (_root_.GlobalTheory.FieldSize.weberSet L n) ≤ R := by
    apply _root_.GlobalTheory.Bauer.le_of_finite_split_not_split (↥K) ℂ R _
    refine ((Ideal.finite_setOfPred_absNorm_le (S := 𝓞 K)
      (S.sup id + Ideal.absNorm (Ideal.span {(n : 𝓞 K)}))).preimage
      (f := fun v : HeightOneSpectrum (𝓞 K) => v.asIdeal)
      (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro 𝔭 ⟨hp, hsplit, hnot⟩
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    by_cases hpS : Ideal.absNorm 𝔭.asIdeal ∈ S
    · exact le_add_right (Finset.le_sup (f := id) hpS)
    by_cases hn𝔭 : (n : 𝓞 K) ∈ 𝔭.asIdeal
    · refine le_add_left (Nat.le_of_dvd (Nat.pos_of_ne_zero hN) ?_)
      exact Ideal.absNorm_dvd_absNorm_of_le ((Ideal.span_singleton_le_iff_mem _).mpr hn𝔭)
    · exfalso
      obtain ⟨π, hπ, hπ1⟩ :=
        (_root_.GlobalTheory.FieldSize.RaySplit.ncard_eq_finrank_iff (↥K) (↥R) n hn0 hR 𝔭 hn𝔭).mp hsplit
      apply hnot
      rw [hπ] at hp hpS ⊢
      exact hS π _ hp hpS rfl hπ1
  exact fun x hx => hMR (IntermediateField.subset_adjoin _ _ hx)

set_option autoImplicit false in
open NumberField IsDedekindDomain Polynomial in
open scoped IntermediateField in

theorem _root_.GlobalTheory.FieldSize.InRayAny.weberSet_subset :
    ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 →
      discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) →
      ∀ n : ℕ, 3 ≤ n → ∀ (R : IntermediateField K ℂ) [NumberField R] [IsAbelianGalois K R],
      _root_.GlobalTheory.FieldSize.IsRay R (Ideal.span {(n : 𝓞 K)}) → _root_.GlobalTheory.FieldSize.weberSet L n ⊆ R :=
  weberSet_subset_of_isRay_span_natCast

end GlobalTheory.FieldSize.InRayAny
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.WeberSetSubsetRayFieldStatement
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weber_set_subset_ray_field : ∀ (K : IntermediateField ℚ ℂ) [NumberField K] [IsTotallyComplex K], Module.finrank ℚ K = 2 → discr K < -4 → ∀ L : PeriodPair, (∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 K, ((a : K) : ℂ) = z) → ∀ n : ℕ, Odd n → 3 ≤ n → ∀ (R : IntermediateField K ℂ) [NumberField R] [IsAbelianGalois K R], IsRay R (Ideal.span {(n : 𝓞 K)}) → weberSet L n ⊆ R := by
  first | exact @GlobalTheory.FieldSize.InRay.weberSet_subset | exact GlobalTheory.FieldSize.InRay.weberSet_subset | (intros; apply GlobalTheory.FieldSize.InRay.weberSet_subset <;> assumption)
end

