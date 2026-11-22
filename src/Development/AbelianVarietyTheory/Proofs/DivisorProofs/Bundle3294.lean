import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3121
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3205
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3116
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3282
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3281
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1626
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1756
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1857
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1632
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3280
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2388
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2414
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2746
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2548
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3279
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2826
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RelAmpleNearFibreFlatProjective
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0617
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3274
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3186
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0457

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableLogNormSectionArithmeticVariety
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem intg_logSec_of_arithVar : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (σ : k →+* ℂ) (L : Fin D → MLine p σ) (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → Intg L (M.logSec s) := by
  intro hP k _ X _ _ p D hX σ L M s hs
  have := hX.isDomain
  have := hX.finite
  have hσ : Function.Injective σ := by
    have hk : RingHom.ker σ = ⊥ := Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (by
      ext n
      simp [Ideal.mem_comap, RingHom.mem_ker])
    exact (RingHom.injective_iff_ker_eq_bot σ).2 hk
  let K := FractionRing k
  obtain ⟨τ, rfl⟩ : ∃ τ : K →+* ℂ, σ = τ.comp (algebraMap k K) :=
    ⟨IsFractionRing.lift hσ, by ext a; simp⟩
  let G := Limits.pullback p (spMap (algebraMap k K))
  let j : G ⟶ X := Limits.pullback.fst _ _
  let q : G ⟶ Sp K := Limits.pullback.snd _ _
  have hp : IsPullback j q p (spMap (algebraMap k K)) := IsPullback.of_hasPullback _ _
  obtain ⟨hGi, hGn, hproj, hdim, hgen, -, hstalk, -, -⟩ := GlobalTheory.T.generic_fiber_arithmetic_variety_integral_projective k K X G p q j hp D hX
  obtain ⟨s', hs', -, -, hlog⟩ := GlobalTheory.T.exists_section_generic_fiber_pullback_local_iso k K X G p q j hp τ hstalk M s hs hgen
  have h1 := GlobalTheory.T.log_norm_section_integrable_mixedChern_projective hP K G q τ D hproj hdim (fun i => (L i).bc hp.w τ) (M.bc hp.w τ) s' hs'
  have h2 := ((GlobalTheory.T.mixedChernMeasure_integral_eq_genericFibre k K X G p q j hp τ D hX L).2 (M.logSec s)).1
  refine h2.1 ?_
  have e : (M.bc hp.w τ).logSec s' = fun y => M.logSec s (bcPt hp.w τ y) := funext hlog
  rwa [e] at h1

end GlobalTheory.Mix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolynomialEqIntersectionNumber
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc

theorem integral_evalF_c1W_eq_interPoly : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, P.IsHomogeneous X.dim → (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  intro hCD F _ σ X κ _ Δ L r ψ hψ P hP
  haveI := CxPts.compactSpace σ X.isProjOver
  haveI := CxPts.t2Space_cxPts_of_isProjOver σ X.isProjOver
  haveI := CxPts.secondCountableTopology_of_isProjOver σ X.isProjOver
  have hform : ∀ G : MvPolynomial κ ℝ, (atlas X σ).IsForm (evalF (atlas X σ) (fun a => c1W (ψ a)) G) :=
    fun G => ((GlobalTheory.formCalculus _ _ (atlas X σ)).2.2.2.1 κ _ G
      (fun a => (GlobalTheory.T.firstChernFormOfWeight_isForm_dbar_eq_zero F σ X (L a) (ψ a) (hψ a).2).1)).1
  have Pw := GlobalTheory.LineForm.wInt_props (CxPts X.str σ) X.dim (atlas X σ)
  have hint : ∀ G : MvPolynomial κ ℝ, ∀ ε : ℤˣ,
      Integrable (fun _ => (1 : ℝ)) ((atlas X σ).part (evalF (atlas X σ) (fun a => c1W (ψ a)) G) ε) :=
    fun G ε => by
      haveI := Pw.1 _ (hform G) ε
      exact integrable_const _
  have hadd : ∀ G₁ G₂ : MvPolynomial κ ℝ,
      (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) (G₁ + G₂)) =
        (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G₁) +
          (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G₂) := fun G₁ G₂ => by
    rw [← wInt_one, ← wInt_one, ← wInt_one, GlobalTheory.LineForm.GeoInt.evalF_add]
    exact (Pw.2.1 _ _ _ (hform G₁) (hform G₂) (hint G₁) (hint G₂)).2
  have hsmul : ∀ (t : ℝ) (G : MvPolynomial κ ℝ),
      (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) (t • G)) =
        t * (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) G) := fun t G => by
    rw [← wInt_one, ← wInt_one, GlobalTheory.LineForm.GeoInt.evalF_smul]
    exact Pw.2.2.1 _ t _ (hform G)
  have hspan := GlobalTheory.LineForm.GeoInt.mem_span_pow_lin X.dim P hP
  clear hP
  induction hspan using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨n, rfl⟩ := hx
    obtain ⟨L', r', ψ', hpr, hci, hc1⟩ := GlobalTheory.T.exists_smoothWeight_integral_combination F σ X κ Δ L r ψ hψ n
    have e1 : evalF (atlas X σ) (fun a => c1W (ψ a)) (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) =
        fld (atlas X σ) (c1W ψ' ^ X.dim) := by
      funext x
      rw [hc1]
      simp only [evalF, fld, GlobalTheory.ArInt.lin, map_pow, map_sum, map_mul, MvPolynomial.map_C,
        MvPolynomial.map_X, MvPolynomial.aeval_C, MvPolynomial.aeval_X, Finset.sum_apply, Pi.smul_apply, Pi.pow_apply]
      congr 2
    have e2 : X.interPoly Δ (GlobalTheory.ArInt.lin (fun i => (n i : ℝ)) ^ X.dim) = (X.inter fun _ => ∑ a, n a • Δ a : ℝ) := by
      have := Var.interPoly_prod_sum X Δ (fun _ a => n a)
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
      exact this
    rw [e1, e2, HolAtlas.integral, GlobalTheory.T.part_firstChernFormOfWeight_pow_eq_chernPart F σ X L' ψ' hci, GlobalTheory.T.part_firstChernFormOfWeight_pow_eq_chernPart F σ X L' ψ' hci,
      ← (hCD F X σ _ L' r' hpr ψ' hci).2]
    simp only [Weight.chernInt, Measure.restrict_univ, integral_const, smul_eq_mul, mul_one]
  | zero =>
    rw [map_zero]
    have := hsmul 0 0
    rw [zero_smul, zero_mul] at this
    exact this
  | add x y _ _ hx hy =>
    rw [map_add, hadd, hx, hy]
  | smul t x _ hx =>
    rw [map_smul, hsmul, hx, smul_eq_mul]

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelDbarZero
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

namespace GlobalTheory.CxFormStokesBoth

open Set

section
variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem eq_sum_fn_mul {N : ℕ} (χ : Fin N → M → ℝ) (hχ : ∀ y, ∑ j, χ j y = 1) (η : A.Fld) :
    η = ∑ j, A.fn (χ j) * η := by
  rw [← Finset.sum_mul]
  have : (∑ j, A.fn (χ j)) = 1 := by
    funext x
    simp only [Finset.sum_apply, HolAtlas.fn, Pi.one_apply]
    rw [← map_sum, ← Complex.ofReal_sum, hχ, Complex.ofReal_one, map_one]
  rw [this, one_mul]

theorem dbar_sum {N : ℕ} (α : Fin N → A.Fld) (hα : ∀ j, A.IsForm (α j)) :
    A.dbar (∑ j, α j) = ∑ j, A.dbar (α j) := by
  have C := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A
  have h0 : A.IsForm 0 := by simpa using (C.2.1 0 1 1 C.1 C.1).2.2.1
  have hd0 : A.dbar 0 = 0 := by
    have := (C.2.1 0 0 0 h0 h0).2.2.2.2.2.2.1
    rw [add_zero] at this
    exact left_eq_add.mp this
  have key : ∀ s : Finset (Fin N), A.IsForm (∑ j ∈ s, α j) ∧ A.dbar (∑ j ∈ s, α j) = ∑ j ∈ s, A.dbar (α j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using ⟨h0, hd0⟩
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have := C.2.1 0 (α a) _ (hα a) ih.1
      exact ⟨this.1, by rw [this.2.2.2.2.2.2.1, ih.2]⟩
  exact (key Finset.univ).2
end

theorem stokes : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    ∀ η : A.Fld, A.IsForm η → A.integral (A.del η) = 0 ∧ A.integral (A.dbar η) = 0 := by
  intro M _ _ _ _ _ _ n A η hη
  have C := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A
  obtain ⟨N, c, χ, hs, hsupp, hone⟩ := GlobalTheory.T.exists_finite_smooth_partition_unity_holAtlas A
  have hf : ∀ j, A.IsForm (A.fn (χ j) * η) := fun j =>
    (C.2.1 0 _ _ (HolAtlas.isForm_fn A (hs j)) hη).2.1
  have hdec := eq_sum_fn_mul A χ hone η
  constructor
  · rw [hdec, GlobalTheory.T.holAtlas_del_finset_sum A _ hf, GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ (fun j => (C.2.1 0 _ _ (hf j) (hf j)).2.2.2.1)]
    exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.integral_del_chartSupported_mul_form_eq_zero A η (χ j) (c j) hη (hs j) (hsupp j)
  · rw [hdec, dbar_sum A _ hf, GlobalTheory.T.holAtlas_integral_fin_sum_compact A _ (fun j => (C.2.1 0 _ _ (hf j) (hf j)).2.2.2.2.1)]
    exact Finset.sum_eq_zero fun j _ => GlobalTheory.T.integral_dbar_cutoff_mul_form_eq_zero_local_stokes A η (χ j) (c j) hη (hs j) (hsupp j)

end GlobalTheory.CxFormStokesBoth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemePullbackOfIsPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem isAbelianScheme_pullback_of_isPullback : ∀ (S T S' : Scheme.{0}) (G : Over S) [GrpObj G] (t : T ⟶ S) (A : Over S') [GrpObj A] (a : pullback G.hom t ⟶ A.left) (g : T ⟶ S'), IsSemiAbelian G → IsAbelianScheme A → IsPullback a (pullback.snd G.hom t) A.hom g → IsAbelianScheme ((Over.pullback t).obj G) := by
  intro S T S' G _ t A _ a g hG hA sq
  exact
  { comm := by have := hG.comm; infer_instance
    smooth := by have := hG.smooth; change Smooth (pullback.snd G.hom t); infer_instance
    proper := by
      have := hA.proper; change IsProper (pullback.snd G.hom t)
      exact MorphismProperty.of_isPullback (P := @IsProper) sq inferInstance
    geomConnected := by
      have := hA.geomConnected; change GeometricallyConnected (pullback.snd G.hom t)
      exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) sq inferInstance }

theorem ampleDiv_closure_on_chart : ∀ (R₀ : Type) [CommRing R₀] [IsDomain R₀] (f : R₀) (A : Over (Sp (Localization.Away f))) [GrpObj A] [IsIntegral A.left], IsAbelianScheme A → ∀ D : CartierDiv A.left, AmpleDiv D → LBIso ((toLB D).pull (GrpObj.inv : A ⟶ A).left) (toLB D) → ∀ (R : Type) [CommRing R] [IsRegularLocalRing R] [IsDomain R] [CharZero R], IsAdicComplete (maximalIdeal R) R → ∀ (ρ : R₀ →+* R), ρ.Flat → ρ f ≠ 0 → ∀ (G : Over (Sp R)) [GrpObj G] [IsIntegral G.left], IsSemiAbelian G → ∀ (V : G.left.Opens) (φ : V.toScheme ⟶ A.left) (θ : A.left.functionField →+* G.left.functionField) (D₁ : CartierDiv G.left), (∀ z : G.left, z ∈ V ↔ ρ f ∉ (G.hom z).asIdeal) → IsPullback φ (V.ι ≫ G.hom) (A.hom ≫ awayMap f) (spMap ρ) → ∀ (y : Sp (FractionRing R) ⟶ Sp (Localization.Away f)) (α : pullback G.hom (jK R) ⟶ A.left), IsGrpPullback ((Over.pullback (jK R)).obj G) A y α → (∀ (T : Scheme.{0}) (t : T ⟶ pullback G.hom (jK R)) (t' : T ⟶ V.toScheme), t ≫ pullback.fst _ _ = t' ≫ V.ι → t ≫ α = t' ≫ φ) → PFF V.ι φ θ → PPull V.ι φ θ D D₁ → AmpleDiv D₁ := by
  intro R₀ _ _ f A _ _ hA D hD hsym R _ _ _ _ hR ρ hflat hρf G _ _ hG V φ θ D₁ hV hsq y α hα hcomp hff hpp
  obtain ⟨g, l, hl, sq⟩ := GlobalTheory.GenericFibreChart.exists_isPullback_generic R₀ f A R ρ hρf G V φ hV hsq
  have hGK : IsAbelianScheme ((Over.pullback (jK R)).obj G) :=
    isAbelianScheme_pullback_of_isPullback _ _ _ G (jK R) A (l ≫ φ) g hG hA sq
  haveI : IsProper ((Over.pullback (jK R)).obj G).hom := hGK.proper
  haveI : IsProper A.hom := hA.proper
  haveI : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
  have hAD : IsAmpleLB (toLB D) := (ampleDiv_iff_isAmpleLB A.left D).1 hD
  have h1 : IsAmpleLB ((toLB D).pull (l ≫ φ)) := hAD.pull_of_isPullback sq
  have h3 : LBIso ((toLB D₁).pull V.ι) ((toLB D).pull φ) := GlobalTheory.Desc.PullOpen.lbIso_pull _ _ V φ θ D D₁ hff hpp
  have hL₁ := isLB_toLB D₁
  have h4 : LBIso ((toLB D₁).pull (pullback.fst G.hom (jK R))) ((toLB D).pull (l ≫ φ)) := by
    rw [← hl]
    exact LBIso.trans (LB.isLB_pull hL₁ _) (LB.isLB_pull (LB.isLB_pull hL₁ _) _)
      (LB.isLB_pull (isLB_toLB D) _) (GlobalTheory.OriginCohom.lbIso_pull_pull_comp hL₁ V.ι l).symm
      (LBIso.trans (LB.isLB_pull (LB.isLB_pull hL₁ _) _) (LB.isLB_pull (LB.isLB_pull (isLB_toLB D) _) _)
        (LB.isLB_pull (isLB_toLB D) _) (GlobalTheory.Mum.UExt.lbIso_pull h3 l)
        (GlobalTheory.OriginCohom.lbIso_pull_pull_comp (isLB_toLB D) φ l))
  have h5 : IsAmpleLB ((toLB D₁).pull (pullback.fst G.hom (jK R))) := h1.of_lbIso (LB.isLB_pull hL₁ _) h4
  have h6 := (relAmple_iff_isAmpleLB_of_isAffine ((Over.pullback (jK R)).obj G) (LB.isLB_pull hL₁ _)).2 h5
  have hlα : α = l ≫ φ := by
    have := hcomp _ (𝟙 _) l (by rw [Category.id_comp, hl])
    rwa [Category.id_comp] at this
  have hs1 := GlobalTheory.T.symmetric_lineBundle_pullback_grpPullback _ _ A ((Over.pullback (jK R)).obj G) y α hα (toLB D) (isLB_toLB D) hsym
  rw [hlα] at hs1
  have hK₁ := LB.isLB_pull hL₁ (pullback.fst G.hom (jK R))
  have hK := LB.isLB_pull (isLB_toLB D) (l ≫ φ)
  have hs2 : LBIso (((toLB D₁).pull (pullback.fst G.hom (jK R))).pull
      (GrpObj.inv : (Over.pullback (jK R)).obj G ⟶ (Over.pullback (jK R)).obj G).left)
      ((toLB D₁).pull (pullback.fst G.hom (jK R))) :=
    LBIso.trans (LB.isLB_pull hK₁ _) (LB.isLB_pull hK _) hK₁ (GlobalTheory.Mum.UExt.lbIso_pull h4 _)
      (LBIso.trans (LB.isLB_pull hK _) hK hK₁ hs1 h4.symm)
  haveI : IsIntegrallyClosed R := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  have hs3 := GlobalTheory.T.lineBundle_symmetric_of_symmetric_generic_fibre R G hG (toLB D₁) hL₁ hs2
  have h7 := GlobalTheory.T.raynaud_lineBundle_relAmple_of_generic_semiAbelian R hR G hG hGK (toLB D₁) hL₁ h6 hs3
  haveI : QuasiCompact G.hom := hG.quasiCompact
  haveI : CompactSpace G.left := QuasiCompact.compactSpace_of_compactSpace G.hom
  exact (ampleDiv_iff_isAmpleLB G.left D₁).2 h7

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorOfNefFibresAmple
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
open Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.AmpleNefFibZ

theorem exists_prime_le (P : Ideal ℤ) [P.IsPrime] :
    ∃ l : ℕ, l.Prime ∧ ∀ r : ℤ, r ∉ Ideal.span {(l : ℤ)} → r ∉ P := by
  obtain ⟨M, hM, hPM⟩ := Ideal.exists_le_maximal P (Ideal.IsPrime.ne_top ‹_›)
  set m := Submodule.IsPrincipal.generator M
  have hmM : Ideal.span {m} = M := Submodule.IsPrincipal.span_singleton_generator M
  have hm0 : m ≠ 0 := by
    rintro h
    have := Ideal.bot_lt_of_maximal M Int.not_isField
    rw [← hmM, h, Ideal.span_singleton_eq_bot.2 rfl] at this
    exact lt_irrefl _ this
  have hmp : Prime m := (Ideal.span_singleton_prime hm0).1 (hmM ▸ hM.isPrime)
  refine ⟨m.natAbs, Int.prime_iff_natAbs_prime.1 hmp, fun r hr hrP => hr ?_⟩
  rw [Ideal.mem_span_singleton, Int.natAbs_dvd]
  rw [← Ideal.mem_span_singleton, hmM]
  exact hPM hrP

theorem isAmpleLB_tens_of_nefFib : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, NefFib L → IsAmpleLB A.B → IsAmpleLB (L.tens A).B := by
  intro k _ X _ p D hX L A hL hA
  haveI : Module.Finite ℤ k := hX.finite
  set s : X ⟶ Sp ℤ := p ≫ spMap (Int.castRingHom k) with hs_def
  have hsZ : s = ShFam.Pad.toSpZ X := specZIsTerminal.hom_ext _ _
  have hP : IsProjOver s := hsZ ▸ ShFam.Pad.isProjOver_toSpZ hX.isProjOver
  have hPB : AbLaw.IsProjBy s := (ProjSpace.isProjBy_iff_isProjOver s).2 hP
  haveI : IsProper s := hsZ ▸ FibreProj.isProper_of_isArithVar (ShFam.Pad.isArithVar_toSpZ hX)
  have hM : (L.tens A).B.IsLB := (L.tens A).isLB
  haveI : IsProper (Over.mk s).hom := ‹IsProper s›
  refine (relAmple_iff_isAmpleLB_of_isAffine (Over.mk s) hM).1 ?_
  refine AmpleLocal.relAmple_of_locally _ (Over.mk s) _ hM inferInstance inferInstance fun P => ?_
  obtain ⟨l, hl, hlP⟩ := @exists_prime_le P.asIdeal P.isPrime
  haveI : Fact l.Prime := ⟨hl⟩
  have F := GlobalTheory.T.isAmple_tensor_nef_ample_finiteFieldFibre k X p D hX L A hL hA l
  have hFib : Out.RelAmple ((Over.pullback (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l))))).obj (Over.mk s))
      ((L.tens A).B.pull (pullback.fst s (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l)))))) := by
    haveI : IsProper ((Over.pullback (Spec.map (CommRingCat.ofHom (Int.castRingHom (ZMod l))))).obj (Over.mk s)).hom :=
      inferInstanceAs (IsProper (pullback.snd s _))
    exact (relAmple_iff_isAmpleLB_of_isAffine _ (LB.isLB_pull hM _)).2 F
  have hfrac : ∀ y : ZMod l, ∃ a b : ℤ, Int.castRingHom (ZMod l) b ≠ 0 ∧
      y * Int.castRingHom (ZMod l) b = Int.castRingHom (ZMod l) a :=
    fun y => ⟨(y.val : ℤ), 1, by simp, by simp⟩
  obtain ⟨r, hr, hA'⟩ := AmpleNear.relAmple_near_fibre ℤ (Over.mk s) (L.tens A).B hX.flat hPB hM (ZMod l)
    (Int.castRingHom (ZMod l)) hfrac hFib
  have hrl : r ∉ Ideal.span {(l : ℤ)} := by
    rw [Ideal.mem_span_singleton]
    intro h
    exact hr ((ZMod.intCast_zmod_eq_zero_iff_dvd r l).2 h)
  let U : (Spec (CommRingCat.of ℤ)).Opens := PrimeSpectrum.basicOpen r
  haveI : IsAffine U.toScheme := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of ℤ) r
  exact ⟨U, hlP r hrl, AmpleFibres.relAmple_restrict U (Over.mk s) hM hA'⟩

end GlobalTheory.AmpleNefFibZ
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsogenyCompIffAndDegreeMulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIsogeny_comp_iff_and_degree_mul : ∀ (K : Type) [Field K] (A B C : AbVar K) (f : A ⟶ B) (g : B ⟶ C), A.dim = B.dim → B.dim = C.dim → (IsIsogeny (f ≫ g) ↔ IsIsogeny f ∧ IsIsogeny g) ∧ deg (f ≫ g) = deg f * deg g := by
  first | exact @GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp | exact GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp | (intros; apply GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerRigExtMapRelFrobLeRangeRigOfOmega
section
set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDiv.FrobRigKer

variable {O A B : Type} [CommRing O] [CommRing A] [CommRing B] [Bialgebra O A] [Bialgebra O B]

variable (O A) in

def evalZeroTwo : A ⊗[O] A →ₗ[O] O :=
  (TensorProduct.lid O O).toLinearMap ∘ₗ TensorProduct.map (counit (R := O)) (counit (R := O))

@[simp] theorem evalZeroTwo_tmul (a b : A) :
    evalZeroTwo O A (a ⊗ₜ b) = counit (R := O) a * counit (R := O) b := by
  simp [evalZeroTwo]

theorem evalZeroTwo_pullTwo (f : A →ₐc[O] B) (c : A ⊗[O] A) :
    evalZeroTwo O B (pullbackTwo f c) = evalZeroTwo O A c := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [pullbackTwo, evalZeroTwo_tmul]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]

theorem evalZeroTwo_comul (b : A) : evalZeroTwo O A (comul b) = counit (R := O) b := by
  have key : TensorProduct.map (counit (R := O)) (counit (R := O)) (comul (R := O) b) =
      LinearMap.lTensor O (counit (R := O)) (LinearMap.rTensor A (counit (R := O)) (comul b)) := by
    rw [← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply]
  show TensorProduct.lid O O (TensorProduct.map (counit (R := O)) (counit (R := O)) (comul b)) = _
  rw [key, Coalgebra.rTensor_counit_comul, LinearMap.lTensor_tmul, TensorProduct.lid_tmul, one_smul]

theorem evalZeroTwo_cobOne (b : A) : evalZeroTwo O A (cobOne O A b) = - counit (R := O) b := by
  rw [cobOne_apply, map_sub, map_sub, evalZeroTwo_comul, evalZeroTwo_tmul, evalZeroTwo_tmul,
    Bialgebra.counit_one]
  ring

theorem mk_kerIdeal_apply (f : A →ₐc[O] B) (a : A) :
    Ideal.Quotient.mkₐ O (kerIdeal f) (f a) = counit (R := O) a • 1 := by
  have hmem : a - algebraMap O A (counit (R := O) a) ∈ augIdeal O A := by
    simp [RingHom.mem_ker]
  have himg := Ideal.mem_map_of_mem (f : A →ₐ[O] B) hmem
  have e : (f : A →ₐ[O] B) (algebraMap O A (counit (R := O) a)) = algebraMap O B (counit (R := O) a) :=
    AlgHom.commutes _ _
  rw [map_sub, e] at himg
  rw [Algebra.smul_def, mul_one, ← AlgHom.commutes (Ideal.Quotient.mkₐ O (kerIdeal f)),
    Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
  exact himg

theorem map_mk_pullTwo (f : A →ₐc[O] B) (c : A ⊗[O] A) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ O (kerIdeal f)) (Ideal.Quotient.mkₐ O (kerIdeal f))
      (pullbackTwo f c) = evalZeroTwo O A c • 1 := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | tmul a b =>
    simp only [pullbackTwo, TensorProduct.map_tmul, BialgHom.coe_toLinearMap,
      Algebra.TensorProduct.map_tmul, mk_kerIdeal_apply, evalZeroTwo_tmul,
      Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', TensorProduct.tmul_smul, smul_smul]
    rw [mul_comm]
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, add_smul]

theorem map_mk_cobOne_eq_zero (f : A →ₐc[O] B) {c : A ⊗[O] A} {b : B}
    (hb : counit (R := O) b = 0) (hc : cobOne O B b = pullbackTwo f c) :
    Algebra.TensorProduct.map (Ideal.Quotient.mkₐ O (kerIdeal f)) (Ideal.Quotient.mkₐ O (kerIdeal f))
      (cobOne O B b) = 0 := by
  rw [hc, map_mk_pullTwo, ← evalZeroTwo_pullTwo f c, ← hc, evalZeroTwo_cobOne, hb, neg_zero,
    zero_smul]

def oneFun {p : ℕ} (G : PDivGroup p O) : G.funs := ⟨fun _ => 1, fun _ => map_one _⟩

theorem funsMap_oneFun {p : ℕ} {G H : PDivGroup p O} (f : G ⟶ H) :
    funsMap f (oneFun H) = oneFun G :=
  Subtype.ext (funext fun n => map_one (f.app n))

theorem dUnit_one : dUnit O (1 : A) = 0 := by
  simp [dUnit]

end GlobalTheory.PDiv.FrobRigKer

namespace GlobalTheory.PDivGroup

open GlobalTheory.PDiv.FrobRigKer

theorem ker_rigExtMap_relFrob_le_range_rigOfOmega (p : ℕ) [Fact p.Prime] (K : Type) [Field K]
    (h : (p : K) = 0) (G : PDivGroup p K) :
    LinearMap.ker (rigExtMap (relFrob h G)) ≤ LinearMap.range (frobTwist h G).rigOfOmega := by
  have : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out)).2 h
  intro x hx
  rw [LinearMap.mem_ker] at hx
  obtain ⟨⟨c, w⟩, rfl⟩ : ∃ z, (frobTwist h G).rigMk z = x := Submodule.mkQ_surjective _ x
  rw [rigExtMap_mk] at hx
  obtain ⟨B, hB⟩ := (Submodule.Quotient.mk_eq_zero _).1 hx
  have hB1 : G.cob B = cocyclesMap (relFrob h G) c := congrArg Prod.fst hB
  have hB2 : G.dFun B = G.omegaMap _ (relFrob h G) w := congrArg Prod.snd hB
  set t : K := counit (R := K) (B.1 1) with ht
  set B₁ : G.funs := B - t • oneFun G with hB₁
  set c₁ : (frobTwist h G).cocycles := c - t • (frobTwist h G).cob (oneFun (frobTwist h G))
    with hc₁def
  have hc₁ : G.cob B₁ = cocyclesMap (relFrob h G) c₁ := by
    simp only [hB₁, hc₁def, map_sub, map_smul, hB1, cocyclesMap_cob, funsMap_oneFun]
  have hb0 : counit (R := K) (B₁.1 1) = 0 := by
    show counit (R := K) (B.1 1 - t • (1 : G.A 1)) = 0
    rw [map_sub, map_smul, Bialgebra.counit_one, smul_eq_mul, mul_one, ht, sub_self]
  have hbd : dUnit K (B₁.1 1) = 0 := by
    have e1 : G.dFun B = 0 := by rw [hB2, omegaMap_relFrob, LinearMap.zero_apply]
    have e2 : G.dFun (oneFun G) = 0 := Subtype.ext (funext fun n => dUnit_one)
    have e : G.dFun B₁ = 0 := by rw [hB₁, map_sub, map_smul, e1, e2, smul_zero, sub_zero]
    exact congrArg (fun z : G.omega => z.1 1) e
  have hcob : cobOne K (G.A 1) (B₁.1 1) = pullbackTwo ((relFrob h G).app 1) (c₁.1 1) :=
    congrArg (fun z : G.cocycles => z.1 1) hc₁
  have hker := GlobalTheory.T.frobeniusKernelIdeal_eq_kernel_relativeFrobenius p K h G 1
  have hmem : B₁.1 1 ∈ frobKerIdeal p K (G.A 1) := by
    refine GlobalTheory.T.mem_frobeniusKernelIdeal_of_zero_differential p K (G.A 1) _ hb0 hbd ?_
    rw [hker]
    exact map_mk_cobOne_eq_zero ((relFrob h G).app 1) hb0 hcob
  rw [hker] at hmem
  have hV : (verschiebung h G).app 1 (B₁.1 1) = 0 :=
    GlobalTheory.T.app_one_eq_zero_of_kernel_ideal_of_comp_eq_prime_smul p K G (frobTwist h G) (relFrob h G) (verschiebung h G)
      (verschiebung_comp_relFrob h G) _ hmem
  have hcomp : cocyclesMap (verschiebung h G) (cocyclesMap (relFrob h G) c₁) =
      cocyclesMap (verschiebung h G ≫ relFrob h G) c₁ :=
    Subtype.ext (funext fun n => (pullTwo_comp _ _ _).symm)
  obtain ⟨B', hB'⟩ : c₁ ∈ LinearMap.range (frobTwist h G).cob := by
    refine GlobalTheory.T.pDivCocycle_mem_range_cob_of_pullback_mulP (frobTwist h G) c₁ (funsMap (verschiebung h G) B₁) ?_ hV
    rw [← cocyclesMap_cob, hc₁, hcomp, verschiebung_comp_relFrob]
  set B₀ : (frobTwist h G).funs := B' + t • oneFun (frobTwist h G) with hB₀
  have hc0 : (frobTwist h G).cob B₀ = c := by
    rw [hB₀, map_add, map_smul, hB', hc₁def, sub_add_cancel]
  refine ⟨w - (frobTwist h G).dFun B₀, ?_⟩
  show Submodule.Quotient.mk ((0 : (frobTwist h G).cocycles), w - (frobTwist h G).dFun B₀) =
    Submodule.Quotient.mk (c, w)
  refine ((Submodule.Quotient.eq
    (LinearMap.range ((frobTwist h G).cob.prod (frobTwist h G).dFun))).2
    (LinearMap.mem_range.2 ⟨B₀, Prod.ext ?_ ?_⟩)).symm
  · show (frobTwist h G).cob B₀ = c - 0
    rw [sub_zero]
    exact hc0
  · show (frobTwist h G).dFun B₀ = w - (w - (frobTwist h G).dFun B₀)
    exact (sub_sub_cancel w _).symm

end GlobalTheory.PDivGroup
end
end

