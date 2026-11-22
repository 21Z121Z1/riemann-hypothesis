import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1188
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1296
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1182
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3295
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1391
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2376
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2664
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3293
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3146
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3287
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3294
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3241
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2926
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3280
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3010
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodMetricTopChernFormIntegralEqSmooth
section
open AlgebraicGeometry MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)

namespace GlobalTheory.GoodTop

theorem goodTopChernForm : GlobalTheory.Published.GoodTopChernForm := by
  intro F _ σ X m E O H H₀ hH hG hH₀ t ht
  rw [hasChernIntegral_iff] at ht ⊢
  haveI := X.smooth_str
  haveI : SecondCountableTopology (CxPts X.str σ) := inferInstance
  have hp : ∀ y : CxPts X.str σ, ∃ e S A W c, y ∈ W ∧ GoodPatch E O H e S A W c := fun y => by
    by_cases hy : y ∈ ptsIn X.str σ O
    · exact GlobalTheory.T.exists_goodPatch_of_complexPoint_openPart E O H hH y hy
    · exact GlobalTheory.T.exists_poincareGoodPatch_outside_open E O H hG y hy
  choose e S A W c hyW hP using hp
  obtain ⟨s, ρ, hρ, hsupp, hsum⟩ := GlobalTheory.T.exists_smooth_partition_of_unity_complexPoints W fun y => (hP y).isOpen.mem_nhds (hyW y)
  choose a b ha hb hab using fun i : s => GlobalTheory.T.transgression_topChernForm_goodPatch E O H H₀ hH hH₀ (hP i) (hρ i) (hsupp i)
  have hd : ∀ i j : AlgChart X.str σ X.dim,
      DifferentiableOn ℂ (j.e ∘ i.e.symm) (i.e.target ∩ i.e.symm ⁻¹' j.e.source) := fun i j => i.holo_trans j
  have hcov : ∀ y, ∃ i : AlgChart X.str σ X.dim, y ∈ i.e.source := fun y => AlgChart.exists_mem_source y
  have hm : ∀ U : X.X.Opens, MeasurableSet (ptsIn X.str σ U) := fun U => (isOpen_ptsIn U).measurableSet
  have hc : ∀ i, Continuous (ρ i) := fun i => continuous_iff_continuousAt.2 fun y => (hρ i y).continuousAt
  have h₁ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (topDens E H) (ptsIn X.str σ O) (∑ i, a i) := by
    refine GlobalTheory.T.hasTopFormChartIntegral_congr_on _ (hm O) (fun i y _ _ => ?_)
      (GlobalTheory.T.integral_finite_sum_topForms _ hd hcov (hm O) (fun i => GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree E O H hH (hc i)) ha)
    rw [← Finset.sum_mul, hsum, one_mul]
  have h₂ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (topDens E H₀) (ptsIn X.str σ ⊤) (∑ i, b i) := by
    refine GlobalTheory.T.hasTopFormChartIntegral_congr_on _ (hm ⊤) (fun i y _ _ => ?_)
      (GlobalTheory.T.integral_finite_sum_topForms _ hd hcov (hm ⊤) (fun i => GlobalTheory.T.continuous_mul_top_chern_form_isTopDegree E ⊤ H₀ hH₀ (hc i)) hb)
    rw [← Finset.sum_mul, hsum, one_mul]
  have h₃ : HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun _ _ => 0) (ptsIn X.str σ O) (∑ i, (a i - b i)) :=
    GlobalTheory.T.hasTopFormChartIntegral_congr_on _ (hm O) (fun i y _ hy => GlobalTheory.T.sum_transgression_densities_partition_unity_eq_zero E O H H₀ ρ hρ hsum i y hy)
      (GlobalTheory.T.integral_finite_sum_topForms _ hd hcov (hm O) (fun i => GlobalTheory.T.transgression_correction_isTopDegreeForm E O H H₀ hH hH₀ (hρ i)) hab)
  have e₂ : ∑ i, b i = t := h₂.2.symm.trans ht.2
  have e₃ : ∑ i, (a i - b i) = 0 := h₃.2.symm.trans (GlobalTheory.T.hasTopFormChartIntegral_zero _ _).2
  rw [Finset.sum_sub_distrib, sub_eq_zero, e₂] at e₃
  exact e₃ ▸ h₁

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasDualRepresentativeOfRelAmpleNoetherian
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.DualPol

theorem hasRepAF_of_relAmple : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → HasRepAF A g (𝟙_ _) := by
  intro R _ _ A _ g hA hg L hL ha
  obtain ⟨B, P, q, hP, hgood, hfa, hfin, hfl, hsu, hF, hK⟩ := GlobalTheory.T.exists_quotient_kernel_polarisation_descended_bundle R A g hA hg L hL ha
  have hinj : Inj A P := GlobalTheory.T.dualPoint_eq_of_quotient_family_iso R A g hA hg L hL ha B P q hP hfin hfl hsu hF hK
  have hex : ∀ (T : Over (Sp R)) (N : LB (A ⊗ T).left), Fam A N →
      ∃ x : T ⟶ B, LBIso N (ev P (fst A T) (snd A T ≫ x)) := by
    intro T N hN
    obtain ⟨H, h, x, hhf, hhs, hhq, hx⟩ := GlobalTheory.T.exists_flatCover_additiveFamily_eq_lambda R A g hA hg L hL ha T N hN
    have key : ∀ (Y : Over (Sp R)) (a : Y ⟶ A) (y : Y ⟶ H),
        evc hP.isLB a (y ≫ x ≫ q) = evc hN.isLB a (y ≫ h) := by
      intro Y a y
      rw [hx, ← Category.assoc, hF]
    have hc : ∀ {Z : Scheme} (g₁ g₂ : Z ⟶ H.left), g₁ ≫ h.left = g₂ ≫ h.left →
        g₁ ≫ (x ≫ q).left = g₂ ≫ (x ≫ q).left := by
      intro Z g₁ g₂ e
      let Z' : Over (Sp R) := Over.mk (g₁ ≫ H.hom)
      have e2 : g₂ ≫ H.hom = g₁ ≫ H.hom := by
        rw [← Over.w h, ← Category.assoc, ← e, Category.assoc]
      let k₁ : Z' ⟶ H := Over.homMk g₁ rfl
      let k₂ : Z' ⟶ H := Over.homMk g₂ e2
      have hkh : k₁ ≫ h = k₂ ≫ h := Over.OverMorphism.ext e
      have hs : Same A P P (k₁ ≫ x ≫ q) (k₂ ≫ x ≫ q) := by
        rw [same_iff hP.isLB hP.isLB]
        have e₁ := key (A ⊗ Z') (fst A Z') (snd A Z' ≫ k₁)
        have e₂ := key (A ⊗ Z') (fst A Z') (snd A Z' ≫ k₂)
        simp only [Category.assoc] at e₁ e₂
        rw [e₁, e₂, hkh]
      have := congrArg (fun t => t.left) (hinj Z' _ _ hs)
      simpa [k₁, k₂] using this
    haveI : Flat h.left := hhf
    haveI : Surjective h.left := hhs
    haveI : QuasiCompact h.left := hhq
    let d : T.left ⟶ B.left := EffectiveEpi.desc h.left (x ≫ q).left hc
    have hd : h.left ≫ d = (x ≫ q).left := EffectiveEpi.fac h.left (x ≫ q).left hc
    have hdB : d ≫ B.hom = T.hom := by
      rw [← cancel_epi h.left, ← Category.assoc, hd, Over.w (x ≫ q), Over.w h]
    let xT : T ⟶ B := Over.homMk d hdB
    have hxT : h ≫ xT = x ≫ q := Over.OverMorphism.ext hd
    refine ⟨xT, (same_id_iff hN.isLB hP.isLB xT).1 ?_⟩
    refine GlobalTheory.T.sameLineBundleFamily_descends_flat_surjective_quasiCompact (Sp R) A hA T B T H N P hN hP (𝟙 T) xT h hhf hhs hhq ?_
    rw [same_iff hN.isLB hP.isLB, Category.comp_id, hxT, key]
  refine ⟨B, toUnit B, P, ⟨hP, fun T t N hN ↦ ?_⟩, hgood, hfa⟩
  obtain ⟨x, hx⟩ := hex T N hN
  refine ⟨x, ⟨toUnit_unique _ _, hx⟩, fun y hy ↦ hinj T y x ?_⟩
  have h1 := (cls_eq_iff hN.isLB (pull_isLB hP.isLB _)).2 hy.2
  have h2 := (cls_eq_iff hN.isLB (pull_isLB hP.isLB _)).2 hx
  exact (cls_eq_iff (pull_isLB hP.isLB _) (pull_isLB hP.isLB _)).1 (h1.symm.trans h2)

end GlobalTheory.DualPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomDegreeIntegerCombinationIsHomogeneousStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.homDegree_integerCombination_isHomogeneous : ∀ (K : Type) [Field K] (A B : AbVar K), A.dim = B.dim → ∀ (n : ℕ) (f : Fin n → (A ⟶ B)), ∃ F : MvPolynomial (Fin n) ℚ, F.IsHomogeneous (2 * A.dim) ∧ ∀ m : Fin n → ℤ, MvPolynomial.eval (fun i => (m i : ℚ)) F = (deg (∑ i, m i • f i) : ℚ) := by
  first | (exact @GlobalTheory.AV.AbVar.deg_isHomogeneousPoly) | (exact GlobalTheory.AV.AbVar.deg_isHomogeneousPoly) | (intros; apply GlobalTheory.AV.AbVar.deg_isHomogeneousPoly  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomTorsionFree
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem hom_torsionFree : ∀ (K : Type) [Field K] (A B : AbVar K) (n : ℤ) (f : A ⟶ B), n ≠ 0 → n • f = 0 → f = 0 := by
  intro K _ A B n f hn h
  have hs := (GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree K A n hn).1.2
  refine GlobalTheory.T.cancel_of_surjective_abelianVarietyHom K A A (n • 𝟙 A) hs B f 0 ?_
  rw [Preadditive.zsmul_comp, Category.id_comp, Limits.comp_zero, h]

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightReciprocityTwoSectionsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inductiveMixedHeight_reciprocity_two_sections : ArchRecip → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M N : HermLB q) (L : Fin e → HermLB q) (s : M.B.Sec) (t : N.B.Sec) (hs : genericPoint Y ∈ nonzeroLocus s) (ht : genericPoint Y ∈ nonzeroLocus t), (∀ z : Y, Order.coheight z = 1 → z ∈ nonzeroLocus s ∨ z ∈ nonzeroLocus t) → recVal (T (e + 1) (Fin.cons N L)) (Fin.cons N L : Fin (e + 1) → HermLB q) M (isRatSec_ratOfSec s hs) = recVal (T (e + 1) (Fin.cons M L)) (Fin.cons M L : Fin (e + 1) → HermLB q) N (isRatSec_ratOfSec t ht) := by
  first | exact @GlobalTheory.MixHt.recVal_cons_recip | exact GlobalTheory.MixHt.recVal_cons_recip | (intros; apply GlobalTheory.MixHt.recVal_cons_recip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductiveMixedHeightTensorAdditiveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.MixHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inductiveMixedHeight_tensor_additive : ArchInteg → ∀ (k : Type) [CommRing k] (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (q : Y ⟶ Sp k), IsAmb q → ∀ e : ℕ, topologicalKrullDim Y = (e + 1 + 1 : ℕ) → ∀ T, IsMix q (e + 1) T → ∀ (M : HermLB q) (r : M.B.ι → Y.functionFieldˣ) (hr : IsRatSec M.B r) (A B : HermLB q) (L : Fin e → HermLB q), recVal (T (e + 1) (Fin.cons (A.tens B) L)) (Fin.cons (A.tens B) L : Fin (e + 1) → HermLB q) M hr = recVal (T (e + 1) (Fin.cons A L)) (Fin.cons A L : Fin (e + 1) → HermLB q) M hr + recVal (T (e + 1) (Fin.cons B L)) (Fin.cons B L : Fin (e + 1) → HermLB q) M hr := by
  first | exact @GlobalTheory.MixHt.recVal_tens_cons | exact GlobalTheory.MixHt.recVal_tens_cons | (intros; apply GlobalTheory.MixHt.recVal_tens_cons <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableLogNormSectionArithmeticVarietyStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_logNormSection_arithmeticVariety : GlobalTheory.Published.Principalisation → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (σ : k →+* ℂ) (L : Fin D → MLine p σ) (M : MLine p σ) (s : M.B.Sec), genericPoint X ∈ nonzeroLocus s → Intg L (M.logSec s) := by
  first | exact @GlobalTheory.Mix.intg_logSec_of_arithVar | exact GlobalTheory.Mix.intg_logSec_of_arithVar | (intros; apply GlobalTheory.Mix.intg_logSec_of_arithVar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralChernFormPolynomialEqIntersectionNumberStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_chernForm_polynomial_eq_intersectionNumber : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (κ : Type) [Fintype κ] (Δ : κ → X.Dv) (L : κ → LB X.X) (r : ∀ a, (L a).ι → X.Fnˣ) (ψ : ∀ a, Weight X.str σ (L a)), (∀ a, Presents (Δ a) (L a) (r a) ∧ (ψ a).IsCInf) → ∀ P : MvPolynomial κ ℝ, P.IsHomogeneous X.dim → (atlas X σ).integral (evalF (atlas X σ) (fun a => c1W (ψ a)) P) = X.interPoly Δ P := by
  first | exact @GlobalTheory.ChernCalc.integral_evalF_c1W_eq_interPoly | exact GlobalTheory.ChernCalc.integral_evalF_c1W_eq_interPoly | (intros; apply GlobalTheory.ChernCalc.integral_evalF_c1W_eq_interPoly <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDelDbarZeroStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_del_dbar_zero : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    ∀ η : A.Fld, A.IsForm η → A.integral (A.del η) = 0 ∧ A.integral (A.dbar η) = 0 := by
  first | exact @GlobalTheory.CxFormStokesBoth.stokes | exact GlobalTheory.CxFormStokesBoth.stokes | (intros; apply GlobalTheory.CxFormStokesBoth.stokes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralRealPolyEqOfDbarCohomologous
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

set_option autoImplicit false

namespace GlobalTheory.ChernCalc

theorem integral_evalF_of_dbarCoh : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n) (ι : Type) (w w' : ι → A.Pt → Ev n), (∀ i, DbarCoh A (w i) (w' i)) → ∀ P : MvPolynomial ι ℝ, A.integral (evalF A w P) = A.integral (evalF A w' P) := by
  intro M _ _ _ _ _ _ n A ι w w' hw P
  obtain ⟨hD1, -, hDalg⟩ := dbarCoh_algebra M n A
  obtain ⟨-, hc, -, -, -⟩ := GlobalTheory.formCalculus M n A
  obtain ⟨hfin, hadd, -, -⟩ := GlobalTheory.LineForm.wInt_props M n A
  have key : DbarCoh A (fun x => aeval (fun i => w i x) (P.map (algebraMap ℝ ℂ)))
      (fun x => aeval (fun i => w' i x) (P.map (algebraMap ℝ ℂ))) := by
    induction P using MvPolynomial.induction_on with
    | C a =>
      have h := (hDalg (a : ℂ) 1 1 1 1 hD1 hD1).1
      convert h using 1 <;> funext x <;> simp [Algebra.algebraMap_eq_smul_one]
    | add p q hp hq =>
      have h := (hDalg 1 _ _ _ _ hp hq).2.1
      convert h using 1 <;> funext x <;> simp
    | mul_X p i hp =>
      have h := (hDalg 1 _ _ _ _ hp (hw i)).2.2
      convert h using 1 <;> funext x <;> simp
  obtain ⟨-, hf', -, -, u, hu, eu⟩ := key
  have e1 : evalF A w P = evalF A w' P + A.dbar u := by
    show fld A _ = fld A _ + _
    rw [← eu]
    abel
  have hdu : A.IsForm (A.dbar u) := (hc 1 u u hu hu).2.2.2.2.1
  have int1 : ∀ α : A.Fld, A.IsForm α → ∀ ε : ℤˣ, Integrable (fun _ : M => (1 : ℝ)) (A.part α ε) := fun α h ε => by
    haveI := hfin α h ε
    exact integrable_const 1
  calc A.integral (evalF A w P) = wInt A (fun _ => 1) (evalF A w' P + A.dbar u) := by rw [wInt_one, e1]
    _ = wInt A (fun _ => 1) (evalF A w' P) + wInt A (fun _ => 1) (A.dbar u) :=
      (hadd _ _ _ hf' hdu (int1 _ hf') (int1 _ hdu)).2
    _ = A.integral (evalF A w' P) := by
      rw [wInt_one, wInt_one, (GlobalTheory.CxFormStokesBoth.stokes M n A u hu).2, add_zero]

end GlobalTheory.ChernCalc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralSmul
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineGysin

section Atlas

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem fld_add (u v : A.Pt → Ev n) : fld A (u + v) = fld A u + fld A v := by
  funext x; simp [fld]

theorem evalF_add {ι : Type} (w : ι → A.Pt → Ev n) (P Q : MvPolynomial ι ℝ) :
    evalF A w (P + Q) = evalF A w P + evalF A w Q := by
  funext x; simp [evalF, fld]

theorem evalF_mul {ι : Type} (w : ι → A.Pt → Ev n) (P Q : MvPolynomial ι ℝ) :
    evalF A w (P * Q) = evalF A w P * evalF A w Q := by
  funext x; simp [evalF, fld]

theorem evalF_C {ι : Type} (w : ι → A.Pt → Ev n) (a : ℝ) :
    evalF A w (C a) = ((a : ℂ)) • (1 : A.Fld) := by
  funext x
  simp only [evalF, fld, map_C, aeval_C, Pi.smul_apply, Pi.one_apply]
  first
  | (rw [Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one]; rfl)
  | (rw [Subalgebra.coe_algebraMap, Algebra.algebraMap_eq_smul_one, Complex.coe_algebraMap])
  | (simp [Algebra.algebraMap_eq_smul_one, -Complex.coe_smul])

theorem evalF_X {ι : Type} (w : ι → A.Pt → Ev n) (i : ι) : evalF A w (X i) = fld A (w i) := by
  funext x; simp [evalF, fld]

theorem evalF_one {ι : Type} (w : ι → A.Pt → Ev n) : evalF A w 1 = 1 := by
  funext x; simp [evalF, fld]

theorem evalF_rename {ι κ : Type} (w : κ → A.Pt → Ev n) (e : ι → κ) (P : MvPolynomial ι ℝ) :
    evalF A w (rename e P) = evalF A (fun i => w (e i)) P := by
  funext x; simp [evalF, fld, map_rename, aeval_rename, Function.comp_def]

end Atlas

end GlobalTheory.LineGysin

namespace GlobalTheory.LineGysin

section Int

variable {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M]
  [BorelSpace M] {n : ℕ} (A : HolAtlas M n)

theorem integral_add {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.integral (α + β) = A.integral α + A.integral β := by
  have L := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  rw [← wInt_one, ← wInt_one, ← wInt_one]
  refine (L.2.1 _ α β hα hβ (fun ε => ?_) (fun ε => ?_)).2
  · haveI := L.1 α hα ε; exact integrable_const _
  · haveI := L.1 β hβ ε; exact integrable_const _

theorem integral_smul (t : ℝ) {α : A.Fld} (hα : A.IsForm α) :
    A.integral ((t : ℂ) • α) = t * A.integral α := by
  have L := GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous M n A
  rw [← wInt_one, ← wInt_one]
  exact L.2.2.1 _ t α hα

end Int

end GlobalTheory.LineGysin

namespace GlobalTheory.LineGysin

theorem dvd_swap (t : ℝ) (T : MvPolynomial (Fin 3) ℝ) :
    (X 3 - X 1 * X 2 : MvPolynomial (Fin 4) ℝ) ∣
      rename (![1, 2, 0] : Fin 3 → Fin 4) (C t * X 0 * aeval ![X 0 + X 1, X 0 * X 1, X 2] T) -
        C t * X 1 * aeval ![X 1 + X 2, X 3, X 0] T := by
  set I : Ideal (MvPolynomial (Fin 4) ℝ) := Ideal.span {X 3 - X 1 * X 2}
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq, ← Ideal.Quotient.mkₐ_eq_mk ℝ]
  have h1 : ∀ g : Fin 3 → MvPolynomial (Fin 4) ℝ,
      Ideal.Quotient.mkₐ ℝ I (aeval g T) = aeval (fun j => Ideal.Quotient.mkₐ ℝ I (g j)) T := fun g => by
    rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have h2 : ∀ g : Fin 3 → MvPolynomial (Fin 3) ℝ,
      rename (![1, 2, 0] : Fin 3 → Fin 4) (aeval g T) = aeval (fun j => rename (![1, 2, 0] : Fin 3 → Fin 4) (g j)) T :=
    fun g => by rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  have h3 : Ideal.Quotient.mkₐ ℝ I (X 1 * X 2) = Ideal.Quotient.mkₐ ℝ I (X 3) := by
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq]
    exact Ideal.mem_span_singleton.2 ⟨-1, by ring⟩
  simp only [map_mul, rename_C, rename_X, h2]
  rw [h1, h1]
  congr 1
  refine congrArg (fun f => aeval f T) ?_
  funext j
  fin_cases j
  · simp
  · simpa [Ideal.Quotient.mkₐ_eq_mk] using h3
  · simp

theorem gysin : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ (t : ℝ) (T : MvPolynomial (Fin 3) ℝ),
      (hY.atlas σ).integral (evalF (hY.atlas σ) (fun i => c1F hY σ (![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] i))
          (C t * X 0 * aeval ![X 0 + X 1, X 0 * X 1, X 2] T)) =
        -t * (hB.atlas σ).integral (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3, X 0] T)) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl _ A σ t T
  haveI : CompactSpace (CxPts p σ) := CxPts.compactSpace σ hY.isProjOver
  haveI : T2Space (CxPts p σ) := CxPts.t2Space_cxPts_of_isProjOver σ hY.isProjOver
  haveI : SecondCountableTopology (CxPts p σ) := CxPts.secondCountableTopology_of_isProjOver σ hY.isProjOver
  obtain ⟨bB1, bB2, bB3⟩ := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  obtain ⟨bY1, bY2, -⟩ := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  obtain ⟨hol, hc1, hE⟩ := bB3 Y p (d + 1) hY π w
  obtain ⟨hc2, hsum⟩ := hE E h H flB fl
  have cB := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)
  have cY := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hY.atlas σ)
  have pl := cB.2.2.2.2 _ _ (hY.atlas σ) _ hol
  simp only [pullF] at hc1 hc2
  have gens : ∀ i : Fin 3, evalF (hY.atlas σ) (fam4 hY σ (H.pull π w) fl (A.pull π w)) (![X 1 + X 2, X 3, X 0] i) =
      pullF hB hY σ π w (evalF (hB.atlas σ) (fam4 hB σ H flB A) (![X 1 + X 2, X 3, X 0] i)) := by
    intro i
    simp only [pullF]
    fin_cases i
    · change evalF _ _ (X 1 + X 2) = (hB.atlas σ).pullback _ _ (evalF _ _ (X 1 + X 2))
      rw [evalF_add,
        evalF_add, evalF_X, evalF_X, evalF_X, evalF_X]
      change fld _ (c1F hY σ (VMetric.grLB fl 0 (H.pull π w))) + fld _ (c1F hY σ (VMetric.grLB fl 1 (H.pull π w))) =
        (hB.atlas σ).pullback _ _ (fld _ (c1F hB σ (VMetric.grLB flB 0 H)) + fld _ (c1F hB σ (VMetric.grLB flB 1 H)))
      rw [← fld_add, hsum, fld_add, hc1, hc1, (pl.2 0 _ _).1]
    · change evalF _ _ (X 3) = (hB.atlas σ).pullback _ _ (evalF _ _ (X 3))
      rw [evalF_X, evalF_X]
      exact hc2
    · change evalF _ _ (X 0) = (hB.atlas σ).pullback _ _ (evalF _ _ (X 0))
      rw [evalF_X, evalF_X]
      exact hc1 A
  have hpull : ∀ P : MvPolynomial (Fin 3) ℝ,
      evalF (hY.atlas σ) (fam4 hY σ (H.pull π w) fl (A.pull π w)) (aeval ![X 1 + X 2, X 3, X 0] P) =
        pullF hB hY σ π w (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3, X 0] P)) := by
    intro P
    induction P using MvPolynomial.induction_on with
    | C a =>
      simp only [aeval_C, MvPolynomial.algebraMap_eq, evalF_C, pullF]
      rw [(pl.2 _ 1 1).2.2.1, pl.1]
    | add P Q hP hQ =>
      rw [map_add, evalF_add, evalF_add, hP, hQ]
      simp only [pullF]
      rw [(pl.2 0 _ _).1]
    | mul_X P i hP =>
      rw [map_mul, evalF_mul, evalF_mul, hP, aeval_X, gens i]
      simp only [pullF]
      rw [(pl.2 0 _ _).2.1]
  have e3 : (fun i => c1F hY σ (![VMetric.grLB fl 0 (H.pull π w), VMetric.grLB fl 1 (H.pull π w), A.pull π w] i)) =
      fun i => fam4 hY σ (H.pull π w) fl (A.pull π w) ((![1, 2, 0] : Fin 3 → Fin 4) i) := by
    funext i; fin_cases i <;> rfl
  rw [e3, ← evalF_rename,
    GlobalTheory.T.integral_evalForm_mod_relation_eq k Y p (d + 1) hY _ (h.pull π w) (H.pull π w) fl (A.pull π w) σ _ _ (dvd_swap t T),
    evalF_mul, evalF_mul, evalF_C, evalF_X, hpull]

  have hcB : ∀ i, (hB.atlas σ).IsForm (fld (hB.atlas σ) (fam4 hB σ H flB A i)) := by
    intro i
    fin_cases i
    · exact (bB1 A A).1.1
    · exact (bB1 _ A).1.1
    · exact (bB1 _ A).1.1
    · exact (bB2 E h H flB flB).2.1.1
  have hφ := (cB.2.2.2.1 (Fin 4) _ (aeval ![X 1 + X 2, X 3, X 0] T) hcB).1
  have hpφ : (hY.atlas σ).IsForm (pullF hB hY σ π w (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3, X 0] T))) :=
    ((pl.2 0 _ 0).2.2.2 hφ).1
  have hx0 : (hY.atlas σ).IsForm (fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0))) := (bY1 _ (A.pull π w)).1.1
  have hom : (hY.atlas σ).IsForm (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl)) :=
    (bY2 _ (h.pull π w) (H.pull π w) fl fl).1.1
  have G := GlobalTheory.T.flag_bundle_chern_integral_pull_third k B Y q p d hB hY π w E h H flB fl ‹_› A σ _ hφ
  have G1 := (G 1).1
  have G0 := (G 0).2
  rw [hs, pow_zero, mul_one] at G0
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.choose_zero_right, mul_one, Nat.cast_one, map_one,
    Nat.sub_zero, Nat.mul_zero, Nat.zero_sub, Nat.choose_self, one_mul, evalF_one, CharP.cast_eq_zero, zero_add,
    div_one, MvPolynomial.C_1] at G0
  rw [pow_one] at G1
  set x0 := fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0))
  set om := fld (hY.atlas σ) (omF hY σ (h.pull π w) fl)
  set pφ := pullF hB hY σ π w (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3, X 0] T))
  have key : (t : ℂ) • (1 : (hY.atlas σ).Fld) * fld (hY.atlas σ) (fam4 hY σ (H.pull π w) fl (A.pull π w) 1) * pφ =
      (t : ℂ) • ((x0 + om) * pφ + ((-1 : ℝ) : ℂ) • (om * pφ)) := by
    rw [smul_mul_assoc, one_mul, smul_mul_assoc]
    congr 1
    rw [add_mul]
    simp only [Complex.ofReal_neg, Complex.ofReal_one, neg_smul, one_smul, add_neg_cancel_right]
    rfl
  have f1 : (hY.atlas σ).IsForm ((x0 + om) * pφ) := (cY.2.1 0 _ _ (cY.2.1 0 _ _ hx0 hom).1 hpφ).2.1
  have f2 : (hY.atlas σ).IsForm (om * pφ) := (cY.2.1 0 _ _ hom hpφ).2.1
  have f3 : (hY.atlas σ).IsForm (((-1 : ℝ) : ℂ) • (om * pφ)) := (cY.2.1 _ _ _ f2 f2).2.2.1
  have f4 : (hY.atlas σ).IsForm ((x0 + om) * pφ + ((-1 : ℝ) : ℂ) • (om * pφ)) := (cY.2.1 0 _ _ f1 f3).1
  rw [key, integral_smul _ _ f4, integral_add _ f1 f3, integral_smul _ _ f2, G1, G0]
  ring

end GlobalTheory.LineGysin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAmpleTensorOfNefFibresAmpleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAmple_tensor_of_nef_fibres_ample : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ L A : HermLB p, NefFib L → IsAmpleLB A.B → IsAmpleLB (L.tens A).B := by
  first | exact @GlobalTheory.AmpleNefFibZ.isAmpleLB_tens_of_nefFib | exact GlobalTheory.AmpleNefFibZ.isAmpleLB_tens_of_nefFib | (intros; apply GlobalTheory.AmpleNefFibZ.isAmpleLB_tens_of_nefFib <;> assumption)
end

