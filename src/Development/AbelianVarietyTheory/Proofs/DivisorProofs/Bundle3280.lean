import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullThird
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2919
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1623
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3246
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0025
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3263
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2183
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsTauZeroNonzeroAll
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2114
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3264
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDualStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), Module.Finite K G.omega ∧ Module.Finite K G.RigExt ∧ Module.finrank K G.RigExt = G.height ∧ Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height := by
  first | exact @GlobalTheory.PDivGroup.finrank_rigExt_omega | exact GlobalTheory.PDivGroup.finrank_rigExt_omega | (intros; apply GlobalTheory.PDivGroup.finrank_rigExt_omega <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleChernIntegralPullThirdStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_chern_integral_pull_third : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ m : ℕ,
      (hY.atlas σ).integral ((fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0)) + fld (hY.atlas σ) (omF hY σ (h.pull π w) fl)) ^ m * pullF hB hY σ π w φ) = 0 ∧
      (hY.atlas σ).integral (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) * (fld (hY.atlas σ) (c1F hY σ (fam5 π w H flB fl A 0)) + fld (hY.atlas σ) (omF hY σ (h.pull π w) fl)) ^ m * pullF hB hY σ π w φ) =
        1 / (m + 1 : ℝ) * (hB.atlas σ).integral (evalF (hB.atlas σ) (fam4 hB σ H flB A) (aeval ![X 1 + X 2, X 3] (hs m)) * φ) := by
  first | exact @GlobalTheory.FibGlob.integral_fibre | exact GlobalTheory.FibGlob.integral_fibre | (intros; apply GlobalTheory.FibGlob.integral_fibre <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineCurvature
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineForm

theorem mul_sub_mul_of_add_eq {R : Type} [CommRing R] {a b c e : R} (h : a + b = c + e) :
    c * e - a * b = (e - a) * (c - a) := by
  linear_combination (-a) * h

section Calc

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem ddc_sub_of_isForm (α β : A.Fld) (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.IsForm (α - β) ∧ A.ddc (α - β) = A.ddc α - A.ddc β := by
  have C := (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1
  have e : α - β = α + (-1 : ℂ) • β := by rw [neg_one_smul, sub_eq_add_neg]
  have hβ' : A.IsForm ((-1 : ℂ) • β) := (C (-1) β β hβ hβ).2.2.1
  have hdα : A.IsForm (A.dbar α) := (C 0 α α hα hα).2.2.2.2.1
  have hdβ : A.IsForm (A.dbar β) := (C 0 β β hβ hβ).2.2.2.2.1
  have hdβ' : A.IsForm ((-1 : ℂ) • A.dbar β) := (C (-1) _ _ hdβ hdβ).2.2.1
  refine ⟨e ▸ (C 0 α _ hα hβ').1, ?_⟩
  rw [e, HolAtlas.ddc, HolAtlas.ddc, HolAtlas.ddc, (C 0 α _ hα hβ').2.2.2.2.2.2.1, (C (-1) β β hβ hβ).2.2.2.2.2.2.2.2,
    (C 0 _ _ hdα hdβ').2.2.2.2.2.1, (C (-1) _ _ hdβ hdβ).2.2.2.2.2.2.2.1, smul_add, smul_comm GlobalTheory.HermFrame.kappa (-1 : ℂ),
    neg_one_smul, sub_eq_add_neg]

theorem ddc_pullback {M' : Type} [TopologicalSpace M'] {n' : ℕ} (A' : HolAtlas M' n') (f : M' → M) (hf : A.IsHolo A' f)
    (α : A.Fld) (hα : A.IsForm α) : A'.ddc (A.pullback A' f α) = A.pullback A' f (A.ddc α) := by
  have C := (GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.1
  have P := ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.2 M' n' A' f hf).2
  have hdα : A.IsForm (A.dbar α) := (C 0 α α hα hα).2.2.2.2.1
  rw [HolAtlas.ddc, HolAtlas.ddc, ((P 0 α α).2.2.2 hα).2.2, ((P 0 (A.dbar α) (A.dbar α)).2.2.2 hdα).2.1,
    (P GlobalTheory.HermFrame.kappa (A.del (A.dbar α)) (A.del (A.dbar α))).2.2.1]

theorem fld_sub (f g : A.Pt → Ev n) : fld A (f - g) = fld A f - fld A g := by
  funext x; simp [fld]

theorem fld_mul (f g : A.Pt → Ev n) : fld A (f * g) = fld A f * fld A g := by
  funext x; simp [fld]

theorem pullback_sub {M' : Type} [TopologicalSpace M'] {n' : ℕ} (A' : HolAtlas M' n') (f : M' → M) (hf : A.IsHolo A' f)
    (α β : A.Fld) : A.pullback A' f (α - β) = A.pullback A' f α - A.pullback A' f β := by
  have P := ((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.2 M' n' A' f hf).2
  rw [show α - β = α + (-1 : ℂ) • β by rw [neg_one_smul, sub_eq_add_neg], (P 0 α ((-1 : ℂ) • β)).1, (P (-1) β β).2.2.1,
    neg_one_smul, sub_eq_add_neg]

theorem pullback_mul {M' : Type} [TopologicalSpace M'] {n' : ℕ} (A' : HolAtlas M' n') (f : M' → M) (hf : A.IsHolo A' f)
    (α β : A.Fld) : A.pullback A' f (α * β) = A.pullback A' f α * A.pullback A' f β :=
  (((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas M n A).2.2.2.2 M' n' A' f hf).2 0 α β).2.1

end Calc

theorem ddc_omF_sub_pull : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    (hY.atlas σ).IsForm (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) ∧ (hY.atlas σ).ddc (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) = evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) ((X 4 - X 0) * (X 3 - X 0)) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl _ A σ
  have TY := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  have TB := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  obtain ⟨hHolo, hc1, hE⟩ := TB.2.2 Y p (d + 1) hY π w
  obtain ⟨hc2, hsum⟩ := hE E h H flB fl
  have cY := TY.2.1 _ (h.pull π w) (H.pull π w) fl fl
  have cB := TB.2.1 E h H flB flB
  have hpf : ∀ α, pullF hB hY σ π w α =
      (hB.atlas σ).pullback (hY.atlas σ) (GlobalTheory.Points.PtsOver.map π w _) α := fun _ => rfl
  have hωB : (hB.atlas σ).IsForm (fld (hB.atlas σ) (omF hB σ h flB)) := cB.1.1
  have hpω : (hY.atlas σ).IsForm (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) := by
    rw [hpf]
    exact ((((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _ hHolo).2 0 (fld (hB.atlas σ) (omF hB σ h flB))
      (fld (hB.atlas σ) (omF hB σ h flB))).2.2.2 hωB).1
  obtain ⟨hF, hD⟩ := ddc_sub_of_isForm (hY.atlas σ) _ _ cY.1.1 hpω
  refine ⟨hF, ?_⟩
  rw [hD, hpf, ddc_pullback _ _ _ hHolo _ hωB, cY.2.2.2.2.2.2.2, cB.2.2.2.2.2.2.2, fld_sub (hB.atlas σ), fld_mul (hB.atlas σ),
    pullback_sub _ _ _ hHolo, pullback_mul _ _ _ hHolo, ← hpf, ← hpf, ← hpf, ← hc2, ← hc1, ← hc1]
  simp only [← fld_mul, ← fld_sub, evalF]
  congr 1
  funext x
  have hx := congrFun hsum x
  simp only [Pi.add_apply] at hx
  simp [fam5]
  exact mul_sub_mul_of_add_eq (R := Ev (d + 1)) hx

end GlobalTheory.LineForm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineIntegralFormula
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open GlobalTheory.Points
open scoped Classical ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibCos

theorem map_eq_of_local {Z T : Type} [TopologicalSpace T] [CompactSpace T] [MeasurableSpace T] [OpensMeasurableSpace T]
    [MeasurableSpace Z] (μ : Measure Z) (ν : Measure T) (f : Z → T) (hf : Measurable f) (v : Z → ℝ) (hv : Measurable v)
    (hloc : ∀ b₀ : T, ∃ U : Set T, IsOpen U ∧ b₀ ∈ U ∧ ∀ S : Set T, MeasurableSet S → S ⊆ U → ∀ J : Set ℝ,
      MeasurableSet J → μ (f ⁻¹' S ∩ v ⁻¹' J) = ν S * volume (J ∩ Set.Icc (0 : ℝ) 1)) :
    Measure.map v μ = ν Set.univ • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  choose U hUo hU hUS using hloc
  obtain ⟨t, -, ht⟩ := isCompact_univ.elim_nhds_subcover U fun b _ => (hUo b).mem_nhds (hU b)
  ext J hJ
  have key : Measure.map f (μ.restrict (v ⁻¹' J)) = volume (J ∩ Set.Icc (0 : ℝ) 1) • ν := by
    refine Measure.ext_of_biUnion_eq_univ (S := (t : Set T)) t.countable_toSet
      (Set.eq_univ_of_univ_subset (by simpa using ht)) fun b _ => ?_
    ext A hA
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA, Measure.map_apply hf (hA.inter (hUo b).measurableSet),
      Measure.restrict_apply (hf (hA.inter (hUo b).measurableSet)),
      hUS b _ (hA.inter (hUo b).measurableSet) Set.inter_subset_right J hJ, Measure.smul_apply, smul_eq_mul, mul_comm]
  have e := congrArg (fun m : Measure T => m Set.univ) key
  simp only [Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ,
    Set.univ_inter, Measure.smul_apply, smul_eq_mul] at e
  rw [Measure.map_apply hv hJ, e, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply hJ, mul_comm]

end GlobalTheory.FibCos

theorem GlobalTheory.FibCos.map_part : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ φ : (hB.atlas σ).Fld, (hB.atlas σ).IsForm φ → ∀ ε : ℤˣ,
      Measure.map v ((hY.atlas σ).part (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 0 - X 3) * pullF hB hY σ π w φ) ε) =
        (hB.atlas σ).part φ (-ε) Set.univ • volume.restrict (Set.Icc (0 : ℝ) 1) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv φ hφ ε
  haveI : CompactSpace (CxPts q σ) := hB.compactSpace σ
  refine GlobalTheory.FibCos.map_eq_of_local _ _ _ (PtsOver.continuous_map π w (spMap σ)).measurable v
    (GlobalTheory.CosSqMeas.measurable_cosSq k B Y q p d hB hY π w E h H flB fl hfl A σ v hv) fun b₀ => ?_
  obtain ⟨U, hUo, hb, G, hG, hS⟩ := GlobalTheory.T.flag_bundle_line_bundle_chern_relation k B Y q p d hB hY π w E h H flB fl hfl A σ v hv φ hφ ε b₀
  refine ⟨U, hUo, hb, fun S hSm hSU J hJ => ?_⟩
  rw [hS S hSm hSU J hJ, setLIntegral_congr_fun hSm (fun b hb => GlobalTheory.T.fibre_cosine_pushforward_uniform (G b) (hG b (hSU hb)) J hJ),
    setLIntegral_const, mul_comm]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleHermitianLineLimit
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.CovTest.SwapLine GlobalTheory.LineForm
open scoped Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LineMeet

open Filter Topology Matrix
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.HermFrame GlobalTheory.Points
open scoped ContDiff ComplexOrder

theorem pull_ofValues {n m : ℕ} (L : V n →L[ℂ] V m) {α : V m → V m → ℂ} (hα : IsSesq α) :
    pull L (ofValues α : Alt m) = ofValues (fun ξ η => α (L ξ) (L η)) := by
  simp only [ofValues, GlobalTheory.LineForm.OmReal.sesq_expand hα (L _), AddSubmonoidClass.coe_finset_sum, Subalgebra.coe_smul,
    sym, map_sum, map_smul, map_mul, (pull_dz L _).1, (pull_dz L _).2, Finset.sum_mul, Finset.mul_sum, Finset.sum_smul,
    Finset.smul_sum, smul_mul_smul_comm, smul_smul]
  conv_lhs => enter [2, a, 2, b]; rw [Finset.sum_comm]
  conv_lhs => enter [2, a]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, c, 2, a]; rw [Finset.sum_comm]
  conv_lhs => enter [2, c]; rw [Finset.sum_comm]

theorem form_submatrix {r r' : Type} [Fintype r] [Fintype r'] (e : r' ≃ r) (M : Matrix r r ℂ) (u u' : r → ℂ) :
    form (M.submatrix e e) (u ∘ e) (u' ∘ e) = form M u u' := by
  simp only [form_eq_sum, submatrix_apply, Function.comp_apply]
  rw [← e.sum_comp]
  exact Finset.sum_congr rfl fun a _ => by rw [← e.sum_comp]

theorem ddc_fn_apply {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {f : M → ℝ}
    (hf : A.SmoothOn Set.univ fun y => (f y : ℂ)) (x : A.Pt) :
    A.ddc (A.fn f) x = ofValues (ddc (fun v => f (x.ch.symm v)) x.crd) := by
  have hn : x.ch.target ∈ 𝓝 x.crd := x.ch.open_target.mem_nhds (x.ch.map_source x.2)
  have h1 := Complex.reCLM.contDiff.comp_contDiffOn (hf x.1.1)
  have h2 : ContDiffOn ℝ ∞ (fun v => f (x.ch.symm v)) x.ch.target :=
    (h1.mono fun v hv => ⟨hv, trivial⟩).congr fun v _ => by simp
  rw [← delAt_dbarAt_fun ((h2.contDiffAt hn).of_le (by norm_cast))]
  refine GlobalTheory.SecForm.DdcGerm.ddc_eq_of_eventuallyEq A _ x _ ?_
  filter_upwards [hn] with v hv
  rw [HolAtlas.loc, dif_pos hv]
  rfl

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} {D D' : ℕ}

theorem gram_and_cos {π : Y ⟶ B} {w : π ≫ q = p} {E : B.Modules} (h : VMetric q E 2) {flB : Vert.Flag E 2}
    {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2} {σ : k →+* ℂ} {v : CxPts p σ → ℝ}
    (hv : GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v)
    (a : VBExt.AdaptedChart (lineSC fl) 1 1) (b : VBExt.AdaptedChart (lineSC flB) 1 1) {y : CxPts p σ}
    (ha : y ∈ ptsIn p σ a.U) (hb : PtsOver.map π w _ y ∈ ptsIn q σ b.U)
    {A K : Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ}
    (hA : A = ((((b.mid (lineSC_shortExact flB)).pull (h.met σ).isVB π).tr p σ (a.mid (lineSC_shortExact fl)) y).submatrix
      finSumFinEquiv finSumFinEquiv))
    (hK : K = (h.met σ).gram b.frame (PtsOver.map π w _ y)) :
    ((h.pull π w).met σ).gram a.frame y = chg A K ∧
      ‖form K (Pi.single (Sum.inl 0) 1) (fun i => A i (Sum.inl 0))‖ ^ 2 =
        v y * (chg A K (Sum.inl 0) (Sum.inl 0)).re * (K (Sum.inl 0) (Sum.inl 0)).re := by
  have hS := lineSC_shortExact flB
  have hS' := lineSC_shortExact fl
  set m := (h.pull π w).met σ with hm
  let c : Chart E 2 := b.mid hS
  let c' : Chart ((Scheme.Modules.pullback π).obj E) 2 := c.pull (h.met σ).isVB π
  have hc' : y ∈ ptsIn p σ c'.U := hb
  have hG : m.G c' y = (h.met σ).G c (PtsOver.map π w _ y) := (h.met σ).pull_G π w c hb
  have hK' : K = (m.G c' y).submatrix (finSumFinEquiv (m := 1) (n := 1)) (finSumFinEquiv (m := 1) (n := 1)) := by
    rw [hG, hK]
    exact Met.gram_frame (S := lineSC flB) (r := 1) (s := 1) (h.met σ) hS b hb
  have e₁ : m.gram a.frame y = chg A K := by
    rw [hK', hA, chg_submatrix]
    refine (Met.gram_frame (S := lineSC fl) (r := 1) (s := 1) m hS' a ha).trans ?_
    exact congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M.submatrix (finSumFinEquiv (m := 1) (n := 1))
      (finSumFinEquiv (m := 1) (n := 1))) (m.trans c' (a.mid hS') y hc')
  refine ⟨e₁, ?_⟩
  have hy : y ∈ ptsIn p σ (a.U ⊓ π ⁻¹ᵁ b.U) := mem_ptsIn_inf.2 ⟨ha, hb⟩
  have key := hv (a.U ⊓ π ⁻¹ᵁ b.U) (Twist.resM _ inf_le_left (a.e 0))
    (QCoh.pullbackSections π _ inf_le_right (b.e 0)) y hy
  rw [QCoh.pullback_map_app_pullbackSections, Twist.app_resM, m.form_resM _ _ _ hy] at key
  have e₂ : m.form (QCoh.pullbackSections π E (inf_le_right : a.U ⊓ π ⁻¹ᵁ b.U ≤ _) ((flB.ι 1).app b.U (b.e 0)))
      (QCoh.pullbackSections π E (inf_le_right : a.U ⊓ π ⁻¹ᵁ b.U ≤ _) ((flB.ι 1).app b.U (b.e 0))) y =
      K (Sum.inl 0) (Sum.inl 0) := by
    rw [hK]
    exact (h.met σ).form_pull π w _ _ _ hy
  have e₃ : m.form ((fl.ι 1).app a.U (a.e 0)) ((fl.ι 1).app a.U (a.e 0)) y = chg A K (Sum.inl 0) (Sum.inl 0) := by
    rw [← e₁]; rfl
  have e₄ : m.form (QCoh.pullbackSections π E (inf_le_right : a.U ⊓ π ⁻¹ᵁ b.U ≤ _) ((flB.ι 1).app b.U (b.e 0)))
      (Twist.resM _ (inf_le_left : a.U ⊓ π ⁻¹ᵁ b.U ≤ _) ((fl.ι 1).app a.U (a.e 0))) y =
      form K (Pi.single (Sum.inl 0) 1) (fun i => A i (Sum.inl 0)) := by
    rw [m.form_eq c' hc' _ _ hy, Chart.crd_pull c _ π w _ _ hy hb, Chart.crd_resM _ _ _ hy, hK',
      ← form_submatrix (finSumFinEquiv (m := 1) (n := 1))]
    congr 1
    · funext i
      refine (b.crd_frame hS hb i (.inl 0)).trans ?_
      simp [Pi.single_apply, one_apply]
    · funext i
      rw [hA]
      simp [Chart.tr, VBExt.AdaptedChart.mid, VBExt.AdaptedChart.frame, c', c, -finSumFinEquiv_apply_left]
  rw [e₂, e₃, e₄] at key
  exact key

theorem ddc_mul_omF_sub (hB : IsRegVar q D) (hY : IsRegVar p D') {π : Y ⟶ B} {w : π ≫ q = p} {E : B.Modules}
    {h : VMetric q E 2} (H : h.IsCInf) {flB : Vert.Flag E 2}
    {fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2} {σ : k →+* ℂ} {v : CxPts p σ → ℝ}
    (hv : GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v)
    (hs : (hY.atlas σ).SmoothOn Set.univ fun y => ((1 - v y : ℝ) : ℂ)) (x : (hY.atlas σ).Pt) (hx1 : v x.pt = 1) :
    (hY.atlas σ).ddc ((hY.atlas σ).fn fun y => 1 - v y) x *
      ((omF hY σ (h.pull π w) fl x : Alt D') - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)) x) = 0 := by
  have hS := lineSC_shortExact flB
  have hS' := lineSC_shortExact fl
  set f : CxPts p σ → CxPts q σ := PtsOver.map π w _ with hf
  have hm : ∀ z, (f z).1 = z.1 ≫ π := fun _ => rfl
  let x' : (hB.atlas σ).Pt := ⟨(_, f x.pt), ((hB.atlas σ).cover (f x.pt)).choose_spec⟩
  let a := frameAt fl x.pt
  let b := frameAt flB (f x.pt)
  have ha : x.pt ∈ ptsIn p σ a.U := mem_frameAt fl x.pt
  have hb : f x.pt ∈ ptsIn q σ b.U := mem_frameAt flB (f x.pt)
  let c' : Chart ((Scheme.Modules.pullback π).obj E) 2 := (b.mid hS).pull (h.met σ).isVB π
  have hc' : x.pt ∈ ptsIn p σ c'.U := hb
  let φ := x'.ch ∘ f ∘ x.ch.symm
  let G : V D → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := fun u => (h.met σ).gram b.frame (x'.ch.symm u)
  let A : V D' → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ := fun u =>
    (c'.tr p σ (a.mid hS') (x.ch.symm u)).submatrix (finSumFinEquiv (m := 1) (n := 1)) (finSumFinEquiv (m := 1) (n := 1))
  have e : x.ch.symm x.crd = x.pt := x.ch.left_inv x.2
  have ho := ChartGlue.isOpen_over x.ch (x'.ch.open_source.preimage (continuous_of_comp hm))
  have hx := ho.mem_nhds (ChartGlue.mem_over x.ch x.2 (show x.pt ∈ f ⁻¹' x'.ch.source from x'.2))
  have hφ : AnalyticAt ℂ φ x.crd :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (AlgChart.holo_map hm x.1.1 x'.1.1) hx
  have hφx : φ x.crd = x'.crd := congrArg (fun z => x'.ch (f z)) e
  have hG : MContDiffAt ∞ G (φ x.crd) := by
    rw [hφx]; exact ((H σ).gram b.frame hb).mContDiffAt x'.1.1 x'.2
  have hGp : ∀ᶠ u in 𝓝 (φ x.crd), (G u).PosDef := by
    rw [hφx]; exact Met.eventually_posDef (S := lineSC flB) (r := 1) (s := 1) (h.met σ) hS b x'.1.1 x'.2 hb
  have hG1 : MContDiffAt 1 G (φ x.crd) := hG.of_le (by norm_cast)
  have e₁ : pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)) x = ofValues (extTrace (fun u => G (φ u)) x.crd) := by
    change pull (fderiv ℂ φ x.crd) (ofValues (extTrace G x'.crd) : Alt D) = _
    rw [← hφx, pull_ofValues _ (OmReal.isSesq_extTrace hG1 hGp)]
    refine congrArg (fun α : V D' → V D' → ℂ => (ofValues α : Alt D')) (funext fun ξ => funext fun η => ?_)
    rw [extTrace_comp_holo hG1 hGp hφ.contDiffAt]
  have hloc : ∀ᶠ u in 𝓝 x.crd, ((h.pull π w).met σ).gram a.frame (x.ch.symm u) = chg (A u) (G (φ u)) ∧
      ‖form (G (φ u)) (Pi.single (Sum.inl 0) 1) (fun i => A u i (Sum.inl 0))‖ ^ 2 =
        v (x.ch.symm u) * (chg (A u) (G (φ u)) (Sum.inl 0) (Sum.inl 0)).re * (G (φ u) (Sum.inl 0) (Sum.inl 0)).re := by
    filter_upwards [hx, (ChartGlue.isOpen_over x.ch (isOpen_ptsIn a.U)).mem_nhds (ChartGlue.mem_over x.ch x.2 ha),
      (ChartGlue.isOpen_over x.ch (isOpen_ptsIn c'.U)).mem_nhds (ChartGlue.mem_over x.ch x.2 hc')] with u h₁ h₂ h₃
    exact gram_and_cos h hv a b h₂.2 h₃.2 rfl (congrArg ((h.met σ).gram b.frame) (x'.ch.left_inv h₁.2))
  have e₂ : (omF hY σ (h.pull π w) fl x : Alt D') = ofValues (extTrace (fun u => chg (A u) (G (φ u))) x.crd) := by
    rw [← extTrace_congr (hloc.mono fun u hu => hu.1)]
    rfl
  rw [e₁, e₂, ddc_fn_apply _ hs]
  refine GlobalTheory.T.hermitian_frame_form_norm_sq_eq D' (fun u => G (φ u)) A (fun u => v (x.ch.symm u)) x.crd
    (fun i j => ((hG i j).of_le (by norm_cast)).comp x.crd (hφ.contDiffAt.restrict_scalars ℝ))
    (hφ.continuousAt.eventually hGp) (fun i j => ?_) ?_ (by rw [e, hx1]) (hloc.mono fun u hu => hu.2)
  · exact GlobalTheory.SCV.analyticAt_of_differentiableOn (AlgChart.holo x.1.1 _ _)
      ((ChartGlue.isOpen_over x.ch (isOpen_ptsIn _)).mem_nhds
        (ChartGlue.mem_over x.ch x.2 (mem_ptsIn_inf.2 ⟨ha, hc'⟩)))
  · simp only [A, det_submatrix_equiv_self, e]
    exact (isUnit_iff_isUnit_det _).1 (c'.isUnit_tr (a.mid hS') hc' ha)

theorem tendsto_integral_conc : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) [IsIntegral B] [IsIntegral Y] (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (d : ℕ)
    (hB : IsRegVar q d) (hY : IsRegVar p (d + 1)) (π : Y ⟶ B) (w : π ≫ q = p) (E : B.Modules) (h : VMetric q E 2) (H : h.IsCInf)
    (flB : Vert.Flag E 2) (fl : Vert.Flag ((Scheme.Modules.pullback π).obj E) 2),
    IsFlagBundle π (fun _ : Unit => E) (fun _ => 2) (fun _ => fl) → ∀ (A : HermLB q) (σ : k →+* ℂ),
    ∀ v : CxPts p σ → ℝ, GlobalTheory.CurveDens.IsCosSq ((h.pull π w).met σ) (fl.ι 1) ((Scheme.Modules.pullback π).map (flB.ι 1)) v →
    ∀ K : MvPolynomial (Fin 5) ℝ, Filter.Tendsto (fun t : ℝ => (hY.atlas σ).integral ((hY.atlas σ).fn (fun y => t / (1 - v y + t) ^ 2) *
      ((hY.atlas σ).ddc ((hY.atlas σ).fn (fun y => 1 - v y)) + ((hY.atlas σ).fn (fun y => 1 - v y)) * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (X 4 - X 0)) * (evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) (K) * (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) - pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB)))))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  intro k _ B Y _ _ q p d hB hY π w E h H flB fl hfl A σ v hv K
  obtain ⟨-, -, hsm⟩ := GlobalTheory.CosSqSmooth.cosSq_smooth k B Y q p d hB hY π w E h H flB fl hfl A σ v hv
  have hs : (hY.atlas σ).SmoothOn Set.univ fun y => ((1 - v y : ℝ) : ℂ) := fun i =>
    ((contDiffOn_const (c := (1 : ℂ))).sub (hsm i)).congr fun u _ => by simp
  obtain ⟨-, halg, -, hev, -⟩ := GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hY.atlas σ)
  obtain ⟨hc1, hom, -⟩ := GlobalTheory.T.firstChern_form_properties k Y p (d + 1) hY σ
  obtain ⟨-, homB, hpl⟩ := GlobalTheory.T.firstChern_form_properties k B q d hB σ
  have hf := (hY.atlas σ).isForm_fn hs
  have hP (P : MvPolynomial (Fin 5) ℝ) := (hev _ (fun i => c1F hY σ (fam5 π w H flB fl A i)) P
    fun i => (hc1 _ (fam5 π w H flB fl A i)).1.1).1
  have hdb := (halg 0 _ _ hf hf).2.2.2.2.1
  have hdd := (halg 0 _ _ hdb hdb).2.2.2.1
  have hddc : (hY.atlas σ).IsForm ((hY.atlas σ).ddc ((hY.atlas σ).fn fun y => 1 - v y)) :=
    (halg kappa _ _ hdd hdd).2.2.1
  have h₁ := (hom _ (h.pull π w) (H.pull π w) fl fl).1.1
  have h₂ : (hY.atlas σ).IsForm (pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) :=
    ((((GlobalTheory.T.smoothForms_calculus_holomorphicAtlas _ _ (hB.atlas σ)).2.2.2.2 _ _ (hY.atlas σ) _ (hpl Y p _ hY π w).1).2 0 _ 0).2.2.2
      (homB E h H flB flB).1.1).1
  have h₃ : (hY.atlas σ).IsForm (fld (hY.atlas σ) (omF hY σ (h.pull π w) fl) -
      pullF hB hY σ π w (fld (hB.atlas σ) (omF hB σ h flB))) := by
    rw [sub_eq_add_neg, ← neg_one_smul ℂ (pullF hB hY σ π w _)]
    exact (halg 0 _ _ h₁ (halg (-1) _ _ h₂ h₂).2.2.1).1
  simp only [mul_assoc ((hY.atlas σ).fn fun y => _ / (1 - v y + _) ^ 2)]
  refine GlobalTheory.T.flag_bundle_chern_integral_rank_two k B Y q p d hB hY π w E h H flB fl hfl A σ v hv _
    (halg 0 _ _ (halg 0 _ _ hddc (halg 0 _ _ hf (hP _)).2.1).1 (halg 0 _ _ (hP K) h₃).2.1).2.1 fun x hx => ?_
  have key := ddc_mul_omF_sub hB hY H hv hs x hx
  have hz : (hY.atlas σ).fn (fun y => 1 - v y) x = 0 := by simp [HolAtlas.fn, hx]
  have hc : ∀ β : Alt (d + 1), β * evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) K x =
      evalF (hY.atlas σ) (fun i => c1F hY σ (fam5 π w H flB fl A i)) K x * β := fun β =>
    Subalgebra.mem_center_iff.1 (Subtype.property _) β
  simp only [Pi.mul_apply, Pi.add_apply, Pi.sub_apply, hz, zero_mul, add_zero]
  rw [← mul_assoc, hc, mul_assoc]
  erw [key]
  simp [dens]

end GlobalTheory.LineMeet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundleSmoothRelativeDimensionStatement
section
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagAr GlobalTheory.ShFam.Pad GlobalTheory.VB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_bundle_smooth_relative_dimension : ∀ (B Y : Scheme.{0}) (π : Y ⟶ B) (ι : Type) [Fintype ι] (E : ι → B.Modules) (r : ι → ℕ) (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (r a)), (∀ a, GlobalTheory.VB.IsVB (E a) (r a)) → IsFlagBundle π E r fl → SmoothOfRelativeDimension (∑ a, r a * (r a - 1) / 2) π := by
  first | exact @GlobalTheory.FlagSmooth.smooth_of_isFlagBundle | exact GlobalTheory.FlagSmooth.smooth_of_isFlagBundle | (intros; apply GlobalTheory.FlagSmooth.smooth_of_isFlagBundle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatExistsAtLastIndexStatement
section
set_option synthInstance.maxHeartbeats 400000
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_exists_at_last_index : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (PP A M : ℝ), RowsT p → (i : ℕ) + 1 = D.R.m → GramAt p i → WtNum p i PP → HostNum D L PP A M → FnAlgClosed (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c → FlatExistsAt (p.T.U ((i : ℕ) + 1)) (xiR D) (-flatDegVal (dat p i) (ofRecord D L p.Del p.h0).logOm) := by
  first | exact @GlobalTheory.DefFlat.flatExistsAt_core | exact GlobalTheory.DefFlat.flatExistsAt_core | (intros; apply GlobalTheory.DefFlat.flatExistsAt_core <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatVectorEqUnitSmulCentralTranslatePlacePartStatement
section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.ExportSeries
open Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.ConjTwist (BaseOf UnitOff)
open GlobalTheory.FlatVecSum (princ)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical
open GlobalTheory.BigOn.Exp.TupLe.Swap

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flatVector_eq_unit_smul_centralTranslate_placePart : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m) (t : T0), VStd D i → ∀ (Sa : Finset (Pl D.host.E)), Sa ⊆ R.Q t → ∀ (eg ea : AE D) (fg : WO (Vc D i) (Wc D i) → ℂ), IsIdemSum eg R.Pg → IsIdemSum ea Sa → GlobalTheory.BaseCmp.IsTypeVec R i eg fg → ∃ (z : GA D (Vc D i)) (c : ℂ), SuppAt ea (Vc D i) z ∧ SuppAt (idem (R.Q t)) (Vc D i) z ∧ UnitOff (GlobalTheory.TwistField.tupPrime R t) c ∧ ∀ h g, ThAt R i ea fg (GlobalTheory.BaseCmp.flatDat R i Sa (R.xiR t) ea) h → ThAt R i (cA D ea) fg (adjDat R i Sa (R.xiR t) (cA D ea)) g → h = c • R.ωP i t (z⁻¹, 1) g := by
  first | exact @GlobalTheory.PartFlat.flat_eq_unit_smul_om_part | exact GlobalTheory.PartFlat.flat_eq_unit_smul_om_part | (intros; apply GlobalTheory.PartFlat.flat_eq_unit_smul_om_part <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrameExponentialVolumeLargeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.CovHt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.frame_exponential_volume_large : Hypotheses2 → HypothesesH → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ u1, Quo p i PP u1 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (σ : Y.d.c₂.F →+* ℂ), GoodEmb Y.d.c₂ σ → ∀ y : FPt (Y.U σ).X, (⟨y.1, y.2.1⟩ : Σ k, Frame ((Y.U σ).X k).Ψ (Fm.D x ι).R.r) ∈ framesOn (Y.U σ) Z → (Y.d.l₂.M : ℝ) * ((Y.U σ).X y.1).firstMinimumSq y.2.1 < (Fm.L x ι).sc.b → ENNReal.ofReal (Real.exp (-(2 * (ReciprocityTheory.ChartRestriction.G.I2.PT.f (Fm.D x ι).host.E : ℝ) / (ReciprocityTheory.ChartRestriction.G.I2.PT.rd (Fm.D x ι).host.E ^ 2 * ((Y.U σ).X y.1).la1 y.2.1 ^ 2) / 625))) ≤ bergOn (Y.U σ) ((Fm.D x ι).sp.W ((i : ℕ) + 1)) (Y.dict σ) Z (wtOf (dat p i) u1 0) y := by
  first | exact @GlobalTheory.ThinBerg.thin_bergOn | exact GlobalTheory.ThinBerg.thin_bergOn | (intros; apply GlobalTheory.ThinBerg.thin_bergOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosDefL2LeSupOfLinIndepStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gram_posDef_l2_le_sup_of_lin_indep : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p) (ω : ∀ σ, VolDens p σ D) (a b : ℤ) (ι : Type) [Fintype ι] [DecidableEq ι] (f : ι → X.functionField), (∀ i, f i ∈ P.H a b) → LinearIndependent ℤ f → IsFam (fun σ => (ω σ).meas) (vals P a b f) ∧ (gram (fun σ => (ω σ).meas) (vals P a b f)).PosDef ∧ ∀ (c : ι → ℂ) (M : ℝ), (∀ σ y, cmb (vals P a b f) c σ y ≤ M) → l2 (fun σ => (ω σ).meas) (vals P a b f) c ≤ (∑ᶠ σ, ((ω σ).meas Set.univ).toReal) * M := by
  first | exact @GlobalTheory.HSAmp.gram_posDef_and_l2_le_sup_bound | exact GlobalTheory.HSAmp.gram_posDef_and_l2_le_sup_bound | (intros; apply GlobalTheory.HSAmp.gram_posDef_and_l2_le_sup_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicMorseSectionsMLAddAUniformStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphicMorse_sections_mL_add_A_uniform : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → GenSmooth p D → ∀ (P : Pair p), P.L.SemiPos D → ∀ (ω : ∀ σ, VolDens p σ D) (ρ : ∀ σ, CxPts p σ → ℝ), (∀ σ, (ω σ).IsRatio (P.L.φ σ) (ρ σ)) → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, ∀ (ι : Type) [Fintype ι] (f : ι → X.functionField), (∀ i, f i ∈ P.H m 1) → ∀ (c : ι → ℂ) (σ : k →+* ℂ) (y : CxPts p σ), cmb (vals P m 1 f) c σ y ≤ (ρ σ y / D.factorial + ε) * (m : ℝ) ^ D * l2 (fun σ => (ω σ).meas) (vals P m 1 f) c := by
  first | exact @GlobalTheory.HSAmp.Morse.cmb_le | exact GlobalTheory.HSAmp.Morse.cmb_le | (intros; apply GlobalTheory.HSAmp.Morse.cmb_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralDbarCutoffMulFormEqZeroLocalStokesStatement
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_dbar_cutoff_mul_form_eq_zero_local_stokes : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (γ : A.Fld) (χ : M → ℝ) (i : A.ι), A.IsForm γ → A.SmoothOn univ (fun y => (χ y : ℂ)) → tsupport χ ⊆ (A.e i).source → A.integral (A.dbar (A.fn χ * γ)) = 0 := by
  first | exact @GlobalTheory.CxForm.DbarLocStokes.integral_dbar_fn_mul_eq_zero | exact GlobalTheory.CxForm.DbarLocStokes.integral_dbar_fn_mul_eq_zero | (intros; apply GlobalTheory.CxForm.DbarLocStokes.integral_dbar_fn_mul_eq_zero <;> assumption)
end

