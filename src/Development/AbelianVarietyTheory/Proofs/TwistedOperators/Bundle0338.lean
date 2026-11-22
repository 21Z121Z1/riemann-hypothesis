import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0320
import Development.AbelianVarietyTheory.Definitions.Foundations.IsRestrictedProdFinAwayIffIsProdMeasureFinAway
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0332
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0321
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0319
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0328
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0322
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.PseudoCoefficientSeparation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0323
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralBargmannEqZeroOfMoments
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockTransl
open Formalism.L2.Ker (VCx DVar derivAt0)

noncomputable section

namespace GlobalTheory.FockTransl

section BargmannUnique

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem bk_smul_left (c : ι → ℝ) (u : ℂ) (z₀ z : VCx ι a b) : bk c (u • z₀) z = u * bk c z₀ z := by
  unfold bk
  simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem conjMono_add (m m' : DVar ι a b →₀ ℕ) (z : VCx ι a b) :
    conjMono (m + m') z = conjMono m z * conjMono m' z := by
  unfold conjMono
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem conjMono_single_one (k : DVar ι a b) (z : VCx ι a b) :
    conjMono (Finsupp.single k 1) z = conj (z k.1 k.2.1 k.2.2) := by
  unfold conjMono; simp [Finsupp.prod_single_index]

abbrev monoSpan (ι : Type) [Fintype ι] (a b : ℕ) : Submodule ℂ (VCx ι a b → ℂ) :=
  Submodule.span ℂ (Set.range fun m : DVar ι a b →₀ ℕ => conjMono m)

theorem monoSpan_mul {P Q : VCx ι a b → ℂ} (hP : P ∈ monoSpan ι a b) (hQ : Q ∈ monoSpan ι a b) :
    P * Q ∈ monoSpan ι a b := by
  have h := Submodule.mul_mem_mul hP hQ
  rw [Submodule.span_mul_span] at h
  refine Submodule.span_mono ?_ h
  rintro _ ⟨_, ⟨m, rfl⟩, _, ⟨m', rfl⟩, rfl⟩
  exact ⟨m + m', funext fun z => conjMono_add m m' z⟩

theorem bk_mem_monoSpan (c : ι → ℝ) (z₀ : VCx ι a b) : (fun z => bk c z₀ z) ∈ monoSpan ι a b := by
  have : (fun z => bk c z₀ z) = ∑ τ, ∑ i, ∑ j,
      ((c τ : ℂ) * z₀ τ i j) • conjMono (Finsupp.single (τ, i, j) 1) := by
    funext z
    simp only [bk, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, conjMono_single_one]
  rw [this]
  exact Submodule.sum_mem _ fun τ _ => Submodule.sum_mem _ fun i _ => Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)

theorem bk_pow_mem_monoSpan (c : ι → ℝ) (z₀ : VCx ι a b) (n : ℕ) :
    (fun z => bk c z₀ z ^ n) ∈ monoSpan ι a b := by
  induction n with
  | zero =>
    have : (fun z : VCx ι a b => bk c z₀ z ^ 0) = conjMono 0 := by funext z; simp [conjMono]
    rw [this]; exact Submodule.subset_span ⟨0, rfl⟩
  | succ n ih =>
    have := monoSpan_mul ih (bk_mem_monoSpan c z₀)
    convert this using 1
    funext z; simp [pow_succ]

theorem exp_norm_le_four (w : ℂ) : Real.exp ‖w‖ ≤ Real.exp ((1 - Complex.I) * w).re +
    Real.exp ((1 + Complex.I) * w).re + Real.exp ((-1 - Complex.I) * w).re + Real.exp ((-1 + Complex.I) * w).re := by
  have h1 : ((1 - Complex.I) * w).re = w.re + w.im := by simp [Complex.mul_re] <;> ring
  have h2 : ((1 + Complex.I) * w).re = w.re + -w.im := by simp [Complex.mul_re] <;> ring
  have h3 : ((-1 - Complex.I) * w).re = -w.re + w.im := by simp [Complex.mul_re] <;> ring
  have h4 : ((-1 + Complex.I) * w).re = -w.re + -w.im := by simp [Complex.mul_re] <;> ring
  rw [h1, h2, h3, h4]
  have key : Real.exp ‖w‖ ≤ Real.exp |w.re| * Real.exp |w.im| := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.2 (Complex.norm_le_abs_re_add_abs_im w)
  have hre : Real.exp |w.re| ≤ Real.exp w.re + Real.exp (-w.re) := by
    rcases abs_cases w.re with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith [Real.exp_pos w.re, Real.exp_pos (-w.re)]
  have him : Real.exp |w.im| ≤ Real.exp w.im + Real.exp (-w.im) := by
    rcases abs_cases w.im with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith [Real.exp_pos w.im, Real.exp_pos (-w.im)]
  calc Real.exp ‖w‖ ≤ (Real.exp w.re + Real.exp (-w.re)) * (Real.exp w.im + Real.exp (-w.im)) :=
        key.trans (mul_le_mul hre him (by positivity) (by positivity))
    _ = _ := by simp only [add_mul, mul_add, ← Real.exp_add]; ring

theorem integral_moment_span_eq_zero {c : ι → ℝ} (hc : ∀ τ, 0 < c τ) {F : VCx ι a b → ℂ}
    (hF : Continuous F) {M : ℝ} (hM : ∀ z, ‖F z‖ ≤ M)
    (hmom : ∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0)
    {P : VCx ι a b → ℂ} (hP : P ∈ monoSpan ι a b) :
    Integrable (fun z => P z * (Real.exp (-gq c z / 2) : ℂ) * F z) ∧
      ∫ z, P z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨m, rfl⟩ := hx
    exact ⟨((GlobalTheory.T.integrable_conjMonomial_bargmann_gaussian ι a b c hc).1 m).mul_bdd hF.aestronglyMeasurable
      (Filter.Eventually.of_forall hM), hmom m⟩
  | zero => simp
  | add x y _ _ hx hy =>
    have e : (fun z => (x + y) z * (Real.exp (-gq c z / 2) : ℂ) * F z) =
        fun z => x z * (Real.exp (-gq c z / 2) : ℂ) * F z + y z * (Real.exp (-gq c z / 2) : ℂ) * F z := by
      funext z; simp only [Pi.add_apply]; ring
    rw [e]
    exact ⟨hx.1.add hy.1, by rw [integral_add hx.1 hy.1, hx.2, hy.2, add_zero]⟩
  | smul r x _ hx =>
    have e : (fun z => (r • x) z * (Real.exp (-gq c z / 2) : ℂ) * F z) =
        fun z => r * (x z * (Real.exp (-gq c z / 2) : ℂ) * F z) := by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]
    exact ⟨hx.1.const_mul r, by rw [integral_const_mul, hx.2, mul_zero]⟩

theorem integral_bargmann_eq_zero_of_moments : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (c : ι → ℝ), (∀ τ, 0 < c τ) → ∀ F : VCx ι a b → ℂ, Continuous F → (∃ M : ℝ, ∀ z, ‖F z‖ ≤ M) → (∀ m : DVar ι a b →₀ ℕ, ∫ z, conjMono m z * (Real.exp (-gq c z / 2) : ℂ) * F z = 0) → ∀ z₀, ∫ z, Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
  intro ι _ a b c hc F hF hMex hmom z₀
  obtain ⟨M, hM⟩ := hMex
  have hexpR : ∀ x : ℝ, HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℝ)) (Real.exp x) := fun x => by
    rw [Real.exp_eq_exp_ℝ]; exact NormedSpace.expSeries_div_hasSum_exp _
  have hexpC : ∀ x : ℂ, HasSum (fun n : ℕ => x ^ n / (Nat.factorial n : ℂ)) (Complex.exp x) := fun x => by
    rw [Complex.exp_eq_exp_ℂ]; exact NormedSpace.expSeries_div_hasSum_exp _
  have hgq : Continuous (fun z : VCx ι a b => gq c z) := by unfold gq; fun_prop
  have hbk : Continuous (fun z : VCx ι a b => bk c z₀ z) := by unfold bk; fun_prop
  have hg : Continuous (fun z : VCx ι a b => ((Real.exp (-gq c z / 2) : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (Real.continuous_exp.comp (hgq.neg.div_const 2))
  have hsum := hasSum_integral_of_dominated_convergence (μ := volume)
    (F := fun (n : ℕ) z => bk c z₀ z ^ n / (Nat.factorial n : ℂ) * (Real.exp (-gq c z / 2) : ℂ) * F z)
    (f := fun z => Complex.exp (bk c z₀ z) * (Real.exp (-gq c z / 2) : ℂ) * F z)
    (fun n z => ‖bk c z₀ z‖ ^ n / (Nat.factorial n : ℝ) * (Real.exp (-gq c z / 2) * M))
    (fun n => ((((hbk.pow n).div_const _).mul hg).mul hF).aestronglyMeasurable)
    (fun n => Filter.Eventually.of_forall fun z => by
      simp only [norm_mul, norm_div, norm_pow, Complex.norm_natCast, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [mul_assoc]
      gcongr
      exact hM z)
    (Filter.Eventually.of_forall fun z => (hexpR ‖bk c z₀ z‖).summable.mul_right _)
    (by
      have htsum : (fun z => ∑' n : ℕ, ‖bk c z₀ z‖ ^ n / (Nat.factorial n : ℝ) * (Real.exp (-gq c z / 2) * M)) =
          fun z => Real.exp ‖bk c z₀ z‖ * (Real.exp (-gq c z / 2) * M) := by
        funext z; rw [tsum_mul_right, (hexpR _).tsum_eq]
      rw [htsum]
      have hI : ∀ u : ℂ, Integrable fun z : VCx ι a b =>
          ‖Complex.exp (bk c (u • z₀) z) * (Real.exp (-gq c z / 2) : ℂ)‖ :=
        fun u => ((GlobalTheory.T.integrable_conjMonomial_bargmann_gaussian ι a b c hc).2 (u • z₀)).norm
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
      refine Integrable.mono' ((((hI (1 - Complex.I)).add (hI (1 + Complex.I))).add
        (hI (-1 - Complex.I))).add (hI (-1 + Complex.I)) |>.const_mul M)
        ((Real.continuous_exp.comp (continuous_norm.comp hbk)).mul
          ((Real.continuous_exp.comp (hgq.neg.div_const 2)).mul continuous_const)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun z => ?_)
      simp only [Pi.add_apply, bk_smul_left, norm_mul, Complex.norm_exp, Complex.norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      rw [abs_of_nonneg (by positivity)]
      have h4 := exp_norm_le_four (bk c z₀ z)
      have he := Real.exp_pos (-gq c z / 2)
      calc Real.exp ‖bk c z₀ z‖ * (Real.exp (-gq c z / 2) * M)
          = (M * Real.exp (-gq c z / 2)) * Real.exp ‖bk c z₀ z‖ := by ring
        _ ≤ (M * Real.exp (-gq c z / 2)) * (Real.exp ((1 - Complex.I) * bk c z₀ z).re +
            Real.exp ((1 + Complex.I) * bk c z₀ z).re + Real.exp ((-1 - Complex.I) * bk c z₀ z).re +
            Real.exp ((-1 + Complex.I) * bk c z₀ z).re) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
        _ = _ := by ring)
    (Filter.Eventually.of_forall fun z => by
      simpa only [mul_assoc] using (hexpC (bk c z₀ z)).mul_right ((Real.exp (-gq c z / 2) : ℂ) * F z))
  have h0 : ∀ n : ℕ, ∫ z, bk c z₀ z ^ n / (Nat.factorial n : ℂ) * (Real.exp (-gq c z / 2) : ℂ) * F z = 0 := by
    intro n
    have := (integral_moment_span_eq_zero hc hF hM hmom
      (Submodule.smul_mem _ ((Nat.factorial n : ℂ)⁻¹) (bk_pow_mem_monoSpan c z₀ n))).2
    have e : (fun z => bk c z₀ z ^ n / (Nat.factorial n : ℂ) * (Real.exp (-gq c z / 2) : ℂ) * F z) =
        fun z => ((Nat.factorial n : ℂ)⁻¹ • fun z => bk c z₀ z ^ n) z * (Real.exp (-gq c z / 2) : ℂ) * F z := by
      funext z; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [e]; exact this
  simp only [h0] at hsum
  exact hsum.unique hasSum_zero

end BargmannUnique

end GlobalTheory.FockTransl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralFiniteIndicatorSmulArchFunction
section
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S

namespace GlobalTheory.TrProdInt

theorem integral_indicator_smul_of_measurePreserving {X Y Z E : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace Z] [NormedAddCommGroup E] [NormedSpace ℂ E] {μ : Measure X} {m : Measure Y} {ν : Measure Z}
    [SigmaFinite m] [SigmaFinite ν] (e : X ≃ᵐ Y × Z) (he : MeasurePreserving e μ (m.prod ν)) {B : Set Z}
    (hB : MeasurableSet B) (hBf : ν B ≠ ⊤) {a : Y → E} (ha : Integrable a m) :
    Integrable (fun x => B.indicator (fun _ => (1 : ℂ)) (e x).2 • a (e x).1) μ ∧
      ∫ x, B.indicator (fun _ => (1 : ℂ)) (e x).2 • a (e x).1 ∂μ = (ν B).toReal • ∫ y, a y ∂m := by
  set Φ : Y × Z → E := (univ ×ˢ B).indicator (fun p => a p.1) with hΦdef
  have hΦ : (fun x => B.indicator (fun _ => (1 : ℂ)) (e x).2 • a (e x).1) = Φ ∘ e := by
    funext x
    rw [Function.comp_apply, hΦdef]
    by_cases h : (e x).2 ∈ B
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (Set.mem_prod.2 ⟨Set.mem_univ _, h⟩), one_smul]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun hm => h (Set.mem_prod.1 hm).2), zero_smul]
  have hmeasS : MeasurableSet (univ ×ˢ B : Set (Y × Z)) := MeasurableSet.univ.prod hB
  have hres : (m.prod ν).restrict (univ ×ˢ B) = m.prod (ν.restrict B) := by
    rw [← Measure.prod_restrict, Measure.restrict_univ]
  haveI : IsFiniteMeasure (ν.restrict B) := ⟨by simpa using hBf.lt_top⟩
  have hint : Integrable Φ (m.prod ν) := by
    rw [hΦdef, integrable_indicator_iff hmeasS, IntegrableOn, hres]
    exact ha.comp_fst _
  have hval : ∫ p, Φ p ∂(m.prod ν) = (ν B).toReal • ∫ y, a y ∂m := by
    rw [hΦdef, integral_indicator hmeasS, hres, integral_fun_fst]
    simp [Measure.real]
  rw [hΦ]
  refine ⟨(he.integrable_comp_emb e.measurableEmbedding).2 hint, ?_⟩
  rw [show (∫ x, (Φ ∘ e) x ∂μ) = ∫ x, Φ (e x) ∂μ from rfl, he.integral_comp' Φ]
  exact hval

theorem integral_indicatorFin_smul_arch : ∀ (D : D7) (V : HSp D) (μa : ∀ w, Measure (GArch D.sp.cm.sig V.gram w)) (μf : ∀ v, Measure (GLoc D.sp.cm.sig V.gram v)) (μ : Measure (GA D V)), IsRestrictedProd D.sp.cm.sig V.gram (frameLat V) μa μf μ → ∀ (νF : Measure (GFin D.sp.cm.sig V.gram)), IsRestrictedProdFin D.sp.cm.sig V.gram (frameLat V) μf νF → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E] (B : Set (GFin D.sp.cm.sig V.gram)), MeasurableSet B → νF B ≠ ⊤ → ∀ (a : (∀ w, GArch D.sp.cm.sig V.gram w) → E), Integrable a (Measure.pi μa) → Integrable (fun g : GA D V => B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) • a fun w => projArch D.sp.cm.sig V.gram w g) μ ∧ ∫ g, B.indicator (fun _ => (1 : ℂ)) (projFin D.sp.cm.sig V.gram g) • a (fun w => projArch D.sp.cm.sig V.gram w g) ∂μ = (νF B).toReal • ∫ x, a x ∂Measure.pi μa := by
  intro D V μa μf μ hμ νF hF E _ _ _ B hB hBf a ha
  haveI := SelfDual.isLattice_frameLat V
  have hmap := hμ.map_archFin hF
  haveI : ∀ w, (μa w).IsHaarMeasure := hμ.1
  haveI : νF.IsHaarMeasure := hF.2.2.1
  haveI : ∀ w, SigmaFinite (μa w) := fun w => inferInstance
  haveI : SigmaFinite (Measure.pi μa) := Measure.pi.sigmaFinite _
  haveI : SigmaFinite νF := inferInstance
  exact integral_indicator_smul_of_measurePreserving
    (archFinEquiv D.sp.cm.sig V.gram).toHomeomorph.toMeasurableEquiv
    ⟨(archFinEquiv D.sp.cm.sig V.gram).toHomeomorph.toMeasurableEquiv.measurable, hmap⟩ hB hBf ha

end GlobalTheory.TrProdInt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralMatrixCoeffIsotropicEqMulMean
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

private lemma symplO_eq_symplOH_add_symplOH {D : D7} (V W : HSp D) (x y : WO V W) :
    symplO V W x y = symplOH V W x y + symplOH V W x y := by
  unfold symplOH
  rw [← add_mul, ← map_add, add_halves, map_one, one_mul]

private lemma symplOH_swap' {D : D7} (V W : HSp D) (x y : WO V W) :
    symplOH V W y x = -symplOH V W x y := by
  unfold symplOH
  rw [GlobalTheory.OrientedHeis.symplO_skew, mul_neg]

theorem heisO_rat_add {D : D7} (V W : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (G : WO V W → ℂ)
    (hG : IsThetaFunO ψ V W G) (γ₁ : Matrix (Fin W.rank) (Fin V.rank) D.host.E) (ξ u : WO V W)
    (h : symplO V W (ratW W V γ₁) ξ = 0) :
    heisO ψ V W (ratW W V γ₁ + ξ) G u = ψ (symplO V W u (ratW W V γ₁)) * heisO ψ V W ξ G u := by
  have hq := hG.quasi γ₁ (u + ξ)
  have h0 : symplOH V W (ratW W V γ₁) ξ = 0 := by
    unfold symplOH
    rw [h, mul_zero]
  simp only [heisO]
  rw [show u + (ratW W V γ₁ + ξ) = ratW W V γ₁ + (u + ξ) by abel, hq, symplO_eq_symplOH_add_symplOH,
    GlobalTheory.OrientedHeis.symplOH_add_right, GlobalTheory.OrientedHeis.symplOH_add_right, h0,
    symplOH_swap' V W u (ratW W V γ₁), add_zero, neg_neg, ← mul_assoc, ← mul_assoc,
    ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 2
  abel

private lemma symplO_add_left_twisted_operators {D : D7} (V W : HSp D) (x x' y : WO V W) :
    symplO V W (x + x') y = symplO V W x y + symplO V W x' y := by
  rw [symplO_eq_symplOH_add_symplOH V W (x + x') y, symplO_eq_symplOH_add_symplOH V W x y, symplO_eq_symplOH_add_symplOH V W x' y,
    GlobalTheory.OrientedHeis.symplOH_add_left]
  abel

private lemma symplO_add_right_twisted_operators {D : D7} (V W : HSp D) (x y y' : WO V W) :
    symplO V W x (y + y') = symplO V W x y + symplO V W x y' := by
  rw [symplO_eq_symplOH_add_symplOH V W x (y + y'), symplO_eq_symplOH_add_symplOH V W x y, symplO_eq_symplOH_add_symplOH V W x y',
    GlobalTheory.OrientedHeis.symplOH_add_right]
  abel

private lemma symplO_zero_left_twisted_operators {D : D7} (V W : HSp D) (y : WO V W) : symplO V W 0 y = 0 := by
  rw [symplO_eq_symplOH_add_symplOH, GlobalTheory.MixModel.symplOH_zero_left, add_zero]

private lemma symplO_zero_right_twisted_operators {D : D7} (V W : HSp D) (x : WO V W) : symplO V W x 0 = 0 := by
  rw [symplO_eq_symplOH_add_symplOH, GlobalTheory.MixModel.symplOH_zero_right, add_zero]

private lemma continuous_emb_twisted_operators {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) : Continuous (emb V W P Q) :=
  GlobalTheory.MixModel.continuous_sandwich (GlobalTheory.MixModel.rat P) (GlobalTheory.MixModel.rat Q)

private lemma emb_rat_eq_ratW_mul {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (r : Matrix (Fin a) (Fin b) D.host.E) :
    emb V W P Q (GlobalTheory.MixModel.rat r) = ratW W V (P * r * Q) := by
  rw [GlobalTheory.MixModel.ratW_eq, GlobalTheory.MixModel.rat_mul, GlobalTheory.MixModel.rat_mul]
  rfl

private lemma continuous_symplO_comp {D : D7} (V W : HSp D) {X : Type} [TopologicalSpace X] {x y : X → WO V W}
    (hx : Continuous x) (hy : Continuous y) : Continuous fun t => symplO V W (x t) (y t) := by
  simp only [symplO_eq_symplOH_add_symplOH]
  exact (GlobalTheory.OrientedHeis.continuous_symplOH hx hy).add (GlobalTheory.OrientedHeis.continuous_symplOH hx hy)

set_option maxHeartbeats 4000000 in

theorem integral_coef_eq_mul_meanX : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E), P.rank = a → Q.rank = b → (∀ y y' : Mx D a b, symplO V W (GlobalTheory.IsoMean.emb V W P Q y) (GlobalTheory.IsoMean.emb V W P Q y') = 0) → ∀ (k : ℕ) (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E), (∀ (z : Mx D 1 k) (y : Mx D a b), symplO V W (GlobalTheory.IsoMean.cplx V W B z) (GlobalTheory.IsoMean.emb V W P Q y) = 0) → (∀ x : WO V W, (∀ y : Mx D a b, symplO V W x (GlobalTheory.IsoMean.emb V W P Q y) = 0) → ∃ (z : Mx D 1 k) (y : Mx D a b), x = GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y) → (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y = 0 → z = 0 ∧ y = 0) → (∀ (z : Mx D 1 k) (y : Mx D a b), GlobalTheory.IsoMean.cplx V W B z + GlobalTheory.IsoMean.emb V W P Q y ∈ ratL W V → z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b) → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b)), IsCovolOne (GlobalTheory.MixModel.ratMx D a b) μ 𝓨 → ∀ (η : Measure (Mx D 1 k)) (𝓩 : Set (Mx D 1 k)), η.IsAddHaarMeasure → IsAddFundamentalDomain (GlobalTheory.MixModel.ratMx D 1 k) 𝓩 η → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → (∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Integrable (fun y => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) μ) → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → ∫ y, (∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) ∂μ = κ * ∫ z in 𝓩, GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G (GlobalTheory.IsoMean.cplx V W B z) * star (GlobalTheory.IsoMean.meanX V W P Q μ 𝓨 G' (GlobalTheory.IsoMean.cplx V W B z)) ∂η := by
  intro D V W a b P Q hP hQ hiso k B hZX hperp hdir hrat ψ hψ μ 𝓨 hμ η 𝓩 hη h𝓩 ν 𝓕 hν h𝓕 hint
  obtain ⟨hTA, hLC, hSC, hT2, hDisc, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D a b
  obtain ⟨hμH, hμF, hμ1⟩ : μ.IsAddHaarMeasure ∧ IsAddFundamentalDomain (↥(GlobalTheory.MixModel.ratMx D a b)) 𝓨 μ ∧
    μ 𝓨 = 1 := id hμ
  have := hTA
  have := hLC
  have := hSC
  have := hT2
  have := hDisc
  obtain ⟨P', Q', hc1, hc2, hc3, hc4⟩ := GlobalTheory.T.exists_rational_dual_complement_sandwich D V W a b P Q hP hQ ψ hψ
  have hψc : IsCharAF D.host.F ψ := hψ.1
  have hcX := continuous_emb_twisted_operators V W P Q
  have hcX' := continuous_emb_twisted_operators V W P' Q'

  have hratX : ∀ (P₁ : Matrix (Fin W.rank) (Fin a) D.host.E) (Q₁ : Matrix (Fin b) (Fin V.rank) D.host.E),
      ∀ r ∈ GlobalTheory.MixModel.ratMx D a b, emb V W P₁ Q₁ r ∈ ratL W V := by
    intro P₁ Q₁ r hr
    obtain ⟨r₀, rfl⟩ := GlobalTheory.MixModel.mem_ratMx.1 hr
    rw [emb_rat_eq_ratW_mul]
    exact ⟨P₁ * r₀ * Q₁, rfl⟩
  have hratZ : ∀ z ∈ GlobalTheory.MixModel.ratMx D 1 k, cplx V W B z ∈ ratL W V := by
    intro z hz
    obtain ⟨z₀, rfl⟩ := GlobalTheory.MixModel.mem_ratMx.1 hz
    rw [show GlobalTheory.MixModel.rat z₀ = z₀.map (incA D) from rfl, cplx_rat]
    exact ⟨_, rfl⟩

  have hspan : ∀ x : WO V W, ∃ s z y, x = emb V W P' Q' s + cplx V W B z + emb V W P Q y := by
    intro x
    obtain ⟨s, hs⟩ := hc1 x
    obtain ⟨z, y, hzy⟩ := hperp _ hs
    refine ⟨s, z, y, ?_⟩
    rw [add_assoc, ← hzy]
    abel
  have hdir3 : ∀ s z y, emb V W P' Q' s + cplx V W B z + emb V W P Q y = 0 → s = 0 ∧ z = 0 ∧ y = 0 := by
    intro s z y h0
    have hs : ∀ y', symplO V W (emb V W P' Q' s) (emb V W P Q y') = 0 := by
      intro y'
      have h1 := congrArg (fun w => symplO V W w (emb V W P Q y')) h0
      simp only [symplO_add_left_twisted_operators, hZX, hiso, add_zero, symplO_zero_left_twisted_operators] at h1
      exact h1
    obtain rfl := hc2 s hs
    rw [emb_zero, zero_add] at h0
    exact ⟨rfl, hdir z y h0⟩
  have hriff : ∀ s z y, emb V W P' Q' s + cplx V W B z + emb V W P Q y ∈ ratL W V ↔
      s ∈ GlobalTheory.MixModel.ratMx D a b ∧ z ∈ GlobalTheory.MixModel.ratMx D 1 k ∧ y ∈ GlobalTheory.MixModel.ratMx D a b := by
    intro s z y
    constructor
    · intro hw
      have hs : s ∈ GlobalTheory.MixModel.ratMx D a b := by
        refine (hc3 s).1 fun γ hγ => ?_
        have h1 := ((GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W _).2 hw) _ (hratX P Q γ hγ)
        simpa only [symplO_add_left_twisted_operators, hZX, hiso, add_zero] using h1
      refine ⟨hs, hrat z y ?_⟩
      have h2 := (ratL W V).sub_mem hw (hratX P' Q' s hs)
      rwa [add_assoc, add_sub_cancel_left] at h2
    · rintro ⟨hs, hz, hy⟩
      exact (ratL W V).add_mem ((ratL W V).add_mem (hratX P' Q' s hs) (hratZ z hz)) (hratX P Q y hy)
  obtain ⟨κ, hκ0, hκ⟩ := GlobalTheory.T.integral_fundamentalDomain_eq_iterated_decomp D V W a b k (emb V W P' Q') (emb V W P Q) (cplx V W B) hcX'
    (continuous_cplx V W B) hcX (emb_add V W P' Q') (cplx_add V W B) (emb_add V W P Q) hspan hdir3 hriff
    μ 𝓨 hμ η 𝓩 hη h𝓩 ν 𝓕 hν h𝓕
  refine ⟨(κ : ℂ), by exact_mod_cast hκ0.ne', ?_⟩
  intro G G' hG hG'
  obtain ⟨hTc, hTper, hTfub⟩ := GlobalTheory.T.thetaMatrixCoeff_smear_continuous_periodic_fubini D V W a b P Q ψ hψ μ 𝓨 hμ ν 𝓕 hν h𝓕 G G' hG hG'
  obtain ⟨hΦc, hΦper⟩ := GlobalTheory.T.iteratedIntegral_decomp_continuous_periodic D V W a b k (emb V W P' Q') (emb V W P Q) (cplx V W B) hcX'
    (continuous_cplx V W B) hcX (emb_add V W P' Q') (hratX P' Q') μ 𝓨 hμ η 𝓩 hη h𝓩 _ hTc hTper
  beta_reduce at hΦc hΦper

  have : BorelSpace (Mx D a b) := ⟨rfl⟩
  have : MeasurableAdd (Mx D a b) :=
    ⟨fun c => (continuous_const_add c).measurable, fun c => (continuous_add_const c).measurable⟩
  have : MeasurableConstVAdd ↥(GlobalTheory.MixModel.ratMx D a b) (Mx D a b) :=
    ⟨fun g => (continuous_const_add (g : Mx D a b)).measurable⟩
  have : Countable ↥(GlobalTheory.MixModel.ratMx D a b) :=
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  have hsr : (Measure.sum fun γ : ↥(GlobalTheory.MixModel.ratMx D a b) => μ.restrict ((fun x => γ +ᵥ x) '' 𝓨)) = μ :=
    hμF.sum_restrict
  have hHS : HasSum (fun γ : ↥(GlobalTheory.MixModel.ratMx D a b) =>
      ∫ ξ in 𝓨, (∫ u in 𝓕, heisO ψ V W (emb V W P Q (γ +ᵥ ξ)) G u * star (G' u) ∂ν) ∂μ)
      (∫ y, (∫ u in 𝓕, heisO ψ V W (emb V W P Q y) G u * star (G' u) ∂ν) ∂μ) := by
    have h1 := MeasureTheory.hasSum_integral_measure
      (f := fun y => ∫ u in 𝓕, heisO ψ V W (emb V W P Q y) G u * star (G' u) ∂ν)
      (μ := fun γ : ↥(GlobalTheory.MixModel.ratMx D a b) => μ.restrict ((fun x => γ +ᵥ x) '' 𝓨))
      (by rw [hsr]; exact hint G G' hG hG')
    rw [hsr] at h1
    have e : ∀ γ : ↥(GlobalTheory.MixModel.ratMx D a b),
        ∫ y in (fun x => γ +ᵥ x) '' 𝓨, (∫ u in 𝓕, heisO ψ V W (emb V W P Q y) G u * star (G' u) ∂ν) ∂μ =
          ∫ ξ in 𝓨, (∫ u in 𝓕, heisO ψ V W (emb V W P Q (γ +ᵥ ξ)) G u * star (G' u) ∂ν) ∂μ :=
      fun γ => (MeasureTheory.measurePreserving_add_left μ (γ : Mx D a b)).setIntegral_image_emb
        (measurableEmbedding_const_vadd (γ : Mx D a b)) _ 𝓨
    simp only [e] at h1
    exact h1

  have hterm : ∀ γ : ↥(GlobalTheory.MixModel.ratMx D a b),
      ∫ ξ in 𝓨, (∫ u in 𝓕, heisO ψ V W (emb V W P Q (γ +ᵥ ξ)) G u * star (G' u) ∂ν) ∂μ =
        (κ : ℂ) * ∫ s in 𝓨, ψ (symplO V W (emb V W P' Q' s) (emb V W P Q γ)) *
          (∫ z in 𝓩, (∫ y in 𝓨, (∫ ξ in 𝓨, heisO ψ V W (emb V W P Q ξ) G
            (emb V W P' Q' s + cplx V W B z + emb V W P Q y) *
              star (G' (emb V W P' Q' s + cplx V W B z + emb V W P Q y)) ∂μ) ∂μ) ∂η) ∂μ := by
    intro γ
    obtain ⟨γ₀, hγ₀⟩ := GlobalTheory.MixModel.mem_ratMx.1 γ.2
    have hγr : emb V W P Q γ = ratW W V (P * γ₀ * Q) := by rw [← hγ₀, emb_rat_eq_ratW_mul]
    have e1 : ∀ ξ u, heisO ψ V W (emb V W P Q (γ +ᵥ ξ)) G u * star (G' u) =
        ψ (symplO V W u (emb V W P Q γ)) * (heisO ψ V W (emb V W P Q ξ) G u * star (G' u)) := by
      intro ξ u
      rw [show (γ +ᵥ ξ : Mx D a b) = (γ : Mx D a b) + ξ from rfl, emb_add, hγr,
        heisO_rat_add V W ψ G hG (P * γ₀ * Q) _ u (by rw [← hγr]; exact hiso _ _), mul_assoc]
    have hφc : Continuous fun u => ψ (symplO V W u (emb V W P Q γ)) :=
      hψc.1.comp (continuous_symplO_comp V W continuous_id continuous_const)
    simp_rw [e1]
    rw [hTfub _ hφc (fun u => (hψc.2.1 _).le)]
    have h3 := hκ (fun u => ψ (symplO V W u (emb V W P Q γ)) *
        ∫ ξ in 𝓨, heisO ψ V W (emb V W P Q ξ) G u * star (G' u) ∂μ) (hφc.mul hTc) (by
      intro δ hδ u
      rw [symplO_add_left_twisted_operators, AddChar.map_add_eq_mul,
        (GlobalTheory.RatAnnih.ratL_annihilator D ψ hψ V W δ).2 hδ _ (hratX P Q γ γ.2), one_mul, hTper δ hδ u])
    beta_reduce at h3
    rw [h3]
    congr 1
    refine congrArg (fun F : Mx D a b → ℂ => ∫ s in 𝓨, F s ∂μ) (funext fun s => ?_)
    simp only [symplO_add_left_twisted_operators, hZX, hiso, add_zero]
    simp_rw [MeasureTheory.integral_const_mul]
  have hκne : (κ : ℂ) ≠ 0 := by exact_mod_cast hκ0.ne'
  have hsum := (summable_mul_left_iff hκne).1 (by simpa only [hterm] using hHS.summable)
  have hF := GlobalTheory.T.fourierInversion_zero_compactQuotient_summable (Mx D a b) (GlobalTheory.MixModel.ratMx D a b) K hK hKc (↥(GlobalTheory.MixModel.ratMx D a b))
    (fun γ s => ψ (symplO V W (emb V W P' Q' s) (emb V W P Q γ)))
    (fun γ => hψc.1.comp (continuous_symplO_comp V W hcX' continuous_const))
    (by intro γ x y; simp only [emb_add, symplO_add_left_twisted_operators, AddChar.map_add_eq_mul])
    (by intro γ δ x; simp only [AddSubgroup.coe_add, emb_add, symplO_add_right_twisted_operators, AddChar.map_add_eq_mul])
    (by intro x; simp only [ZeroMemClass.coe_zero, emb_zero, symplO_zero_right_twisted_operators, AddChar.map_zero_eq_one])
    (fun γ x => hψc.2.1 _)
    (fun x => ⟨fun h => (hc3 x).1 fun γ hγ => h ⟨γ, hγ⟩, fun h γ => (hc3 x).2 h γ γ.2⟩)
    (fun γ h => Subtype.ext (hc4 γ γ.2 h)) μ 𝓨 hμH hμF hμ1 _ hΦc hΦper hsum
  beta_reduce at hF
  rw [← hHS.tsum_eq, tsum_congr hterm, tsum_mul_left, hF]
  congr 1

  refine congrArg (fun F : Mx D 1 k → ℂ => ∫ z in 𝓩, F z ∂η) (funext fun z => ?_)
  simp only [emb_zero, zero_add]
  have e2 : ∀ y ξ, heisO ψ V W (emb V W P Q ξ) G (cplx V W B z + emb V W P Q y) =
      G (emb V W P Q ξ + (emb V W P Q y + cplx V W B z)) := by
    intro y ξ
    have h0 : symplOH V W (cplx V W B z + emb V W P Q y) (emb V W P Q ξ) = 0 := by
      unfold symplOH
      rw [symplO_add_left_twisted_operators, hZX, hiso, add_zero, mul_zero]
    simp only [heisO, h0, AddChar.map_zero_eq_one, one_mul]
    congr 1
    abel
  have e3 : ∀ y, ∫ ξ in 𝓨, G (emb V W P Q ξ + (emb V W P Q y + cplx V W B z)) ∂μ =
      meanX V W P Q μ 𝓨 G (cplx V W B z) :=
    fun y => meanX_translate D V W a b P Q hiso ψ hψ μ 𝓨 hμ G hG (cplx V W B z) (hZX z) y
  simp_rw [e2, MeasureTheory.integral_mul_const, e3, MeasureTheory.integral_const_mul]
  congr 1
  have e4 : ∀ f : Mx D a b → ℂ, ∫ y in 𝓨, star (f y) ∂μ = star (∫ y in 𝓨, f y ∂μ) :=
    fun f => integral_conj
  rw [e4]
  refine congrArg star (congrArg (fun F : Mx D a b → ℂ => ∫ y in 𝓨, F y ∂μ) (funext fun y => ?_))
  rw [add_comm]

end GlobalTheory.IsoMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwinerOfKFiniteVectorsStatement
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_of_k_finite_vectors : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V] (π : Matrix (Fin n) (Fin n) ℂ → (V →L[ℂ] V)), IsAdmRep ε ρ → IsAdmRep ε π → ∀ T : H →ₗ[ℂ] V, (kFinVec ε ρ).map T = kFinVec ε π → (∀ k ∈ Kset ε, ∀ y, IsKFin ε ρ y → T (ρ k y) = π k (T y)) → (∀ a : H, IsKFin ε ρ a → (∀ y, IsKFin ε ρ y → T y = 0 → ⟪a, y⟫_ℂ = 0) → ∃ w, IsKFin ε π w ∧ ∀ y, IsKFin ε ρ y → ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ) ∧ ∀ w : V, IsKFin ε π w → ∃ a, IsKFin ε ρ a ∧ ∀ y, IsKFin ε ρ y → ⟪a, y⟫_ℂ = ⟪w, T y⟫_ℂ := by
  first | exact @GlobalTheory.KFinDual.kFinite_riesz | exact GlobalTheory.KFinDual.kFinite_riesz | (intros; apply GlobalTheory.KFinDual.kFinite_riesz <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsotropicPartRationalCharactersAdelicMatricesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isotropic_part_rational_characters_adelic_matrices : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ C' : Matrix (Fin V.rank) (Fin r) D.host.E, adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → (∀ (a : Matrix (Fin W.rank) (Fin r) D.host.E), Continuous fun t : Mx D W.rank r => ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D))))) ∧ (∀ (a : Matrix (Fin W.rank) (Fin r) D.host.E) t s, ψ (symplO V W (isoPart V W C' (t + s)) (isoPart V W C (a.map (incA D)))) = ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * ψ (symplO V W (isoPart V W C' s) (isoPart V W C (a.map (incA D))))) ∧ (∀ (a b : Matrix (Fin W.rank) (Fin r) D.host.E) t, ψ (symplO V W (isoPart V W C' t) (isoPart V W C ((a + b).map (incA D)))) = ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) * ψ (symplO V W (isoPart V W C' t) (isoPart V W C (b.map (incA D))))) ∧ (∀ t, (∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) = 1) ↔ t ∈ ratMx D W.rank r) ∧ ∀ a : Matrix (Fin W.rank) (Fin r) D.host.E, (∀ t, ψ (symplO V W (isoPart V W C' t) (isoPart V W C (a.map (incA D)))) = 1) → a = 0 := by
  first | exact @GlobalTheory.IsoDualChars.chars | exact GlobalTheory.IsoDualChars.chars | (intros; apply GlobalTheory.IsoDualChars.chars <;> assumption)
end

