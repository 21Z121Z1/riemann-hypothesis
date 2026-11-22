import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0961
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0978
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0019
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0019
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0035
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0011
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0026
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0973
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlobalWhittakerCoefficientLinearArchimedeanKerne
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JSW.WhitAlg

open GroundTheory.Automorphic.FourierWhittaker

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem continuous_psiNeg :
    Continuous fun X : Pos a → Ad E => (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
  continuous_subtype_val.comp (GroundTheory.Global.continuous_adelicChar.comp (continuous_supSum 0).neg)

theorem whit_eq (F : GA E a → ℂ) (g : GA E a) :
    GlobalTheory.JSW.whit F g = ∫ X in vecDomain E (Pos a),
      F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) ∂vecMeasure E (Pos a) := rfl

theorem integrableOn_whit {F : GA E a → ℂ} (hF : Continuous F) (g : GA E a) :
    IntegrableOn (fun X => F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ))
      (vecDomain E (Pos a)) (vecMeasure E (Pos a)) := by
  have hcont : Continuous fun X : Pos a → Ad E => F (uGL X * g) * (GroundTheory.Global.adelicChar E (-supSum 0 X) : ℂ) :=
    (hF.comp (continuous_uGL.mul continuous_const)).mul continuous_psiNeg
  exact (hcont.continuousOn.integrableOn_compact isCompact_closure_vecDomain).mono_set subset_closure

theorem whit_add_mul {F G : GA E a → ℂ} (hF : Continuous F) (hG : Continuous G) (c : ℂ) (g : GA E a) :
    GlobalTheory.JSW.whit (fun x => F x + c * G x) g = GlobalTheory.JSW.whit F g + c * GlobalTheory.JSW.whit G g := by
  rw [whit_eq, whit_eq, whit_eq, ← integral_const_mul,
    ← integral_add (integrableOn_whit hF g) ((integrableOn_whit hG g).const_mul c)]
  congr 1
  funext X
  ring

theorem whit_kerInf {F : GA E a → ℂ} (hF : Continuous F)
    (hgr : ∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * infGL E a y)‖ ≤ C * height y ^ N)
    {X : Type} [MeasurableSpace X] (ν : Measure X) [SFinite ν] {k : X → ℂ} {γ : X → GL (Fin a) (Cinf E)}
    (hk : GlobalTheory.JSW.IsRapidInf ν k γ) (g : GA E a) :
    GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g = ∫ x, k x * GlobalTheory.JSW.whit F (g * infGL E a (γ x)) ∂ν := by
  set μ := (vecMeasure E (Pos a)).restrict (vecDomain E (Pos a)) with hμ
  haveI : IsFiniteMeasure μ :=
    ⟨by rw [hμ, Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  let ψ : (Pos a → Ad E) → ℂ := fun Y => (GroundTheory.Global.adelicChar E (-supSum 0 Y) : ℂ)
  let f : (Pos a → Ad E) → X → ℂ := fun Y x => k x * F (uGL Y * g * infGL E a (γ x)) * ψ Y
  have hmeas : Measurable (Function.uncurry f) := by
    haveI : BorelSpace ((Pos a → Ad E) × Lie E a) := Prod.borelSpace
    have hc : ContinuousOn (fun p : (Pos a → Ad E) × Lie E a => chart F (uGL p.1 * g) p.2)
        (Set.univ ×ˢ invSet E a) :=
      (GlobalTheory.ConstTermSmooth.continuousOn_chart hF).comp
        (((continuous_uGL.comp continuous_fst).mul continuous_const).prodMk continuous_snd).continuousOn
        fun p hp => ⟨Set.mem_univ _, hp.2⟩
    have hφ : Measurable fun p : (Pos a → Ad E) × X => ((p.1, toL (γ p.2).val) : (Pos a → Ad E) × Lie E a) :=
      measurable_fst.prodMk (hk.2.1.comp measurable_snd)
    have h1 : Measurable fun p : (Pos a → Ad E) × X => chart F (uGL p.1 * g) (toL (γ p.2).val) := by
      have e : (fun p : (Pos a → Ad E) × X => chart F (uGL p.1 * g) (toL (γ p.2).val)) =
          (Set.univ ×ˢ invSet E a).restrict (fun p : (Pos a → Ad E) × Lie E a => chart F (uGL p.1 * g) p.2) ∘
            fun p => (⟨(p.1, toL (γ p.2).val), Set.mem_univ _, val_mem_invSet _⟩ :
              (Set.univ ×ˢ invSet E a : Set ((Pos a → Ad E) × Lie E a))) := rfl
      rw [e]
      exact hc.restrict.measurable.comp hφ.subtype_mk
    have e2 : Function.uncurry f = fun p => k p.2 * chart F (uGL p.1 * g) (toL (γ p.2).val) * ψ p.1 := by
      funext p
      exact congrArg (fun z => k p.2 * z * ψ p.1) (chart_val F _ _).symm
    rw [e2]
    exact ((hk.1.comp measurable_snd).mul h1).mul (continuous_psiNeg.measurable.comp measurable_fst)
  obtain ⟨C, N, hC⟩ := hgr ((fun Y => uGL Y * g) '' closure (vecDomain E (Pos a)))
    (isCompact_closure_vecDomain.image (continuous_uGL.mul continuous_const))
  have hint : Integrable (Function.uncurry f) (μ.prod ν) := by
    have hb : Integrable (fun p : (Pos a → Ad E) × X => (1 : ℝ) * (C * (‖k p.2‖ * height (γ p.2) ^ N))) (μ.prod ν) :=
      (integrable_const (1 : ℝ)).mul_prod ((hk.2.2 N).const_mul C)
    have hae : ∀ᵐ p ∂(μ.prod ν), p.1 ∈ vecDomain E (Pos a) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_vecDomain)
    refine hb.mono' hmeas.aestronglyMeasurable (hae.mono fun p hp => ?_)
    have hb1 := hC (uGL p.1 * g) ⟨p.1, subset_closure hp, rfl⟩ (γ p.2)
    change ‖k p.2 * F (uGL p.1 * g * infGL E a (γ p.2)) * (GroundTheory.Global.adelicChar E (-supSum 0 p.1) : ℂ)‖ ≤ _
    rw [norm_mul, norm_mul, Circle.norm_coe, mul_one]
    calc ‖k p.2‖ * ‖F (uGL p.1 * g * infGL E a (γ p.2))‖ ≤ ‖k p.2‖ * (C * height (γ p.2) ^ N) :=
          mul_le_mul_of_nonneg_left hb1 (norm_nonneg _)
      _ = 1 * (C * (‖k p.2‖ * height (γ p.2) ^ N)) := by ring
  have hin : ∀ Y, GlobalTheory.JSW.kerInf ν k γ F (uGL Y * g) * ψ Y = ∫ x, f Y x ∂ν := fun Y => by
    simp only [f, GlobalTheory.JSW.kerInf]
    rw [integral_mul_const]
  calc GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g = ∫ Y, ∫ x, f Y x ∂ν ∂μ := by
        rw [whit_eq]
        congr 1
        funext Y
        exact hin Y
    _ = ∫ x, ∫ Y, f Y x ∂μ ∂ν := integral_integral_swap hint
    _ = _ := by
        congr 1
        funext x
        rw [whit_eq, ← integral_const_mul]
        congr 1
        funext Y
        simp only [f, ψ, mul_assoc]

theorem whit_linear_kerInf : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (F G : GA E a → ℂ),
    Continuous F → Continuous G →
    (∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖F (g * infGL E a y)‖ ≤ C * height y ^ N) →
    (∀ K : Set (GA E a), IsCompact K → ∃ (C : ℝ) (N : ℕ), ∀ g ∈ K, ∀ y : GL (Fin a) (Cinf E),
      ‖G (g * infGL E a y)‖ ≤ C * height y ^ N) →
    (∀ (c : ℂ) (g : GA E a), GlobalTheory.JSW.whit (fun x => F x + c * G x) g = GlobalTheory.JSW.whit F g + c * GlobalTheory.JSW.whit G g) ∧
      ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin a) (Cinf E)),
        GlobalTheory.JSW.IsRapidInf ν k γ → ∀ g, GlobalTheory.JSW.whit (GlobalTheory.JSW.kerInf ν k γ F) g =
          ∫ x, k x * GlobalTheory.JSW.whit F (g * infGL E a (γ x)) ∂ν := by
  intro E _ _ _ a F G hF hG hFg _
  exact ⟨fun c g => whit_add_mul hF hG c g, fun X _ ν _ k γ hk g => whit_kerInf hF hFg ν hk g⟩

end GlobalTheory.JSW.WhitAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramSchmidtFlagDomainOrthonormalFrames
section
open NumberField IsDedekindDomain Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolRead
open scoped TensorProduct InnerProductSpace Classical

namespace GlobalTheory.FlagGS

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem sgn_mul_self (p a : ℕ) : ((sgn p a : ℝ) : ℂ) * ((sgn p a : ℝ) : ℂ) = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem diag_of_upper {r : ℕ} (s : Fin r → ℂ) (hs : ∀ a, s a * s a = 1) (b : Matrix (Fin r) (Fin r) ℂ)
    (hb : b.BlockTriangular id) (h : bᵀ * diagonal s * b.map (starRingEnd ℂ) = diagonal s) :
    ∃ t : Fin r → ℝ, b = diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I) := by
  have hs0 : ∀ a, s a ≠ 0 := fun a h0 => by simpa [h0] using hs a
  have hss : diagonal s * diagonal s = (1 : Matrix (Fin r) (Fin r) ℂ) := by
    rw [diagonal_mul_diagonal]; simp [hs]
  have h1 : (diagonal s * bᵀ * diagonal s) * b.map (starRingEnd ℂ) = 1 := by
    rw [Matrix.mul_assoc (diagonal s), Matrix.mul_assoc (diagonal s), h, hss]
  have hc : (b.map (starRingEnd ℂ)).BlockTriangular id := fun a c hca => by
    rw [Matrix.map_apply, hb hca, map_zero]
  letI : Invertible (b.map (starRingEnd ℂ)) := invertibleOfLeftInverse _ _ h1
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular hc
  rw [Matrix.inv_eq_left_inv h1] at hinv
  have hoff : ∀ a c, a ≠ c → b a c = 0 := by
    intro a c hac
    rcases lt_or_gt_of_ne hac with hlt | hlt
    · have := hinv (i := c) (j := a) hlt
      rw [mul_diagonal, diagonal_mul, transpose_apply] at this
      simpa [hs0] using this
    · exact hb hlt
  have hd : b = diagonal fun a => b a a := by
    ext a c
    by_cases hac : a = c
    · subst hac; simp
    · rw [diagonal_apply_ne _ hac, hoff a c hac]
  have hn : ∀ a, ‖b a a‖ = 1 := by
    intro a
    have h2 := congrFun (congrFun h a) a
    rw [hd, diagonal_transpose, diagonal_map (map_zero _), diagonal_mul_diagonal, diagonal_mul_diagonal] at h2
    simp only [diagonal_apply_eq] at h2
    have h3 : b a a * starRingEnd ℂ (b a a) = 1 := by
      apply mul_left_cancel₀ (hs0 a)
      linear_combination h2
    have h4 := congrArg norm h3
    rw [norm_mul, Complex.norm_conj, norm_one] at h4
    nlinarith [norm_nonneg (b a a)]
  refine ⟨fun a => Complex.arg (b a a), ?_⟩
  rw [hd]
  congr 1
  funext a
  simp only [diagonal_apply_eq]
  have := Complex.norm_mul_exp_arg_mul_I (b a a)
  rw [hn a] at this
  simpa using this.symm

theorem exp_keeps {r : ℕ} {H Z : Matrix (Fin r) (Fin r) ℂ} (hH : H * H = 1) (hZ : Zᴴ * H + H * Z = 0) :
    (NormedSpace.exp Z)ᴴ * H * NormedSpace.exp Z = H := by
  have hu : IsUnit H.det := Matrix.isUnit_det_of_left_inverse hH
  have hu' : IsUnit H := (isUnit_iff_isUnit_det H).2 hu
  have e : Zᴴ = H * (-Z) * H⁻¹ := by
    have h1 : Zᴴ * H = -(H * Z) := eq_neg_of_add_eq_zero_left hZ
    rw [mul_neg, ← h1, mul_assoc, mul_nonsing_inv _ hu, mul_one]
  rw [← Matrix.exp_conjTranspose, e, Matrix.exp_conj _ _ hu', mul_assoc _ H⁻¹, nonsing_inv_mul _ hu, mul_one, mul_assoc,
    ← Matrix.exp_add_of_commute _ _ (Commute.refl Z).neg_left, neg_add_cancel, NormedSpace.exp_zero, mul_one]

theorem conj_keeps {r : ℕ} (s : Fin r → ℝ) (g : Matrix (Fin r) (Fin r) ℂ)
    (h : gᴴ * diagonal (fun a => (s a : ℂ)) * g = diagonal fun a => (s a : ℂ)) :
    gᵀ * diagonal (fun a => (s a : ℂ)) * g.map (starRingEnd ℂ) = diagonal fun a => (s a : ℂ) := by
  have h2 := congrArg (fun M : Matrix (Fin r) (Fin r) ℂ => M.map (starRingEnd ℂ)) h
  simp only [Matrix.map_mul, diagonal_map (map_zero (starRingEnd ℂ)), Complex.conj_ofReal] at h2
  have e : gᴴ.map (starRingEnd ℂ) = gᵀ := by
    ext a c; simp [conjTranspose_apply]
  rwa [e] at h2

theorem gram_schmidt_frames : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), (∀ y, IsUnitFr X y → y ∈ X.dom) ∧ (∀ x ∈ X.dom, ∃ y, IsUnitFr X y ∧ ∃ b ∈ Bor X.Ψ r, x = rmul y b) ∧ (∀ y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, IsUnitFr X (rmul y b) → ∃ t : X.Ψ → Fin r → ℝ, b = (fun τ => (Matrix.diagonal fun a => Complex.exp ((t τ a : ℂ) * Complex.I) : Matrix (Fin r) (Fin r) ℂ) : Frame X.Ψ r)) ∧ (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom) ∧ (∀ y, IsUnitFr X y → ∀ γ ∈ X.Γ, IsUnitFr X (lact γ y)) ∧ (∀ y, IsUnitFr X y → ∀ Z ∈ unitLie X, IsUnitFr X (rmul y (expFr Z))) ∧ ∀ (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P : Frame X.Ψ r → ℂ) y, IsUnitFr X y → ∀ b ∈ Bor X.Ψ r, P (rmul y b) = bchar la b * P y → X.pnorm la P (rmul y b) = ‖P y‖ := by
  intro E _ _ _ r X
  have hdom : ∀ y, IsUnitFr X y → y ∈ X.dom := fun y hy => ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.orth_mem_dom X hy
  refine ⟨hdom, fun x hx => ?_, fun y hy b hb hyb => ?_,
    fun x hx b hb => ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb, fun y hy γ hγ τ => ?_, fun y hy Z hZ τ => ?_,
    fun la P y hy b hb hP => ?_⟩
  · have hb := FrameDegreeData.bOf_mem X hx
    refine ⟨rmul x (FrameDegreeData.bOf X x), FrameDegreeData.ortho_bOf X hx, fun τ => ((mat (FrameDegreeData.bOf X x) τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ),
      fun τ => ?_, ?_⟩
    · have hu : IsUnit (mat (FrameDegreeData.bOf X x) τ).det := isUnit_iff_ne_zero.2 (hb τ).1
      letI := Matrix.invertibleOfIsUnitDet _ hu
      refine ⟨?_, fun a c hca => Matrix.blockTriangular_inv_of_blockTriangular (FrameDegreeData.upper_of_bor X hb τ) hca⟩
      exact (Matrix.isUnit_nonsing_inv_det _ hu).ne_zero
    · funext τ
      have hu : IsUnit (mat (FrameDegreeData.bOf X x) τ).det := isUnit_iff_ne_zero.2 (hb τ).1
      exact (Matrix.mul_nonsing_inv_cancel_right _ (mat x τ) hu).symm
  · have h : ∀ τ : X.Ψ, ∃ t : Fin r → ℝ, mat b τ = diagonal fun a => Complex.exp ((t a : ℂ) * Complex.I) := by
      intro τ
      have h1 := hyb τ
      rw [show mat (rmul y b) τ = mat y τ * mat b τ from rfl, FrameDegreeData.gram_mul, hy τ] at h1
      exact diag_of_upper _ (fun a => sgn_mul_self _ _) _ (FrameDegreeData.upper_of_bor X hb τ) h1
    choose t ht using h
    exact ⟨t, funext fun τ => ht τ⟩
  · rw [ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.gram_lact X hγ]
    exact hy τ
  · rw [show mat (rmul y (expFr Z)) τ = mat y τ * NormedSpace.exp (mat Z τ) from rfl, FrameDegreeData.gram_mul, hy τ]
    refine conj_keeps _ _ (exp_keeps ?_ (hZ τ))
    rw [diagonal_mul_diagonal]
    simp only [sgn_mul_self]
    exact diagonal_one
  · have hx := hdom y hy
    unfold Data.pnorm
    rw [hP, norm_mul]
    have hbc : ‖bchar la b‖ = ∏ τ, ∏ i, ‖b τ i i‖ ^ la τ i := by
      unfold bchar
      simp only [norm_prod, norm_zpow]
    rw [hbc, mul_comm (∏ τ, ∏ i, ‖b τ i i‖ ^ la τ i) ‖P y‖, mul_assoc, ← Finset.prod_mul_distrib]
    conv_rhs => rw [← mul_one ‖P y‖]
    congr 1
    refine Finset.prod_eq_one fun τ _ => ?_
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun i _ => ?_
    rw [FrameDegreeData.ratio_rmul X y hx hb τ i,
      FrameDegreeData.factor_eq _ _ (norm_pos_iff.2 (FrameDegreeData.bdiag_ne X hb τ i)) (norm_nonneg _), norm_div,
      ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.norm_dmin_orth' X hy, ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf.norm_dmin_orth' X hy,
      div_one, Real.one_rpow]

end GlobalTheory.FlagGS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarmonicValueIntegralGermFramePowerCharZero
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.FramePower

theorem exists_nabValN_eq_of_map {R K O : Type} [CommRing R] [Algebra ℚ R] [CommRing K] [Algebra ℚ K] [Algebra R K]
    [CommRing O] [StarRing O] {d : ℕ} (B : FB R d O) (h : PS R 2 d) (hc : MvPowerSeries.constantCoeff h = 0)
    (w0 : O) (k k' : ℕ) {n : ℕ} (g : PS R n d) :
    ∃ g' : PS R n d, ∀ {Ix : Type} [Fintype Ix] (cp : Ix → Fin n) (u : Ix → Fin d → K) (P : MvPolynomial Ix K),
      nabValN B K (FB.toK K h) w0 k (FB.toK K g) cp u P = nabValN B K (FB.toK K h) w0 k' (FB.toK K g') cp u P := by
  have gC : GP (comp1 (B.actK R w0) (pt R (n := 1) d 0)) :=
    gp_comp1 _ _ (GlobalTheory.GaugeBaseChange.gp_actK B w0) (gp_pt 0)
  have cL : MvPowerSeries.constantCoeff (B.hL R h w0) = 0 := gt_const_ev _ (pair_points_zero_constant (gp_pt 0) gC) h hc
  have eL : MvPowerSeries.map (algebraMap R K) (B.hL R h w0) = B.hL K (FB.toK K h) w0 := by
    unfold FB.hL
    rw [GlobalTheory.GaugeBaseChange.map_ev_two _ _ _ (gp_pt _) gC, GlobalTheory.QuadDeriv.baseChange_comp1 _ _ _ (gp_pt _),
      GlobalTheory.QuadDeriv.baseChange_pt]
    have := GlobalTheory.GaugeBaseChange.baseChange_actK B (Algebra.ofId R K) w0
    exact congrArg (fun t => ev (n := 1) ![pt K d 0, comp1 t (pt K d 0)] (FB.toK K h)) this
  set S : PS R n d := ∑ b : Fin n, ev (n := n) ![pt R d b] (B.hL R h w0) with hS
  have gp : ∀ b : Fin n, ∀ j : Fin 1, GP ((![pt R d b] : Fin 1 → Pt R n d) j) := by
    intro b j; fin_cases j; exact gp_pt b
  have cS : MvPowerSeries.constantCoeff S = 0 := by
    rw [hS, map_sum]
    exact Finset.sum_eq_zero fun b _ => gt_const_ev _ (gp b) _ cL
  have eS : MvPowerSeries.map (algebraMap R K) S =
      ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K (FB.toK K h) w0) := by
    rw [hS, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.QuadDeriv.map_ev _ _ (gp b), eL]
    congr 1
    funext j; fin_cases j
    exact GlobalTheory.QuadDeriv.baseChange_pt _ _
  have cm : ∀ m : ℕ, MvPowerSeries.constantCoeff ((m : R) • S) = 0 := fun m => by
    rw [MvPowerSeries.smul_eq_C_mul, map_mul, cS, mul_zero]
  have em : ∀ m : ℕ, FB.expS K ((m : K) • ∑ b : Fin n, ev (n := n) ![pt K d b] (B.hL K (FB.toK K h) w0)) =
      FB.toK K (FB.expS R ((m : R) • S)) := fun m => by
    rw [FB.toK.eq_1 K (FB.expS R _), GlobalTheory.GaugeBaseChange.map_expS _ _ (cm m), MvPowerSeries.smul_eq_C_mul, MvPowerSeries.smul_eq_C_mul,
      map_mul, MvPowerSeries.map_C, map_natCast (algebraMap R K), eS]
  refine ⟨g * FB.expS R ((k : R) • S - (k' : R) • S), fun cp u P => ?_⟩
  unfold nabValN
  rw [em, em, FB.toK, FB.toK, FB.toK, FB.toK, ← map_mul, ← map_mul, _root_.mul_assoc,
    ← gt_expS_add _ _ (by rw [map_sub, cm, cm, sub_zero]) (cm k'), sub_add_cancel]

end GlobalTheory.FramePower

open GlobalTheory.FramePower in

theorem GlobalTheory.FramePower.exists_nabValN_eq_of_harmonic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), CharZero (IsLocalRing.ResidueField T.V) → letI := io.toAlgebra; ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n k k' : ℕ) (P : MvPolynomial (LtN Dw n) c.F), P ∈ harmA c a n → ∀ f : PS T.Fr n (chD C.ch), IsIntPS T f → ∃ f' : PS T.Fr n (chD C.ch), IsIntPS T f' ∧ nabValN C.ch.B T.Fr C.ch.h H.w0 k f (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) = nabValN C.ch.B T.Fr C.ch.h H.w0 k' f' (fun ℓ : LtN Dw n => ℓ.2.2) (fun ℓ : LtN Dw n => C.ch.uvec ⟨ℓ.1, ℓ.2.1⟩) (MvPolynomial.map io P) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  have hstar : ∀ a : 𝓞 E, star a = H.bar a := fun _ => rfl
  intro T io y C hchar
  letI := io.toAlgebra
  intro a n k k' P hP f hf
  obtain ⟨B, hBT, hB⟩ := GlobalTheory.PlaceInt.integralBiext_gauge_eig_bound E H Dw l Xo c hstar T io y C
  obtain ⟨hg, -, heig, -⟩ := hB B hBT
  obtain ⟨hF, hA, -⟩ := C.gen.1
  obtain ⟨e1, e2, -⟩ := hBT
  have eF : B.FK T.Fr = C.ch.B.FK T.Fr := by
    funext i
    change MvPowerSeries.map _ (B.G.F i) = MvPowerSeries.map _ (C.ch.B.G.F i)
    rw [GlobalTheory.ChartBiext.toK_self, hF, e1]
  have eA : ∀ a, B.actK T.Fr a = C.ch.B.actK T.Fr a := by
    intro a
    funext i
    change MvPowerSeries.map _ (B.A.act a i) = MvPowerSeries.map _ (C.ch.B.A.act a i)
    rw [GlobalTheory.ChartBiext.toK_self, hA, e2]
  letI : Algebra ℚ T.V := (IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) (g := Int.castRingHom T.V) (by
    rintro ⟨z, hz⟩
    have h0 : z ≠ 0 := nonZeroDivisors.ne_zero hz
    rw [← residue_ne_zero_iff_isUnit]
    simpa using h0)).toAlgebra
  obtain ⟨h0, hh0⟩ := GlobalTheory.canonGauge_exists T.V (chD C.ch) (𝓞 E) T.V B
  have hh1 : B.IsCanonGauge T.Fr (FB.toK T.Fr h0) :=
    GlobalTheory.GaugeBaseChange.isCanonGauge_map B (Algebra.ofId T.V T.Fr) hh0
  choose g hg' using hf
  have ef : f = FB.toK T.Fr (g : PS T.V n (chD C.ch)) := by
    ext m
    exact (hg' m).symm.trans (MvPowerSeries.coeff_map (algebraMap T.V T.Fr) m (g : PS T.V n (chD C.ch))).symm
  obtain ⟨g', hgg⟩ := exists_nabValN_eq_of_map (K := T.Fr) B h0 (GlobalTheory.GaugeBaseChange.const_of_axis hh0.ax0)
    H.w0 k k' (g : PS T.V n (chD C.ch))
  have key := GlobalTheory.nabValN_harmonic_gauge_independent T.V (chD C.ch) (𝓞 E) T.Fr B (gaugeOf C) (FB.toK T.Fr h0) hg hh1
    (E →+* ℂ) Dw.mult ComplexEmbedding.conjugate (InPsi H) (fun τ => io.comp (embK c τ)) (fun τ => by ext x; simp)
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or H)
    (fun τ a => by
      rw [RingHom.comp_apply, RingHom.comp_apply, hstar]
      congr 1
      apply Subtype.ext
      rw [embK_coe, embK_coe, ComplexEmbedding.conjugate_coe_eq, H.bar_eq, IsCMField.complexEmbedding_complexConj])
    (fun σ τ hne => by
      have hex : ∃ a : 𝓞 E, σ (a : E) ≠ τ (a : E) := by
        by_contra hc
        push Not at hc
        exact hne (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => by simpa using hc a))
      obtain ⟨a, ha⟩ := hex
      refine ⟨a, ?_⟩
      have h0 : embK c σ a - embK c τ a ≠ 0 := by
        rw [sub_ne_zero]
        intro h1
        apply ha
        rw [← embK_coe c, ← embK_coe c, h1]
      rw [RingHom.comp_apply, RingHom.comp_apply, ← map_sub]
      exact (Ne.isUnit h0).map _)
    C.ch.uvec heig n (MvPolynomial.map io P) (ReciprocityTheory.ChartRestriction.G.PullbackSections.harmK_map io hP.1.1) H.w0
  refine ⟨FB.toK T.Fr g', fun m => ⟨_, (MvPowerSeries.coeff_map _ _ _).symm⟩, ?_⟩
  rw [← GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eF eA, ← GlobalTheory.ChartBiext.nabValN_congr B C.ch.B eF eA]
  refine (key k f).trans (Eq.trans ?_ (key k' _).symm)
  rw [ef]
  exact hgg _ _ _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianFormNegOnOrthogonalOfPositiveIndexOne
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.SignatureOneForms

theorem form_re_eq_sum {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (v : Fin n → ℂ) :
    (star v ⬝ᵥ A *ᵥ v).re = ∑ i, hA.eigenvalues i *
      Complex.normSq ((star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) i) := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set d : Fin n → ℂ := RCLike.ofReal ∘ hA.eigenvalues with hd
  set c := star U *ᵥ v with hc
  have hspec : A = U * diagonal d * star U := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [Unitary.conjStarAlgAut_apply, hU, hd]
  have h0 := congrArg (fun M => star v ⬝ᵥ M *ᵥ v) hspec
  have h1 : star v ⬝ᵥ A *ᵥ v = star c ⬝ᵥ (diagonal d *ᵥ c) := by
    rw [h0, ← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, hc, star_mulVec]
    simp [Matrix.star_eq_conjTranspose]
  rw [h1]
  simp only [dotProduct, mulVec_diagonal, Complex.re_sum, hd, Function.comp_apply, Pi.star_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.normSq_apply]
  simp [Complex.mul_re, Complex.mul_im]
  ring

theorem form_re_neg {n : ℕ} {A : Matrix (Fin n) (Fin n) ℂ} (hA : A.IsHermitian) (hdet : A.det ≠ 0)
    (i₀ : Fin n) (hpos : ∀ i, 0 < hA.eigenvalues i → i = i₀) (v : Fin n → ℂ) (hv : v ≠ 0)
    (hv0 : (star (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) *ᵥ v) i₀ = 0) :
    (star v ⬝ᵥ A *ᵥ v).re < 0 := by
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  set c := star U *ᵥ v with hc
  have hne : ∀ i, hA.eigenvalues i ≠ 0 := by
    intro i hi
    apply hdet
    rw [hA.det_eq_prod_eigenvalues]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])
  have hcne : c ≠ 0 := by
    intro h0
    apply hv
    have : U *ᵥ c = v := by
      rw [hc, mulVec_mulVec, hU, Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2, one_mulVec]
    rw [← this, h0, mulVec_zero]
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hcne
  have hji : j ≠ i₀ := by
    rintro rfl
    exact hj hv0
  have hjneg : hA.eigenvalues j < 0 :=
    lt_of_le_of_ne (not_lt.mp fun h => hji (hpos j h)) (hne j)
  rw [form_re_eq_sum hA v]
  have key : ∑ i, hA.eigenvalues i * Complex.normSq (c i) < ∑ _i : Fin n, (0 : ℝ) := by
    apply Finset.sum_lt_sum
    · intro i _
      by_cases hi : i = i₀
      · subst hi
        simp [hv0]
      · have : hA.eigenvalues i ≤ 0 := not_lt.mp fun h => hi (hpos i h)
        nlinarith [Complex.normSq_nonneg (c i)]
    · refine ⟨j, Finset.mem_univ j, ?_⟩
      exact mul_neg_of_neg_of_pos hjneg (Complex.normSq_pos.mpr hj)
  simpa using key

end GlobalTheory.SignatureOneForms

namespace GlobalTheory

theorem re_form_neg_of_orth_of_sigPosH_eq_one : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (hA : A.IsHermitian), A.det ≠ 0 → sigPosH hA = 1 → ∀ x y : Fin n → ℂ, 0 < (star x ⬝ᵥ A *ᵥ x).re → star x ⬝ᵥ A *ᵥ y = 0 → y ≠ 0 → (star y ⬝ᵥ A *ᵥ y).re < 0 := by
  intro n A hA hdet hsig x y hx hxy hy
  unfold sigPosH at hsig
  obtain ⟨⟨i₀, hi₀⟩, huniq⟩ := Fintype.card_eq_one_iff.mp hsig
  have hpos : ∀ i, 0 < hA.eigenvalues i → i = i₀ := fun i h => congrArg Subtype.val (huniq ⟨i, h⟩)
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hU
  have hyx : star y ⬝ᵥ A *ᵥ x = 0 := by
    have h := congrArg star hxy
    rw [star_zero] at h
    rw [← h, star_dotProduct, star_mulVec, hA.eq, ← dotProduct_mulVec]
  by_contra hQ
  push_neg at hQ
  set a₀ := (star U *ᵥ x) i₀ with ha₀
  set b₀ := (star U *ᵥ y) i₀ with hb₀
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  by_cases ha : a₀ = 0
  · exact absurd (GlobalTheory.SignatureOneForms.form_re_neg hA hdet i₀ hpos x hx0 ha) (not_lt.mpr hx.le)
  set w := b₀ • x - a₀ • y with hw
  have hw0 : (star U *ᵥ w) i₀ = 0 := by
    simp only [hw, mulVec_sub, mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ← ha₀, ← hb₀]
    ring
  have hQw : star w ⬝ᵥ A *ᵥ w = (Complex.normSq b₀ : ℂ) * (star x ⬝ᵥ A *ᵥ x)
      + (Complex.normSq a₀ : ℂ) * (star y ⬝ᵥ A *ᵥ y) := by
    simp only [hw, star_sub, star_smul, mulVec_sub, mulVec_smul, sub_dotProduct, dotProduct_sub,
      smul_dotProduct, dotProduct_smul, hxy, hyx, smul_eq_mul, Complex.normSq_eq_conj_mul_self]
    simp only [RCLike.star_def]
    ring
  by_cases hw' : w = 0
  · have h1 : star x ⬝ᵥ A *ᵥ w = b₀ * (star x ⬝ᵥ A *ᵥ x) := by
      simp [hw, mulVec_sub, mulVec_smul, dotProduct_sub, dotProduct_smul, hxy]
    rw [hw', mulVec_zero, dotProduct_zero] at h1
    have hQx : star x ⬝ᵥ A *ᵥ x ≠ 0 := fun h => by rw [h] at hx; simp at hx
    have hb : b₀ = 0 := by
      rcases mul_eq_zero.mp h1.symm with h | h
      · exact h
      · exact absurd h hQx
    have : a₀ • y = 0 := by
      have hw2 : b₀ • x - a₀ • y = 0 := hw ▸ hw'
      rw [hb, zero_smul, zero_sub, neg_eq_zero] at hw2
      exact hw2
    exact hy ((smul_eq_zero.mp this).resolve_left ha)
  · have hneg := GlobalTheory.SignatureOneForms.form_re_neg hA hdet i₀ hpos w hw' hw0
    rw [hQw, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul] at hneg
    nlinarith [Complex.normSq_nonneg a₀, Complex.normSq_nonneg b₀,
      mul_nonneg (Complex.normSq_nonneg b₀) hx.le, mul_nonneg (Complex.normSq_nonneg a₀) hQ]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.InjectiveRankEmbeddingStatement
section
open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.injective_rank_embedding : ∀ (P Q R : ℕ) (h : P ≤ R) (k : ℕ), Function.Injective (embR P Q R h k) := by
  first | exact @GlobalTheory.CharPair.embR_injective | exact GlobalTheory.CharPair.embR_injective | (intros; apply GlobalTheory.CharPair.embR_injective <;> assumption)
end

