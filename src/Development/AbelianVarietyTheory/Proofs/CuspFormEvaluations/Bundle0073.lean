import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0067
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0011
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LiftIndexPowFourLeDegree
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.MaximalCuspKernels.KerExistsStatement
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0046
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0063
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.DatTheta
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0074
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0037
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfM
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0059
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0070
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.FirstMinimumInvariantContinuousPosOnFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0037
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0034
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0010
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0038

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ComponentModelWeightDimensionDictionaryStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.componentModelWeight_dimension_dictionary : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (k : (T.U j T.σ₀).Comp), (∀ u u' : WeightFamilies.Wt D j, laR T j (wadd u u') k = laR T j u k + laR T j u' k) ∧ (∀ (m : ℕ) (u : WeightFamilies.Wt D j), laR T j (wsmul m u) k = m • laR T j u k) ∧ (∀ (u v : WeightFamilies.Wt D j) (m : ℕ), laR T j (addL u v m) k = laR T j u k + m • laR T j v k) ∧ (∀ i : ℕ, laR T j (etWt D j i) k = (i * (g0 D / 2)) • de2W ((T.U j T.σ₀).X k)) ∧ nd ((T.U j T.σ₀).X k) = WeightFamilies.dimY D j ∧ ((T.U j T.σ₀).X k).p0 = (D.R.sigW j).2 ∧ ((T.U j T.σ₀).X k).Ψ.card = D.R.f ∧ ∃ tt : ((T.U j T.σ₀).X k).Ψ ≃ D.what₂.Tau, ∀ (u : WeightFamilies.Wt D j) (τ : ((T.U j T.σ₀).X k).Ψ) (a : Fin D.R.r), laR T j u k τ a = if ((T.U j T.σ₀).X k).p0 ≤ (a : ℕ) then (ext0 (u.aP (tt τ)) ((a : ℕ) - ((T.U j T.σ₀).X k).p0) : ℤ) + ((u.n / 2 : ℕ) : ℤ) else -(ext0 (u.aM (tt τ)) (((T.U j T.σ₀).X k).p0 - 1 - (a : ℕ)) : ℤ) - ((u.n / 2 : ℕ) : ℤ) := by
  first | exact @GlobalTheory.Shares.WtDic.weights_dictionary | exact GlobalTheory.Shares.WtDic.weights_dictionary | (intros; apply GlobalTheory.Shares.WtDic.weights_dictionary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ConjCmHalfIntegralGeneratorEqOneSub
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

namespace GlobalTheory.ExtraWeight

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_multiple_mem (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (v : Fin r → E) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ (c : E) • v ∈ X.Λ :=
  _root_.GlobalTheory.SmulMemOfSpan.exists_smul_mem_lattice X v

theorem herm_smul_smul (G : Matrix (Fin r) (Fin r) E) (a b : E) (x y : Fin r → E) :
    herm G (a • x) (b • y) = a * ReciprocityTheory.ChartRestriction.G.FD.cc b * herm G x y := by
  simp only [herm, ReciprocityTheory.ChartRestriction.G.FD.cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem exists_isIso (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) {ρ : ℕ} (cu : FJ.CuspFD X ρ) (hρ : 0 < ρ) :
    ∃ ξ : Fin r → E, X.IsIso ξ := by
  obtain ⟨c, hc, hm⟩ := exists_multiple_mem X (cu.e ⟨0, hρ⟩)
  refine ⟨_, hm, by rw [herm_smul_smul, cu.iso, mul_zero], ?_⟩
  exact smul_ne_zero (by simpa using hc) (cu.ind.ne_zero _)

theorem conj_cmHalfIntegralGenerator_eq_one_sub (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : ReciprocityTheory.ChartRestriction.G.FD.cc (H.w0 : E) = 1 - (H.w0 : E) :=
  _root_.GlobalTheory.CMConjugationOfSquareRoot.main H

theorem even_im_hermitian_sub (X : DataX E r) (w0 : 𝓞 E) (hw : ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E) = 1 - (w0 : E)) :
    ∀ u ∈ X.Λ, ∀ v ∈ X.Λ, ∃ k : ℤ,
      Algebra.trace ℚ E (X.ξ0 * herm X.Gm u (((w0 : E) - ReciprocityTheory.ChartRestriction.G.FD.cc (w0 : E)) • v)) -
        Algebra.trace ℚ E (X.ξ0 * herm X.Gm u v) = 2 * k :=
  _root_.UpperTheory.Reformulated.B.Ue6.even_im_hermitian_sub X w0 hw

end General

theorem extra_weight_exists : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (large₂ : SizeData₂ D) (w : WeightFamilies.Wt D j), GamAt T.toCore → ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → j < D.R.m → (D.R.f : ℝ) ^ 2 ≤ D.host.rdE → 16 ≤ D.host.rdE → D.R.m ^ 4 ≤ D.R.f → ∀ k : (T.U j T.σ₀).Comp, BasePotentialExistence ((T.U j T.σ₀).X k) (de2W ((T.U j T.σ₀).X k)) D.R.r (1 / (2 * (5 : ℝ) ^ 4 * |(NumberField.discr D.host.E : ℝ)| ^ ((1 : ℝ) / D.R.f))) := by
  intro D T h j hj large₂ w hG hP hL hrn hjm hf2 hrd hm4 k
  obtain ⟨e, -⟩ := GlobalTheory.CuspDataBounds.cusp_data_bounds D T h hG large₂ j hj w hP hL hrn T.σ₀ T.good_σ₀
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField, Formalism.BasicNotions.Ranks.f, Formalism.BasicNotions.Ranks.n]
    ring
  have hcard : ((T.U j T.σ₀).X k).Ψ.card = D.R.f := by
    have h2c := Formalism.L2.Pj.DatLin.two_card ((T.U j T.σ₀).X k).cmType
    rw [hfr] at h2c
    omega
  have hPf : ReciprocityTheory.ChartRestriction.G.I2.PT.f D.host.E = D.R.f := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.f
    omega
  have hPr : ReciprocityTheory.ChartRestriction.G.I2.PT.rd D.host.E = D.host.rdE := rfl
  have hp0 : ((T.U j T.σ₀).X k).p0 = D.R.m - j :=
    ((h.unf j hj T.σ₀ T.good_σ₀).2.1 k).1.trans (h.pins.2.2.2 j hj).2.1
  have hf1 : (1 : ℝ) ≤ D.R.f := by
    have : 0 < D.R.f := by unfold Ranks.f Ranks.n; positivity
    exact_mod_cast this
  obtain ⟨cu⟩ := h.cuNe j hj k
  have hρ : 0 < WeightFamilies.rho D j := by
    show 0 < D.R.m - j
    omega
  have key := GlobalTheory.ThetaWeight.exists_weight GlobalTheory.theta_bound_tStatement D.host.E D.R.r (e k).toX
    (exists_isIso _ cu hρ)
    ⟨⟨T.Q.H.w0, even_im_hermitian_sub _ _ (conj_cmHalfIntegralGenerator_eq_one_sub T.Q.H)⟩, by rw [hPf, hPr]; nlinarith, by rw [hPf, hPr]; exact hf2,
      by rw [hPr]; exact hrd, D.R.m, by omega, by rw [hPf]; exact hm4,
      Or.inl (by show ((T.U j T.σ₀).X k).p0 ≤ _; omega)⟩
  rw [← hcard]
  exact key

end GlobalTheory.ExtraWeight
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormHalfSupAtOrthonormalFrameFirstMinStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspForm_halfSup_at_orthonormalFrame_firstMin : ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∀ f ∈ T.C j w, 0 < supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) → ∃ (k : (T.U j σ).Comp) (xf : ((T.U j σ).X k).dom), (∀ τ' i', ‖dmin ((T.U j σ).X k).Gm xf.1 τ' i'‖ = 1) ∧ ((T.U j σ).X k).IsOrtho xf.1 ∧ supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) f) ≤ 2 * ‖toC (evR (T.Q.Xo j) T.Q.c f ((T.U j σ).un k xf))‖ ∧ 0 < ((T.U j σ).X k).firstMinimumSq xf.1 ∧ Real.log (1 / ((T.U j σ).X k).firstMinimumSq xf.1) ≤ 80 * large₂.sc.L := by
  first | exact @GlobalTheory.RunIn.half_sup_at_ortho_frame | exact GlobalTheory.RunIn.half_sup_at_ortho_frame | (intros; apply GlobalTheory.RunIn.half_sup_at_ortho_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingAtPointsMulPowMemSpan
section
namespace GlobalTheory.Shares.VanDiv

section Model

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem leviO_phla_add_nsmul (x0 : Frame X.Ψ r) (F L : Wt X.Ψ r) (k : ℕ) {z : V (nd X)} (hz : z ∈ OmF X x0)
    (ξ : Fin (nd X) → ℂ) :
    leviO X x0 (phla X (F + k • L)) z ξ = leviO X x0 (phla X F) z ξ + k * leviO X x0 (phla X L) z ξ := by
  have h1 := (IW.phla_cpt_cdAt X x0 hz F).of_le HE.two_le_inf
  have h3 := (IW.phla_cpt_cdAt X x0 hz L).of_le HE.two_le_inf
  have e : (fun w => ((phla X (F + k • L) (cpt X x0 w) : ℝ) : ℂ)) =ᶠ[nhds z]
      fun w => ((phla X F (cpt X x0 w) + (k : ℝ) * phla X L (cpt X x0 w) : ℝ) : ℂ) := by
    filter_upwards [(ExF.isOpen_OmF X x0).mem_nhds hz] with w hw
    rw [OW.phla_add_nsmul X hw]
  unfold leviO leviM
  rw [Y.fc_leviV_congr _ _ _ _ e, Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 (contDiffAt_const.mul h3),
    Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3]
  simp only [Complex.add_re, Complex.re_ofReal_mul]

theorem pnorm_mul_pow_sq (F L : Wt X.Ψ r) (m : ℕ) (g w : Frame X.Ψ r → ℂ) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm (F + m • L) (fun x => g x * w x ^ m) x ^ 2 = X.pnorm F g x ^ 2 * (X.pnorm L w x ^ 2) ^ m := by
  rw [OW.pnorm_sq X _ _ hx, OW.pnorm_sq X _ _ hx, OW.pnorm_sq X _ _ hx, OW.phla_add_nsmul X hx, neg_add,
    Real.exp_add, ← mul_neg, Real.exp_nat_mul, map_mul, map_pow]
  ring

theorem model_division (Xa : ArchInM X) (Fl : FlatM X Xa) (hm : Margins X Xa) (k : ℕ)
    (hfin : ∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (Xa.Fp + (k + (nd X + 1)) • Xa.L),
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x)
    (g : Frame X.Ψ r → ℂ) (hg : X.IsBddSec (Xa.Fp + k • Xa.L) g) (hv : ∀ j, g (Fl.xs j) = 0) :
    ∃ h : Fin (nd X) → Frame X.Ψ r → ℂ, (∀ i, h i ∈ X.SS (Xa.Fp + (k + nd X) • Xa.L)) ∧
      ∀ x ∈ X.dom, g x * Fl.w0 x ^ (nd X + 1) = ∑ i, Fl.s i x * h i x := by
  obtain ⟨-, ⟨bb, m, hbb, hbm, hmar⟩, hL, -, hcusp⟩ := hm
  have e : ∀ a : ℕ, Xa.Fp + k • Xa.L + a • Xa.L = Xa.Fp + (k + a) • Xa.L := fun a => by
    rw [add_nsmul, add_assoc]
  obtain ⟨C, hC⟩ := hg.2
  have hC2 : ∀ x ∈ X.dom, X.pnorm (Xa.Fp + k • Xa.L) g x ^ 2 ≤ C ^ 2 := fun x hx =>
    pow_le_pow_left₀ (BoundedSectionAlgebra.pnorm_nonneg X _ _ _) (hC x hx) 2
  obtain ⟨B, hB⟩ := Fl.weightForm_vanishes.1.1.2
  obtain ⟨K, hK⟩ := Fl.denom_le_family
  obtain ⟨h, hh, hs⟩ := GlobalTheory.DivFreeWeight.division_order_one E r X Xa Fl (Xa.Fp + k • Xa.L)
    ⟨bb, m, hbb, hbm, fun x0 ho z hz ξ => by
      have h1 := hmar x0 ho z hz ξ
      have h2 := mul_nonneg (Nat.cast_nonneg (α := ℝ) k) (hL x0 ho z hz ξ)
      rw [leviO_phla_add_nsmul x0 _ _ k hz]
      linarith⟩
    (by rw [e]; exact hcusp _) (by rw [e]; exact hfin)
    (fun x => g x * Fl.w0 x ^ (nd X + 1))
    ⟨GlobalTheory.Up.DivCorePf.isSec_mul hg.1 (GlobalTheory.Up.DivCorePf.isSec_pow Fl.weightForm_vanishes.1.1.1 _),
      √(C ^ 2 * (B ^ 2) ^ (nd X + 1)), fun x hx => by
        refine Real.le_sqrt_of_sq_le ?_
        rw [pnorm_mul_pow_sq _ _ _ _ _ hx]
        exact mul_le_mul (hC2 x hx) (pow_le_pow_left₀ (sq_nonneg _)
          (pow_le_pow_left₀ (BoundedSectionAlgebra.pnorm_nonneg X _ _ _) (hB x hx) 2) _) (by positivity) (by positivity)⟩
    ⟨C ^ 2 * |K| ^ (nd X + 1), fun x hx => by
      rw [pnorm_mul_pow_sq _ _ _ _ _ hx, mul_assoc, ← mul_pow]
      refine mul_le_mul (hC2 x hx) (pow_le_pow_left₀ (sq_nonneg _) ((hK x hx).trans ?_) _)
        (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)⟩
    (fun j => by simp [hv j])
  exact ⟨h, fun i => hcusp _ _ (e _ ▸ hh i), hs⟩

end Model

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem sp_le_span {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} (R : Rdg X)
    (u : WeightFamilies.Wt D j) : ∃ (K : ℕ) (b : Fin K → B.Cusp j u),
      R.sp u Set.univ ≤ Submodule.span ℂ (Set.range fun i => R.ev (X.inc u (b i))) := by
  obtain ⟨K, b, hb⟩ := Module.Finite.exists_fin (R := B.KO) (M := B.Cusp j u)
  refine ⟨K, b, Submodule.span_le.2 ?_⟩
  rintro _ ⟨F, -, rfl⟩
  obtain ⟨a, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B.KO).1 (hb ▸ Submodule.mem_top : F ∈ _)
  simp only [map_sum, map_smul, R.ev_smul]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem vanishing_division : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → ∀ k : ℕ, ∀ g ∈ R.sp (addL wF wL k) Set.univ, (∀ q, g (xs q) = 0) → ∃ m : ℕ, R.s w t 0 ^ (m + 1) * g ∈ R.deep w t (addL wF wL (k + m)) 1 := by
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en hen honto k g hg hv
  classical
  have hwt : ∀ (a : ℕ) c, laR T j (addL wF wL a) c = (A.Xa c).Fp + a • (A.Xa c).L := fun a c => by
    rw [(GlobalTheory.Shares.WtDic.weights_dictionary D T h j hj c).2.2.1, A.hF, A.hL]
  obtain ⟨f, hf, hgf⟩ := (GlobalTheory.Shares.span_readings_components D T h j hj n R e hR (addL wF wL k)).1 g hg
  have hfin : ∀ (a : ℕ) (c : (T.U j T.σ₀).Comp), ∃ (K : ℕ) (b : Fin K → Frame ((T.U j T.σ₀).X c).Ψ D.R.r → ℂ),
      ∀ f ∈ ((T.U j T.σ₀).X c).SS ((A.Xa c).Fp + a • (A.Xa c).L),
      ∃ cc : Fin K → ℂ, ∀ x ∈ ((T.U j T.σ₀).X c).dom, f x = ∑ i, cc i * b i x := by
    intro a c
    obtain ⟨K, b, hb⟩ := sp_le_span R (addL wF wL a)
    refine ⟨K, fun i => rdR h j (b i) c, fun p hp => ?_⟩
    have h1 := (GlobalTheory.Shares.span_readings_components D T h j hj n R e hR _).2.1 _ _ (honto a)
      (Function.update (fun _ => 0) c p) (fun c' => by
        by_cases hc : c' = c
        · subst hc
          rw [Function.update_self, hwt]
          exact hp
        · rw [Function.update_of_ne hc]
          exact (siegelSpaceAlgebra_holds _ _ _ 0 0).2.2.1.1.1)
    obtain ⟨cc, hcc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hb h1)
    refine ⟨cc, fun x hx => ?_⟩
    have h2 := congrFun hcc (e.symm ⟨c, ⟨x, hx⟩⟩)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2] at h2
    rw [Equiv.apply_symm_apply] at h2
    simpa using h2.symm
  have hdiv := fun c => model_division (A.Xa c) (Fl.Fl c) (A.mar c) k (hfin _ c) (f c)
    (hwt k c ▸ (hf c).1.1) (fun i => by
      have h1 := hv (en.symm ⟨c, i⟩)
      rw [hgf, hen, Equiv.apply_symm_apply] at h1
      exact h1)
  choose H hH hsum using hdiv
  refine ⟨WeightFamilies.dimY D j, ?_⟩
  have hs : ∀ i y, R.s w t i y = ∑ a, t (i, a) * rdR h j (w a) (e y).1 (e y).2.1 := fun i y => by
    simp only [Rdg.s, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hR.2]
  have hmem : ∀ i : Fin (WeightFamilies.dimY D j),
      (fun y => H (e y).1 (Fin.cast (A.dim _).symm i) (e y).2.1) ∈ R.sp (addL wF wL (k + WeightFamilies.dimY D j)) Set.univ :=
    fun i => (GlobalTheory.Shares.span_readings_components D T h j hj n R e hR _).2.1 _ _ (honto _) (fun c => H c (Fin.cast (A.dim c).symm i))
      (fun c => by
        rw [hwt]
        have h1 := hH c (Fin.cast (A.dim c).symm i)
        rwa [show k + nd ((T.U j T.σ₀).X c) = k + WeightFamilies.dimY D j by rw [A.dim c]] at h1)
  have heq : R.s w t 0 ^ (WeightFamilies.dimY D j + 1) * g =
      ∑ i : Fin (WeightFamilies.dimY D j), R.mon w t (Pi.single i 1) * fun y => H (e y).1 (Fin.cast (A.dim _).symm i) (e y).2.1 := by
    have hmon : ∀ i : Fin (WeightFamilies.dimY D j), R.mon w t (Pi.single i 1) = R.s w t i.succ := fun i => by
      unfold Rdg.mon
      rw [Finset.prod_eq_single i (fun b _ hb => by simp [hb]) (by simp)]
      simp
    funext y
    simp only [hmon, Finset.sum_apply, Pi.mul_apply, Pi.pow_apply, hs]
    have h1 := hsum _ _ (e y).2.2
    rw [show nd ((T.U j T.σ₀).X (e y).1) + 1 = WeightFamilies.dimY D j + 1 by rw [A.dim]] at h1
    rw [← Fl.h0, hgf, mul_comm, h1]
    refine Fintype.sum_equiv (finCongr (A.dim (e y).1)) _ _ fun a => ?_
    rw [Fl.hs]
    rfl
  rw [heq]
  exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨Pi.single i 1, _, by simp, hmem i, rfl⟩

end GlobalTheory.Shares.VanDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormVanishingLowCoeffMemLeadingAddDeepSpan
section
noncomputable section

namespace GlobalTheory.Containment

section Model

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
  MeasureTheory Topology GlobalTheory.Shares ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem exists_valBasis (X : Data E r) (G : Wt X.Ψ r) {δ m : ℕ} (xs : Fin δ → Frame X.Ψ r)
    (t : Fin m → Frame X.Ψ r → ℂ) (ht : ∀ k, X.IsBddSec G (t k))
    (hs : ∀ v : Fin δ → ℂ, ∃ a : Fin m → ℂ, ∀ j, ∑ k, a k * t k (xs j) = v j) :
    ∃ t' : Fin δ → Frame X.Ψ r → ℂ, (∀ k, X.IsBddSec G (t' k)) ∧ IsValBasisM X xs t' := by
  classical
  choose a ha using fun i : Fin δ => hs (Pi.single i 1)
  have hv : ∀ i j, (∑ k, a i k • t k) (xs j) = (Pi.single i (1 : ℂ) : Fin δ → ℂ) j := fun i j => by
    rw [← ha i j, Finset.sum_apply]; rfl
  have hsum : ∀ (c : Fin δ → ℂ) j, ∑ i, c i * (∑ k, a i k • t k) (xs j) = c j := fun c j => by
    simp only [hv]
    simp [Pi.single_apply]
  refine ⟨fun i => ∑ k, a i k • t k, fun i => ?_, fun v => ⟨v, hsum v⟩, fun c hc => ?_⟩
  · exact Finset.sum_induction _ (X.IsBddSec G) (fun _ _ h1 h2 => bdd_add X h1 h2) (bdd_zero X G)
      fun k _ => bdd_smul X _ (ht k)
  · funext j
    rw [← hsum c j, hc j]; rfl

theorem division_one (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (hm : Margins X Xa)
    (hfin : ∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (Xa.Fp + Xa.T • Xa.L),
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x)
    {m : ℕ} (t : Fin m → Frame X.Ψ r → ℂ) (ht : ∀ k, X.IsBddSec Xa.Fp (t k))
    (hs : ∀ v : Fin Fl.δ → ℂ, ∃ a : Fin m → ℂ, ∀ j, ∑ k, a k * t k (Fl.xs j) = v j)
    (f : Frame X.Ψ r → ℂ) (hf : f ∈ X.SSgt (Xa.Fp + Xa.T • Xa.L) Xa.c1)
    (cc : (Fin (nd X) → ℕ) → Fin m → ℂ)
    (hO : ∀ j, (fun z : V (nd X) => f (cpt X (Fl.xs j) z) -
      leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc (cpt X (Fl.xs j) z)) =O[𝓝 0] fun z => ‖z‖ ^ (Xa.T - nd X)) :
    ∃ h : (Fin (nd X) → ℕ) → Frame X.Ψ r → ℂ,
      (∀ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), h α ∈ X.SS (Xa.Fp + nd X • Xa.L)) ∧
      ∀ x ∈ X.dom, f x - leadM X Fl.s Fl.w0 t Xa.T (Xa.T - nd X) cc x =
        ∑ α ∈ Finset.Nat.antidiagonalTuple (nd X) (Xa.T - nd X), monoM X Fl.s α x * h α x := by
  obtain ⟨-, hm2, hm3, -, hcusp⟩ := hm
  have hPD := GlobalTheory.ClosedDiscontinuity.propDisc_closed r X
  have hFM := GlobalTheory.DriftCovolume.finMu_unconditional r X
  obtain ⟨x0, ho, FF, hFF, hmu⟩ := id hFM
  obtain ⟨hb, hint⟩ := DivStartStatement_holds r X Xa Fl hPD hFM m t ht x0 ho FF hFF f hf.1
    ((GlobalTheory.highModes_le_pow_w r X Xa f hf).2 x0 FF hFF hmu) cc
  obtain ⟨t', ht', hbas⟩ := exists_valBasis X Xa.Fp Fl.xs t ht hs
  have hl0 : ∀ x, leadM X Fl.s Fl.w0 t' Xa.T (Xa.T - nd X) 0 x = 0 := fun x => by simp [leadM]
  have hvan := GlobalTheory.vanS_of_isBigO r X Xa Fl (Xa.T - nd X) _ hb.1.1.continuousOn hO
  obtain ⟨h, hh, hx⟩ := divCoreStatement_holds r X Xa Fl hPD hFM hm2 hm3 (hcusp _)
    (by simpa using hcusp 0) (hcusp _) hfin _ t' ht' hbas x0 ho FF hFF _ (hcusp _ _ hb) hint 0
    (by simpa only [hl0, sub_zero] using hvan)
  exact ⟨h, fun α hα => hcusp _ _ (hh α hα), fun x hx' => by simpa only [hl0, sub_zero] using hx x hx'⟩

theorem division_one' (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (hm : Margins X Xa) {D Tn : ℕ}
    (hD : nd X = D) (hT : Xa.T = Tn)
    (hfin : ∃ (K : ℕ) (g : Fin K → Frame X.Ψ r → ℂ), ∀ f ∈ X.SS (Xa.Fp + Tn • Xa.L),
      ∃ c : Fin K → ℂ, ∀ x ∈ X.dom, f x = ∑ i, c i * g i x)
    {m : ℕ} (t : Fin m → Frame X.Ψ r → ℂ) (ht : ∀ k, X.IsBddSec Xa.Fp (t k))
    (hs : ∀ v : Fin Fl.δ → ℂ, ∃ a : Fin m → ℂ, ∀ j, ∑ k, a k * t k (Fl.xs j) = v j)
    (f : Frame X.Ψ r → ℂ) (hf : f ∈ X.SSgt (Xa.Fp + Tn • Xa.L) Xa.c1)
    (cc : (Fin D → ℕ) → Fin m → ℂ)
    (hO : ∀ j, (fun z : V (nd X) => f (cpt X (Fl.xs j) z) - ∑ α ∈ multiLt D (Tn - D), ∑ k,
      cc α k * (∏ q, Fl.s (Fin.cast hD.symm q) (cpt X (Fl.xs j) z) ^ α q) *
        Fl.w0 (cpt X (Fl.xs j) z) ^ (Tn - ∑ q, α q) * t k (cpt X (Fl.xs j) z))
        =O[𝓝 0] fun z => ‖z‖ ^ (Tn - D)) :
    ∃ h : (Fin D → ℕ) → Frame X.Ψ r → ℂ,
      (∀ α ∈ Finset.Nat.antidiagonalTuple D (Tn - D), h α ∈ X.SS (Xa.Fp + D • Xa.L)) ∧
      ∀ x ∈ X.dom, f x - ∑ α ∈ multiLt D (Tn - D), ∑ k,
        cc α k * (∏ q, Fl.s (Fin.cast hD.symm q) x ^ α q) * Fl.w0 x ^ (Tn - ∑ q, α q) * t k x =
        ∑ α ∈ Finset.Nat.antidiagonalTuple D (Tn - D), (∏ q, Fl.s (Fin.cast hD.symm q) x ^ α q) * h α x := by
  subst hD hT
  exact division_one X Xa Fl hm hfin t ht hs f hf cc hO

theorem eventually_diff (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {P : Frame X.Ψ r → ℂ}
    (hP : DifferentiableOn ℂ P X.dom) :
    ∀ᶠ z in 𝓝 (0 : V (nd X)), DifferentiableAt ℂ (fun z => P (cpt X x z)) z := by
  have h0 : (0 : V (nd X)) ∈ OmF X x := by
    show cpt X x 0 ∈ X.dom
    rw [GlobalTheory.LeadJets.cpt_zero]; exact hx
  filter_upwards [(OntoB.isOpen_OmF X x).mem_nhds h0] with z hz
  exact (OntoB.hol_comp X x hP).differentiableAt ((OntoB.isOpen_OmF X x).mem_nhds hz)

theorem division_all {κ : Type} (X : κ → Data E r) (Xa : ∀ k, ArchInM (X k)) (Fl : ∀ k, FlatM (X k) (Xa k))
    (hm : ∀ k, Margins (X k) (Xa k)) {D Tn : ℕ} (hD : ∀ k, nd (X k) = D) (hT : ∀ k, (Xa k).T = Tn)
    (hfin : ∀ k, ∃ (K : ℕ) (g : Fin K → Frame (X k).Ψ r → ℂ), ∀ f ∈ (X k).SS ((Xa k).Fp + Tn • (Xa k).L),
      ∃ c : Fin K → ℂ, ∀ x ∈ (X k).dom, f x = ∑ i, c i * g i x)
    {m : ℕ} (t : Fin m → ∀ k, Frame (X k).Ψ r → ℂ) (ht : ∀ i k, (X k).IsBddSec (Xa k).Fp (t i k))
    (hs : ∀ v : (Σ k, Fin (Fl k).δ) → ℂ, ∃ a : Fin m → ℂ, ∀ p, ∑ i, a i * t i p.1 ((Fl p.1).xs p.2) = v p)
    (f : ∀ k, Frame (X k).Ψ r → ℂ) (hf : ∀ k, f k ∈ (X k).SSgt ((Xa k).Fp + Tn • (Xa k).L) (Xa k).c1) :
    ∃ (cc : (Fin D → ℕ) → Fin m → ℂ) (h : ∀ k, (Fin D → ℕ) → Frame (X k).Ψ r → ℂ),
      (∀ k, ∀ α ∈ Finset.Nat.antidiagonalTuple D (Tn - D), h k α ∈ (X k).SS ((Xa k).Fp + D • (Xa k).L)) ∧
      ∀ k, ∀ x ∈ (X k).dom, f k x - ∑ α ∈ multiLt D (Tn - D), ∑ i,
        cc α i * (∏ q, (Fl k).s (Fin.cast (hD k).symm q) x ^ α q) * (Fl k).w0 x ^ (Tn - ∑ q, α q) * t i k x =
        ∑ α ∈ Finset.Nat.antidiagonalTuple D (Tn - D),
          (∏ q, (Fl k).s (Fin.cast (hD k).symm q) x ^ α q) * h k α x := by
  classical
  have hs0 : ∀ k j a, (Fl k).s a ((Fl k).xs j) = 0 := fun k j =>
    ((Fl k).S_eq _ ((Fl k).xs_mem j)).2 ⟨j, 1, one_mem _, nmat (X k) 0, GlobalTheory.LeadJets.nmat_zero_mem_Bor _, by
      rw [GlobalTheory.LeadJets.rmul_nmat_zero, GlobalTheory.LeadJets.lact_one]⟩
  obtain ⟨cc, hcc⟩ := GlobalTheory.JetsPure.main (Σ k, Fin (Fl k).δ) (Fin m) D Tn (Tn - D) (by omega)
    (fun p => nd (X p.1)) (fun p => finCongr (hD p.1))
    (fun p z => f p.1 (cpt (X p.1) ((Fl p.1).xs p.2) z))
    (fun p z => (Fl p.1).w0 (cpt (X p.1) ((Fl p.1).xs p.2) z))
    (fun p q z => (Fl p.1).s (Fin.cast (hD p.1).symm q) (cpt (X p.1) ((Fl p.1).xs p.2) z))
    (fun p i z => t i p.1 (cpt (X p.1) ((Fl p.1).xs p.2) z))
    (fun p => by
      have hx := (Fl p.1).xs_mem p.2
      refine (eventually_diff _ hx (hf p.1).1.1.1.1).and ((eventually_diff _ hx (Fl p.1).weightForm_vanishes.1.1.1.1).and
        (Filter.Eventually.and ?_ ?_))
      · exact Filter.eventually_all.2 fun q => eventually_diff _ hx ((Fl p.1).s_van _).1.1.1.1
      · exact Filter.eventually_all.2 fun i => eventually_diff _ hx (ht i p.1).1.1)
    (fun p => ⟨by simpa only [GlobalTheory.LeadJets.cpt_zero] using (Fl p.1).w0_ne p.2,
      fun q => by simpa only [GlobalTheory.LeadJets.cpt_zero] using hs0 p.1 p.2 _, (Fl p.1).coord p.2⟩)
    (by simpa only [GlobalTheory.LeadJets.cpt_zero] using hs)
  have hsk : ∀ k, ∀ v : Fin (Fl k).δ → ℂ, ∃ a : Fin m → ℂ, ∀ j, ∑ i, a i * t i k ((Fl k).xs j) = v j := by
    intro k v
    obtain ⟨a, ha⟩ := hs fun p => if hp : p.1 = k then v (Fin.cast (by rw [hp]) p.2) else 0
    exact ⟨a, fun j => by simpa using ha ⟨k, j⟩⟩
  choose h hh hx using fun k => division_one' (X k) (Xa k) (Fl k) (hm k) (hD k) (hT k) (hfin k)
    (fun i => t i k) (fun i => ht i k) (hsk k) (f k) (hf k) cc fun j => hcc ⟨k, j⟩
  exact ⟨cc, h, hh, hx⟩

end Model

section Record

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.RunIn GlobalTheory.Shares

theorem sp_le_span_fin {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} (R : Rdg X)
    (u : WeightFamilies.Wt D j) : ∃ (m : ℕ) (g : Fin m → R.Y → ℂ), R.sp u Set.univ ≤ Submodule.span ℂ (Set.range g) := by
  obtain ⟨m, b, hb⟩ := Module.Finite.exists_fin (R := B.KO) (M := B.Cusp j u)
  refine ⟨m, fun i => R.ev (X.inc u (b i)), Submodule.span_le.2 ?_⟩
  rintro _ ⟨F, -, rfl⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun B.KO).1 (hb ▸ Submodule.mem_top : F ∈ Submodule.span B.KO (Set.range b))
  simp only [map_sum, map_smul, R.ev_smul, SetLike.mem_coe]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem main : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (n : SecNorm (recB h.toLawsCore)) (R : Rdg (recPlusN h j hj n)) (e : R.Y ≃ DomPt T j), IsRdgU h j hj n R e → ∀ (N : ℕ) (wL wF : WeightFamilies.Wt D j) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (Tn : ℕ) (c1 : ℝ) (A : ArchAt h j w wF Tn c1) (t : Idx D j N → ℂ) (Fl : FlatAt h j A t) (δ : ℕ) (xs : Fin δ → R.Y) (en : Fin δ ≃ Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ), (∀ q, e (xs q) = ⟨(en q).1, ⟨(Fl.Fl (en q).1).xs (en q).2, (Fl.Fl (en q).1).xs_mem _⟩⟩) → (∀ k : ℕ, RdOnto h j (addL wF wL k)) → ∀ (CR c : ℝ), c1 = WeightFamilies.c1 D CR Tn c j → (∀ F ∈ WeightFamilies.MggK (recB h.toLawsCore) CR Tn c j (addL wF wL Tn), ∀ k : (T.U j T.σ₀).Comp, rdR h j F k ∈ ((T.U j T.σ₀).X k).SSgt (laR T j (addL wF wL Tn) k) c1) → ∀ (m : ℕ) (θ : Fin m → R.Y → ℂ), (∀ i, θ i ∈ R.sp wF Set.univ) → Submodule.span ℂ (Set.range (vals xs θ)) = ⊤ → R.sp (addL wF wL Tn) (WeightFamilies.MggK n.base CR Tn c j (addL wF wL Tn)) ≤ Submodule.span ℂ (Set.range (R.lead w t Tn (a0 D j Tn) θ)) ⊔ R.deep w t ((recPlusN h j hj n).wF0 wL wF) (a0 D j Tn) := by
  classical
  intro D T h j hj n R e hR N wL wF w Tn c1 A t Fl δ xs en hxs hOnto CR c _ hMg m θ hθ hspan
  have hsp := span_readings_components D T h j hj n R e hR
  have hwt : ∀ (k : (T.U j T.σ₀).Comp) (a : ℕ), laR T j (addL wF wL a) k = (A.Xa k).Fp + a • (A.Xa k).L := fun k a => by
    rw [A.hF, A.hL]
    exact (WtDic.weights_dictionary D T h j hj k).2.2.1 wF wL a
  choose θf hθf hθe using fun i => (hsp wF).1 (θ i) (hθ i)
  have hs : ∀ (i : Fin (WeightFamilies.dimY D j + 1)) (y : R.Y),
      R.s w t i y = ∑ k, t (i, k) * rdR h j (w k) (e y).1 (e y).2.1 := fun i y => by
    unfold Rdg.s
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun k _ => by rw [Pi.smul_apply, smul_eq_mul, hR.2]
  have hs0 : ∀ y, R.s w t 0 y = (Fl.Fl (e y).1).w0 (e y).2.1 := fun y => by rw [hs, Fl.h0]
  have hs1 : ∀ (q : Fin (WeightFamilies.dimY D j)) y,
      R.s w t q.succ y = (Fl.Fl (e y).1).s (Fin.cast (A.dim _).symm q) (e y).2.1 := fun q y => by
    rw [hs, Fl.hs]; rfl
  have hfin : ∀ k : (T.U j T.σ₀).Comp, ∃ (K : ℕ) (g : Fin K → Frame ((T.U j T.σ₀).X k).Ψ D.R.r → ℂ),
      ∀ f ∈ ((T.U j T.σ₀).X k).SS ((A.Xa k).Fp + Tn • (A.Xa k).L),
        ∃ c : Fin K → ℂ, ∀ x ∈ ((T.U j T.σ₀).X k).dom, f x = ∑ i, c i * g i x := by
    intro k
    obtain ⟨K, g, hg⟩ := sp_le_span_fin R (addL wF wL Tn)
    refine ⟨K, fun i x => if hx : x ∈ ((T.U j T.σ₀).X k).dom then g i (e.symm ⟨k, x, hx⟩) else 0, fun f hf => ?_⟩
    have hmem := (hsp (addL wF wL Tn)).2.1 _ _ (hOnto Tn) (Pi.single k f) fun k' => by
      by_cases hk : k' = k
      · subst hk
        rw [Pi.single_eq_same, hwt]; exact hf
      · rw [Pi.single_eq_of_ne hk, hwt]
        exact (A.mar k').2.2.2.2 _ _ (BoundedSectionAlgebra.bdd_zero _ _)
    obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hg hmem)
    refine ⟨cf, fun x hx => ?_⟩
    have h1 := congrFun hcf (e.symm ⟨k, x, hx⟩)
    rw [Equiv.apply_symm_apply, Finset.sum_apply] at h1
    simp only [dif_pos hx]
    simpa using h1.symm
  have hsurj : ∀ v : (Σ k : (T.U j T.σ₀).Comp, Fin (Fl.Fl k).δ) → ℂ, ∃ a : Fin m → ℂ, ∀ p,
      ∑ i, a i * θf i p.1 ((Fl.Fl p.1).xs p.2) = v p := by
    intro v
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1
      (hspan ▸ Submodule.mem_top : (fun q => v (en q)) ∈ Submodule.span ℂ (Set.range (vals xs θ)))
    refine ⟨a, fun p => ?_⟩
    obtain ⟨q, rfl⟩ := en.surjective p
    rw [← congrFun ha q, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    show _ = a i * θ i (xs q)
    rw [hθe, hxs]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨F, hF, rfl⟩
  obtain ⟨cc, g, hg, hx⟩ := division_all (T.U j T.σ₀).X A.Xa Fl.Fl A.mar A.dim A.hT hfin θf
    (fun i k => by rw [A.hF]; exact (hθf i k).1.1) hsurj (rdR h j F)
    (fun k => by rw [← hwt, A.hc]; exact hMg F hF k)
  have hdec : R.ev ((recPlusN h j hj n).inc (addL wF wL Tn) F) =
      ∑ α ∈ ReciprocityTheory.ChartRestriction.G.AR.multiLt (WeightFamilies.dimY D j) (Tn - WeightFamilies.dimY D j), ∑ i,
        cc α i • (R.mon w t α * R.s w t 0 ^ (Tn - ∑ q, α q) * θ i) +
      ∑ α ∈ Finset.Nat.antidiagonalTuple (WeightFamilies.dimY D j) (Tn - WeightFamilies.dimY D j),
        R.mon w t α * fun y => g (e y).1 α (e y).2.1 := by
    funext y
    rw [hR.2, sub_eq_iff_eq_add'.1 (hx (e y).1 (e y).2.1 (e y).2.2)]
    simp only [Rdg.mon, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Finset.prod_apply,
      Pi.pow_apply, smul_eq_mul, hs0, hs1, hθe, mul_assoc]
  show R.ev ((recPlusN h j hj n).inc (addL wF wL Tn) F) ∈ _
  rw [hdec]
  refine Submodule.add_mem_sup (Submodule.sum_mem _ fun α hα => Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨(⟨α, GlobalTheory.LeadJets.mem_multiLt.1 hα⟩, i), rfl⟩))
    (Submodule.sum_mem _ fun α hα => Submodule.subset_span
      ⟨α, _, Finset.Nat.mem_antidiagonalTuple.1 hα, ?_, rfl⟩)
  exact (hsp (addL wF wL (WeightFamilies.dimY D j))).2.1 _ _ (hOnto _) (fun k => g k α) fun k => by
    rw [hwt]; exact hg k α hα

end Record

end GlobalTheory.Containment
end
end

