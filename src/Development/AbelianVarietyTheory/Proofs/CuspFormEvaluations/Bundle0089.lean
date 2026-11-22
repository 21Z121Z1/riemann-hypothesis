import Mathlib
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0088
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0008
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0009
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0007
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0015
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0014
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0003
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0062
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0073
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0084
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SumLeFinsumOfSurjectsOntoFinset
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ThConst
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0001
import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0010
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsScalarEvaluationsCuspFormsFiniteNetStatement
section
open Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.NetNorms NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scalar_evaluations_cusp_forms_finite_net : ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (n : ℕ) (ev : Fin n → ((recB h.toLawsCore).Cusp j w →ₛₗ[σ] ℂ)), (∀ F, ∃ y, (recB h.toLawsCore).supN j w σ F / 4 ≤ ‖ev y F‖) ∧ (∀ y F, ‖ev y F‖ ≤ (recB h.toLawsCore).supN j w σ F) ∧ Real.log (16 * (n : ℝ)) ≤ 1041 * Zb D large₂ ^ 3 ∧ ∀ (m : ℕ) (F : Fin m → (recB h.toLawsCore).Cusp j w), LinearIndependent T.Q.c.F F → LinearIndependent ℂ (fun i => fun y => ev y (F i)) := by
  first | exact @GlobalTheory.exists_scalar_readings_on_net | exact GlobalTheory.exists_scalar_readings_on_net | (intros; apply GlobalTheory.exists_scalar_readings_on_net <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGeneratorReadingNeZeroAllFrames
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem exists_theta_ne_zero_record : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), D.R.r ≤ w.n → 3 * WeightAlgebra.DF w + 2 ≤ T.Q.l.M → ∀ (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ k, ∀ x ∈ ((T.U j σ).X k).dom, ∃ f ∈ T.th j w, rdU (T.U j σ) f k x ≠ 0 := by
  intro hC D T h j hj w hn hM σ hσ k x hx
  obtain ⟨_, _, _, _, hr1, hxi, hDF, _, hc, _⟩ := GlobalTheory.T.unitaryDatumNumbers_for_supBounds D T h j hj w
  obtain ⟨st, hnab⟩ := h.nabPin j hj
  obtain ⟨f, hf, hne⟩ := GlobalTheory.T.exists_thetaGenerator_reading_ne_zero_at_frame hC _ _ _ _ (T.Q.Xo j) T.Q.c σ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
    ((Formalism.L2.PjFree.goodEmb_iff σ).2 hσ) ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.toLawsCore.unf j hj σ hσ)) hr1
    (2 * xiR D) (mul_pos two_pos hxi) (hc σ hσ) (wtA w) w.n (dom_wtA w) hn (by omega) st (T.nab j) hnab k x hx
  refine ⟨f, hf, ?_⟩
  rwa [Formalism.L2.PjFree.rdU_ofPj] at hne

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogSupNormShortThetaGeneratorLe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

set_option maxHeartbeats 800000 in

theorem log_sup_short_generator_le : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (g : T.R j), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j w.n).l₂.M → Λ.LevOK N (T.dδ j w.n).l₂.M → AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x0 → P ∈ harmL T.Q.c Λ (wtA w) → IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 P g → g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → ∀ (σ : T.Q.c.F →+* ℂ) (ℓ : ℝ), 0 ≤ ℓ → l1At σ P ≤ Real.exp ℓ → Real.log (T.Ns j w σ g) ≤ ℓ + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L := by
  intro hCh D T hT hG large₂ j hj w hRows hL hr hLast hSh hA Λ N x0 P g hU hTb hTM hLev hX hP hS hg σ ℓ hℓ hl1
  obtain ⟨hfd, hrd, hrd1, hf1, hr1, hxi, hDF, habs, hc, hlie, hlA, hpde, hpde', hl1g⟩ := GlobalTheory.T.unitaryDatumNumbers_for_supBounds D T hT j hj w
  have hRw := hRows
  obtain ⟨-, hlrd, -, -, hlf, hlp, hlp', hlDF, hln⟩ := hRows
  set σ' := goodOf T.Q.c σ with hσ'
  have hgood : GoodEmb T.Q.c σ' := goodEmb_goodOf _ σ
  have hgC : g ∈ T.C j w :=
    hSh.8 j hj (wtA w) w.n (dom_wtA w) hLast (dom_wtA w) hLast ⟨hg, Λ, N, x0, P, hU, hTb, hTM, hLev, hX, hP, hS⟩
  obtain ⟨Cls, _, _, δ, gdet, hcmp⟩ := hSh.6 j hj w.n
  have hUC : GlobalTheory.Dict.UnitC (T.dδ j w.n) := FiniteOrderRule.unitC_of_cmp _ _ _ _ _ _ _ _ Cls δ gdet hcmp
  obtain ⟨p, hp, hpd⟩ := hSh.4
  have hpdw : (T.dδ j w.n).pd = p := hpd j hj w.n
  have hp0 : 0 < p := by rcases hp with rfl | rfl <;> assumption
  have hlogp : Real.log p ≤ large₂.sc.L := by rcases hp with rfl | rfl <;> assumption
  obtain ⟨ph, ψ, xψ, -, hpin, -⟩ := hSh.5 j hj w.n hr
  have hunf : IsUnf (T.U j σ') := hT.unf j hj σ' hgood
  have hNs : T.Ns j w σ g = lieFac (T.Q.Dw j) (xiR D) (wtA w) *
      supN (T.U j σ').X (laU (T.U j σ') (wtA w) w.n) (rdU (T.U j σ') g) := rfl
  rw [hNs, hlie]
  set S := supN (T.U j σ').X (laU (T.U j σ') (wtA w) w.n) (rdU (T.U j σ') g) with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; unfold supN; exact ENNReal.toReal_nonneg
  have hL0 : (0:ℝ) ≤ large₂.sc.L := by linarith
  have ha0 : (0:ℝ) ≤ absA w := by rw [habs]; positivity
  rcases hS0.eq_or_lt with hS00 | hSpos
  · rw [← hS00, mul_zero, Real.log_zero]
    positivity
  obtain ⟨k, xf, -, hortho, hSle, hla, hlog⟩ :=
    GlobalTheory.T.cuspForm_halfSup_at_orthonormalFrame_firstMin D T hT hG large₂ j hj w hRw hL hr hLast σ' hgood g hgC hSpos
  set lam := Real.sqrt (((T.U j σ').X k).firstMinimumSq xf.1) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr hla
  have hlam2 : lam ^ 2 = ((T.U j σ').X k).firstMinimumSq xf.1 := Real.sq_sqrt hla.le
  have hv := GlobalTheory.T.norm_short_generator_eval_le_orthonormal_frame hCh D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c σ' D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ')) ((Formalism.L2.PjFree.goodEmb_iff σ').mpr hgood)
    ((Formalism.L2.PjFree.isUnf_ofPj _).mpr hunf) hr1 (2 * xiR D) (by linarith) (hc σ' hgood) (wtA w) w.n
    (dom_wtA w) hr (T.dδ j w.n) (hSh.2 j hj w.n) (by rw [hpdw]; exact hp0) hlA hA (hSh.3 j hj w.n)
    ⟨ph, ψ, xψ, hpin⟩ hUC Λ N x0 P g hU hTM hLev (hSh.1 j hj w.n (hT.kPsi j hj) Λ hU hTb) hP hS
    k xf hortho lam hlam0 hlam2.le
  have hp1eq : (∑ m ∈ P.support, ‖σ' (P.coeff m)‖) = l1At σ P := hl1g _ σ P
  rw [hfd, hp1eq] at hv
  have hcle : ((T.dδ j w.n).pd : ℝ) ^ (D.R.f * D.R.r * w.n) ≤
      Real.exp (D.R.f * D.R.r * w.n * large₂.sc.L) := by
    rw [hpdw]
    have hp' : (0:ℝ) < p := by exact_mod_cast hp0
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hp']
    apply Real.exp_le_exp.mpr
    push_cast
    have hfrn : (0:ℝ) ≤ D.R.f * D.R.r * w.n := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlogp hfrn]
  have hp1 : 0 ≤ l1At σ P := by unfold l1At; exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  exact GlobalTheory.log_exp_mul_le_of_generator_sup_bound D.R.f D.R.r w.n (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w))
    large₂.sc.L ℓ (absA w) (rdE D.host.E) lam (2 * xiR D) _ S _ (l1At σ P) hL hf1 hr1 hr
    (by rw [habs]; exact_mod_cast hDF) (by rw [habs]; exact hlDF) hln hlf hrd1 (by rw [hrd]; exact hlrd)
    hlam0 (by rw [hlam2]; exact hlog) (by linarith) hℓ hp1 hl1 (by positivity) hcle hS0 hSle hv

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogSupNormThetaGeneratorLeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_supNorm_thetaGenerator_le : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → ∀ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n → ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f → ∀ (σ : T.Q.c.F →+* ℂ) (ℓ : ℝ), 0 ≤ ℓ → l1At σ P ≤ Real.exp ℓ → Real.log (T.Ns j w σ f) ≤ ℓ + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L := by
  first | exact @GlobalTheory.RunIn.log_sup_theta_generator_le | exact GlobalTheory.RunIn.log_sup_theta_generator_le | (intros; apply GlobalTheory.RunIn.log_sup_theta_generator_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.SumLeFinsumOfSurjectsOntoFinsetStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.AnVal GlobalTheory.BlockTh GlobalTheory.EtaAn
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedThetaRule_archimedeanValue_bound : ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)] (σ : c.F →+* ℂ) (r : ℕ) (U : Unf Xo c σ r) (k : U.Comp) (x : (U.X k).dom) (xR : ℝ) (nab : NabV Xo c), IsNab Xo c nab → GoodEmb c σ → IsUnf U → FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (U.un k x) → (U.X k).IsOrtho x.1 → (∀ τ : E →+* ℂ, ‖τ (U.X k).ξ0‖ = xR) → ∀ α : 𝓞 E, α * H.bar α = (l.M : 𝓞 E) → l.Mb = Ideal.span {H.bar α} → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (P₁ : MvPolynomial (LtN Dw n) c.F), P₁ ∈ harmA c a n → IsBlockProd P₁ → ∀ (R0 : ℝ) (m : ℕ), RunOK E r P₁.totalDegree l.M R0 m → (Dw.p ≤ m ∨ Dw.q ≤ m) → ∃ (T : I2.PT E) (Pr : I2.Par T P₁.totalDegree), T.r = r ∧ Pr.q = l.M ∧ Pr.m = m ∧ Pr.ph = I2.phiFD (U.X k) (I2.th (E := E) l.M R0) x.1 ∧ ∀ f : (Fin n → LevQ Dw l) → Rul Xo c, (∀ q, IsThRule Xo c nab (fun b => levRep (q b)) P₁ (f q)) → (2 * xR / l.M) ^ P₁.totalDegree * Pr.Jbound n ≤ ∑ᶠ q, ‖toC (evR Xo c (f q) (U.un k x))‖ ^ 2 := by
  first | exact @GlobalTheory.ThetaLower.thetaRule_sum_lower | exact GlobalTheory.ThetaLower.thetaRule_sum_lower | (intros; apply GlobalTheory.ThetaLower.thetaRule_sum_lower <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaGeneratorsNoCommonZeroOfChartIndependence
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory

theorem noCommonZero_of_chartIndep : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → NoCommonZeroSt := by
  intro hC D T h j hj w hn _hlast hM _hα σ hσ k x hx

  obtain ⟨-, -, -, -, hr1, hxi, hDF, -, hc, -⟩ := GlobalTheory.T.unitaryDatumNumbers_for_supBounds D T h j hj w

  obtain ⟨st, hnab⟩ := h.nabPin j hj

  obtain ⟨f, hf, hne⟩ := GlobalTheory.T.exists_thetaGenerator_reading_ne_zero_at_frame hC _ _ _ _ _ _ σ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
    ((Formalism.L2.PjFree.goodEmb_iff σ).mpr hσ) ((Formalism.L2.PjFree.isUnf_ofPj _).mpr (h.unf j hj σ hσ)) hr1
    (2 * xiR D) (by linarith) (fun k τ => hc σ hσ k τ) (wtA w) w.n (dom_wtA w) hn (by omega) st (T.nab j)
    hnab k x hx
  exact ⟨f, hf, by rwa [Formalism.L2.PjFree.rdU_ofPj] at hne⟩

end GlobalTheory
end

