import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0086
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0083
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0005
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsStabForm
import Development.AbelianVarietyTheory.Definitions.ThetaValues.FlatMemLatIffStdLat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0007
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0073
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0002
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0062
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.Bundle0087

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsScalarEvaluationsCuspFormsFiniteNet
section
noncomputable section

open Formalism.MainNotions.Gaps Formalism.MainNotions.Gaps.NetNorms NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory

private theorem linearIndependent_inclusion_of_le {K R ι : Type} [Field K] [AddCommGroup R] [Module K R]
    {A B : Submodule K R} (hAB : A ≤ B) (F : ι → A) (hF : LinearIndependent K F) :
    LinearIndependent K (fun i => (⟨F i, hAB (F i).2⟩ : B)) := by
  exact hF.map' (Submodule.inclusion hAB) (Submodule.ker_inclusion A B hAB)

theorem exists_scalar_readings_on_net : ∀ (D : D7) (T : Top D) (h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → 16 ≤ D.R.f → ∀ σ : T.Q.c.F →+* ℂ, GoodEmb T.Q.c σ → ∃ (n : ℕ) (ev : Fin n → ((recB h.toLawsCore).Cusp j w →ₛₗ[σ] ℂ)), (∀ F, ∃ y, (recB h.toLawsCore).supN j w σ F / 4 ≤ ‖ev y F‖) ∧ (∀ y F, ‖ev y F‖ ≤ (recB h.toLawsCore).supN j w σ F) ∧ Real.log (16 * (n : ℝ)) ≤ 1041 * Zb D large₂ ^ 3 ∧ ∀ (m : ℕ) (F : Fin m → (recB h.toLawsCore).Cusp j w), LinearIndependent T.Q.c.F F → LinearIndependent ℂ (fun i => fun y => ev y (F i)) := by
  intro D T h hG large₂ j hj w hP hL hr hf σ hσ
  classical
  obtain ⟨NN, -, hnet, hlog⟩ :=
    GlobalTheory.RunIn.exists_net_max_at_goodEmb D T h hG large₂ j hj w hP hL hr hf σ hσ
  have hind0 := GlobalTheory.cusp_readings_linearIndependent
  unfold ReciprocityTheory.ChartRestriction.G.PullbackSections.AlgInjAtSt at hind0

  obtain ⟨L, hLdef⟩ : ∃ L, L = lieFac (T.Q.Dw j) (xiR D) (wtA w) := ⟨_, rfl⟩
  have hL0 : 0 < L := hLdef ▸ lieFac_pos _ _ _

  have hpn : ∀ (k : (T.U j σ).Comp) (P : Frame ((T.U j σ).X k).Ψ D.R.r → ℂ) x,
      ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA w) w.n k) P x
        = ‖P x‖ * ((T.U j σ).X k).nfac (laU (T.U j σ) (wtA w) w.n k) x := fun _ _ _ => rfl
  have hnf : ∀ (k : (T.U j σ).Comp) x, 0 ≤ ((T.U j σ).X k).nfac (laU (T.U j σ) (wtA w) w.n k) x := by
    intro k x
    have h1 := GlobalTheory.NetNormExamples.pnorm_nonneg ((T.U j σ).X k) (laU (T.U j σ) (wtA w) w.n k)
      (fun _ => (1 : ℂ)) x
    rwa [hpn, norm_one, one_mul] at h1
  have hg : goodOf T.Q.c σ = σ := by rw [goodOf, if_pos hσ]

  have hsup : ∀ F : (recB h.toLawsCore).Cusp j w, (recB h.toLawsCore).supN j w σ F =
      L * supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) (rdU (T.U j σ) F.1) := by
    intro F
    dsimp only [recB, cutN]
    rw [if_pos hj]
    dsimp only [Formalism.L2.Pj.Core.Ns, supC]
    rw [hg, hLdef]

  have hhol : ∀ F : (recB h.toLawsCore).Cusp j w,
      rdU (T.U j σ) F.1 ∈ holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) := by
    intro F
    have hC : F.1 ∈ cusp (T.Q.Xo j) T.Q.c (T.U j) (wtA w) w.n := (Submodule.mem_inf.mp F.2).1
    exact ((mem_cusp _ _ _ _ _ _).mp hC).2 σ hσ

  let pt : Fin NN.card → FPt (T.U j σ).X := fun y => (NN.equivFin.symm y).1
  have hsurj : ∀ p ∈ NN, ∃ y, pt y = p := fun p hp =>
    ⟨NN.equivFin ⟨p, hp⟩, by simp only [pt, Equiv.symm_apply_apply]⟩
  let a : Fin NN.card → ℝ := fun y =>
    L * ((T.U j σ).X (pt y).1).nfac (laU (T.U j σ) (wtA w) w.n (pt y).1) (pt y).2
  have ha : ∀ y, 0 ≤ a y := fun y => mul_nonneg hL0.le (hnf _ _)

  let ev : Fin NN.card → ((recB h.toLawsCore).Cusp j w →ₛₗ[σ] ℂ) := fun y =>
    { toFun := fun F => (a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2
      map_add' := fun F G => by
        show (a y : ℂ) * rdU (T.U j σ) (F.1 + G.1) (pt y).1 (pt y).2 =
          (a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2 + (a y : ℂ) * rdU (T.U j σ) G.1 (pt y).1 (pt y).2
        rw [map_add, Pi.add_apply, Pi.add_apply, mul_add]
      map_smul' := fun c F => by
        show (a y : ℂ) * rdU (T.U j σ) (c • F.1) (pt y).1 (pt y).2 =
          σ c • ((a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2)
        rw [LinearMap.map_smulₛₗ, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
        ring }
  have hev : ∀ y F, ev y F = (a y : ℂ) * rdU (T.U j σ) F.1 (pt y).1 (pt y).2 := fun _ _ => rfl
  have hnorm : ∀ y F, ‖ev y F‖ =
      L * ((T.U j σ).X (pt y).1).pnorm (laU (T.U j σ) (wtA w) w.n (pt y).1)
        (rdU (T.U j σ) F.1 (pt y).1) (pt y).2 := by
    intro y F
    rw [hev, norm_mul, Complex.norm_of_nonneg (ha y), hpn]
    simp only [a]
    ring
  refine ⟨NN.card, ev, ?_, ?_, ?_, ?_⟩
  ·
    intro F
    obtain ⟨p, hp, hb⟩ := hnet _ (hhol F)
    obtain ⟨y, rfl⟩ := hsurj p hp
    refine ⟨y, ?_⟩
    rw [hnorm, hsup]
    have := mul_le_mul_of_nonneg_left hb hL0.le
    linarith
  ·
    intro y F
    rw [hnorm, hsup]
    exact mul_le_mul_of_nonneg_left
      (GlobalTheory.NetNormExamples.pnorm_le_supN (T.U j σ) _ (hhol F) (pt y)) hL0.le
  · exact hlog
  ·
    intro m F hF
    have hF' := linearIndependent_inclusion_of_le (B := T.C j w) inf_le_left F hF
    have hind := hind0 D T h j hj w σ hσ m _ hF'
    rw [Fintype.linearIndependent_iff] at hind ⊢
    intro g hgz i
    refine hind g ?_ i
    show ∑ i, g i • rdU (T.U j σ) (F i).1 = 0
    obtain ⟨Q, hQ⟩ : ∃ Q, Q = ∑ i, g i • rdU (T.U j σ) (F i).1 := ⟨_, rfl⟩
    rw [← hQ]
    have hQmem : Q ∈ holSub (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) := by
      rw [hQ]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hhol (F i))
    have hval : ∀ y, (a y : ℂ) * Q (pt y).1 (pt y).2 = 0 := by
      intro y
      have h1 := congrFun hgz y
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hev] at h1
      rw [hQ, Finset.sum_apply, Finset.sum_apply, Finset.mul_sum, ← h1]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, Pi.smul_apply, smul_eq_mul]
      ring
    obtain ⟨p, hp, hb⟩ := hnet Q hQmem
    obtain ⟨y, rfl⟩ := hsurj p hp
    have h0 : ((T.U j σ).X (pt y).1).pnorm (laU (T.U j σ) (wtA w) w.n (pt y).1) (Q (pt y).1) (pt y).2 = 0 := by
      have hn := congrArg (‖·‖) (hval y)
      simp only [norm_mul, Complex.norm_of_nonneg (ha y), norm_zero] at hn
      simp only [a] at hn
      rw [hpn]
      have h2 : L * (‖Q (pt y).1 (pt y).2‖ *
          ((T.U j σ).X (pt y).1).nfac (laU (T.U j σ) (wtA w) w.n (pt y).1) (pt y).2) = 0 := by
        rw [← hn]; ring
      exact (mul_eq_zero.mp h2).resolve_left hL0.ne'
    have hS : supN (T.U j σ).X (laU (T.U j σ) (wtA w) w.n) Q ≤ 0 := by
      rw [h0, mul_zero] at hb
      exact hb
    funext k x
    by_cases hx : x ∈ ((T.U j σ).X k).dom
    · show Q k x = 0
      apply GlobalTheory.NetNormExamples.eq_zero_of_pnorm ((T.U j σ).X k) (laU (T.U j σ) (wtA w) w.n k) _ hx
      exact le_antisymm
        ((GlobalTheory.NetNormExamples.pnorm_le_supN (T.U j σ) _ hQmem ⟨k, ⟨x, hx⟩⟩).trans hS)
        (GlobalTheory.NetNormExamples.pnorm_nonneg _ _ _ _)
    · show Q k x = 0
      rw [hQ, Finset.sum_apply, Finset.sum_apply]
      refine Finset.sum_eq_zero fun i _ => ?_
      have hz : rdU (T.U j σ) (F i).1 k x = 0 := by
        simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, dif_neg hx]
      rw [Pi.smul_apply, Pi.smul_apply, hz, smul_zero]

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGeneratorReadingNeZeroAtFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaGenerator_reading_ne_zero_at_frame : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → r ≤ n → 3 * Formalism.L2.Pj.DF Dw a + 2 ≤ l.M → ∀ (_ : StarRing (𝓞 E)) (nab : NabV Xo c), IsNab Xo c nab → ∀ k, ∀ x ∈ (U.X k).dom, ∃ f ∈ thGen Xo c nab a n, Formalism.L2.PjFree.rdU U f k x ≠ 0 := by
  first | exact @GlobalTheory.ThetaNoZero.exists_thGen_rdU_ne_zero | exact GlobalTheory.ThetaNoZero.exists_thGen_rdU_ne_zero | (intros; apply GlobalTheory.ThetaNoZero.exists_thGen_rdU_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogSupNormThetaGeneratorLe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem log_sup_theta_generator_le : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → ∀ (x : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F), P ∈ harmA T.Q.c (wtA w) w.n → ∀ f : T.R j, IsThRule (T.Q.Xo j) T.Q.c (T.nab j) x P f → ∀ (σ : T.Q.c.F →+* ℂ) (ℓ : ℝ), 0 ≤ ℓ → l1At σ P ≤ Real.exp ℓ → Real.log (T.Ns j w σ f) ≤ ℓ + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L := by
  intro hCI D T hT hG large₂ j hj w hPR hL hr hLP x P hP f hf σ ℓ hℓ hp1
  obtain ⟨inst, hnab⟩ := hT.nabPin j hj
  have hunf : IsUnf (T.U j (goodOf T.Q.c σ)) := hT.toLawsCore.unf j hj _ (goodEmb_goodOf T.Q.c σ)
  obtain ⟨hfd, hrdl, hrd1, hf1, hr1, hxi, hDF, habs, hcU, hlie, -, -, -, hl1⟩ :=
    GlobalTheory.T.unitaryDatumNumbers_for_supBounds D T hT j hj w
  obtain ⟨-, hLrd, -, -, hLf, -, -, hLa, hLn⟩ := id hPR
  have hL0 : (0 : ℝ) < large₂.sc.L := by linarith
  have ha0 : (0 : ℝ) ≤ absA w := by rw [habs]; exact Nat.cast_nonneg _
  have hσg : GoodEmb T.Q.c (goodOf T.Q.c σ) := goodEmb_goodOf T.Q.c σ
  have hNs : T.Ns j w σ f = lieFac (T.Q.Dw j) (xiR D) (wtA w) *
      supN (T.U j (goodOf T.Q.c σ)).X (laU (T.U j (goodOf T.Q.c σ)) (wtA w) w.n)
        (rdU (T.U j (goodOf T.Q.c σ)) f) := rfl
  have hS0 : 0 ≤ supN (T.U j (goodOf T.Q.c σ)).X (laU (T.U j (goodOf T.Q.c σ)) (wtA w) w.n)
      (rdU (T.U j (goodOf T.Q.c σ)) f) := ENNReal.toReal_nonneg
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [hNs, ← h0, mul_zero, Real.log_zero]
    positivity

  have hC : f ∈ T.C j w := ReciprocityTheory.ChartRestriction.G.PullbackSections.PfTies1.cuspTie D T hT j hj w hLP x P hP f hf
  obtain ⟨k, xf, -, hort, hSle, hla, hlog⟩ :=
    GlobalTheory.T.cuspForm_halfSup_at_orthonormalFrame_firstMin D T hT hG large₂ j hj w hPR hL hr hLP (goodOf T.Q.c σ) hσg f hC hpos
  have hlam0 : 0 < Real.sqrt (((T.U j (goodOf T.Q.c σ)).X k).firstMinimumSq xf.1) := Real.sqrt_pos.mpr hla
  have hlam2 : Real.sqrt (((T.U j (goodOf T.Q.c σ)).X k).firstMinimumSq xf.1) ^ 2 =
      ((T.U j (goodOf T.Q.c σ)).X k).firstMinimumSq xf.1 := Real.sq_sqrt hla.le

  have hU := GlobalTheory.T.thetaGenerator_pointwise_bound_orthonormal_frame hCI _ _ _ _ (T.Q.Xo j) T.Q.c (goodOf T.Q.c σ) D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j (goodOf T.Q.c σ))) ((Formalism.L2.PjFree.goodEmb_iff _).mpr hσg)
    ((Formalism.L2.PjFree.isUnf_ofPj _).mpr hunf) hr1 (2 * xiR D) (by linarith)
    (fun k τ => hcU _ hσg k τ) (wtA w) w.n (dom_wtA w) inst (T.nab j) hnab x P hP f hf k xf hort
    _ hlam0 hlam2.le
  rw [hfd] at hU
  have key := GlobalTheory.log_exp_mul_le_of_generator_sup_bound D.R.f D.R.r w.n
    (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w)) large₂.sc.L ℓ (absA w) (rdE D.host.E)
    (Real.sqrt (((T.U j (goodOf T.Q.c σ)).X k).firstMinimumSq xf.1)) (2 * xiR D) 1 _ _ (l1At σ P)
    hL hf1 hr1 hr (by rw [habs]; exact_mod_cast hDF) (by rw [habs]; exact hLa) hLn hLf hrd1
    (by rw [hrdl]; exact hLrd) hlam0 (by rw [hlam2]; exact hlog) (by linarith) hℓ
    (by unfold l1At; exact Finset.sum_nonneg fun _ _ => norm_nonneg _) hp1 zero_le_one
    (Real.one_le_exp (by positivity)) hS0 hSle (by rw [one_mul, ← hl1 _ σ P]; exact hU)
  rw [hNs, hlie]
  exact key

end GlobalTheory.RunIn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormShortGeneratorEvalLeOrthonormalFrameStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_short_generator_eval_le_orthonormal_frame : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (r : ℕ) (U : Formalism.L2.PjFree.Unf Xo c σ r), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → 1 ≤ r → ∀ t : ℝ, 0 < t → (∀ k τ, (U.X k).c τ = t) → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ), Dom a n → r ≤ n → ∀ d : DeltaDat Xo c n, d.IsLev → 0 < d.pd → l.A = 1 → d.l₂.A = 1 → (∃ _ : StarRing (𝓞 E), IsNab d.Xo₂ d.c₂ d.nab₂) → (∃ ph ψ x₀, d.PhiPin ph ψ x₀) → UnitC d → ∀ (Λ : GenLat E n) (N : ℕ) (x0 : Fin n → Dw.La) (P : MvPolynomial (LtN Dw n) c.F) (f : Rul Xo c), Λ.Unimod → Λ.TrivAt d.l₂.M → Λ.LevOK N d.l₂.M → (∃ β : c.F, β ≠ 0 ∧ BetaIs (Dw := Dw) c Λ β ∧ BetaAbs (Dw := Dw) c Λ β) → P ∈ harmL c Λ a → IsShortRule Xo c d Λ N x0 P f → ∀ k (x : (U.X k).dom), (U.X k).IsOrtho x.1 → ∀ lam : ℝ, 0 < lam → lam ^ 2 ≤ (U.X k).firstMinimumSq x.1 → ‖Formalism.L2.PjFree.toC (evR Xo c f (U.un k x))‖ ≤ (d.pd : ℝ) ^ (fdeg E * r * n) * ((∑ m ∈ P.support, ‖σ (P.coeff m)‖) * (Real.pi * Real.exp 1 * t * (Formalism.L2.Pj.DF Dw a : ℕ)) ^ (((Formalism.L2.Pj.DF Dw a : ℕ) : ℝ) / 2) * Real.sqrt 2 * (1 + 4 * Real.sqrt (2 * (fdeg E * r : ℕ) * n) * (2 * (fdeg E : ℝ) ^ ((3 : ℝ) / 2) * n ^ 2 * rdE E) / (Real.sqrt Real.pi * lam)) ^ (fdeg E * r * n)) := by
  first | exact @GlobalTheory.Dict.ShortPoint.norm_evR_le | exact GlobalTheory.Dict.ShortPoint.norm_evR_le | (intros; apply GlobalTheory.Dict.ShortPoint.norm_evR_le <;> assumption)
end

