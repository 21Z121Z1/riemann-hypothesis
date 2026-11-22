import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.PoincarePointwiseStatement
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0046
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0048
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0043
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0040
import Development.AbelianVarietyTheory.Definitions.UpperBounds.PhRec
import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0014
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.CurvatureMarginsDefiniteCase
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares

theorem margins_of_definite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X), X.p0 = 0 → Nonempty X.Ψ → (∀ x, Xa.ps0 x = 0) → IsStrictDom X Xa.L → (∀ τ (a b : Fin r), a ≤ b → (Xa.Fp - kapW X - nd X • Xa.L) τ b ≤ (Xa.Fp - kapW X - nd X • Xa.L) τ a) → Margins X Xa := by
  intro E _ _ _ r X Xa h0 _ hps _ hgap
  have hA : ∀ (m : ℝ) x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      m * leviRh X x0 z ξ ≤ leviO X x0 (phla X Xa.Fp) z ξ - leviDens X x0 z ξ -
        (nd X : ℝ) * leviO X x0 (phla X Xa.L) z ξ := fun m x0 ho z hz ξ => by
    rw [← IW.leviM_comb X x0 ho hz]
    exact (GlobalTheory.CurvMarginClosed.curv_and_margin_closed (E := E)).2 r X _ m
      (fun τ i j a _ => hgap τ i j a) (fun τ i j _ b => hgap τ i j b)
      (fun τ i j a _ => absurd a (by omega)) x0 ho z hz ξ
  have hB : ∀ x0, IsOrth X x0 → ∀ z ∈ OmF X x0, ∀ ξ : Fin (nd X) → ℂ,
      0 ≤ leviO X x0 (phla X Xa.L) z ξ := fun x0 ho z hz ξ => by
    by_cases hξ : ξ = 0
    · subst hξ; simp [leviO, leviM, leviV]
    · exact (Xa.posL x0 (IW.orth_mem_dom X x0 ho) z hz ξ hξ).le
  have hP : ∀ x0 z ξ, leviO X x0 Xa.ps0 z ξ = 0 := fun x0 z ξ => by
    simp only [leviO, leviM, hps]
    rw [RgC.leviV_const, Complex.zero_re]
  refine ⟨⟨_, _, lt_add_one _, lt_add_one _, fun t _ x0 ho z hz ξ => ?_⟩,
    ⟨_, _, lt_add_one _, lt_add_one _, fun x0 ho z hz ξ => ?_⟩, hB, ⟨0, fun x _ => (hps x).le⟩,
    fun k P hP => ⟨hP, fun ξ hξ =>
      (GlobalTheory.PoincareSeriesCompare.not_isIso_of_definite X (Or.inl h0) ξ hξ).elim⟩⟩
  · rw [hP, mul_zero, add_zero]
    exact hA _ x0 ho z hz ξ
  · exact (hA _ x0 ho z hz ξ).trans
      (sub_le_self _ (mul_nonneg (Nat.cast_nonneg _) (hB x0 ho z hz ξ)))

end GlobalTheory.Shares
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExpLeOfNegLogSqrtLe
section
noncomputable section

namespace GlobalTheory.BigRec

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem pnorm_pos_of_ne_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (la : ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r)
    (P : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ) {x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom)
    (hP : P x ≠ 0) : 0 < X.pnorm la P x := by
  have hd : ∀ τ i, ReciprocityTheory.ChartRestriction.G.FD.dmin X.Gm x τ i ≠ 0 := by
    intro τ i h0
    have := (hx τ).2 i
    rw [h0] at this
    simp at this
  refine mul_pos (norm_pos_iff.2 hP) (Finset.prod_pos fun τ _ => Finset.prod_pos fun i _ => ?_)
  exact Real.rpow_pos_of_pos (norm_pos_iff.2 (div_ne_zero (hd _ _) (hd _ _))) _

theorem exp_le_of_neg_log_sqrt_le {S a b : ℝ} (hS : 0 < S) (h : -Real.log (Real.sqrt S) ≤ a + b) :
    Real.exp (-(2 * b)) ≤ Real.exp (2 * a) * S := by
  rw [Real.log_sqrt hS.le] at h
  calc Real.exp (-(2 * b)) ≤ Real.exp (2 * a + Real.log S) := Real.exp_le_exp.2 (by linarith)
    _ = Real.exp (2 * a) * S := by rw [Real.exp_add, Real.exp_log hS]

section Gen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_rdU_ne_zero {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) {N : ℕ} (w : Fin N → Rul Xo c)
    (hw : NoCommonZero Xo c w) (k : U.Comp) {x : ReciprocityTheory.ChartRestriction.G.FD.Frame (U.X k).Ψ r} (hx : x ∈ (U.X k).dom) :
    ∃ m, rdU U (w m) k x ≠ 0 := by
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  obtain ⟨m, hm⟩ := hw (CAt σ) (U.un k ⟨x, hx⟩)
  refine ⟨m, ?_⟩
  have e : rdU U (w m) k x = toC (evR Xo c (w m) (U.un k ⟨x, hx⟩)) := dif_pos hx
  rw [e]
  exact hm

theorem model_ineq_of_log_bound {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (xR : ℝ) (σ : c.F →+* ℂ)
    {N N' : ℕ} (i : ℕ) (w : Fin N → Rul Xo c) (e : Fin (N' + 1) ≃ Fin N) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (th tableLineDegreeFive DF tableLineDegreeTwo cc : ℝ) (hσ : GoodEmb c σ)
    (hI : I2AtFramePoints U xR (fun m => w (e m)) (a, n) th tableLineDegreeFive DF cc) (hw : NoCommonZero Xo c w)
    (k : (U σ).Comp) (eW : ReciprocityTheory.ChartRestriction.G.FD.Wt ((U σ).X k).Ψ r)
    (et : ReciprocityTheory.ChartRestriction.G.FD.Frame ((U σ).X k).Ψ r → ℂ)
    (het : ∀ x ∈ ((U σ).X k).dom, ((U σ).X k).pnorm eW et x ≤
      Real.exp (-(i : ℝ) * (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((U σ).X k) th x - tableLineDegreeTwo))) :
    ReciprocityTheory.ChartRestriction.G.AR.Up.InterpolationModelInequalities ((U σ).X k) (laU (U σ) a n k) eW (fun m => rdU (U σ) (w m) k) et cc i
      (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((U σ).X k) th) := by
  refine ⟨⟨Real.exp (2 * (tableLineDegreeFive * DF)) * lieFac Dw xR a ^ 2, fun x hx => ?_⟩,
    Real.exp (2 * (i * tableLineDegreeTwo)), fun x hx => ?_⟩
  · have h1 := hI σ hσ k x hx
    have hs : ∑ m, recNrm (U σ) xR a n (w (e m)) k x ^ 2 =
        lieFac Dw xR a ^ 2 * ∑ m, ((U σ).X k).pnorm (laU (U σ) a n k) (rdU (U σ) (w m) k) x ^ 2 := by
      rw [Finset.mul_sum, ← e.sum_comp]
      exact Finset.sum_congr rfl fun m _ => by rw [recNrm, mul_pow]
    have hpos : 0 < ∑ m, ((U σ).X k).pnorm (laU (U σ) a n k) (rdU (U σ) (w m) k) x ^ 2 := by
      obtain ⟨m, hm⟩ := exists_rdU_ne_zero (U σ) w hw k hx
      exact Finset.sum_pos' (fun _ _ => sq_nonneg _)
        ⟨m, Finset.mem_univ _, pow_pos (pnorm_pos_of_ne_zero _ _ _ hx hm) 2⟩
    simp only [hs] at h1
    have h2 := exp_le_of_neg_log_sqrt_le (mul_pos (pow_pos (lieFac_pos Dw xR a) 2) hpos) h1
    rw [← mul_assoc, ← mul_assoc] at h2
    exact h2
  · have h0 : 0 ≤ ((U σ).X k).pnorm eW et x :=
      mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ =>
        Real.rpow_nonneg (norm_nonneg _) _)
    refine (pow_le_pow_left₀ h0 (het x hx) 2).trans (le_of_eq ?_)
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring

end Gen

theorem firstMin_fn_nonneg {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (th : ℝ) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) :
    0 ≤ ReciprocityTheory.ChartRestriction.G.I2.phiFD X th x := by
  unfold ReciprocityTheory.ChartRestriction.G.I2.phiFD
  split_ifs <;> positivity

theorem firstMin_fn_lower {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) {th : ℝ} (hth : 0 < th) :
    ∃ ca ε0 : ℝ, 0 < ca ∧ 0 < ε0 ∧ ∀ x ∈ X.dom, X.la1 x < ε0 →
      ca / X.la1 x ^ 2 ≤ ReciprocityTheory.ChartRestriction.G.I2.phiFD X th x := by
  have hf : 0 < ReciprocityTheory.ChartRestriction.G.I2.PT.f E := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.f
    have h1 := IsTotallyComplex.finrank E
    have h2 : 0 < Module.finrank ℚ E := Module.finrank_pos
    omega
  have hrd : 0 < ReciprocityTheory.ChartRestriction.G.I2.PT.rd E := by
    unfold ReciprocityTheory.ChartRestriction.G.I2.PT.rd
    exact Real.rpow_pos_of_pos (abs_pos.2 (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E))) _
  refine ⟨2 * ReciprocityTheory.ChartRestriction.G.I2.PT.f E / ReciprocityTheory.ChartRestriction.G.I2.PT.rd E ^ 2, th, by positivity, hth,
    fun x _ hlt => ?_⟩
  unfold ReciprocityTheory.ChartRestriction.G.I2.phiFD
  rw [if_pos hlt, div_div]

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem phRec_of_firstMin : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (wL : WeightFamilies.Wt D j) (N N' i : ℕ) (w : Fin N → (recB h.toLawsCore).Cusp j wL) (e : Fin (N' + 1) ≃ Fin N) (et : (recB h.toLawsCore).Cusp j (etWt D j i)) (th tableLineDegreeFive DF tableLineDegreeTwo c : ℝ), GoodEmb T.Q.c σ → 0 < th → I2AtFramePoints (T.U j) (xiR D) (fun m => (w (e m)).1) (wtA wL, wL.n) th tableLineDegreeFive DF c → NoCommonZero (T.Q.Xo j) T.Q.c (fun m => (w m).1) → (∀ k : (T.U j σ).Comp, ∀ x ∈ ((T.U j σ).X k).dom, ((T.U j σ).X k).pnorm (laU (T.U j σ) (wtA (etWt D j i)) ((etWt D j i)).n k) (rdU (T.U j σ) et.1 k) x ≤ Real.exp (-(i : ℝ) * (ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th x - tableLineDegreeTwo))) → PhRec h j σ w i et c := by
  intro D T h j hj σ wL N N' i w e et th tableLineDegreeFive DF tableLineDegreeTwo c hσ hth hI hw het k
  exact ⟨ReciprocityTheory.ChartRestriction.G.I2.phiFD ((T.U j σ).X k) th, fun x _ => firstMin_fn_nonneg _ th x,
    firstMin_fn_lower _ hth,
    model_ineq_of_log_bound (T.U j) (xiR D) σ i (fun m => (w m).1) e (wtA wL) wL.n th tableLineDegreeFive DF tableLineDegreeTwo c hσ hI hw k _ _
      (het k)⟩

end GlobalTheory.BigRec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HolomorphicBoundOfWeightedL2
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

theorem norm_le_rpow_of_weighted_sq_integrable :
    ∀ (n : ℕ) (g : V n → ℂ) (ρ b : ℝ), 0 < ρ → 0 ≤ b → DifferentiableOn ℂ g (Metric.ball 0 ρ) →
      ∫⁻ z in Metric.ball (0 : V n) ρ,
        ENNReal.ofReal (‖g z‖ ^ 2 * (‖z‖ ^ 2) ^ (-(b + (n : ℝ)))) < ⊤ →
      ∃ C ε : ℝ, 0 < ε ∧ ∀ z : V n, z ≠ 0 → ‖z‖ < ε → ‖g z‖ ≤ C * ‖z‖ ^ b := by
  intro n g ρ b hρ hb hg hI
  set I := ∫⁻ z in Metric.ball (0 : V n) ρ,
        ENNReal.ofReal (‖g z‖ ^ 2 * (‖z‖ ^ 2) ^ (-(b + (n : ℝ)))) with hIdef
  set v := volume (Metric.ball (0 : V n) 1) with hv
  have hv0 : v ≠ 0 := (Metric.measure_ball_pos volume _ one_pos).ne'
  have hvt : v ≠ ⊤ := measure_ball_lt_top.ne
  have hvr : 0 < v.toReal := ENNReal.toReal_pos hv0 hvt
  have hdim : Module.finrank ℝ (V n) = 2 * n := by
    rw [finrank_real_of_complex, finrank_euclideanSpace_fin]
  set K : ℝ := (4 : ℝ) ^ b * 16 ^ n * I.toReal / v.toReal with hK
  have hK0 : 0 ≤ K := by positivity
  refine ⟨Real.sqrt K, ρ / 2, by positivity, fun z hz hzρ => ?_⟩
  set t := ‖z‖ with ht
  have ht0 : 0 < t := norm_pos_iff.2 hz
  have hsub : Metric.ball z (t / 2) ⊆ Metric.ball (0 : V n) ρ := by
    apply Metric.ball_subset_ball'
    rw [dist_zero_right]; linarith
  have hmv := ReciprocityTheory.L2DbarEstimates.C.mv n z (t / 2) g (fun _ => 1) (hg.mono hsub) measurable_const
  simp only [mul_one, lintegral_const, Measure.restrict_apply_univ, one_mul] at hmv
  rw [Measure.addHaar_ball_of_pos volume z (half_pos ht0), hdim, ← hv] at hmv
  have hs : 0 ≤ b + (n : ℝ) := by positivity
  have hbound : ∫⁻ w in Metric.ball z (t / 2), ‖g w‖ₑ ^ 2 ≤
      ENNReal.ofReal (((2 * t) ^ 2) ^ (b + (n : ℝ))) * I := by
    calc ∫⁻ w in Metric.ball z (t / 2), ‖g w‖ₑ ^ 2
        ≤ ∫⁻ w in Metric.ball z (t / 2), ENNReal.ofReal (((2 * t) ^ 2) ^ (b + (n : ℝ))) *
            ENNReal.ofReal (‖g w‖ ^ 2 * (‖w‖ ^ 2) ^ (-(b + (n : ℝ)))) := by
          refine setLIntegral_mono' Metric.isOpen_ball.measurableSet fun w hw => ?_
          have hw' : ‖w - z‖ < t / 2 := by rwa [Metric.mem_ball, dist_eq_norm] at hw
          have h1 : ‖w‖ ≤ 2 * t := by
            have := norm_sub_norm_le w z
            linarith
          have h2 : 0 < ‖w‖ := by
            have := norm_sub_norm_le z w
            rw [norm_sub_rev] at this
            linarith
          rw [← ENNReal.ofReal_mul (by positivity), ← ofReal_norm,
            ← ENNReal.ofReal_pow (norm_nonneg _)]
          apply ENNReal.ofReal_le_ofReal
          have h3 : (‖w‖ ^ 2) ^ (b + (n : ℝ)) ≤ ((2 * t) ^ 2) ^ (b + (n : ℝ)) :=
            Real.rpow_le_rpow (by positivity) (pow_le_pow_left₀ h2.le h1 2) hs
          have h4 : 0 < (‖w‖ ^ 2) ^ (b + (n : ℝ)) := by positivity
          rw [Real.rpow_neg (by positivity)]
          calc ‖g w‖ ^ 2 = (‖w‖ ^ 2) ^ (b + (n : ℝ)) *
                (‖g w‖ ^ 2 * ((‖w‖ ^ 2) ^ (b + (n : ℝ)))⁻¹) := by field_simp
            _ ≤ _ := mul_le_mul_of_nonneg_right h3 (by positivity)
      _ = ENNReal.ofReal (((2 * t) ^ 2) ^ (b + (n : ℝ))) * ∫⁻ w in Metric.ball z (t / 2),
            ENNReal.ofReal (‖g w‖ ^ 2 * (‖w‖ ^ 2) ^ (-(b + (n : ℝ)))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := by
          gcongr
          exact lintegral_mono_set hsub
  have hfin := hmv.trans hbound
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hI.ne) hfin
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
    toReal_enorm, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)] at hr
  have hid : ((2 * t) ^ 2) ^ (b + (n : ℝ)) =
      (4 : ℝ) ^ b * (t ^ b) ^ 2 * (16 ^ n * (t / 2) ^ (2 * n)) := by
    rw [Real.rpow_add (by positivity), Real.rpow_natCast]
    congr 1
    · rw [show (2 * t) ^ 2 = 4 * (t * t) by ring, Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow ht0.le ht0.le, sq]
    · rw [pow_mul, ← mul_pow]
      congr 1
      ring
  rw [hid] at hr
  have hp : 0 < (t / 2) ^ (2 * n) := by positivity
  have hsq : ‖g z‖ ^ 2 ≤ K * (t ^ b) ^ 2 := by
    have hc : 0 < (t / 2) ^ (2 * n) * v.toReal := by positivity
    refine le_of_mul_le_mul_right (hr.trans (le_of_eq ?_)) hc
    rw [hK]
    field_simp
  calc ‖g z‖ ≤ Real.sqrt (K * (t ^ b) ^ 2) := Real.le_sqrt_of_sq_le hsq
    _ = Real.sqrt K * t ^ b := by
      rw [Real.sqrt_mul hK0, Real.sqrt_sq (by positivity)]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.HolomorphicIsBigOOfHalfPowerBound
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory

theorem isBigO_norm_pow_of_le_rpow_sub_half {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [Nontrivial E] (a : ℕ) (g : E → ℂ) (ρ C : ℝ) (hρ : 0 < ρ)
    (hd : DifferentiableOn ℂ g (Metric.ball 0 ρ))
    (hb : ∀ z : E, z ≠ 0 → ‖z‖ < ρ → ‖g z‖ ≤ C * ‖z‖ ^ ((a : ℝ) - 1 / 2)) :
    g =O[𝓝 0] fun z => ‖z‖ ^ a := by
  have hball : Metric.ball (0 : E) ρ ∈ 𝓝 (0 : E) := Metric.ball_mem_nhds _ hρ
  have hc : ContinuousAt g 0 := hd.continuousOn.continuousAt hball
  cases a with
  | zero =>
    simp only [pow_zero]
    exact hc.tendsto.isBigO_one ℝ
  | succ m =>
    have he : ((m + 1 : ℕ) : ℝ) - 1 / 2 = (m : ℝ) + 1 / 2 := by push_cast; ring
    rw [he] at hb
    have hpos : (0 : ℝ) < (m : ℝ) + 1 / 2 := by positivity
    have hb' : ∀ z : E, z ≠ 0 → ‖z‖ < ρ → ‖g z‖ ≤ |C| * ‖z‖ ^ ((m : ℝ) + 1 / 2) :=
      fun z hz hzρ => (hb z hz hzρ).trans
        (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
    have hpow : ∀ s : ℝ, 0 < s →
        Filter.Tendsto (fun z : E => |C| * ‖z‖ ^ s) (𝓝 0) (𝓝 0) := by
      intro s hs
      have h1 : Continuous (fun z : E => |C| * ‖z‖ ^ s) :=
        continuous_const.mul (continuous_norm.rpow_const fun _ => Or.inr hs.le)
      have h2 := h1.tendsto 0
      simpa [Real.zero_rpow hs.ne'] using h2
    have hg0 : g 0 = 0 := by
      haveI : (𝓝[≠] (0 : E)).NeBot := Module.punctured_nhds_neBot ℂ E 0
      have h1 : Filter.Tendsto g (𝓝[≠] 0) (𝓝 (g 0)) := hc.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Filter.Tendsto g (𝓝[≠] 0) (𝓝 0) := by
        refine squeeze_zero_norm' ?_ ((hpow _ hpos).mono_left nhdsWithin_le_nhds)
        filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hball] with z hz hzρ
        exact hb' z hz (mem_ball_zero_iff.1 hzρ)
      exact tendsto_nhds_unique h1 h2
    have hb'' : ∀ z : E, ‖z‖ < ρ → ‖g z‖ ≤ |C| * ‖z‖ ^ ((m : ℝ) + 1 / 2) := by
      intro z hz
      rcases eq_or_ne z 0 with rfl | h
      · rw [hg0, norm_zero]; positivity
      · exact hb' z h hz
    have hmaps : Set.MapsTo g (Metric.ball 0 ρ)
        (Metric.closedBall (g 0) (|C| * ρ ^ ((m : ℝ) + 1 / 2))) := by
      intro z hz
      have hz' := mem_ball_zero_iff.1 hz
      rw [hg0, mem_closedBall_zero_iff]
      refine (hb'' z hz').trans ?_
      gcongr
    have ho : (fun w => g w - g 0) =o[𝓝 0] (fun w : E => ‖w - 0‖ ^ m) := by
      simp only [hg0, sub_zero]
      rw [Asymptotics.isLittleO_iff]
      intro ε hε
      filter_upwards [hball, (hpow (1 / 2) (by norm_num)).eventually (gt_mem_nhds hε)]
        with z hz hzε
      refine (hb'' z (mem_ball_zero_iff.1 hz)).trans ?_
      rw [Real.rpow_add' (norm_nonneg z) hpos.ne', Real.rpow_natCast, norm_pow, norm_norm]
      calc |C| * (‖z‖ ^ m * ‖z‖ ^ (1 / 2 : ℝ)) = (|C| * ‖z‖ ^ (1 / 2 : ℝ)) * ‖z‖ ^ m := by ring
        _ ≤ ε * ‖z‖ ^ m := by gcongr
    refine Asymptotics.IsBigO.of_bound (|C| * ρ ^ ((m : ℝ) + 1 / 2) / ρ ^ (m + 1)) ?_
    filter_upwards [hball] with z hz
    have key := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO hd hmaps ho hz
    rw [hg0, dist_zero_right, dist_zero_right, div_pow] at key
    rw [norm_pow, norm_norm]
    refine key.trans_eq ?_
    ring

theorem isBigO_norm_pow_of_le_rpow_sub_half_euclidean :
    ∀ (n a : ℕ) (g : V n → ℂ) (ρ C : ℝ), 0 < n → 0 < ρ → DifferentiableOn ℂ g (Metric.ball 0 ρ) → (∀ z : V n, z ≠ 0 → ‖z‖ < ρ → ‖g z‖ ≤ C * ‖z‖ ^ ((a : ℝ) - 1 / 2)) → g =O[𝓝 0] fun z => ‖z‖ ^ a := by
  intro n a g ρ C hn hρ hd hb
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nontrivial (V n) := inferInstance
  exact isBigO_norm_pow_of_le_rpow_sub_half a g ρ C hρ hd hb

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IndependentDifferentialsRatiosOfTrdegValues
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BigRec

namespace GlobalTheory.BigRec

theorem adjoin_div_le {K F κ : Type} [Field K] [Field F] [Algebra K F] (a : κ → F) (p q : κ) (hq : a q ≠ 0) :
    IntermediateField.adjoin K (Set.range fun k => a k / a p) ≤
      IntermediateField.adjoin K (Set.range fun k => a k / a q) := by
  refine IntermediateField.adjoin_le_iff.mpr ?_
  rintro _ ⟨k, rfl⟩
  have hk : a k / a q ∈ IntermediateField.adjoin K (Set.range fun k => a k / a q) :=
    IntermediateField.subset_adjoin K _ ⟨k, rfl⟩
  have hp : a p / a q ∈ IntermediateField.adjoin K (Set.range fun k => a k / a q) :=
    IntermediateField.subset_adjoin K _ ⟨p, rfl⟩
  have hkp := div_mem hk hp
  rwa [div_div_div_cancel_right₀ hq] at hkp

theorem ratio_single {F Γ : Type} [Field F] [AddCommGroup Γ] (g : Γ) (a b : F) (hb : b ≠ 0) :
    ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := F) (AddMonoidAlgebra.single g a : AddMonoidAlgebra F Γ)
      (AddMonoidAlgebra.single g b) = a / b := by
  have hex : ∃ c : F, (AddMonoidAlgebra.single g a : AddMonoidAlgebra F Γ) = c • AddMonoidAlgebra.single g b :=
    ⟨a / b, by rw [AddMonoidAlgebra.smul_single', div_mul_cancel₀ a hb]⟩
  rw [ReciprocityTheory.ChartRestriction.G.T0.ratio, dif_pos hex]
  have hc := hex.choose_spec
  rw [AddMonoidAlgebra.smul_single'] at hc
  have hv : a = hex.choose * b := by
    first
    | exact AddMonoidAlgebra.single_injective g hc
    | simpa using hc
  exact eq_div_of_mul_eq hb hv.symm

theorem independent_differentials_ratios_of_trdeg_values {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} [Fintype (Comp Xo c)] (hG : GenFrEx Xo c)
    (d : ReciprocityTheory.ChartRestriction.G.T0.Data c.F (Comp Xo c) (fun Z => Om Z) (WTZ E) (fun Z => AC Z))
    {κ : Type} (w : κ → Rul Xo c) (e : κ ≃ Fin (d.N + 1)) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ)
    (htr : FnTrdeg Xo c d.D) (hw : ∀ k, d.w (e k) = valC hG a n (w k)) (hb : ∀ Z, d.w (d.jc Z) Z ≠ 0)
    (hbig : ∀ Z : Comp Xo c, ∃ k₀, evC hG Z (w k₀) ≠ 0 ∧ Algebra.trdeg c.F
      (IntermediateField.adjoin c.F (Set.range fun k => evC hG Z (w k) / evC hG Z (w k₀))) = d.D) :
    A1Bigness d := by
  unfold A1Bigness
  intro Z
  have hfull : Algebra.trdeg c.F (Om Z) = d.D := by
    unfold FnTrdeg at htr
    exact htr Z
  refine (GlobalTheory.trdegD_iff_exists_linearIndependent_D d Z hfull (hb Z)).mp ?_
  unfold ReciprocityTheory.ChartRestriction.G.AR.Up.TrdegD
  obtain ⟨k₀, hk₀, htk⟩ := hbig Z
  have hwZ : ∀ k, d.w (e k) Z = AddMonoidAlgebra.single (wtZ a n) (evC hG Z (w k)) := by
    intro k
    rw [hw k]
    rfl
  set kc := e.symm (d.jc Z) with hkc
  have hjc : d.jc Z = e kc := (e.apply_symm_apply _).symm
  have hc0 : evC hG Z (w kc) ≠ 0 := by
    intro h0
    apply hb Z
    rw [hjc, hwZ, h0, AddMonoidAlgebra.single_zero]
  have hrange : (Set.range fun j => ReciprocityTheory.ChartRestriction.G.T0.ratio (Ω := Om Z) (d.w j Z) (d.w (d.jc Z) Z)) =
      Set.range fun k => evC hG Z (w k) / evC hG Z (w kc) := by
    rw [← e.surjective.range_comp]
    congr 1
    funext k
    simp only [Function.comp]
    rw [hjc, hwZ, hwZ]
    exact ratio_single _ _ _ hc0
  rw [hrange]
  have hsame : IntermediateField.adjoin c.F (Set.range fun k => evC hG Z (w k) / evC hG Z (w kc)) =
      IntermediateField.adjoin c.F (Set.range fun k => evC hG Z (w k) / evC hG Z (w k₀)) :=
    le_antisymm (adjoin_div_le (fun k => evC hG Z (w k)) kc k₀ hk₀)
      (adjoin_div_le (fun k => evC hG Z (w k)) k₀ kc hc0)
  rw [hsame]
  exact htk

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem independent_differentials_ratios_cusp_forms_trdeg : ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (ka wL wF : WeightFamilies.Wt D j) (G : GlobalFamilyData (recPlus h j hj) ka wL wF) [Fintype (Comp (T.Q.Xo j) T.Q.c)] (d : ReciprocityTheory.ChartRestriction.G.T0.Data T.Q.c.F (Comp (T.Q.Xo j) T.Q.c) (fun Z => Om Z) (WTZ D.host.E) (fun Z => AC Z)) (e : Fin G.N ≃ Fin (d.N + 1)), d.D = WeightFamilies.dimY D j → (∀ k, d.w (e k) = valC hG (wtA wL) wL.n (G.w k).1) → (∀ Z, d.w (d.jc Z) Z ≠ 0) → (∀ Z : Comp (T.Q.Xo j) T.Q.c, ∃ k₀, evC hG Z (G.w k₀).1 ≠ 0 ∧ Algebra.trdeg T.Q.c.F (IntermediateField.adjoin T.Q.c.F (Set.range fun k => evC hG Z (G.w k).1 / evC hG Z (G.w k₀).1)) = WeightFamilies.dimY D j) → A1Bigness d := by
  intro D T h j hj hG ka wL wF G _ d e hD hw hb hbig
  have hpin : T.Q.PinDat := by
    have hp := h.toLawsCore.pins
    unfold Par.Pins at hp
    exact hp.2.2.2
  have htr := (GlobalTheory.FlagDim.fnFG_fnTrdeg_record D T.Q hpin j hj).2
  rw [← hD] at htr hbig
  exact independent_differentials_ratios_of_trdeg_values hG d (fun k => (G.w k).1) e (wtA wL) wL.n htr hw hb hbig

end GlobalTheory.BigRec
end

