import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.Bundle0006

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LocalUnramifiedOf
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

section PK7

open GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.AutomorphicL2Unitary GlobalTheory.LFun Formalism.UG Formalism.L2.Host

theorem local_unramified_of : JacquetShalikaLocal.L7 → JacquetShalikaLocal.lift_levelP_alt₂ → jumpWindows.G0 → jumpWindows.G5 → K7 := by
  intro hL7 hL12 hG0 hG5 E _ _ _ a ψ hψ w hc
  refine ⟨WeilJacquetShalikaLaw.psiW ψ w, WeilJacquetShalikaLaw.psiOK hψ hc, fun y => rfl, ?_⟩
  intro z φ hφ hsat h hh u
  have hcomm := (hG0 E a).2.2.2.2.2.2.2.1 w h hh
  obtain ⟨hΛ, hrt, hgood, hreg⟩ := hG5 E a ψ hψ
  rcases hsat with rfl | hsat
  · have h0 : ∀ g, Wh ψ (0 : XB E a) g = 0 := fun g => by
      obtain ⟨Λ, hΛ'⟩ := hΛ g
      rw [← hΛ' 0 hφ, map_zero]
    rw [h0, h0, zero_mul]
  let v : GL (Fin a) (w.adicCompletion E) → ℂ := fun x => Wh ψ φ (h * fl a w x)
  have hfix : ∀ k ∈ KGL w a, Rt E a (fl a w k) φ = φ := fun k hk => GlobalTheory.LGrp.mem_fixed.1 hsat.2.1 k hk
  have hv : v ∈ WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := by
    intro n hn x
    change Wh ψ φ (h * fl a w (n * x)) = _ * Wh ψ φ (h * fl a w x)
    rw [map_mul, ← mul_assoc, hcomm n, mul_assoc]
    exact WeilJacquetShalikaLaw.law (hreg φ hφ).2.2 w n hn _
  let vs : WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a := ⟨v, hv⟩
  have hv1 : (vs : GL (Fin a) (w.adicCompletion E) → ℂ) 1 = Wh ψ φ h := by
    change Wh ψ φ (h * fl a w 1) = _
    rw [map_one, mul_one]
  by_cases h0 : vs = 0
  · have e : ∀ x, (vs : GL (Fin a) (w.adicCompletion E) → ℂ) x = 0 := fun x =>
      congrFun (congrArg Subtype.val h0) x
    have e1 : Wh ψ φ (h * fl a w u) = 0 := e u
    rw [e1, ← hv1, e 1, zero_mul]
  have hK := Final.GLintComm E w a
  have hsv : IsSatVecGL w (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs (Finset.univ.val.map z) := by
    refine ⟨h0, GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_, by simp, fun ϖ hϖ j hj => ?_⟩
    · apply Subtype.ext
      funext x
      change Wh ψ φ (h * fl a w (x * k)) = Wh ψ φ (h * fl a w x)
      rw [map_mul, ← mul_assoc, ← hrt, hfix k hk]
    · apply Subtype.ext
      have e := map_heckeVec (ρ := WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a)
        (ρ' := GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) hK (Tj_mem_hecke hϖ j) (WeilJacquetShalikaLaw.WS (WeilJacquetShalikaLaw.psiW ψ w) a).subtype (fun _ _ => rfl) vs
      rw [Submodule.subtype_apply, Submodule.subtype_apply] at e
      rw [e, Submodule.coe_smul]
      funext x
      obtain ⟨Λ, hΛ'⟩ := hΛ (h * fl a w x)
      have hfin := finite_heckeVec hK (Tj_mem_hecke hϖ j) (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) v
      have hfin2 := finite_heckeVec hK (Tj_mem_hecke hϖ j) (repW a w) φ
      have e1 := (LinearMap.proj (R := ℂ) (φ := fun _ : GL (Fin a) (w.adicCompletion E) => ℂ) x).toAddMonoidHom.map_finsum hfin
      have e2 := (Λ : XB E a →L[ℂ] ℂ).toLinearMap.toAddMonoidHom.map_finsum hfin2
      have e3 := hsat.2.2.2 ϖ hϖ j hj
      have key : ∀ c : GL (Fin a) (w.adicCompletion E) ⧸ KGL w a,
          (Tj ℂ a (Ov E w) ϖ j c.out • GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ c.out v) x =
            Λ (Tj ℂ a (Ov E w) ϖ j c.out • repW a w c.out φ) := by
        intro c
        rw [map_smul, hΛ' (repW a w c.out φ) (hgood φ (fl a w c.out) hφ)]
        change _ * v (x * c.out) = _ • Wh ψ (Rt E a (fl a w c.out) φ) (h * fl a w x)
        rw [hrt, smul_eq_mul]
        change _ * Wh ψ φ (h * fl a w (x * c.out)) = _
        rw [map_mul, mul_assoc]
      have LHS : heckeVec (GlobalTheory.PRep.rightReg ℂ (GL (Fin a) (w.adicCompletion E)) ℂ) (KGL w a)
          (Tj ℂ a (Ov E w) ϖ j) v x = Λ (heckeVec (repW a w) (KGL w a) (Tj ℂ a (Ov E w) ϖ j) φ) := by
        rw [heckeVec, heckeVec]
        exact e1.trans ((finsum_congr key).trans e2.symm)
      refine LHS.trans ?_
      rw [e3, map_smul, hΛ' φ hφ]
      rfl
  have heig := (hL12 E w).2 a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z hsv
  have := hL7 (w.adicCompletion E) (WeilJacquetShalikaLaw.psiW ψ w) (WeilJacquetShalikaLaw.psiOK hψ hc) a _ (WeilJacquetShalikaLaw.rhoW (WeilJacquetShalikaLaw.psiW ψ w) a) vs z heig
    (WeilJacquetShalikaLaw.ev _ a) (WeilJacquetShalikaLaw.whitW w _) u
  rw [WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.ev_apply, WeilJacquetShalikaLaw.rhoW_apply, one_mul, hv1] at this
  exact this

end PK7

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LogBallEstimates
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LogBallEstimates

theorem neg_log_le {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) : -Real.log t ≤ t ^ (-ε) / ε := by
  have := Real.log_le_rpow_div (inv_pos.2 ht).le hε
  rwa [Real.log_inv, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le] at this

theorem large_power_bound {t σ c C : ℝ} {M : ℕ} (ht : 1 ≤ t) (hM : σ + 1 ≤ M) (hc : 0 ≤ c)
    (h : c ≤ C * (t ^ M)⁻¹) : c * t ^ σ ≤ |C| * min t t⁻¹ ^ (1 : ℝ) := by
  have t0 : 0 < t := by linarith
  rw [min_eq_right ((inv_le_one_of_one_le₀ ht).trans ht), Real.rpow_one]
  have h1 : t ^ σ * t ≤ t ^ M := by
    rw [← Real.rpow_add_one t0.ne', ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le ht hM
  have hp : 0 < t ^ M := by positivity
  have h2 : c ≤ |C| * (t ^ M)⁻¹ := h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity))
  have h3 : t ^ σ ≤ t ^ M * t⁻¹ := by
    rw [le_mul_inv_iff₀ t0]; exact h1
  calc c * t ^ σ ≤ |C| * (t ^ M)⁻¹ * t ^ σ := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = |C| * ((t ^ M)⁻¹ * t ^ σ) := by ring
    _ ≤ |C| * ((t ^ M)⁻¹ * (t ^ M * t⁻¹)) := by gcongr
    _ = |C| * t⁻¹ := by field_simp

theorem big_log {t σ c C : ℝ} {M : ℕ} (ht : 1 ≤ t) (hM : σ + 2 ≤ M) (hc : 0 ≤ c)
    (h : c ≤ C * (t ^ M)⁻¹) : c * t ^ σ * |Real.log t| ≤ |C| * min t t⁻¹ ^ (1 : ℝ) := by
  have t0 : 0 < t := by linarith
  have hl : |Real.log t| ≤ t := by
    rw [abs_of_nonneg (Real.log_nonneg ht)]; linarith [Real.log_le_sub_one_of_pos t0]
  calc c * t ^ σ * |Real.log t| ≤ c * t ^ σ * t := by gcongr
    _ = c * t ^ (σ + 1) := by rw [Real.rpow_add_one t0.ne']; ring
    _ ≤ _ := large_power_bound ht (by linarith) hc h

theorem small_power_bound {t b ε c C : ℝ} (t0 : 0 < t) (t1 : t < 1) (hε : 0 < ε) (hb : 2 * ε ≤ b + 1)
    (hc : 0 ≤ c) (h : c ≤ C * t) : c * t ^ b ≤ |C| * t ^ (2 * ε) := by
  have h2 : c ≤ |C| * t := h.trans (mul_le_mul_of_nonneg_right (le_abs_self C) t0.le)
  calc c * t ^ b ≤ |C| * t * t ^ b := mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = |C| * t ^ (b + 1) := by rw [Real.rpow_add_one t0.ne']; ring
    _ ≤ |C| * t ^ (2 * ε) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge t0 t1.le hb) (abs_nonneg _)

theorem small0 {t b ε c C : ℝ} (t0 : 0 < t) (t1 : t < 1) (hε : 0 < ε) (hb : 2 * ε ≤ b + 1)
    (hc : 0 ≤ c) (h : c ≤ C * t) : c * t ^ b ≤ |C| * (1 + ε⁻¹) * min t t⁻¹ ^ ε := by
  rw [min_eq_left (t1.le.trans (one_le_inv₀ t0 |>.2 t1.le))]
  have h1 := small_power_bound t0 t1 hε hb hc h
  have h2 : t ^ (2 * ε) ≤ t ^ ε := Real.rpow_le_rpow_of_exponent_ge t0 t1.le (by linarith)
  have h3 : 0 ≤ |C| * t ^ ε * ε⁻¹ := by positivity
  calc c * t ^ b ≤ |C| * t ^ ε := h1.trans (by gcongr)
    _ ≤ |C| * t ^ ε + |C| * t ^ ε * ε⁻¹ := by linarith
    _ = |C| * (1 + ε⁻¹) * t ^ ε := by ring

theorem small_log {t b ε c C : ℝ} (t0 : 0 < t) (t1 : t < 1) (hε : 0 < ε) (hb : 2 * ε ≤ b + 1)
    (hc : 0 ≤ c) (h : c ≤ C * t) : c * t ^ b * |Real.log t| ≤ |C| * (1 + ε⁻¹) * min t t⁻¹ ^ ε := by
  rw [min_eq_left (t1.le.trans (one_le_inv₀ t0 |>.2 t1.le))]
  have h1 := small_power_bound t0 t1 hε hb hc h
  have hl : |Real.log t| ≤ t ^ (-ε) / ε := by
    rw [abs_of_neg (Real.log_neg t0 t1)]; exact neg_log_le t0 hε
  have e : t ^ (2 * ε) * (t ^ (-ε) / ε) = t ^ ε * ε⁻¹ := by
    rw [mul_div_assoc', ← Real.rpow_add t0, div_eq_mul_inv]; ring_nf
  have h3 : 0 ≤ |C| * t ^ ε := by positivity
  calc c * t ^ b * |Real.log t| ≤ |C| * t ^ (2 * ε) * (t ^ (-ε) / ε) := by
        gcongr
    _ = |C| * t ^ ε * ε⁻¹ := by rw [mul_assoc, e]; ring
    _ ≤ |C| * t ^ ε + |C| * t ^ ε * ε⁻¹ := by linarith
    _ = |C| * (1 + ε⁻¹) * t ^ ε := by ring

theorem bddBelow_support_primePowerComponent_coeff {t ε c C : ℝ} (t0 : 0 < t) (t1 : t < 1) (hc : 0 ≤ c) (h : c ≤ C) :
    c * t ^ ε ≤ |C| * min t t⁻¹ ^ ε := by
  rw [min_eq_left (t1.le.trans (one_le_inv₀ t0 |>.2 t1.le))]
  exact mul_le_mul_of_nonneg_right (h.trans (le_abs_self C)) (by positivity)

theorem re_lt_of_ball {s s₀ : ℂ} {r : ℝ} (hs : s ∈ Metric.ball s₀ r) : |s.re - s₀.re| < r := by
  rw [Metric.mem_ball, dist_eq_norm] at hs
  rw [← Complex.sub_re]; exact (Complex.abs_re_le_norm _).trans_lt hs

variable {X : Type*} [MeasurableSpace X]

theorem intg (ν : Measure X) (D : X → ℝ) (hD : ∀ x, 0 < D x) (hDm : Measurable D) (F : X → ℂ)
    (hF : AEStronglyMeasurable F ν) (s : ℂ) (g : X → ℝ) (hg : Integrable g ν)
    (h0 : ∀ᵐ x ∂ν, ‖F x‖ * D x ^ s.re ≤ g x) : Integrable (fun x => F x * (D x : ℂ) ^ s) ν :=
  hg.mono' (hF.mul ((Complex.measurable_ofReal.comp hDm).pow_const s).aestronglyMeasurable)
    (h0.mono fun x hx => by rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hD x)]; exact hx)

theorem diffAt (ν : Measure X) (D : X → ℝ) (hD : ∀ x, 0 < D x) (hDm : Measurable D) (F : X → ℂ)
    (hF : AEStronglyMeasurable F ν) (s₀ : ℂ) (r : ℝ) (hr : 0 < r) (g : X → ℝ) (hg : Integrable g ν)
    (h0 : ∀ᵐ x ∂ν, ‖F x‖ * D x ^ s₀.re ≤ g x)
    (hb : ∀ᵐ x ∂ν, ∀ s ∈ Metric.ball s₀ r, ‖F x‖ * D x ^ s.re * |Real.log (D x)| ≤ g x) :
    DifferentiableAt ℂ (fun s => ∫ x, F x * (D x : ℂ) ^ s ∂ν) s₀ := by
  have hDc : Measurable fun x => (D x : ℂ) := Complex.measurable_ofReal.comp hDm
  have hmeas : ∀ s : ℂ, AEStronglyMeasurable (fun x => F x * (D x : ℂ) ^ s) ν := fun s =>
    hF.mul (hDc.pow_const s).aestronglyMeasurable
  have := hasDerivAt_integral_of_dominated_loc_of_deriv_le (𝕜 := ℂ) (μ := ν)
    (F := fun s x => F x * (D x : ℂ) ^ s) (F' := fun s x => F x * ((D x : ℂ) ^ s * Complex.log (D x)))
    (x₀ := s₀) (bound := g) (Metric.ball_mem_nhds s₀ hr) (Filter.Eventually.of_forall fun s => hmeas s)
    (intg ν D hD hDm F hF s₀ g hg h0)
    (hF.mul ((hDc.pow_const s₀).mul (Complex.measurable_log.comp hDc)).aestronglyMeasurable)
    (hb.mono fun x hx s hs => by
      rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (hD x), ← Complex.ofReal_log (hD x).le,
        Complex.norm_real, Real.norm_eq_abs, ← mul_assoc]
      exact hx s hs)
    hg
    (Filter.Eventually.of_forall fun x s _ =>
      ((Complex.hasStrictDerivAt_const_cpow (Or.inl (Complex.ofReal_ne_zero.2 (hD x).ne'))).hasDerivAt.const_mul (F x)))
  exact this.2.differentiableAt

end LogBallEstimates

open LogBallEstimates in
theorem duality_diagonalClass_of_affineProperBaseChange : D0 → V1 → E1 → E2 := by
  intro hD0 hV1 hE1 E _ _ _ k μ _ hk β hβ H H₀ hG
  obtain ⟨hpos, -, hcont, -⟩ := hD0 E k
  have hmin := (hV1 E k μ hk β hβ).2.2
  have hE := hE1 E k μ hk β hβ H₀ hG.meas₀ hG.inv₀ hG.cen hG.bdd
  have hDm : Measurable (Dt : GA E k → ℝ) := hcont.measurable
  have hS : MeasurableSet {g : GA E k | Dt g < 1} := measurableSet_lt hDm measurable_const
  obtain ⟨C₀, hC₀⟩ := hG.bdd
  obtain ⟨C₁, hC₁⟩ := hG.small
  have hFm : Measurable fun g => (Dt g : ℂ) * H g - H₀ g :=
    ((Complex.measurable_ofReal.comp hDm).mul hG.meas).sub hG.meas₀

  have hAb : ∀ (σ : ℝ), ∃ g : GA E k → ℝ, IntegrableOn g {g | Dt g < 1}ᶜ (μ.withDensity β) ∧
      ∀ x, x ∈ {g : GA E k | Dt g < 1}ᶜ → ∀ τ, τ ≤ σ →
        ‖H x‖ * Dt x ^ τ ≤ g x ∧ ‖H x‖ * Dt x ^ τ * |Real.log (Dt x)| ≤ g x := by
    intro σ
    obtain ⟨C, hC⟩ := hG.big (⌈σ⌉₊ + 2)
    refine ⟨fun x => |C| * min (Dt x) (Dt x)⁻¹ ^ (1 : ℝ), ((hmin 1 one_pos).const_mul |C|).integrableOn,
      fun x hx τ hτ => ?_⟩
    have h1 : 1 ≤ Dt x := not_lt.1 hx
    have hM : τ + 2 ≤ ((⌈σ⌉₊ + 2 : ℕ) : ℝ) := by push_cast; linarith [Nat.le_ceil σ]
    exact ⟨large_power_bound h1 (by linarith) (norm_nonneg _) (hC x h1), big_log h1 hM (norm_nonneg _) (hC x h1)⟩
  have hBb : ∀ ε : ℝ, 0 < ε → ∃ g : GA E k → ℝ, IntegrableOn g {g | Dt g < 1} (μ.withDensity β) ∧
      ∀ x, x ∈ {g : GA E k | Dt g < 1} → ∀ b, 2 * ε ≤ b + 1 →
        ‖(Dt x : ℂ) * H x - H₀ x‖ * Dt x ^ b ≤ g x ∧
          ‖(Dt x : ℂ) * H x - H₀ x‖ * Dt x ^ b * |Real.log (Dt x)| ≤ g x := by
    intro ε hε
    refine ⟨fun x => |C₁| * (1 + ε⁻¹) * min (Dt x) (Dt x)⁻¹ ^ ε,
      ((hmin ε hε).const_mul (|C₁| * (1 + ε⁻¹))).integrableOn, fun x hx b hb => ?_⟩
    have h1 : Dt x < 1 := hx
    exact ⟨small0 (hpos x) h1 hε hb (norm_nonneg _) (hC₁ x h1),
      small_log (hpos x) h1 hε hb (norm_nonneg _) (hC₁ x h1)⟩
  let κ : ℂ := ((k : ℂ) * Module.finrank ℚ E)⁻¹ * ∫ g in band E k, H₀ g ∂μ.withDensity β
  let A : ℂ → ℂ := fun s => ∫ g in {g | Dt g < 1}ᶜ, H g * (Dt g : ℂ) ^ s ∂μ.withDensity β
  let B : ℂ → ℂ := fun s => ∫ g in {g | Dt g < 1}, ((Dt g : ℂ) * H g - H₀ g) * (Dt g : ℂ) ^ (s - 1)
    ∂μ.withDensity β
  have hA : ∀ s₀ : ℂ, DifferentiableAt ℂ A s₀ := by
    intro s₀
    obtain ⟨g, hg, hgb⟩ := hAb (s₀.re + 1)
    refine diffAt _ Dt hpos hDm H hG.meas.aestronglyMeasurable s₀ 1 one_pos g hg ?_ ?_
    · exact (ae_restrict_iff' hS.compl).2 (Eventually.of_forall fun x hx => (hgb x hx _ (by linarith)).1)
    · exact (ae_restrict_iff' hS.compl).2 (Eventually.of_forall fun x hx s hs =>
        (hgb x hx _ (by linarith [(abs_lt.1 (re_lt_of_ball hs)).2])).2)
  have hB : ∀ s₀ : ℂ, 0 < s₀.re → DifferentiableAt ℂ B s₀ := by
    intro s₀ h0
    obtain ⟨g, hg, hgb⟩ := hBb (s₀.re / 4) (by linarith)
    have := diffAt _ Dt hpos hDm _ hFm.aestronglyMeasurable (s₀ - 1) (s₀.re / 2) (by linarith) g hg
      ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx =>
        (hgb x hx _ (by rw [Complex.sub_re, Complex.one_re]; linarith)).1))
      ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx s hs =>
        (hgb x hx _ (by
          have := (abs_lt.1 (re_lt_of_ball hs)).1
          rw [Complex.sub_re, Complex.one_re] at this; linarith)).2))
    have h2 : DifferentiableAt ℂ (fun s : ℂ => s - 1) s₀ := differentiableAt_id.sub_const 1
    have h3 := DifferentiableAt.comp s₀ this h2
    exact h3
  refine ⟨fun s => (s - 1) * (A s + B s) + κ, fun s hs => ?_, fun s hs => ?_, fun hb => ?_⟩
  · have h2 : DifferentiableAt ℂ (fun s : ℂ => s - 1) s := differentiableAt_id.sub_const 1
    exact (h2.mul ((hA s).add (hB s hs))).add_const κ |>.differentiableWithinAt
  · obtain ⟨gA, hgA, hgAb⟩ := hAb s.re
    obtain ⟨gB, hgB, hgBb⟩ := hBb (1 / 2) (by norm_num)
    have i1 : IntegrableOn (fun g => H g * (Dt g : ℂ) ^ s) {g | Dt g < 1}ᶜ (μ.withDensity β) :=
      intg _ Dt hpos hDm H hG.meas.aestronglyMeasurable s gA hgA
        ((ae_restrict_iff' hS.compl).2 (Eventually.of_forall fun x hx => (hgAb x hx _ le_rfl).1))
    have i2 : IntegrableOn (fun g => ((Dt g : ℂ) * H g - H₀ g) * (Dt g : ℂ) ^ (s - 1)) {g | Dt g < 1}
        (μ.withDensity β) :=
      intg _ Dt hpos hDm _ hFm.aestronglyMeasurable (s - 1) gB hgB
        ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx =>
          (hgBb x hx _ (by rw [Complex.sub_re, Complex.one_re]; linarith)).1))
    have hs1 : 0 < (s - 1).re := by rw [Complex.sub_re, Complex.one_re]; linarith
    have i3 : IntegrableOn (fun g => H₀ g * (Dt g : ℂ) ^ (s - 1)) {g | Dt g < 1} (μ.withDensity β) :=
      intg _ Dt hpos hDm _ hG.meas₀.aestronglyMeasurable (s - 1) _
        ((hmin _ hs1).const_mul |C₀|).integrableOn
        ((ae_restrict_iff' hS).2 (Eventually.of_forall fun x hx =>
          bddBelow_support_primePowerComponent_coeff (hpos x) hx (norm_nonneg _) (hC₀ x)))
    have hid : ∀ g, H g * (Dt g : ℂ) ^ s =
        ((Dt g : ℂ) * H g - H₀ g) * (Dt g : ℂ) ^ (s - 1) + H₀ g * (Dt g : ℂ) ^ (s - 1) := by
      intro g
      have h0 : (Dt g : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (hpos g).ne'
      rw [Complex.cpow_sub _ _ h0, Complex.cpow_one]
      field_simp
      ring
    have i4 : IntegrableOn (fun g => H g * (Dt g : ℂ) ^ s) {g | Dt g < 1} (μ.withDensity β) := by
      simp_rw [hid]; exact i2.add i3
    have hint : Integrable (fun g => H g * (Dt g : ℂ) ^ s) (μ.withDensity β) := by
      have := i4.union i1
      rwa [Set.union_compl_self, integrableOn_univ] at this
    have hE' := hE (s - 1) hs1
    rw [← integral_add_compl hS hint]
    have hsplit : ∫ g in {g | Dt g < 1}, H g * (Dt g : ℂ) ^ s ∂μ.withDensity β =
        B s + ∫ g in {g | Dt g < 1}, H₀ g * (Dt g : ℂ) ^ (s - 1) ∂μ.withDensity β := by
      simp_rw [hid]; exact integral_add i2 i3
    rw [hsplit]
    show (s - 1) * (A s + B s) + κ = _
    linear_combination -hE'
  · show (1 - 1) * (A 1 + B 1) + κ = 0
    simp only [sub_self, zero_mul, zero_add, κ, hb, mul_zero]

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.LogNormEstimates
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace LogNormEstimates

theorem log_le {D a b : ℝ} (hD : 0 < D) (ha : 0 < a) (h1 : a ≤ D) (h2 : D ≤ b) :
    |Real.log D| ≤ |Real.log a| + |Real.log b| := by
  have l1 := Real.log_le_log ha h1
  have l2 := Real.log_le_log hD h2
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log a), abs_nonneg (Real.log b)]
  · linarith [le_abs_self (Real.log b), abs_nonneg (Real.log a)]

theorem norm_le {p : ℂ} {D a b : ℝ} (hD : 0 < D) (ha : 0 < a) (h : p ≠ 0 → a ≤ D ∧ D ≤ b) (z z₀ : ℂ) :
    ‖p * (D : ℂ) ^ z‖ ≤ ‖p * (D : ℂ) ^ z₀‖ * Real.exp ((|Real.log a| + |Real.log b|) * |z.re - z₀.re|) := by
  by_cases hp : p = 0
  · simp [hp]
  obtain ⟨h1, h2⟩ := h hp
  rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hD, Complex.norm_cpow_eq_rpow_re_of_pos hD]
  have e : D ^ z.re = D ^ z₀.re * D ^ (z.re - z₀.re) := by
    rw [← Real.rpow_add hD]; congr 1; ring
  rw [e, ← mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  rw [Real.rpow_def_of_pos hD]
  apply Real.exp_le_exp.2
  calc Real.log D * (z.re - z₀.re) ≤ |Real.log D * (z.re - z₀.re)| := le_abs_self _
    _ = |Real.log D| * |z.re - z₀.re| := abs_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (log_le hD ha h1 h2) (abs_nonneg _)

theorem re_eq (p : ℂ) {D : ℝ} (hD : 0 < D) (σ u : ℝ) :
    (p * (D : ℂ) ^ ((σ : ℂ) + u * Complex.I)).re = D ^ σ * (p * (D : ℂ) ^ ((u : ℂ) * Complex.I)).re := by
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 hD.ne'), ← Complex.ofReal_cpow hD.le σ,
    show p * (((D ^ σ : ℝ) : ℂ) * (D : ℂ) ^ ((u : ℂ) * Complex.I)) =
      ((D ^ σ : ℝ) : ℂ) * (p * (D : ℂ) ^ ((u : ℂ) * Complex.I)) by ring, Complex.re_ofReal_mul]

set_option synthInstance.maxHeartbeats 400000 in
theorem msc {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {k : ℕ} :
    MeasurableSingletonClass (GA E k) := inferInstance

end LogNormEstimates

theorem log_norm_estimate_of_Q : Q1 → D0 → N3 → C0 → D1 := by
  intro hQ1 hD0 hN3 hC0
  unfold D1 ForMu
  intro E _ _ _ k μ _ hk β hβ S P u z₀ hPc hPinv hP1 hpos hint
  obtain ⟨hDpos, hDmul, hDc, -, hDUU, -⟩ := hD0 E k
  obtain ⟨hG0o, h1G0, hG0inv, -⟩ := hC0 E k S
  obtain ⟨hNP, -, -, hN0⟩ := hN3 E k
  obtain ⟨hνs, hνinv, -⟩ := hNP 0 (by omega)
  obtain ⟨a, b, ha, hab⟩ := hpos
  have hD1 : Dt (1 : GA E k) = 1 := by
    have h := hDmul 1 1
    simp only [mul_one] at h
    exact (mul_left_cancel₀ (hDpos 1).ne' (by rw [mul_one]; exact h.symm))
  have hG0m : MeasurableSet (G0 (k := k) S) := hG0o.measurableSet
  have hcont : ∀ z : ℂ, Continuous fun g : GA E k => P g * (Dt g : ℂ) ^ z := fun z =>
    hPc.mul ((Complex.continuous_ofReal.comp hDc).cpow continuous_const
      fun g => Complex.ofReal_mem_slitPlane.2 (hDpos g))
  set L := |Real.log a| + |Real.log b| with hL
  have hL0 : 0 ≤ L := by positivity
  have hdom : ∀ g ∈ G0 (k := k) S, ∀ z : ℂ,
      ‖P g * (Dt g : ℂ) ^ z‖ ≤ ‖P g * (Dt g : ℂ) ^ z₀‖ * Real.exp (L * |z.re - z₀.re|) := by
    intro g hg z
    exact LogNormEstimates.norm_le (hDpos g) ha (fun hp => ⟨(hab g hg hp).1, (hab g hg hp).2.1⟩) z z₀
  have hintG : ∀ z : ℂ, Integrable (fun g => P g * (Dt g : ℂ) ^ z) ((μ.withDensity β).restrict (G0 S)) := by
    intro z
    refine Integrable.mono' ((hint.norm.mul_const (Real.exp (L * |z.re - z₀.re|))).restrict)
      (hcont z).aestronglyMeasurable ?_
    exact ae_restrict_of_forall_mem hG0m fun g hg => hdom g hg z
  refine ⟨fun z₁ => ?_, fun σ => ?_⟩
  · have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (μ.withDensity β).restrict (G0 S))
      (F := fun z g => P g * (Dt g : ℂ) ^ z)
      (F' := fun z g => P g * (Dt g : ℂ) ^ z * ((Real.log (Dt g) : ℝ) : ℂ)) (x₀ := z₁)
      (bound := fun g => ‖P g * (Dt g : ℂ) ^ z₀‖ * Real.exp (L * (|z₁.re - z₀.re| + 1)) * L) (Metric.ball_mem_nhds z₁ zero_lt_one)
      (Filter.Eventually.of_forall fun z => (hcont z).aestronglyMeasurable) (hintG z₁)
      ((hcont z₁).mul (Complex.continuous_ofReal.comp (hDc.log fun g => (hDpos g).ne'))).aestronglyMeasurable
      ?_ (((hint.norm.mul_const _).mul_const _).restrict) ?_
    · exact hderiv.2.differentiableAt
    · refine ae_restrict_of_forall_mem hG0m fun g hg z hz => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      by_cases hp : P g = 0
      · simp only [hp, zero_mul, norm_zero]; positivity
      have hlog := LogNormEstimates.log_le (hDpos g) ha (hab g hg hp).1 (hab g hg hp).2.1
      have hz' : |z.re - z₀.re| ≤ |z₁.re - z₀.re| + 1 := by
        have h1 : |z.re - z₁.re| ≤ 1 := by
          have := Complex.abs_re_le_norm (z - z₁)
          rw [Metric.mem_ball, dist_eq_norm] at hz
          rw [Complex.sub_re] at this; linarith
        calc |z.re - z₀.re| = |(z.re - z₁.re) + (z₁.re - z₀.re)| := by ring_nf
          _ ≤ |z.re - z₁.re| + |z₁.re - z₀.re| := abs_add_le _ _
          _ ≤ _ := by linarith
      have e1 := hdom g hg z
      have e2 : Real.exp (L * |z.re - z₀.re|) ≤ Real.exp (L * (|z₁.re - z₀.re| + 1)) :=
        Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left hz' hL0)
      calc ‖P g * (Dt g : ℂ) ^ z‖ * |Real.log (Dt g)|
          ≤ (‖P g * (Dt g : ℂ) ^ z₀‖ * Real.exp (L * (|z₁.re - z₀.re| + 1))) * L := by
            apply mul_le_mul _ hlog (abs_nonneg _) (by positivity)
            exact e1.trans (mul_le_mul_of_nonneg_left e2 (norm_nonneg _))
        _ = _ := rfl
    · refine Filter.Eventually.of_forall fun g z _ => ?_
      have hD := hDpos g
      have h := ((hasDerivAt_id z).const_cpow (c := (Dt g : ℂ))
        (Or.inl (Complex.ofReal_ne_zero.2 hD.ne'))).const_mul (P g)
      have e : P g * ((Dt g : ℂ) ^ id z * Complex.log (Dt g) * 1) =
          P g * (Dt g : ℂ) ^ z * ((Real.log (Dt g) : ℝ) : ℂ) := by
        rw [Complex.ofReal_log hD.le]; simp only [id, mul_one]; ring
      exact h.congr_deriv e
  · set f : GA E k → ℝ := fun g => (P g * (Dt g : ℂ) ^ ((u : ℂ) * Complex.I)).re with hf
    have hfc : Continuous f := Complex.continuous_re.comp (hcont _)
    set O : Set (GA E k) := G0 S ∩ {g | 0 < f g} with hO
    have hOo : IsOpen O := hG0o.inter (isOpen_lt continuous_const hfc)
    have hOm : MeasurableSet O := hOo.measurableSet
    have h1O : (1 : GA E k) ∈ O := by
      refine ⟨h1G0, ?_⟩
      show 0 < (P 1 * ((Dt (1 : GA E k) : ℝ) : ℂ) ^ ((u : ℂ) * Complex.I)).re
      rw [hD1, Complex.ofReal_one, Complex.one_cpow, mul_one]; exact hP1
    have hOinv : ∀ n g, UU 0 n → (n * g ∈ O ↔ g ∈ O) := by
      intro n g hn
      simp only [hO, hf, Set.mem_inter_iff, Set.mem_setOf_eq, hG0inv n g hn, hPinv n hn g, hDmul, hDUU 0 n hn,
        one_mul]
    haveI : MeasurableSingletonClass (GA E k) := LogNormEstimates.msc
    have hμO : μ O ≠ 0 := (hOo.measure_pos μ ⟨1, h1O⟩).ne'
    have hβO : μ.withDensity β O ≠ 0 := by
      intro h0
      apply hμO
      have hin : ∀ g, ∫⁻ r, O.indicator 1 (r * g) ∂nuP E k 0 = O.indicator 1 g * nuP E k 0 Set.univ := by
        intro g
        rw [← lintegral_const]
        apply lintegral_congr_ae
        filter_upwards [(hN0 hk).1] with r hr
        by_cases hg : g ∈ O
        · simp [Set.indicator_apply, hg, (hOinv r g hr).2 hg]
        · simp [Set.indicator_apply, hg, mt (hOinv r g hr).1 hg]
      have key := hQ1 (GA E k) μ (Measure.dirac 1) (nuP E k 0) {1} (fun _ => 1) β
        (by rw [Measure.map_dirac' measurable_inv, inv_one]) (by rw [ae_dirac_eq]; exact rfl)
        ⟨measurable_const, fun g => by simp⟩ hβ.1
        (fun g => by
          simp only [lintegral_dirac, mul_one]
          calc ∫⁻ r, β (r⁻¹ * g) ∂nuP E k 0 = ∫⁻ r, β (r * g) ∂(Measure.map (fun h => h⁻¹) (nuP E k 0)) :=
                (lintegral_map (hβ.1.comp (measurable_mul_const g)) measurable_inv).symm
            _ = 1 := by rw [hνinv]; exact hβ.2 g)
        (O.indicator 1) (measurable_one.indicator hOm) (by rintro h rfl g; simp)
      have hw : μ.withDensity (fun _ => (1 : ℝ≥0∞)) = μ := withDensity_one
      rw [hw, lintegral_indicator_one hOm] at key
      rw [key]
      simp_rw [hin]
      rw [lintegral_mul_const _ (measurable_one.indicator hOm), lintegral_indicator_one hOm, h0, zero_mul]
    intro hzero
    have hFi := hintG ((σ : ℂ) + u * Complex.I)
    have hre := integral_re hFi
    rw [hzero] at hre
    simp only [RCLike.re_to_complex, Complex.zero_re] at hre
    have hpos' := (setIntegral_pos_iff_support_of_nonneg_ae (s := G0 S) (μ := μ.withDensity β)
      (f := fun g => (P g * (Dt g : ℂ) ^ ((σ : ℂ) + u * Complex.I)).re)
      (ae_restrict_of_forall_mem hG0m fun g hg => ?_) hFi.re).2 ?_
    · linarith
    · by_cases hp : P g = 0
      · simp [hp]
      show 0 ≤ (P g * (Dt g : ℂ) ^ ((σ : ℂ) + u * Complex.I)).re
      rw [LogNormEstimates.re_eq _ (hDpos g)]
      exact mul_nonneg (Real.rpow_nonneg (hDpos g).le _) (hab g hg hp).2.2
    · refine lt_of_lt_of_le (pos_iff_ne_zero.2 hβO) (measure_mono fun g hg => ⟨?_, hg.1⟩)
      rw [Function.mem_support, LogNormEstimates.re_eq _ (hDpos g)]
      exact (mul_pos (Real.rpow_pos_of_pos (hDpos g) σ) hg.2).ne'

end PositivityTheory.AdelicQuotientData

end
end

