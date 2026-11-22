import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0001
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0796
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.Bundle0005
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ContinuousPrN
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0749
import GroundTheory.AutomorphicForms.CompactFormulaCountable
import GroundTheory.GlobalFields.TateThesis.IdeleMeasureQuotient
import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Bundle0002
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ThetaBounds.Bundle0008
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.Bundle0003

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPartAlt
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent

private theorem tsum_split (δ : ℚ) (f : (Fin 4 → ℚ) → ℂ) (hf : Summable f) :
    ∑' ξ, f ξ = f 0 + (∑' ξ : ({ξ | ξ ≠ 0 ∧ qr δ ξ = 0} : Set (Fin 4 → ℚ)), f ξ) +
      ∑' ξ : ({ξ | qr δ ξ ≠ 0} : Set (Fin 4 → ℚ)), f ξ := by
  set R : Set (Fin 4 → ℚ) := {ξ | ξ ≠ 0 ∧ qr δ ξ = 0}
  set Q : Set (Fin 4 → ℚ) := {ξ | qr δ ξ ≠ 0}
  have h0 : qr δ 0 = 0 := by simp [qr]
  have hpt : ∀ ξ, f ξ = (({0} : Set (Fin 4 → ℚ)).indicator f ξ + R.indicator f ξ) + Q.indicator f ξ := by
    intro ξ
    by_cases hq : qr δ ξ = 0
    · by_cases hξ : ξ = 0
      · subst hξ
        simp [R, Q, h0]
      · simp [R, Q, hξ, hq]
    · have hξ : ξ ≠ 0 := fun e => hq (e ▸ h0)
      simp [R, Q, hξ, hq]
  have s0 := hf.indicator ({0} : Set (Fin 4 → ℚ))
  have sR := hf.indicator R
  have sQ := hf.indicator Q
  rw [tsum_subtype R f, tsum_subtype Q f]
  have e0 : ∑' ξ, ({0} : Set (Fin 4 → ℚ)).indicator f ξ = f 0 := by
    rw [← tsum_subtype]; simp
  rw [← e0, ← (s0.tsum_add sR), ← ((s0.add sR).tsum_add sQ)]
  exact tsum_congr hpt

private theorem cD_one (g : G1 ℚ) : cD 1 g = g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD]

private theorem ab_one' : ab (1 : (A ℚ)ˣ) = 1 := by
  simp [ab]

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {D : Dat ℚ E}

private theorem act_zero (h : GL (Fin 2) (A E)) : D.act h (0 : V4 ℚ) = 0 := by
  have e : D.herm (0 : V4 ℚ) = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Dat.herm, Dat.mkE]
  have e2 : D.unherm (0 : Matrix (Fin 2) (Fin 2) (A E)) = 0 := by
    funext i
    fin_cases i <;> simp [Dat.unherm, Dat.co]
  simp [Dat.act, e, e2]

private theorem om_zero (W : Weil D) (g : G1 ℚ) (ph : S4 ℚ) (x : GL (Fin 2) (A E)) (hx : nu ℚ x = 1) :
    (W.Om g (W.L x ph)).1 (rp 0) = (W.Om g ph).1 (rp 0) := by
  have h1 := W.comm x g
  rw [hx, cD_one] at h1
  have h2 : W.Om g (W.L x ph) = W.L x (W.Om g ph) := by
    have := congrArg (fun T : Module.End ℂ (S4 ℚ) => T ph) h1
    simpa [Module.End.mul_apply] using this.symm
  have hz : rp (0 : Fin 4 → ℚ) = (0 : V4 ℚ) := by
    funext i; simp [rp]
  rw [h2, W.L_apply, hx, ab_one', hz, act_zero]
  simp

private theorem core (hMaj : Maj) (hTh : ThCont) (hMean : MeanZero) (hR1 : Rank1)
    (W : Weil D) (M : Meas ℚ) (N : MeasE E) (P : CuspSub E 2) (hV : N.μ N.D < ⊤)
    (ph : S4 ℚ) (hph : ph ∈ Fock D.δ) (φ : Sm E 2) (hφ : φ ∈ P.V) (g : G1 ℚ)
    (y : GL (Fin 2) (A E)) (hy : nu ℚ y = 1) (hgl : ∀ h : G1 E, nu ℚ (gl h) = 1) :
    (mean N fun x => Th (W.Om g (W.L (x * y) ph)).1 * φ.1 (x * y)) =
      mean N fun x => ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om g (W.L (x * y) ph)).1 * φ.1 (x * y) := by
  obtain ⟨b, a, k', hk', hg⟩ := UpperTheory.ConvolutionTheory.R2.M.iwa ℚ g
  have hapos : 0 < ab a := (IdeleGroup.ideleModule ℚ a).2
  obtain ⟨B, hB⟩ := hMaj E D W M N P ph hph φ hφ {y} isCompact_singleton
    (by rintro k rfl; exact hy) (ab a) hapos 0
  have hB' : ∀ h : G1 E, (Summable fun ξ : Fin 4 → ℚ => ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) ∧
      (∑' ξ : Fin 4 → ℚ, ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖) * ‖φ.1 (gl h * y)‖ ≤ B * ab a ^ 2 := by
    intro h
    have := hB b a k' hk' le_rfl h y rfl
    rw [← hg] at this
    exact ⟨this.1, this.2.1⟩
  have hnu : ∀ h : G1 E, nu ℚ (gl h * y) = 1 := fun h => by rw [nu_mul, hgl, hy, one_mul]
  have hcφ : Continuous φ.1 := GlobalTheory.T.automorphicForm_GL_continuous E 2 φ (P.cusp φ hφ).1
  have hcg : Continuous fun h : G1 E => gl h := by fun_prop
  have hcx : Continuous fun h : G1 E => gl h * y := hcg.mul continuous_const
  haveI : IsFiniteMeasure (N.μ.restrict N.D) := ⟨by simpa using hV⟩
  have hint : ∀ S : Set (Fin 4 → ℚ), IntegrableOn
      (fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y)) N.D N.μ := by
    intro S
    have hc1 : Continuous fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1 :=
      (hTh E D W M N P ph hph S).comp_continuous (f := fun h : G1 E => (g, gl h * y))
        (continuous_const.prodMk hcx) (fun h => hnu h)
    have hc : Continuous fun h : G1 E => ThOn S (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) :=
      hc1.mul (hcφ.comp hcx)
    refine Integrable.of_bound hc.aestronglyMeasurable (B * ab a ^ 2) (Eventually.of_forall fun h => ?_)
    obtain ⟨hs, hb⟩ := hB' h
    have hle : ‖ThOn S (W.Om g (W.L (gl h * y) ph)).1‖ ≤
        ∑' ξ : Fin 4 → ℚ, ‖(W.Om g (W.L (gl h * y) ph)).1 (rp ξ)‖ := by
      have hsS := hs.subtype S
      refine (norm_tsum_le_tsum_norm hsS).trans ?_
      exact tsum_comp_le_tsum_of_inj hs (fun _ => norm_nonneg _) Subtype.val_injective
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hle (norm_nonneg _)).trans hb
  set c : ℂ := (W.Om g ph).1 (rp 0)
  have hz : ∀ h : G1 E, ThOn {0} (W.Om g (W.L (gl h * y) ph)).1 = c := by
    intro h
    have e : ThOn {0} (W.Om g (W.L (gl h * y) ph)).1 = (W.Om g (W.L (gl h * y) ph)).1 (rp 0) := by
      simp [ThOn]
    rw [e]
    exact om_zero W g ph _ (hnu h)
  have hφi : IntegrableOn (fun h : G1 E => c * φ.1 (gl h * y)) N.D N.μ := by
    refine (hint {0}).congr (Eventually.of_forall fun h => ?_)
    simp only [hz]
  have hpt : ∀ h : G1 E, Th (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) =
      c * φ.1 (gl h * y) +
        ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) +
        ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) := by
    intro h
    have hsp := tsum_split D.δ (fun ξ => (W.Om g (W.L (gl h * y) ph)).1 (rp ξ)) (hB' h).1.of_norm
    have e0 : (W.Om g (W.L (gl h * y) ph)).1 (rp 0) = c := om_zero W g ph _ (hnu h)
    have : Th (W.Om g (W.L (gl h * y) ph)).1 = c + ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 +
        ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om g (W.L (gl h * y) ph)).1 := by
      rw [← e0]
      exact hsp
    rw [this]
    ring
  have z1 : ∫ h in N.D, φ.1 (gl h * y) ∂N.μ = 0 := hMean E D W M N P φ hφ y
  have z2 : ∫ h in N.D, ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y) ∂N.μ = 0 :=
    hR1 E D W M N P ph hph φ hφ g y hy
  simp only [mean]
  simp only [hpt]
  have i1 : IntegrableOn (fun h : G1 E => c * φ.1 (gl h * y) +
      ThOn {ξ | ξ ≠ 0 ∧ qr D.δ ξ = 0} (W.Om g (W.L (gl h * y) ph)).1 * φ.1 (gl h * y)) N.D N.μ := hφi.add (hint _)
  rw [integral_add i1 (hint _), integral_add hφi (hint _), integral_const_mul, z1, z2]
  simp

end UpperTheory.ConvolutionTheory.RankTwoDescent

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.f0Eq :
    Maj → ThCont → MeanZero → Rank1 → ThetaLiftEqAnisotropicPart := by
  intro hMaj hTh hMean hR1 E _ _ _ D W M N P ph hph φ hφ
  funext g
  have hS := szLaws E D
  simp only [f0, fOn, J1]
  refine congrArg (UI (E := E)) (funext fun z => ?_)
  exact core hMaj hTh hMean hR1 W M N P (UpperTheory.ConvolutionTheory.RankTwoDescent.volE E N) ph hph φ hφ g (sZ D z) (hS.2.2.1 z) hS.2.2.2.1
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftIsBoundedCuspidal
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.FundamentalDomainContinuity

private theorem cont_nested {X Z Y : Type} [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Z] [SecondCountableTopology Z] [MeasurableSpace Z] [BorelSpace Z]
    [TopologicalSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (μ : Measure Z) (ν : Measure Y) (S : Set Z) (Dm : Set Y) (hS : MeasurableSet S) (hμ : μ S < ⊤) (hν : ν Dm < ⊤)
    (f : X → Z → Y → ℂ) (x₀ : X) (U : Set X) (hU : U ∈ 𝓝 x₀) (B : ℝ)
    (hb : ∀ x ∈ U, ∀ z ∈ closure S, ∀ y, ‖f x z y‖ ≤ B)
    (hc : ∀ y, Continuous fun p : X × Z => f p.1 p.2 y)
    (hy : ∀ x z, Continuous (f x z)) :
    ContinuousAt (fun x => ∫ z in S, ∫ y in Dm, f x z y ∂ν ∂μ) x₀ := by
  have hint : Integrable (fun _ : Y => B) (ν.restrict Dm) := integrableOn_const hν.ne
  have hG : ∀ x ∈ U, ContinuousOn (fun z => ∫ y in Dm, f x z y ∂ν) (closure S) := by
    intro x hx z₀ hz₀
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_ hint ?_
    · exact Eventually.of_forall fun z => (hy x z).aestronglyMeasurable
    · exact eventually_nhdsWithin_of_forall fun z hz => Eventually.of_forall fun y => hb x hx z hz y
    · refine Eventually.of_forall fun y => ?_
      have h1 : Continuous fun z => f x z y := (hc y).comp (Continuous.prodMk_right x)
      exact h1.continuousWithinAt
  refine tendsto_integral_filter_of_dominated_convergence (fun _ => B * ν.real Dm) ?_ ?_ (integrableOn_const hμ.ne) ?_
  · filter_upwards [hU] with x hx
    exact ((hG x hx).aestronglyMeasurable isClosed_closure.measurableSet).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  · filter_upwards [hU] with x hx
    refine ae_restrict_of_forall_mem hS fun z hz => ?_
    exact norm_setIntegral_le_of_norm_le_const hν fun y _ => hb x hx z (subset_closure hz) y
  · refine ae_restrict_of_forall_mem hS fun z hz => ?_
    refine tendsto_integral_filter_of_dominated_convergence (fun _ => B) ?_ ?_ hint ?_
    · exact Eventually.of_forall fun x => (hy x z).aestronglyMeasurable
    · filter_upwards [hU] with x hx
      exact Eventually.of_forall fun y => hb x hx z (subset_closure hz) y
    · refine Eventually.of_forall fun y => ?_
      have h1 : Continuous fun x => f x z y := (hc y).comp (Continuous.prodMk_left z)
      exact h1.continuousAt

variable {E : Type} [Field E] [NumberField E]

private theorem norm_liftIntegral_le (D : Dat ℚ E) (N : MeasE E) (hV : N.μ N.D < ⊤) (Ψ : GL (Fin 2) (A E) → ℂ) (B : ℝ)
    (hB : ∀ z ∈ normOneFundamentalDomain E, ∀ h : G1 E, ‖Ψ (gl h * sZ D (z : IdeleGroup E))‖ ≤ B) :
    ‖J1 D N Ψ‖ ≤ B * N.μ.real N.D * (normOneMeasure E).real (normOneFundamentalDomain E) := by
  unfold J1 UI
  refine norm_setIntegral_le_of_norm_le_const (normOneMeasure_normOneFundamentalDomain_lt_top E) fun z hz => ?_
  unfold mean
  exact norm_setIntegral_le_of_norm_le_const hV fun h _ => hB z hz h

end UpperTheory.ConvolutionTheory.RankTwoDescent.FundamentalDomainContinuity

open UpperTheory.ConvolutionTheory.RankTwoDescent.FundamentalDomainContinuity in
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.thetaPairing_constantTerm_cuspidal :
    Maj → ThCont → ThetaLiftEqAnisotropicPart → Coef → ThetaLiftIsBoundedCuspidal := by
  intro hMaj hTh hF0 hCoef E _ _ _ D W M N P ph hph φ hφ
  obtain ⟨-, hsC, hsN, hgN, -, -, -, -, -, -, -⟩ := szLaws E D
  have hφc : Continuous φ.1 := IsAutForm.continuous (P.cusp φ hφ).1
  have hV : N.μ N.D < ⊤ := volE E N
  set Zc : Set ↥(IdeleGroup.normOneSubgroup E) := closure (normOneFundamentalDomain E) with hZc
  have hZcpt : IsCompact Zc := isCompact_closure_normOneFundamentalDomain E
  have hsz : Continuous fun z : ↥(IdeleGroup.normOneSubgroup E) => sZ D (z : IdeleGroup E) :=
    hsC.comp continuous_subtype_val
  set C : Set (GL (Fin 2) (A E)) := (fun z : ↥(IdeleGroup.normOneSubgroup E) => sZ D (z : IdeleGroup E)) '' Zc with hCdef
  have hC : IsCompact C := hZcpt.image hsz
  have hCn : ∀ k ∈ C, nu ℚ k = 1 := by
    rintro k ⟨z, -, rfl⟩
    exact hsN _
  have hzC : ∀ z ∈ Zc, sZ D (z : IdeleGroup E) ∈ C := fun z hz => ⟨z, hz, rfl⟩
  have hleft : LInv (f0 W N ph φ.1) := by
    intro γ g
    simp only [f0, map_mul, Module.End.mul_apply, W.th_Om]
  have hth := hTh E D W M N P ph hph Set.univ
  have eTh : ∀ u : V4 ℚ → ℂ, ThOn Set.univ u = Th u := fun u => tsum_univ (fun ξ : Fin 4 → ℚ => u (rp ξ))
  have hnu : ∀ (h : G1 E) (z : (A E)ˣ), (gl h * sZ D z) ∈ {x : GL (Fin 2) (A E) | nu ℚ x = 1} := by
    intro h z
    have a1 : ideleNorm ℚ E (Matrix.GeneralLinearGroup.det (gl h)) = 1 := hgN h
    have a2 : ideleNorm ℚ E (Matrix.GeneralLinearGroup.det (sZ D z)) = 1 := hsN z
    change ideleNorm ℚ E (Matrix.GeneralLinearGroup.det (gl h * sZ D z)) = 1
    rw [map_mul, map_mul, a1, a2, one_mul]
  refine ⟨?_, hleft, ?_, ?_⟩
  ·
    refine continuous_iff_continuousAt.2 fun g₀ => ?_
    obtain ⟨U, hUc, hU⟩ := exists_compact_mem_nhds g₀
    obtain ⟨-, hIw⟩ := UpperTheory.ConvolutionTheory.R2.Ff.iwa ℚ
    obtain ⟨V, hVc, hVU⟩ := hIw U hUc
    have hab : Continuous (ab : (A ℚ)ˣ → ℝ) := UpperTheory.ConvolutionTheory.R2.continuous_ab
    have hpos : ∀ a : (A ℚ)ˣ, 0 < ab a := fun a => (IdeleGroup.ideleModule ℚ a).2
    obtain ⟨T, hT⟩ := hVc.exists_bound_of_continuousOn hab.continuousOn
    obtain ⟨T', hT'⟩ := hVc.exists_bound_of_continuousOn
      (f := fun a => (ab a)⁻¹) (hab.inv₀ fun a => (hpos a).ne').continuousOn
    have hc0 : 0 < (|T'| + 1)⁻¹ := inv_pos.2 (by positivity)
    obtain ⟨B, hB⟩ := hMaj E D W M N P ph hph φ hφ C hC hCn _ hc0 0
    refine cont_nested (normOneMeasure E) N.μ (normOneFundamentalDomain E) N.D
      (measurableSet_normOneFundamentalDomain E) (normOneMeasure_normOneFundamentalDomain_lt_top E) hV
      (fun g z h => Th (W.Om g (W.L (gl h * sZ D (z : IdeleGroup E)) ph)).1 * φ.1 (gl h * sZ D (z : IdeleGroup E)))
      g₀ U hU (|B| * T ^ 2) ?_ ?_ ?_
    · intro x hx z hz h
      obtain ⟨b, a, ha, k, hk, rfl⟩ := hVU x hx
      have hle : (|T'| + 1)⁻¹ ≤ ab a := by
        have h1 : (ab a)⁻¹ ≤ |T'| + 1 := by
          have := hT' a ha
          rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hpos a))] at this
          linarith [le_abs_self T']
        exact (inv_le_comm₀ (hpos a) (by positivity)).1 h1
      obtain ⟨h1, h2, -⟩ := hB b a k hk hle h _ (hzC z hz)
      have h3 : ab a ≤ T := by
        have := hT a ha
        rwa [Real.norm_eq_abs, abs_of_pos (hpos a)] at this
      rw [norm_mul]
      calc _ ≤ _ := mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm h1) (norm_nonneg _)
        _ ≤ _ := h2
        _ ≤ |B| * T ^ 2 := mul_le_mul (le_abs_self B)
          (pow_le_pow_left₀ (hpos a).le h3 2) (by have := hpos a; positivity) (abs_nonneg B)
    · intro y
      have hA : Continuous fun p : G1 ℚ × ↥(IdeleGroup.normOneSubgroup E) => (p.1, gl y * sZ D (p.2 : IdeleGroup E)) :=
        continuous_fst.prodMk (continuous_const.mul (hsz.comp continuous_snd))
      have h1 := hth.comp_continuous hA (fun p => hnu y _)
      simp only [eTh] at h1
      exact h1.mul (hφc.comp (continuous_const.mul (hsz.comp continuous_snd)))
    · intro x z
      have hA : Continuous fun h : G1 E => (x, gl h * sZ D (z : IdeleGroup E)) :=
        continuous_const.prodMk (UpperTheory.ConvolutionTheory.R2.continuous_gl.mul continuous_const)
      have h1 := hth.comp_continuous hA (fun h => hnu h _)
      simp only [eTh] at h1
      exact h1.mul (hφc.comp (UpperTheory.ConvolutionTheory.R2.continuous_gl.mul continuous_const))
  ·
    obtain ⟨c, hc, hred⟩ := red ℚ
    obtain ⟨B, hB⟩ := hMaj E D W M N P ph hph φ hφ C hC hCn c hc 0
    refine ⟨B * N.μ.real N.D * (normOneMeasure E).real (normOneFundamentalDomain E), fun g => ?_⟩
    obtain ⟨γ, b, a, k, hk, he, hle⟩ := hred g
    rw [← hleft γ g, he, hF0 E D W M N P ph hph φ hφ]
    refine norm_liftIntegral_le D N hV _ B fun z hz h => ?_
    obtain ⟨h1, -, h3⟩ := hB b a k hk hle h _ (hzC z (subset_closure hz))
    have h4 : ‖ThOn {ξ | qr D.δ ξ ≠ 0} (W.Om (nU b * mD a * k) (W.L (gl h * sZ D (z : IdeleGroup E)) ph)).1‖ ≤
        ∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0},
          ‖(W.Om (nU b * mD a * k) (W.L (gl h * sZ D (z : IdeleGroup E)) ph)).1 (rp ξ.1)‖ :=
      norm_tsum_le_tsum_norm (h1.subtype _)
    rw [norm_mul]
    refine (mul_le_mul_of_nonneg_right h4 (norm_nonneg _)).trans ?_
    simpa using h3
  ·
    intro g
    have h := hCoef E D W M N P ph hph φ hφ 0 g
    have e0 : fOn W N {ξ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = 0} ph φ.1 g = 0 := by
      have e : {ξ : Fin 4 → ℚ | qr D.δ ξ ≠ 0 ∧ qr D.δ ξ = 0} = ∅ := by
        ext ξ
        simp
      rw [e]
      simp [fOn, J1, UI, mean, ThOn]
    have e1 : ∀ b : A ℚ, ψ (-(b * UpperTheory.ConvolutionTheory.R2.rt (0 : ℚ))) = 1 := fun b => by simp [ψ, UpperTheory.ConvolutionTheory.R2.rt]
    rw [e0, mul_zero] at h
    simp only [e1, mul_one] at h
    rw [hF0 E D W M N P ph hph φ hφ]
    exact h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.WtNonneg
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

private theorem cD_one' {F : Type} [Field F] [NumberField F] (g : G1 F) : cD (1 : (A F)ˣ) g = g := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cD]

private theorem norm_eta {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {D : Dat ℚ E} (W : Weil D)
    (a : (A ℚ)ˣ) : ‖((W.η.1 a : ℂˣ) : ℂ)‖ = 1 := by
  have h2 : ((W.η.1 a : ℂˣ) : ℂ) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, W.η_sq a, Units.val_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).mp (by rw [← norm_pow, h2, norm_one])

private theorem om_norm {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {D : Dat ℚ E} (W : Weil D)
    (ph : S4 ℚ) (b : A ℚ) (a : (A ℚ)ˣ) (k' : G1 ℚ) (x : GL (Fin 2) (A E)) (hx : nu ℚ x = 1) (v : V4 ℚ) :
    ‖(W.Om (nU b * mD a * k') (W.L x ph)).1 v‖ =
      ab a ^ 2 * ‖(W.Om k' ph).1 (fun i => (a : A ℚ) * D.act x⁻¹ v i)‖ := by
  have hc : W.Om (nU b * mD a * k') (W.L x ph) = W.L x (W.Om (nU b * mD a * k') ph) := by
    have := W.comm x (nU b * mD a * k')
    rw [hx, cD_one'] at this
    exact (congrArg (fun T : Module.End ℂ (S4 ℚ) => T ph) this).symm
  have hab : ab (1 : (A ℚ)ˣ) = 1 := by simp [ab]
  have hψ : ∀ y : A ℚ, ‖ψ y‖ = 1 := fun y => Circle.norm_coe _
  rw [hc, W.L_apply, hx, hab, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, W.Om_n, W.Om_m]
  simp only [inv_one, Complex.ofReal_one, one_mul, norm_mul, hψ, norm_eta W, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity)]

private theorem rat_eq {E : Type} [Field E] [NumberField E] (γ : Matrix.SpecialLinearGroup (Fin 2) E) :
    gl (ratS E γ) = ratGL E 2 (Matrix.SpecialLinearGroup.toGL γ) := by
  ext i j
  simp [ratS, ratGL]

private theorem qr_rho {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) (g : G1 E) (ξ ξ' : Fin 4 → ℚ)
    (h : D.act (gl g) (rp ξ) = rp ξ') : qr D.δ ξ' = qr D.δ ξ := by
  have hq : ∀ ζ : Fin 4 → ℚ, q4 D.δ (rp ζ) = rt (qr D.δ ζ) := fun ζ => by simp [q4, qr]
  haveI : Nontrivial (A ℚ) :=
    RingHom.domain_nontrivial (RingHom.fst (InfiniteAdeleRing ℚ) (FiniteAdeleRing (𝓞 ℚ) ℚ))
  have := D.quadForm_act (gl g) (rp ξ)
  rw [h, nu_gl, hq, hq, Units.val_one, one_mul] at this
  exact (algebraMap ℚ (A ℚ)).injective this

private theorem sum_tr {Y Y' : Type} (σ : Y ≃ Y') (f : Y → ℝ) (w : Y' → ℝ) (T : ℝ) (hf0 : ∀ y, 0 ≤ f y)
    (hs : Summable w) (h : ∀ y, f y ≤ T * w (σ y)) : Summable f ∧ ∑' y, f y ≤ T * ∑' y', w y' := by
  have hs' : Summable fun y => T * w (σ y) := (σ.summable_iff.2 hs).mul_left T
  have hf : Summable f := Summable.of_nonneg_of_le hf0 h hs'
  refine ⟨hf, (hf.tsum_le_tsum h hs').trans (le_of_eq ?_)⟩
  rw [tsum_mul_left, σ.tsum_eq w]

private theorem wt_nonneg'' (S : Set (Fin 4 → FiniteAdeleRing (𝓞 ℚ) ℚ)) (N : ℕ) (v : V4 ℚ) : 0 ≤ wt S N v := by
  unfold wt
  split_ifs
  · positivity
  · exact le_rfl

private theorem maj_core (hL : LatSum) (hDec : DecE) (E : Type) [Field E] [NumberField E] [IsTotallyComplex E]
    (D : Dat ℚ E) (W : Weil D) (P : CuspSub E 2) (hO : Orb1) (Ω : Set (GL (Fin 2) (A E))) (hΩ : IsCompact Ω)
    (hΩ1 : ∀ k ∈ Ω, nu ℚ k = 1) (c₀ : ℝ) (hc₀ : 0 < c₀)
    (hred : ∀ h : G1 E, ∃ (γ : Matrix.SpecialLinearGroup (Fin 2) E) (u : A E) (β : (A E)ˣ), ∃ k₁ ∈ Ω,
      gl (ratS E γ) * gl h = gl (nU u * mD β) * k₁ ∧ c₀ ≤ ab β)
    (ph : S4 ℚ) (hph : ph ∈ Fock D.δ) (φ : ↥(Sm E 2)) (hφP : φ ∈ P.V) (C : Set (GL (Fin 2) (A E))) (hC : IsCompact C)
    (hC1 : ∀ k ∈ C, nu ℚ k = 1) (c : ℝ) (hc : 0 < c) (s : ℕ) :
    ∃ B : ℝ, ∀ b a, ∀ k' ∈ KK ℚ, c ≤ ab a → ∀ h : G1 E, ∀ k ∈ C,
    (Summable fun ξ : Fin 4 → ℚ => ‖(W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 (rp ξ)‖) ∧
    (∑' ξ : Fin 4 → ℚ, ‖(W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 (rp ξ)‖) * ‖φ.1 (gl h * k)‖ ≤ B * ab a ^ 2 ∧
    (∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, ‖(W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 (rp ξ.1)‖) * ‖φ.1 (gl h * k)‖ ≤
      B * (ab a)⁻¹ ^ s := by
  obtain ⟨K₀, hK₀, hdom⟩ := omCpt ℚ E D W ph hph (KK ℚ) (iwa ℚ).1
  set C' : Set (GL (Fin 2) (A E)) := (fun p : GL (Fin 2) (A E) × GL (Fin 2) (A E) => p.1 * p.2) '' (Ω ×ˢ C) with hC'
  have hC'c : IsCompact C' := (hΩ.prod hC).image continuous_mul
  have hC'1 : ∀ k ∈ C', nu ℚ k = 1 := by
    rintro _ ⟨⟨x, y⟩, ⟨hx, hy⟩, rfl⟩
    change nu ℚ (x * y) = 1
    rw [nu_mul, hΩ1 x hx, hC1 y hy, one_mul]
  set c₁ : ℝ := min c c₀ with hc₁
  have hc₁0 : 0 < c₁ := lt_min hc hc₀
  obtain ⟨n, r, Bl, hlat⟩ := hL E D K₀ C' c₁ (s + 2) hK₀ hC'c hC'1 hc₁0
  obtain ⟨Bn, hBn⟩ := hdom n
  obtain ⟨hLf, -, hdec⟩ := hDec E P φ hφP
  obtain ⟨Bd, hBd⟩ := hdec C' hC'c c₁ hc₁0 r
  refine ⟨|Bn| * (Bl * Bd), fun b a k' hk' hca h k hk => ?_⟩
  obtain ⟨γ, u, β, k₁, hk₁, heq, hβ⟩ := hred h
  obtain ⟨ρ, hρ⟩ := (hO E D).1 γ
  set k₂ : GL (Fin 2) (A E) := k₁ * k with hk₂
  have hk₂C : k₂ ∈ C' := ⟨(k₁, k), ⟨hk₁, hk⟩, rfl⟩
  set x₂ : GL (Fin 2) (A E) := gl (nU u * mD β) * k₂ with hx₂
  have hxx : gl (ratS E γ) * (gl h * k) = x₂ := by
    rw [← mul_assoc, heq, hx₂, hk₂, mul_assoc]
  have hx1 : nu ℚ (gl h * k) = 1 := by rw [nu_mul, nu_gl, hC1 k hk, one_mul]
  have hinv : ∀ ξ, D.act (gl h * k)⁻¹ (rp ξ) = D.act x₂⁻¹ (rp (ρ ξ)) := fun ξ => by
    have hg : (gl h * k)⁻¹ = x₂⁻¹ * gl (ratS E γ) := by
      rw [← hxx, _root_.mul_inv_rev (gl (ratS E γ)) (gl h * k), inv_mul_cancel_right]
    rw [hg, D.act_mul, hρ]
  have hφ : φ.1 (gl h * k) = φ.1 x₂ := by
    rw [← hxx, rat_eq]
    exact (hLf.2 _ _).symm
  have ha0 : 0 < ab a := hc.trans_le hca
  have hβ0 : 0 < ab β := hc₀.trans_le hβ
  set w : (Fin 4 → ℚ) → ℝ := fun ξ => wt K₀ n fun i => (a : A ℚ) * D.act x₂⁻¹ (rp ξ) i with hw
  have hlat' := hlat a u β k₂ hk₂C ((min_le_left _ _).trans hca) ((min_le_right _ _).trans hβ)
  obtain ⟨hws, hw1, hw2⟩ := hlat'
  set f : (Fin 4 → ℚ) → ℝ := fun ξ => ‖(W.Om (nU b * mD a * k') (W.L (gl h * k) ph)).1 (rp ξ)‖ with hf
  set T : ℝ := ab a ^ 2 * |Bn| with hT
  have hT0 : 0 ≤ T := by positivity
  have hfw : ∀ ξ, f ξ ≤ T * w (ρ ξ) := fun ξ => by
    simp only [hf, hw]
    rw [om_norm W ph b a k' _ hx1, hinv, hT, mul_assoc]
    refine mul_le_mul_of_nonneg_left (((hBn k' hk' _)).trans ?_) (by positivity)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) (wt_nonneg'' _ _ _)
  obtain ⟨hfs, hf1⟩ := sum_tr ρ.toEquiv f w T (fun _ => norm_nonneg _) hws hfw
  have hqρ : ∀ ξ, qr D.δ (ρ ξ) = qr D.δ ξ := fun ξ => qr_rho D _ ξ (ρ ξ) (hρ ξ)
  let σ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0} ≃ {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0} :=
    ρ.toEquiv.subtypeEquiv fun ξ => by
      change qr D.δ ξ ≠ 0 ↔ qr D.δ (ρ ξ) ≠ 0
      rw [hqρ]
  obtain ⟨-, hf2⟩ := sum_tr σ (fun ξ => f ξ.1) (fun ξ => w ξ.1) T (fun _ => norm_nonneg _) (hws.subtype _)
    (fun ξ => hfw ξ.1)
  have hw0 : ∀ ξ, 0 ≤ w ξ := fun ξ => wt_nonneg'' _ _ _
  have hW0 : 0 ≤ ∑' ξ, w ξ := tsum_nonneg hw0
  have hW0' : 0 ≤ ∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, w ξ.1 := tsum_nonneg fun ξ => hw0 ξ.1
  have hφb := hBd u β k₂ hk₂C ((min_le_right _ _).trans hβ)
  rw [hφ]
  set Φ : ℝ := ‖φ.1 x₂‖ with hΦ
  have hΦ0 : 0 ≤ Φ := norm_nonneg _
  have hcancel : ab β ^ r * (ab β)⁻¹ ^ r = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hβ0.ne', one_pow]
  refine ⟨hfs, ?_, ?_⟩
  · have h1 : (∑' ξ, w ξ) * Φ ≤ (Bl * ab β ^ r) * (Bd * (ab β)⁻¹ ^ r) :=
      mul_le_mul hw1 hφb hΦ0 (hW0.trans hw1)
    calc (∑' ξ, f ξ) * Φ ≤ (T * ∑' ξ, w ξ) * Φ := mul_le_mul_of_nonneg_right hf1 hΦ0
      _ = T * ((∑' ξ, w ξ) * Φ) := by ring
      _ ≤ T * ((Bl * ab β ^ r) * (Bd * (ab β)⁻¹ ^ r)) := mul_le_mul_of_nonneg_left h1 hT0
      _ = |Bn| * (Bl * Bd) * ab a ^ 2 * (ab β ^ r * (ab β)⁻¹ ^ r) := by rw [hT]; ring
      _ = |Bn| * (Bl * Bd) * ab a ^ 2 := by rw [hcancel, mul_one]
  · have h1 : (∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, w ξ.1) * Φ ≤
        (Bl * (ab a)⁻¹ ^ (s + 2) * ab β ^ r) * (Bd * (ab β)⁻¹ ^ r) :=
      mul_le_mul hw2 hφb hΦ0 (hW0'.trans hw2)
    have hca2 : ab a ^ 2 * (ab a)⁻¹ ^ (s + 2) = (ab a)⁻¹ ^ s := by
      rw [pow_add, mul_comm ((ab a)⁻¹ ^ s), ← mul_assoc, ← mul_pow, mul_inv_cancel₀ ha0.ne', one_pow, one_mul]
    calc (∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, f ξ.1) * Φ
        ≤ (T * ∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, w ξ.1) * Φ := mul_le_mul_of_nonneg_right hf2 hΦ0
      _ = T * ((∑' ξ : {ξ : Fin 4 → ℚ // qr D.δ ξ ≠ 0}, w ξ.1) * Φ) := by ring
      _ ≤ T * ((Bl * (ab a)⁻¹ ^ (s + 2) * ab β ^ r) * (Bd * (ab β)⁻¹ ^ r)) := mul_le_mul_of_nonneg_left h1 hT0
      _ = |Bn| * (Bl * Bd) * (ab a ^ 2 * (ab a)⁻¹ ^ (s + 2)) * (ab β ^ r * (ab β)⁻¹ ^ r) := by rw [hT]; ring
      _ = |Bn| * (Bl * Bd) * (ab a)⁻¹ ^ s := by rw [hcancel, hca2, mul_one]

private theorem cont_gl {E : Type} [Field E] [NumberField E] : Continuous (gl : G1 E → GL (Fin 2) (A E)) := by
  refine Units.continuous_iff.2 ⟨continuous_subtype_val, ?_⟩
  have h : Continuous fun g : G1 E => ((g⁻¹ : G1 E) : Matrix (Fin 2) (Fin 2) (A E)) :=
    continuous_subtype_val.comp continuous_inv
  exact h

theorem UpperTheory.ConvolutionTheory.RankTwoDescent.maj :
    LatSum → DecE → Maj := by
  intro hL hDec E _ _ _ D W _ _ P ph hph φ hφ C hC hC1 c hc s
  obtain ⟨c₀, K, hc₀, hK, hr⟩ := redE E
  refine maj_core hL hDec E D W P orb1 (gl '' K) (hK.image cont_gl) ?_ c₀ hc₀ ?_ ph hph φ hφ C hC hC1 c hc s
  · rintro _ ⟨g, -, rfl⟩
    exact nu_gl g
  · intro h
    obtain ⟨γ, u, b, k, hk, he, hb⟩ := hr h
    refine ⟨γ, u, b, gl k, ⟨k, hk, rfl⟩, ?_, hb⟩
    rw [← map_mul, he, map_mul]
end

