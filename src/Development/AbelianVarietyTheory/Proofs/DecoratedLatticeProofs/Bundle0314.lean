import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0140
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0295
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0270
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0297
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BiThetaOfVac
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0149
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0159
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorCommutesSuperpositionSlicesSource
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.WeilSuperpos

variable {D : D7}

theorem pair_swap {S A B T : HSp D} (o : OrthDec S A B) {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ]
    (k : Ω → WO B T) (a : Ω → ℂ) (hk : Measurable k) (ha : Integrable a μ)
    (ν : Measure (WO A T)) [IsFiniteMeasure ν]
    (Φ : WO S T → ℂ) (hΦc : Continuous Φ) (CΦ : ℝ) (hΦ : ∀ x, ‖Φ x‖ ≤ CΦ)
    (g : WO A T → ℂ) (hgc : Continuous g) (Cg : ℝ) (hg : ∀ x, ‖g x‖ ≤ Cg) :
    ∫ u, (∫ w, a w * Φ ((o.resS T).symm (u, k w)) ∂μ) * star (g u) ∂ν =
      ∫ w, a w * ∫ u, Φ ((o.resS T).symm (u, k w)) * star (g u) ∂ν ∂μ := by
  haveI : BorelSpace (WO S T) := ⟨rfl⟩
  haveI : BorelSpace (WO A T) := ⟨rfl⟩
  haveI : BorelSpace (WO B T) := ⟨rfl⟩
  haveI : SFinite ν := @instSFiniteOfSigmaFinite _ _ ν (@IsFiniteMeasure.toSigmaFinite _ _ ν _)
  obtain ⟨-, -, hA2, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨-, -, hB2, -⟩ := lattice_Mx D T.rank B.rank
  have hσ : Measurable fun q : WO A T × Ω => Φ ((o.resS T).symm (q.1, k q.2)) :=
    hΦc.measurable.comp ((o.continuous_resS_symm T).measurable.comp
      (measurable_fst.prodMk (hk.comp measurable_snd)))
  have hgm : Measurable fun q : WO A T × Ω => star (g q.1) :=
    (continuous_star.comp hgc).measurable.comp measurable_fst
  have h1 : Integrable (fun q : WO A T × Ω => a q.2) (ν.prod μ) := ha.comp_snd ν
  have hint : Integrable (Function.uncurry fun u w => a w * Φ ((o.resS T).symm (u, k w)) * star (g u))
      (ν.prod μ) := by
    refine (h1.norm.mul_const (CΦ * Cg)).mono' ?_ (Filter.Eventually.of_forall fun q => ?_)
    · exact (h1.aestronglyMeasurable.mul hσ.aestronglyMeasurable).mul hgm.aestronglyMeasurable
    · rcases q with ⟨u, w⟩
      simp only [Function.uncurry_apply_pair, norm_mul, norm_star]
      have hC : 0 ≤ CΦ := (norm_nonneg _).trans (hΦ 0)
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left (mul_le_mul (hΦ _) (hg _) (norm_nonneg _) hC) (norm_nonneg _)
  calc ∫ u, (∫ w, a w * Φ ((o.resS T).symm (u, k w)) ∂μ) * star (g u) ∂ν
      = ∫ u, ∫ w, a w * Φ ((o.resS T).symm (u, k w)) * star (g u) ∂μ ∂ν := by
        congr 1; funext u; rw [integral_mul_const]
    _ = ∫ w, ∫ u, a w * Φ ((o.resS T).symm (u, k w)) * star (g u) ∂ν ∂μ := integral_integral_swap hint
    _ = ∫ w, a w * ∫ u, Φ ((o.resS T).symm (u, k w)) * star (g u) ∂ν ∂μ := by
        congr 1; funext w; rw [← integral_const_mul]; congr 1; funext u; ring

theorem exists_sfinite {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) (a : Ω → ℂ) (ha : Integrable a μ) :
    ∃ s : Set Ω, SigmaFinite (μ.restrict s) ∧ ∀ X : Ω → ℂ, ∫ w, a w * X w ∂μ = ∫ w, a w * X w ∂(μ.restrict s) := by
  have hf := ha.aefinStronglyMeasurable
  refine ⟨hf.sigmaFiniteSet, hf.sigmaFinite_restrict, fun X => ?_⟩
  have hs : MeasurableSet hf.sigmaFiniteSet := hf.measurableSet
  have h0 : ∀ᵐ w ∂μ, w ∉ hf.sigmaFiniteSet → a w = 0 := by
    have := hf.ae_eq_zero_compl
    rw [Filter.EventuallyEq, ae_restrict_iff' hs.compl] at this
    exact this.mono fun w hw hws => hw hws
  exact (setIntegral_eq_integral_of_ae_compl_eq_zero (h0.mono fun w hw hws => by rw [hw hws, zero_mul])).symm

variable {ψ : AddChar (AF D.host.F) ℂ}

theorem comm_sfinite {S A B T : HSp D} (o : OrthDec S A B) {χ χ' : (AE D)ˣ →* Circle} {om : Om A T}
    (hW : IsWeilDatumO ψ A T χ χ' om) {F : WO S T → ℂ} (hF : IsThetaFunO ψ S T F)
    {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [SFinite μ] (k : Ω → WO B T) (a : Ω → ℂ)
    (hk : Measurable k) (ha : Integrable a μ) (p : GA D A × GA D T) (u₀ : WO A T) :
    om p (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) u₀ =
      ∫ w, a w * om p (fun u => F ((o.resS T).symm (u, k w))) u₀ ∂μ := by
  have hψ := hW.std
  set H : WO S T → ℂ := fun x => om p (fun u => F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1 with hH
  have hHt : IsThetaFunO ψ S T H := (GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o F hF).1 χ χ' om hW p
  have hHs : ∀ u b, H ((o.resS T).symm (u, b)) = om p (fun u' => F ((o.resS T).symm (u', b))) u := by
    intro u b; simp only [hH, AddEquiv.apply_symm_apply]
  have hsl : ∀ b, IsThetaFunO ψ A T (fun u => F ((o.resS T).symm (u, b))) := by
    intro b
    have := GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices D ψ hψ S A B T o F hF Unit (Measure.dirac ()) (fun _ => b) (fun _ => 1)
      measurable_const (integrable_const _)
    simpa using this
  set G : WO A T → ℂ := fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ with hGdef
  set R : WO A T → ℂ := fun u => ∫ w, a w * om p (fun u' => F ((o.resS T).symm (u', k w))) u ∂μ with hRdef
  have hG : IsThetaFunO ψ A T G := GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices D ψ hψ S A B T o F hF Ω μ k a hk ha
  have hR' : R = fun u => ∫ w, a w * H ((o.resS T).symm (u, k w)) ∂μ := by
    funext u; simp only [hRdef, hHs]
  have hR : IsThetaFunO ψ A T R := by
    rw [hR']; exact GlobalTheory.T.isThetaFunction_superposition_orthogonalSlices D ψ hψ S A B T o H hHt Ω μ k a hk ha
  have hL : IsThetaFunO ψ A T (om p G) := hW.om_pres p G hG
  obtain ⟨v⟩ := GlobalTheory.Unf.Inhab.nonempty_volM D T.rank A.rank
  obtain ⟨hhaar, hfd, hvol⟩ := v.covol
  haveI := hhaar
  haveI : IsFiniteMeasure (v.μ.restrict v.𝓕) :=
    ⟨by rw [Measure.restrict_apply_univ, hvol]; exact ENNReal.one_lt_top⟩
  have key : ∀ g, IsThetaFunO ψ A T g → thPair v.μ v.𝓕 (om p G) g = thPair v.μ v.𝓕 R g := by
    intro g hg
    have hg' : IsThetaFunO ψ A T (om p⁻¹ g) := hW.om_pres _ _ hg
    have hinv : om p (om p⁻¹ g) = g := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    obtain ⟨Cg, hCg⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hg
    obtain ⟨Cg', hCg'⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hg'
    obtain ⟨CF, hCF⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hF
    obtain ⟨CH, hCH⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded S T ψ hψ _ hHt
    calc thPair v.μ v.𝓕 (om p G) g = thPair v.μ v.𝓕 (om p G) (om p (om p⁻¹ g)) := by rw [hinv]
      _ = thPair v.μ v.𝓕 G (om p⁻¹ g) := GlobalTheory.T.weilDatum_preserves_thetaFundamentalDomainPairing D ψ A T χ χ' om hW v p _ _ hG hg'
      _ = ∫ w, a w * thPair v.μ v.𝓕 (fun u => F ((o.resS T).symm (u, k w))) (om p⁻¹ g) ∂μ := by
          unfold thPair
          exact pair_swap o μ k a hk ha _ F hF.cont CF hCF _ hg'.cont Cg' hCg'
      _ = ∫ w, a w * thPair v.μ v.𝓕 (om p (fun u => F ((o.resS T).symm (u, k w)))) g ∂μ := by
          congr 1; funext w; congr 1
          rw [← GlobalTheory.T.weilDatum_preserves_thetaFundamentalDomainPairing D ψ A T χ χ' om hW v p _ _ (hsl _) hg', hinv]
      _ = ∫ w, a w * thPair v.μ v.𝓕 (fun u => H ((o.resS T).symm (u, k w))) g ∂μ := by
          simp only [hHs]
      _ = thPair v.μ v.𝓕 R g := by
          rw [hR']; unfold thPair
          exact (pair_swap o μ k a hk ha _ H hHt.cont CH hCH g hg.cont Cg hCg).symm
  have hd : IsThetaFunO ψ A T (om p G - R) := GlobalTheory.WeilVacMove.isTheta_sub hL hR
  have hkd := key _ hd
  obtain ⟨CL, hCL⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hL
  obtain ⟨CR, hCR⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hR
  obtain ⟨Cd, hCd⟩ := GlobalTheory.IsoMean.isThetaFunO_bounded A T ψ hψ _ hd
  haveI : BorelSpace (WO A T) := ⟨rfl⟩
  have bint : ∀ f : WO A T → ℂ, Continuous f → ∀ C : ℝ, (∀ x, ‖f x‖ ≤ C) →
      Integrable (fun x => f x * star ((om p G - R) x)) (v.μ.restrict v.𝓕) := by
    intro f hf C hC
    refine (integrable_const (C * Cd)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hf.mul (continuous_star.comp hd.cont)).aestronglyMeasurable
    · rw [norm_mul, norm_star]
      exact mul_le_mul (hC x) (hCd x) (norm_nonneg _) ((norm_nonneg _).trans (hC x))
  have h0 : ∫ x in v.𝓕, ((Complex.normSq ((om p G - R) x) : ℝ) : ℂ) ∂v.μ = 0 := by
    have e : ∀ x, ((Complex.normSq ((om p G - R) x) : ℝ) : ℂ) =
        om p G x * star ((om p G - R) x) - R x * star ((om p G - R) x) := by
      intro x
      rw [← sub_mul, ← Pi.sub_apply, Complex.star_def, Complex.mul_conj]
    simp only [e]
    rw [integral_sub (bint _ hL.cont CL hCL) (bint _ hR.cont CR hCR)]
    unfold thPair at hkd
    rw [hkd, sub_self]
  rw [integral_complex_ofReal] at h0
  have h1 : ∫ x in v.𝓕, Complex.normSq ((om p G - R) x) ∂v.μ = 0 := by exact_mod_cast h0
  have hnn : 0 ≤ᵐ[v.μ.restrict v.𝓕] fun x => Complex.normSq ((om p G - R) x) :=
    Filter.Eventually.of_forall fun x => Complex.normSq_nonneg _
  have hi : Integrable (fun x => Complex.normSq ((om p G - R) x)) (v.μ.restrict v.𝓕) := by
    refine (integrable_const (Cd * Cd)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (Complex.continuous_normSq.comp hd.cont).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (Complex.normSq_nonneg _), Complex.normSq_eq_norm_sq, sq]
      exact mul_le_mul (hCd x) (hCd x) (norm_nonneg _) ((norm_nonneg _).trans (hCd x))
  have hae := (integral_eq_zero_iff_of_nonneg_ae hnn hi).1 h1
  have hae' : ∀ᵐ x ∂v.μ.restrict v.𝓕, (om p G - R) x = 0 :=
    hae.mono fun x hx => Complex.normSq_eq_zero.1 hx
  obtain ⟨i1, -, i3, -, i5, -⟩ := lattice_Mx D T.rank A.rank
  haveI := i1; haveI := i3; haveI := i5
  have hz := GlobalTheory.WeilVacMove.eq_zero_of_ae_fundamentalDomain (ratMx D T.rank A.rank) v.μ v.𝓕 hfd (om p G - R) hd.cont
    (GlobalTheory.WeilVacMove.norm_periodic hψ hd) hae'
  have := congrFun hz u₀
  rw [Pi.sub_apply, Pi.zero_apply, sub_eq_zero] at this
  exact this

theorem weil_comm_superpos : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (χ χ' : ((AE D)ˣ →* Circle)) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (Ω : Type) [MeasurableSpace Ω] (μ : Measure Ω) (k : Ω → WO B T) (a : Ω → ℂ), Measurable k → Integrable a μ → ∀ p, IsThetaFunO ψ S T (fun x => om p (fun u => F ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1) ∧ ∀ u₀, om p (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) u₀ = ∫ w, a w * om p (fun u => F ((o.resS T).symm (u, k w))) u₀ ∂μ := by
  intro D ψ S A B T o χ χ' om hW F hF Ω _ μ k a hk ha p
  refine ⟨(GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o F hF).1 χ χ' om hW p, fun u₀ => ?_⟩
  obtain ⟨s, hs, hr⟩ := exists_sfinite μ a ha
  have e1 : (fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂μ) =
      fun u => ∫ w, a w * F ((o.resS T).symm (u, k w)) ∂(μ.restrict s) := funext fun u => hr _
  rw [e1, hr]
  exact comm_sfinite o hW hF (μ.restrict s) k a hk ha.restrict p u₀

end GlobalTheory.WeilSuperpos
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorFirstCommutesHeisenbergDerivativeSecStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_first_commutes_heisenbergDerivative_second : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (A S A' : HSp D) (χA χS χS' χA' : (AE D)ˣ →* Circle) (oma : Om A S) (omb : Om S A'), IsWeilDatumO ψ A S χA χS oma → IsWeilDatumO ψ S A' χS' χA' omb → BiAct D → ∀ G : WO A S → WO S A' → ℂ, IsBiTheta ψ A S A' G → ∀ M' : ℝ →+ WO S A', Continuous M' → (∀ s, (M' s).map (finPart D) = 0) → ∀ p u v, oma p (fun u' => GlobalTheory.WeilVacMove.dLine ψ S A' M' (G u') v) u = GlobalTheory.WeilVacMove.dLine ψ S A' M' (fun v' => oma p (fun u' => G u' v') u) v := by
  first | exact @GlobalTheory.DerivComm.om_dLine_right | exact GlobalTheory.DerivComm.om_dLine_right | (intros; apply GlobalTheory.DerivComm.om_dLine_right <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorOneVariablePreservesSqNormOrthogonal
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

noncomputable section

namespace GlobalTheory.WeilSliceUnit

open scoped ENNReal NNReal Pointwise

variable {D : D7}

theorem borel_Mx (m n : ℕ) : BorelSpace (Mx D m n) := ⟨rfl⟩

theorem isAddFundamentalDomain_prod {A B : Type*} [AddGroup A] [AddGroup B] [MeasurableSpace A]
    [MeasurableSpace B] {Γ : AddSubgroup A} {Δ : AddSubgroup B} {μ : Measure A} {ν : Measure B} [SFinite μ]
    [SFinite ν] {s : Set A} {t : Set B} (hs : IsAddFundamentalDomain Γ s μ) (ht : IsAddFundamentalDomain Δ t ν) :
    IsAddFundamentalDomain (Γ.prod Δ) (s ×ˢ t) (μ.prod ν) where
  nullMeasurableSet := hs.nullMeasurableSet.prod ht.nullMeasurableSet
  ae_covers := by
    have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hs.ae_covers
    have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae ht.ae_covers
    filter_upwards [h1, h2] with p hp hq
    obtain ⟨g, hg⟩ := hp
    obtain ⟨h, hh⟩ := hq
    exact ⟨⟨((g : A), (h : B)), AddSubgroup.mem_prod.2 ⟨g.2, h.2⟩⟩, hg, hh⟩
  aedisjoint := by
    intro g h hgh
    change μ.prod ν ((g +ᵥ s ×ˢ t) ∩ (h +ᵥ s ×ˢ t)) = 0
    let g1 : Γ := ⟨(g : A × B).1, (AddSubgroup.mem_prod.1 g.2).1⟩
    let h1 : Γ := ⟨(h : A × B).1, (AddSubgroup.mem_prod.1 h.2).1⟩
    let g2 : Δ := ⟨(g : A × B).2, (AddSubgroup.mem_prod.1 g.2).2⟩
    let h2 : Δ := ⟨(h : A × B).2, (AddSubgroup.mem_prod.1 h.2).2⟩
    by_cases e1 : g1 = h1
    · have e2 : g2 ≠ h2 := fun e2 => hgh (Subtype.ext (Prod.ext (congrArg Subtype.val e1) (congrArg Subtype.val e2)))
      have h0 : ν ((g2 +ᵥ t) ∩ (h2 +ᵥ t)) = 0 := ht.aedisjoint e2
      refine measure_mono_null (t := Set.univ ×ˢ ((g2 +ᵥ t) ∩ (h2 +ᵥ t))) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨Set.mem_univ _, ?_, ?_⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.2
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.2
      · rw [Measure.prod_prod, h0, mul_zero]
    · have h0 : μ ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) = 0 := hs.aedisjoint e1
      refine measure_mono_null (t := ((g1 +ᵥ s) ∩ (h1 +ᵥ s)) ×ˢ Set.univ) ?_ ?_
      · rintro p ⟨hp1, hp2⟩
        rw [Set.mem_vadd_set_iff_neg_vadd_mem] at hp1 hp2
        refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp1.1
        · rw [Set.mem_vadd_set_iff_neg_vadd_mem]; exact hp2.1
      · rw [Measure.prod_prod, h0, zero_mul]

theorem lintegral_resS {S A B T : HSp D} (o : OrthDec S A B) (μ : Measure (WO S T)) [μ.IsAddHaarMeasure]
    (𝓕 : Set (WO S T)) (h𝓕 : IsAddFundamentalDomain (ratL T S) 𝓕 μ) (μA : Measure (WO A T)) (μB : Measure (WO B T))
    [μA.IsAddHaarMeasure] [μB.IsAddHaarMeasure] (FA : Set (WO A T)) (FB : Set (WO B T))
    (hA : IsAddFundamentalDomain (ratL T A) FA μA) (hB : IsAddFundamentalDomain (ratL T B) FB μB) :
    ∃ c : ℝ≥0, ∀ Φ : WO A T × WO B T → ℝ≥0∞, (∀ γ ∈ ratL T S, ∀ x, Φ (o.resS T (γ + x)) = Φ (o.resS T x)) →
      ∫⁻ x in 𝓕, Φ (o.resS T x) ∂μ = c • ∫⁻ y, Φ y ∂((μA.restrict FA).prod (μB.restrict FB)) := by
  haveI := borel_Mx (D := D) T.rank S.rank
  haveI := borel_Mx (D := D) T.rank A.rank
  haveI := borel_Mx (D := D) T.rank B.rank
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D T.rank S.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D T.rank B.rank
  haveI : Countable (ratL T S) :=
    (TopologicalSpace.separableSpace_iff_countable.1 inferInstance : Countable (ratMx D T.rank S.rank))
  haveI : MeasurableConstVAdd (ratL T S) (WO S T) := ⟨fun _ => (continuous_const.add continuous_id).measurable⟩
  haveI : VAddInvariantMeasure (ratL T S) (WO S T) μ := ⟨fun c s _ => measure_preimage_add μ (c : WO S T) s⟩
  let e : WO S T ≃ₜ (WO A T × WO B T) :=
    { (o.resS T).toEquiv with continuous_toFun := o.continuous_resS T, continuous_invFun := o.continuous_resS_symm T }
  let em := e.toMeasurableEquiv
  haveI : (μ.map em).IsAddHaarMeasure :=
    (o.resS T).isAddHaarMeasure_map μ (o.continuous_resS T) (o.continuous_resS_symm T)
  obtain ⟨c, hmeq⟩ : ∃ c : ℝ≥0, μ.map em = c • μA.prod μB :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul (μ.map em) (μA.prod μB)⟩
  refine ⟨c, fun Φ hper => ?_⟩
  have hqmp : Measure.QuasiMeasurePreserving em μ (μA.prod μB) :=
    ⟨em.measurable, by rw [hmeq]; exact Measure.smul_absolutelyContinuous⟩
  have hprod := isAddFundamentalDomain_prod hA hB
  have hmem : ∀ g : (ratL T A).prod (ratL T B), (o.resS T).symm (g : WO A T × WO B T) ∈ ratL T S := fun g => by
    rw [o.mem_ratL_resS, AddEquiv.apply_symm_apply]; exact AddSubgroup.mem_prod.1 g.2
  have hP : IsAddFundamentalDomain (ratL T S) (em ⁻¹' (FA ×ˢ FB)) μ := by
    refine hprod.preimage_of_equiv hqmp (e := fun g => ⟨_, hmem g⟩) ⟨fun g g' h => ?_, fun h => ?_⟩ fun g x => ?_
    · exact Subtype.ext ((o.resS T).symm.injective (congrArg Subtype.val h))
    · refine ⟨⟨o.resS T h, AddSubgroup.mem_prod.2 ((o.mem_ratL_resS T h).1 h.2)⟩, Subtype.ext ?_⟩
      exact (o.resS T).symm_apply_apply h
    · change o.resS T ((o.resS T).symm (g : WO A T × WO B T) + x) = (g : WO A T × WO B T) + o.resS T x
      rw [map_add, AddEquiv.apply_symm_apply]
  rw [h𝓕.setLIntegral_eq hP (fun x => Φ (o.resS T x)) (fun g x => hper g g.2 x)]
  change ∫⁻ x in em ⁻¹' (FA ×ˢ FB), Φ (em x) ∂μ = _
  rw [← lintegral_map_equiv _ em, ← em.restrict_map, hmeq, Measure.restrict_smul, lintegral_smul_measure,
    Measure.prod_restrict]

end GlobalTheory.WeilSliceUnit

namespace GlobalTheory.WeilSliceUnit

open scoped ENNReal NNReal

variable {D : D7}

theorem enorm_sq_periodic {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S T : HSp D} {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : ∀ γ ∈ ratL T S, ∀ x, ‖f (γ + x)‖ₑ ^ 2 = ‖f x‖ₑ ^ 2 := by
  rintro _ ⟨g, rfl⟩ x
  have h : ‖f (ratW T S g + x)‖ = ‖f x‖ := by rw [hf.quasi, norm_mul, hψ.1.2.1, one_mul]
  show ‖f (ratW T S g + x)‖ₑ ^ 2 = _
  rw [← ofReal_norm, ← ofReal_norm, h]

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S A B T : HSp D) (o : OrthDec S A B) (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), μ.IsAddHaarMeasure → IsAddFundamentalDomain (ratL T S) 𝓕 μ → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f → (∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om A T), IsWeilDatumO ψ A T χ χ' om → ∀ p, ∫⁻ x in 𝓕, ‖om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ) ∧ ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om B T), IsWeilDatumO ψ B T χ χ' om → ∀ p, ∫⁻ x in 𝓕, ‖om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2‖ₑ ^ 2 ∂μ = ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ := by
  intro D ψ S A B T o μ 𝓕 hμ h𝓕 f hf
  haveI := borel_Mx (D := D) T.rank S.rank
  haveI := borel_Mx (D := D) T.rank A.rank
  haveI := borel_Mx (D := D) T.rank B.rank
  obtain ⟨i1, i2, i3, i4, i5, -⟩ := lattice_Mx D T.rank S.rank
  obtain ⟨j1, j2, j3, j4, j5, -⟩ := lattice_Mx D T.rank A.rank
  obtain ⟨k1, k2, k3, k4, k5, -⟩ := lattice_Mx D T.rank B.rank
  obtain ⟨μA, FA, hA⟩ := exists_isCovolOne D T.rank A.rank
  obtain ⟨μB, FB, hB⟩ := exists_isCovolOne D T.rank B.rank
  haveI := hA.1
  haveI := hB.1
  have hFA : IsAddFundamentalDomain (ratL T A) FA μA := hA.2.1
  have hFB : IsAddFundamentalDomain (ratL T B) FB μB := hB.2.1
  obtain ⟨c, hc⟩ := lintegral_resS o μ 𝓕 h𝓕 μA μB FA FB hFA hFB
  have hslice := GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ S A B T o f hf
  have hΦ0 : Measurable fun y : WO A T × WO B T => ‖f ((o.resS T).symm y)‖ₑ ^ 2 :=
    ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (hf.cont.comp (o.continuous_resS_symm T)))).measurable
  have e0 : ∀ hψ : IsStdChar D ψ (-1), ∫⁻ x in 𝓕, ‖f x‖ₑ ^ 2 ∂μ = c • ∫⁻ y, ‖f ((o.resS T).symm y)‖ₑ ^ 2
      ∂((μA.restrict FA).prod (μB.restrict FB)) := by
    intro hψ
    have h := hc (fun y => ‖f ((o.resS T).symm y)‖ₑ ^ 2) (fun γ hγ x => by
      simp only [AddEquiv.symm_apply_apply]; exact enorm_sq_periodic hψ hf γ hγ x)
    simpa only [AddEquiv.symm_apply_apply] using h
  refine ⟨fun χ χ' om hW p => ?_, fun χ χ' om hW p => ?_⟩
  · have hψ := hW.std
    have hF := hslice.1 χ χ' om hW p
    have hbox := (GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T o).2.2.2 f hf
    have hfun : (fun y : WO A T × WO B T => ‖om p (fun u => f ((o.resS T).symm (u, y.2))) y.1‖ₑ ^ 2) =
        fun y => ‖(fun x => om p (fun u => f ((o.resS T).symm (u, (o.resS T x).2))) (o.resS T x).1)
          ((o.resS T).symm y)‖ₑ ^ 2 := by
      funext y; simp only [AddEquiv.apply_symm_apply]
    have hΦ1 : Measurable fun y : WO A T × WO B T => ‖om p (fun u => f ((o.resS T).symm (u, y.2))) y.1‖ₑ ^ 2 := by
      rw [hfun]
      exact ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (hF.cont.comp (o.continuous_resS_symm T)))).measurable
    have e1 := hc (fun y => ‖om p (fun u => f ((o.resS T).symm (u, y.2))) y.1‖ₑ ^ 2)
      (fun γ hγ x => enorm_sq_periodic hψ hF γ hγ x)
    rw [e1, e0 hψ]
    congr 1
    rw [lintegral_prod_symm _ hΦ1.aemeasurable, lintegral_prod_symm _ hΦ0.aemeasurable]
    refine lintegral_congr fun v => ?_
    show ∫⁻ u in FA, ‖om p (fun u => f ((o.resS T).symm (u, v))) u‖ₑ ^ 2 ∂μA =
      ∫⁻ u in FA, ‖f ((o.resS T).symm (u, v))‖ₑ ^ 2 ∂μA
    exact hW.om_unit μA FA hA.1 hFA p (fun u => f ((o.resS T).symm (u, v))) (hbox.1 v)
  · have hψ := hW.std
    have hF := hslice.2 χ χ' om hW p
    have hbox := (GlobalTheory.T.thetaFunction_products_slices_orthogonalDecomposition D ψ hψ S A B T o).2.2.2 f hf
    have hfun : (fun y : WO A T × WO B T => ‖om p (fun v => f ((o.resS T).symm (y.1, v))) y.2‖ₑ ^ 2) =
        fun y => ‖(fun x => om p (fun v => f ((o.resS T).symm ((o.resS T x).1, v))) (o.resS T x).2)
          ((o.resS T).symm y)‖ₑ ^ 2 := by
      funext y; simp only [AddEquiv.apply_symm_apply]
    have hΦ1 : Measurable fun y : WO A T × WO B T => ‖om p (fun v => f ((o.resS T).symm (y.1, v))) y.2‖ₑ ^ 2 := by
      rw [hfun]
      exact ((ENNReal.continuous_pow 2).comp (continuous_enorm.comp (hF.cont.comp (o.continuous_resS_symm T)))).measurable
    have e1 := hc (fun y => ‖om p (fun v => f ((o.resS T).symm (y.1, v))) y.2‖ₑ ^ 2)
      (fun γ hγ x => enorm_sq_periodic hψ hF γ hγ x)
    rw [e1, e0 hψ]
    congr 1
    rw [lintegral_prod _ hΦ1.aemeasurable, lintegral_prod _ hΦ0.aemeasurable]
    refine lintegral_congr fun u => ?_
    show ∫⁻ v in FB, ‖om p (fun v => f ((o.resS T).symm (u, v))) v‖ₑ ^ 2 ∂μB =
      ∫⁻ v in FB, ‖f ((o.resS T).symm (u, v))‖ₑ ^ 2 ∂μB
    exact hW.om_unit μB FB hB.1 hFB p (fun v => f ((o.resS T).symm (u, v))) (hbox.2 u)

end GlobalTheory.WeilSliceUnit

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorTargetSummandPreservesThetaFunctions
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger (dagger dagger_dagger conjAdjoint)

namespace GlobalTheory.SliceTarget

variable {D : D7} {T A B : HSp D}

theorem pA_giA (o : OrthDec T A B) : o.pA ⬝ giA T = giA A ⬝ adj o.jA := by
  rw [o.pA_eq]
  simp only [Matrix.mul_assoc, gA_mul_giA, Matrix.mul_one]

theorem resT_dagger (o : OrthDec T A B) (S : HSp D) (y : WO T S) :
    o.resT S (dagger T S y) = (dagger A S (o.resS S y).1, dagger B S (o.resS S y).2) := by
  have hA := pA_giA o
  have hB : o.pB ⬝ giA T = giA B ⬝ adj o.jB := pA_giA o.symm
  simp only [OrthDec.resT_apply, OrthDec.resS_apply, dagger, adj_mul, cancel₂ hA, cancel₂ hB, Matrix.mul_assoc]

theorem dagger_resS_symm (o : OrthDec T A B) (S : HSp D) (u : WO A S) (v : WO B S) :
    dagger T S ((o.resS S).symm (u, v)) = (o.resT S).symm (dagger A S u, dagger B S v) := by
  rw [AddEquiv.eq_symm_apply, resT_dagger, AddEquiv.apply_symm_apply]

theorem main : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (T A B S : HSp D) (o : OrthDec T A B) (F : WO S T → ℂ), IsThetaFunO ψ S T F → ∀ (χ χ' : (AE D)ˣ →* Circle) (om : Om S A), IsWeilDatumO ψ S A χ χ' om → ∀ p, IsThetaFunO ψ S T fun x => om p (fun u => F ((o.resT S).symm (u, (o.resT S x).2))) (o.resT S x).1 := by
  intro D ψ T A B S o F hF χ χ' om hom p
  have hd := (GlobalTheory.T.hermitianAdjoint_symplectic_action_theta_heisenberg D ψ hom.std S T).2.2.1
  have h := (GlobalTheory.T.weilOperator_oneVariable_keeps_thetaFunctions D ψ T A B S o _ ((hd F).2 hF)).1 χ' χ (conjAdjoint om)
    (GlobalTheory.T.conj_weil_datum_via_adjoint_exchanged_pair D ψ S A χ χ' om hom) p.swap
  refine (hd _).1 ?_
  convert h using 1
  funext y
  show starRingEnd ℂ (om p (fun u => F ((o.resT S).symm (u, (o.resT S (dagger T S y)).2))) (o.resT S (dagger T S y)).1) =
    starRingEnd ℂ (om p (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S A) fun u => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) F ((o.resS S).symm (u, (o.resS S y).2)))
      (dagger A S (o.resS S y).1))
  have e : (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger S A) fun u => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) F ((o.resS S).symm (u, (o.resS S y).2))) =
      fun u => F ((o.resT S).symm (u, dagger B S (o.resS S y).2)) := by
    funext u
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, dagger_resS_symm, dagger_dagger, Complex.conj_conj]
  rw [resT_dagger, e]

end GlobalTheory.SliceTarget
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepLinearModelGLPairApplyMemSchwartzBruhatFuStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRepLinearModelGLPair_apply_mem_schwartzBruhatFunctions : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a b : Type) [Fintype a]
    [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k) (Φ : SB (Matrix b a k)),
    om μ g h Φ.1 ∈ SB (Matrix b a k) := by
  first | exact @GlobalTheory.SplitWeil.ValOne.om_val_mem_SB | exact GlobalTheory.SplitWeil.ValOne.om_val_mem_SB | (intros; apply GlobalTheory.SplitWeil.ValOne.om_val_mem_SB <;> assumption)
end

