import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0171
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0229
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0021
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0228
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0144
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0224
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0016
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0226
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0015
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaSourceAction
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0233
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0107
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0230
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0230
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0217
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EntryAgree
import Formalism.LocalToGlobal.Columns.ChainTw

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MeanPairingEisensteinSimplePole
section
open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Filter Topology Set Metric

namespace GlobalTheory.RegSch.EisensteinPairing

variable {D : D7} {T T₀ : HSp D} {r : ℕ} {d : HypDec T T₀ r} {b : GL (Fin T.rank) (AE D)} {s₀ : ℂ} {j k : ℕ}

theorem eisenstein_analytic_half_plane (hA : EisensteinContinues d b) (h : GA D T) :
    AnalyticOnNhd ℂ (sphericalEisenstein d b h) (rightOf (rhoH T r)) := by
  have e : sphericalEisenstein d b h = fun s => ∑' q, (fun _ => (1 : ℂ)) q *
      npow ((fun q => GlobalTheory.Eis.term (stab d) (GQ T) (iwAbs (absDet d) (Kmax T b)) h q) q) (s - (-(rhoH T r : ℂ))) := by
    funext s
    simp only [sphericalEisenstein, GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term, sphericalSection, one_mul, sub_neg_eq_add]
  rw [e]
  refine GlobalTheory.Eis.analyticOnNhd_tsum_npow (fun _ => iwAbs_pos _ _ _) fun s hs => ?_
  have := hA.1 s hs h
  simpa only [GlobalTheory.Eis.CosetConv, GlobalTheory.Eis.term, sphericalSection, one_mul, sub_neg_eq_add] using this

theorem eisenstein_left_invariant_rational (hI : HasIw d (Kmax T b)) {γ : GA D T} (hγ : γ ∈ GQ T) (h : GA D T) :
    sphericalEisenstein d b (γ * h) = sphericalEisenstein d b h := by
  funext s
  have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (stab d ⊓ GQ T) (sphericalSection d b s) := by
    intro δ hδ g
    obtain ⟨u, hu⟩ := GlobalTheory.EisCont.det_onX_rat d ⟨δ, hδ.1⟩ hδ.2
    have h1 : absDet d ⟨δ, hδ.1⟩ = 1 := by
      rw [absDet, MonoidHom.comp_apply, MonoidHom.comp_apply, ← hu]
      exact absE_inclR u
    have h2 := hI.isIwasawa.iwAbs_left ⟨δ, hδ.1⟩ g
    rw [h1, one_mul] at h2
    exact congrArg (npow · _) h2
  exact GlobalTheory.Eis.leftInv_cosetSum hL γ hγ h

theorem regularAt_succ (h : EisensteinRegularAt d b s₀ k) : EisensteinRegularAt d b s₀ (k + 1) := by
  obtain ⟨ε, H, hr, e, hd, hc, C, N, hb⟩ := h
  refine ⟨ε, fun s g => (s - s₀) * H s g, hr, fun s hs h0 g => by simp only [e s hs h0]; ring,
    fun g => (differentiableOn_id.sub_const _).mul (hd g), (by fun_prop : ContinuousOn (fun x : ℂ × _ => x.1 - s₀) _).mul hc,
    ε * C, N, fun s hs g => ?_⟩
  rw [norm_mul, mul_assoc]
  exact mul_le_mul (mem_ball_iff_norm.1 hs).le (hb s hs g) (norm_nonneg _) hr.le

theorem regularAt_pred (h : EisensteinRegularAt d b s₀ (k + 1)) (hp : ∀ g, PoleLE (sphericalEisenstein d b g) s₀ j) (hj : j ≤ k) :
    EisensteinRegularAt d b s₀ k := by
  obtain ⟨ε, H, hr, e, hd, hc, C, N, hb⟩ := h
  have h0 : ∀ g, H s₀ g = 0 := fun g => by
    obtain ⟨E, hE, -⟩ := id (hp g)
    obtain ⟨c, hc⟩ := hE.poleLE_iff.1 (hp g)
    have h1 : Tendsto (fun s => (s - s₀) ^ (k + 1 - j)) (𝓝[≠] s₀) (𝓝 0) :=
      (Continuous.tendsto' (by fun_prop) s₀ 0 (by simp; omega)).mono_left nhdsWithin_le_nhds
    refine tendsto_nhds_unique (((hd g).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left
      (nhdsWithin_le_nhds (s := {s₀}ᶜ))) ((zero_mul c ▸ h1.mul hc).congr' ?_)
    filter_upwards [hE.cont_eventuallyEq, self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₀ hr)]
      with s h2 h3 h4
    rw [e s h4 h3, ← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega), ← h2]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.Eis.dslope_family hr hd hc hb h0
  refine ⟨ε / 2, fun s g => dslope (H · g) s₀ s, half_pos hr, fun s hs hs' g => ?_, h1, h2, C / ε, N, fun s hs g => ?_⟩
  · have := sub_ne_zero.2 hs'
    simp only [dslope_of_ne _ hs', slope_def_field, h0, e s (ball_subset_ball (by linarith) hs) hs']
    field_simp
    ring
  · rw [div_mul_eq_mul_div]; exact h3 s hs g

theorem regularAt_of_poleLE (h : EisensteinRegularAt d b s₀ k) (hp : ∀ g, PoleLE (sphericalEisenstein d b g) s₀ j) :
    EisensteinRegularAt d b s₀ j := by
  rcases le_total k j with hk | hk
  · exact Nat.le_induction h (fun _ _ => regularAt_succ) j hk
  · exact Nat.decreasingInduction (motive := fun i _ => j ≤ i → EisensteinRegularAt d b s₀ i)
      (fun i _ ih hi => regularAt_pred (ih (by omega)) hp hi) (fun _ => h) hk le_rfl

theorem meanPair_const_mul (m : Measure (GA D T)) (F E : GA D T → ℂ) (c : ℂ) :
    meanPair T m F (fun h => c * E h) = c * meanPair T m F E := by
  simp only [meanPair, MeasureTheory.average]
  rw [← MeasureTheory.integral_const_mul]
  refine congrArg _ (funext fun q => ?_)
  simp only [GlobalTheory.AutomorphicL2Unitary.descend, mul_left_comm]

theorem pair_family {m : Measure (GA D T)} (hm : m.IsHaarMeasure) {F : GA D T → ℂ} (hF : GlobalTheory.Grow.RapidDec T F)
    {A : ℂ → GA D T → ℂ} {ε : ℝ} (hinv : ∀ s ∈ ball s₀ ε, ∀ γ ∈ GQ T, ∀ h, A s (γ * h) = A s h)
    (hd : ∀ h, DifferentiableOn ℂ (A · h) (ball s₀ ε))
    (hc : ContinuousOn (fun x : ℂ × GA D T => A x.1 x.2) (ball s₀ ε ×ˢ univ)) {C : ℝ} {N : ℕ}
    (hb : ∀ s ∈ ball s₀ ε, ∀ h, ‖A s h‖ ≤ C * GlobalTheory.Grow.height T h ^ N) :
    (∀ s ∈ ball s₀ ε, Integrable (descend (GQ T) fun h => F h * A s h) (autMeasure T m)) ∧
      DifferentiableOn ℂ (fun s => meanPair T m F (A s)) (ball s₀ ε) := by
  have : BorelSpace (GA D T) := ⟨rfl⟩
  have hbi := (GlobalTheory.Core.Rk.IP.integrable_quotHeight_pow_mul_norm_of_rapidDec D T m hm F hF N).const_mul (C * 2 ^ N)
  have hmeas : ∀ s ∈ ball s₀ ε, AEStronglyMeasurable (descend (GQ T) fun h => F h * A s h) (autMeasure T m) := by
    intro s hs
    have hL : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ T) fun h => F h * A s h := fun γ hγ g => by
      simp only [hF.left hγ, hinv s hs γ hγ]
    have hcont : Continuous (A s) := hc.comp_continuous (f := fun g => (s, g)) (by fun_prop) fun g => ⟨hs, trivial⟩
    refine Measurable.aestronglyMeasurable (measurable_from_quotient.2 ?_)
    have h' : (descend (GQ T) (fun h => F h * A s h) ∘ Quotient.mk'') = fun h => F h * A s h :=
      funext fun g => hL.descend_mk g
    rw [h']
    exact (hF.continuous.mul hcont).measurable
  have := GlobalTheory.differentiableOn_integral_of_holomorphic_of_locally_dominated
    (μ := autMeasure T m) (F := fun q s => descend (GQ T) (fun h => F h * A s h) q)
    (isOpen_ball (x := s₀) (ε := ε)) hmeas (ae_of_all _ fun q => (hd _).const_mul _)
    fun x hx => ⟨ball s₀ ε, isOpen_ball.mem_nhds hx, _, hbi, ae_of_all _ fun q y hy => by
      have h1 := GlobalTheory.Grow.norm_le_quotHeight_pow (hinv y hy) (hb y hy) q.out
      show ‖F q.out * A y q.out‖ ≤ _
      rw [norm_mul, mul_comm, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)⟩
  refine ⟨fun s hs => (this.2 s hs).1, ?_⟩
  simp only [meanPair, MeasureTheory.average_eq]
  exact this.1.const_smul _

theorem pair_regular (hI : HasIw d (Kmax T b)) {m : Measure (GA D T)} (hm : m.IsHaarMeasure) {F : GA D T → ℂ}
    (hF : GlobalTheory.Grow.RapidDec T F) (hk : EisensteinRegularAt d b s₀ k) :
    ∃ (M : ℂ → ℂ) (E : GA D T → ℂ), AnalyticAt ℂ M s₀ ∧ M s₀ = meanPair T m F E ∧
      Integrable (descend (GQ T) fun h => F h * E h) (autMeasure T m) ∧
      (∀ h, Tendsto (fun s => (s - s₀) ^ k * cont (sphericalEisenstein d b h) s) (𝓝[≠] s₀) (𝓝 (E h))) ∧
      M =ᶠ[𝓝[≠] s₀] fun s => (s - s₀) ^ k * meanPair T m F fun h => cont (sphericalEisenstein d b h) s := by
  obtain ⟨ε, H, hr, e, hd, hc, C, N, hb⟩ := hk
  have ht : ∀ h, Tendsto (fun s => (s - s₀) ^ k * cont (sphericalEisenstein d b h) s) (𝓝[≠] s₀) (𝓝 (H s₀ h)) := fun h => by
    refine (((hd h).continuousOn.continuousAt (ball_mem_nhds _ hr)).tendsto.mono_left nhdsWithin_le_nhds).congr' ?_
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₀ hr)] with w h1 h2
    exact e w h2 h1 h
  have hinv : ∀ s ∈ ball s₀ ε, ∀ γ ∈ GQ T, ∀ h, H s (γ * h) = H s h := by
    intro s hs γ hγ g
    rcases eq_or_ne s s₀ with rfl | h0
    · have h1 := ht (γ * g)
      rw [eisenstein_left_invariant_rational hI hγ] at h1
      exact tendsto_nhds_unique h1 (ht g)
    · rw [e s hs h0, e s hs h0, eisenstein_left_invariant_rational hI hγ]
  obtain ⟨hi, hdiff⟩ := pair_family hm hF hinv hd hc hb
  refine ⟨_, H s₀, hdiff.analyticAt (ball_mem_nhds _ hr), rfl, hi s₀ (mem_ball_self hr), ht, ?_⟩
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (ball_mem_nhds s₀ hr)] with w h1 h2
  rw [← meanPair_const_mul]
  exact congrArg _ (funext (e w h2 h1))

end GlobalTheory.RegSch.EisensteinPairing

open GlobalTheory.RegSch.EisensteinPairing in

theorem GlobalTheory.RegSch.mean_pairing_eisenstein_continues : ∀ (D : D7) (T T₀ : HSp D) (r : ℕ) (d : HypDec T T₀ r) (b : GL (Fin T.rank) (AE D)), IsMaj T b → HasIw d (Kmax T b) → EisensteinContinues d b → ∀ m : Measure (GA D T), m.IsHaarMeasure → ∀ F : GA D T → ℂ, GlobalTheory.Grow.RapidDec T F → Continues (fun s => meanPair T m F fun h => sphericalEisenstein d b h s) ∧ PoleLE (fun s => meanPair T m F fun h => sphericalEisenstein d b h s) (rhoH T r) 1 ∧ ResidueAt (fun s => meanPair T m F fun h => sphericalEisenstein d b h s) (rhoH T r) (eisensteinResidue d b * meanPair T m F 1) ∧ ∀ (s : ℂ) (E : GA D T → ℂ), (∀ h, HolValueAt (sphericalEisenstein d b h) s (E h)) → Integrable (descend (GQ T) fun h => F h * E h) (autMeasure T m) ∧ HolValueAt (fun s => meanPair T m F fun h => sphericalEisenstein d b h s) s (meanPair T m F E) := by
  intro D T T₀ r d b _ hI hA m hm F hF
  set Z : ℂ → ℂ := fun s => meanPair T m F fun h => cont (sphericalEisenstein d b h) s with hZ
  have hmer : ∀ s₁, MeromorphicAt Z s₁ := by
    intro s₁
    obtain ⟨k, hk⟩ := hA.2.2.1 s₁
    obtain ⟨M, E, han, -, -, -, e⟩ := pair_regular hI hm hF hk
    have h1 : MeromorphicAt (fun s : ℂ => s - s₁) s₁ := (MeromorphicAt.id s₁).sub (MeromorphicAt.const _ _)
    have hm1 : MeromorphicAt (fun s => ((s - s₁) ^ k)⁻¹ * M s) s₁ := (h1.pow k).inv.mul han.meromorphicAt
    refine hm1.congr ?_
    filter_upwards [self_mem_nhdsWithin, e] with w h1 h2
    rw [h2, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ (sub_ne_zero.2 h1)), one_mul]
  have hext : IsMerExt (fun s => meanPair T m F fun h => sphericalEisenstein d b h s) univ Z :=
    ⟨isRightDomain_univ, fun s _ => hmer s, rhoH T r, fun s hs =>
      congrArg (meanPair T m F) (funext fun h => eqOn_cont (eisenstein_analytic_half_plane hA h) hs)⟩
  have key : ∀ (s₁ : ℂ) (j : ℕ) (E : GA D T → ℂ), (∀ h, PoleLE (sphericalEisenstein d b h) s₁ j) →
      (∀ h, CoeffAt (sphericalEisenstein d b h) s₁ (-j) (E h)) →
      Integrable (descend (GQ T) fun h => F h * E h) (autMeasure T m) ∧
        Tendsto (fun s => (s - s₁) ^ j * Z s) (𝓝[≠] s₁) (𝓝 (meanPair T m F E)) := by
    intro s₁ j E hp hc
    obtain ⟨k, hk⟩ := hA.2.2.1 s₁
    obtain ⟨M, E', han, h0, hi, ht, e⟩ := pair_regular hI hm hF (regularAt_of_poleLE hk hp)
    have hE : E' = E := funext fun h => by
      obtain ⟨H, hH, -⟩ := id (hp h)
      refine tendsto_nhds_unique (ht h) ((hH.tendsto_of_poleLE (hp h) (hc h)).congr' ?_)
      filter_upwards [hH.cont_eventuallyEq] with w hw
      rw [hw]
    subst hE
    exact ⟨hi, (h0 ▸ han.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).congr' e⟩
  have hρ := (key (rhoH T r) 1 (fun h => eisensteinResidue d b * (1 : GA D T → ℂ) h) (fun h => (hA.2.2.2.2 h).1)
    fun h => by simpa using (hA.2.2.2.2 h).2).2
  rw [meanPair_const_mul] at hρ
  refine ⟨⟨Z, hext⟩, (hext.isExtAt trivial).poleLE_iff.2 ⟨_, hρ⟩, (hext.isExtAt trivial).coeffAt_of_tendsto hρ,
    fun s E hE => ?_⟩
  obtain ⟨h1, h2⟩ := key s 0 E (fun h => (holValueAt_iff_poleLE.1 (hE h)).1) fun h => by simpa using (hE h).valueAt
  exact ⟨h1, (hext.isExtAt trivial).holValueAt_iff.2 (by simpa using h2)⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemDoublingSiegelParabolicIffChartMemSiegelUnnStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_doublingSiegelParabolic_iff_chart_mem_siegelUnn : ∀ (D : D7) (A : HSp D) (μ : D.host.E), IsSkew μ → ∀ κ : GA D (dblSp A) ≃* G D A.rank, IsChart A μ κ → ∀ g, g ∈ siegel A ↔ κ g ∈ P D A.rank := by
  first | exact @GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P | exact GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P | (intros; apply GlobalTheory.StdUnn.mem_siegel_iff_chart_mem_P <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalIffSecondModelStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_flagUnipotentRadical_iff_secondModel : ∀ (D : D7) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (t lam : D.host.E), t ≠ 0 → lam ≠ 0 → IdE X → ∀ (V₀ : HSp D) (d : HypDec (D.sp.Y 0) V₀ D.R.rS), d.e = GlobalTheory.Core.SBesEx.eM X h t lam → ∀ n, n ∈ flagN d ↔ (iotaX X h n).1 ∈ X.NinfU u ∧ (iotaX X h n).2 ∈ X.NfinU u := by
  first | exact @GlobalTheory.Core.SBesFlagTie.mem_flagN_iff | exact GlobalTheory.Core.SBesFlagTie.mem_flagN_iff | (intros; apply GlobalTheory.Core.SBesFlagTie.mem_flagN_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeStabilizerIffScaledFrameConjStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_latticeStabilizer_iff_scaledFrameConj : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (Λ : Submodule (𝓞 E) (Fin N → E)) (b M M' : GL (Fin N) (AF F ⊗[F] E)) (u : (AF F ⊗[F] E)ˣ), IsLatticeFrame Λ b → (∀ v i j, compFin F E v (M'.1 i j) ∈ intLoc F E v ∧ compFin F E v ((M'⁻¹).1 i j) ∈ intLoc F E v) → M.1 = (u : AF F ⊗[F] E) • M'.1 → ∀ (v : HeightOneSpectrum (𝓞 F)) (x : GL (Fin N) (Fv F v ⊗[F] E)), x ∈ Formalism.UG.stabGL (latLoc F Λ v) ↔ (Formalism.UG.bc (compFin F E v) (b * M))⁻¹ * x * Formalism.UG.bc (compFin F E v) (b * M) ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v) := by
  first | exact @GlobalTheory.StdUnn.StabFin.mem_stab_iff | exact GlobalTheory.StdUnn.StabFin.mem_stab_iff | (intros; apply GlobalTheory.StdUnn.StabFin.mem_stab_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemUnitaryStandardIffConjSimilitudeStatement
section
open scoped Matrix NNReal ComplexConjugate TensorProduct ContDiff
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.Core.Rk.SWLaw GlobalTheory.Core.Rk.SW GlobalTheory.StdUnn
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_unitaryStandard_iff_conj_similitude : ∀ (R : Type) [CommRing R] (σ : R →+* R), (∀ x, σ (σ x) = x) → ∀ (N : ℕ) (M y : GL (Fin N) R) (r : Rˣ), Formalism.UG.cT σ M.1 * M.1 = (r : R) • 1 → (y ∈ Formalism.UG.UJ σ (1 : Matrix (Fin N) (Fin N) R) ↔ M⁻¹ * y * M ∈ Formalism.UG.UJ σ (1 : Matrix (Fin N) (Fin N) R)) := by
  first | exact @GlobalTheory.StdUnn.mem_UJ_one_iff_conj_similitude | exact GlobalTheory.StdUnn.mem_UJ_one_iff_conj_similitude | (intros; apply GlobalTheory.StdUnn.mem_UJ_one_iff_conj_similitude <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelSourceSupportFiniteComponentInBox
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff

namespace GlobalTheory.Unf

theorem extY_map_infPart_eq_zero {D : D7} {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (a : Mx D T.rank ρ) (ha : a.map (infPart D) = 0) : (d.extY T a).map (infPart D) = 0 := by
  rw [HypDec.extY_apply, Matrix.map_mul, ha, Matrix.zero_mul]

theorem mixS_support_inBox : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (U : AddSubgroup (WO S T)), IsOpen (U : Set (WO S T)) → ∃ K : Set (Mx D T.rank ρ), IsCompact K ∧ ∀ f ∈ GlobalTheory.Size.thetaLevel ψ S T U, ∀ x w, d.mixS T ψ v.μ v.𝓕 f x w ≠ 0 → InBox K x := by
  intro D ψ hψ S S₀ T ρ d v U hU
  obtain ⟨K, hK, hbox⟩ := GlobalTheory.T.finiteAnnihilator_open_subgroup_in_box D ψ hψ S S₀ T ρ d U hU
  refine ⟨K, hK, fun f hf x w hne => hbox x fun a ha haU => ?_⟩
  have hY := (GlobalTheory.T.heisenbergOperator_thetaFunctional_mixedSourceModel D ψ hψ S S₀ T ρ d v f hf.1).2.1 x a
  rw [hf.2 _ haU (extY_map_infPart_eq_zero d T a ha)] at hY
  have hw := congrFun hY w
  rw [Pi.smul_apply, smul_eq_mul] at hw
  have h1 : (ψ (symplO S T (d.extX T x) (d.extY T a)) - 1) * d.mixS T ψ v.μ v.𝓕 f x w = 0 := by
    rw [sub_mul, one_mul, ← hw, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right hne)

end GlobalTheory.Unf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MulVecMapResolution
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain

namespace GlobalTheory.MulVecTensorResolution

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem mulVec_map_tmul {v : HeightOneSpectrum (𝓞 F)} {k l : ℕ} (M : Matrix (Fin k) (Fin l) E)
    (a : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) (x : Fin l → E) :
    Matrix.mulVec (Matrix.map M fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) (fun i => a ⊗ₜ[F] x i) =
      fun j => a ⊗ₜ[F] (Matrix.mulVec M x) j := by
  funext j
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
    TensorProduct.tmul_sum]

theorem map_mem_latLoc {v : HeightOneSpectrum (𝓞 F)} {k l : ℕ} (M : Matrix (Fin k) (Fin l) E)
    {L₁ : Submodule (𝓞 E) (Fin l → E)} {L₂ : Submodule (𝓞 E) (Fin k → E)}
    (hM : ∀ x ∈ L₁, Matrix.mulVec M x ∈ L₂) {w : Fin l → TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E}
    (hw : w ∈ GlobalTheory.AdelicU.latLoc F L₁ v) :
    Matrix.mulVec (Matrix.map M fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) w ∈ GlobalTheory.AdelicU.latLoc F L₂ v := by
  refine GlobalTheory.AdelicU.latLoc_induction
    (p := fun w => Matrix.mulVec (Matrix.map M fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) w ∈
      GlobalTheory.AdelicU.latLoc F L₂ v) ?_ ?_ ?_ ?_ hw
  · intro a ha x hx
    rw [mulVec_map_tmul]
    exact GlobalTheory.AdelicU.tmul_mem_latLoc ha (hM x hx)
  · rw [Matrix.mulVec_zero]; exact zero_mem _
  · intro y z hy hz
    rw [Matrix.mulVec_add]; exact add_mem hy hz
  · intro y hy
    rw [Matrix.mulVec_neg]; exact neg_mem hy

theorem mulVec_map_resolution {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n m t : ℕ}
    {e e' : Matrix (Fin n) (Fin t) R} {i₀ : Matrix (Fin n) (Fin m) R} {qX qY : Matrix (Fin t) (Fin n) R}
    {q0 : Matrix (Fin m) (Fin n) R} (h : e * qX + i₀ * q0 + e' * qY = 1) (y : Fin n → S) :
    y = e.map φ *ᵥ (qX.map φ *ᵥ y) + i₀.map φ *ᵥ (q0.map φ *ᵥ y) + e'.map φ *ᵥ (qY.map φ *ᵥ y) := by
  have h' := congrArg φ.mapMatrix h
  simp only [map_add, map_one, RingHom.mapMatrix_apply, Matrix.map_mul] at h'
  simp only [Matrix.mulVec_mulVec, ← Matrix.add_mulVec]
  rw [h', Matrix.one_mulVec]

theorem main : ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [inst_3 : Algebra F E] {n m t : ℕ} {e e' : Matrix (Fin n) (Fin t) E} {i₀ : Matrix (Fin n) (Fin m) E} {qX qY : Matrix (Fin t) (Fin n) E} {q0 : Matrix (Fin m) (Fin n) E}, e * qX + i₀ * q0 + e' * qY = (1 : Matrix (Fin n) (Fin n) E) → qX * e = (1 : Matrix (Fin t) (Fin t) E) → qX * i₀ = (0 : Matrix (Fin t) (Fin m) E) → qX * e' = (0 : Matrix (Fin t) (Fin t) E) → q0 * e = (0 : Matrix (Fin m) (Fin t) E) → q0 * i₀ = (1 : Matrix (Fin m) (Fin m) E) → q0 * e' = (0 : Matrix (Fin m) (Fin t) E) → qY * e = (0 : Matrix (Fin t) (Fin t) E) → qY * i₀ = (0 : Matrix (Fin t) (Fin m) E) → qY * e' = (1 : Matrix (Fin t) (Fin t) E) → ∀ {L : Submodule (NumberField.RingOfIntegers E) (Fin n → E)} {L' : Submodule (NumberField.RingOfIntegers E) (Fin m → E)} {L₁ : Submodule (NumberField.RingOfIntegers E) (Fin t → E)}, (∀ (z : Fin n → E), z ∈ L ↔ Matrix.mulVec qX z ∈ L₁ ∧ Matrix.mulVec q0 z ∈ L' ∧ Matrix.mulVec qY z ∈ L₁) → ∀ (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) (y : Fin n → TensorProduct F (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) E), y ∈ GlobalTheory.AdelicU.latLoc F L v ↔ Matrix.mulVec (Matrix.map qX fun (x : E) ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y ∈ GlobalTheory.AdelicU.latLoc F L₁ v ∧ Matrix.mulVec (Matrix.map q0 fun (x : E) ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y ∈ GlobalTheory.AdelicU.latLoc F L' v ∧ Matrix.mulVec (Matrix.map qY fun (x : E) ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y ∈ GlobalTheory.AdelicU.latLoc F L₁ v := by
  intro F E _ _ _ _ n m t e e' i₀ qX qY q0 hsum hXe hXi hXe' h0e h0i h0e' hYe hYi hYe' L L' L₁ hL v y
  have mX : ∀ x ∈ L, Matrix.mulVec qX x ∈ L₁ := fun x hx => ((hL x).1 hx).1
  have m0 : ∀ x ∈ L, Matrix.mulVec q0 x ∈ L' := fun x hx => ((hL x).1 hx).2.1
  have mY : ∀ x ∈ L, Matrix.mulVec qY x ∈ L₁ := fun x hx => ((hL x).1 hx).2.2
  have me : ∀ x ∈ L₁, Matrix.mulVec e x ∈ L := fun x hx => (hL _).2
    ⟨by rw [Matrix.mulVec_mulVec, hXe, Matrix.one_mulVec]; exact hx,
     by rw [Matrix.mulVec_mulVec, h0e, Matrix.zero_mulVec]; exact zero_mem _,
     by rw [Matrix.mulVec_mulVec, hYe, Matrix.zero_mulVec]; exact zero_mem _⟩
  have mi : ∀ x ∈ L', Matrix.mulVec i₀ x ∈ L := fun x hx => (hL _).2
    ⟨by rw [Matrix.mulVec_mulVec, hXi, Matrix.zero_mulVec]; exact zero_mem _,
     by rw [Matrix.mulVec_mulVec, h0i, Matrix.one_mulVec]; exact hx,
     by rw [Matrix.mulVec_mulVec, hYi, Matrix.zero_mulVec]; exact zero_mem _⟩
  have me' : ∀ x ∈ L₁, Matrix.mulVec e' x ∈ L := fun x hx => (hL _).2
    ⟨by rw [Matrix.mulVec_mulVec, hXe', Matrix.zero_mulVec]; exact zero_mem _,
     by rw [Matrix.mulVec_mulVec, h0e', Matrix.zero_mulVec]; exact zero_mem _,
     by rw [Matrix.mulVec_mulVec, hYe', Matrix.one_mulVec]; exact hx⟩
  constructor
  · intro hy
    exact ⟨map_mem_latLoc qX mX hy, map_mem_latLoc q0 m0 hy, map_mem_latLoc qY mY hy⟩
  · rintro ⟨h1, h2, h3⟩
    have key : y = Matrix.mulVec (Matrix.map e fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x)
          (Matrix.mulVec (Matrix.map qX fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y) +
        Matrix.mulVec (Matrix.map i₀ fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x)
          (Matrix.mulVec (Matrix.map q0 fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y) +
        Matrix.mulVec (Matrix.map e' fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x)
          (Matrix.mulVec (Matrix.map qY fun x : E ↦ (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v) ⊗ₜ[F] x) y) :=
      mulVec_map_resolution
        (Algebra.TensorProduct.includeRight : E →ₐ[F] Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv F v ⊗[F] E).toRingHom hsum y
    rw [key]
    exact add_mem (add_mem (map_mem_latLoc e me h1) (map_mem_latLoc i₀ mi h2)) (map_mem_latLoc e' me' h3)

end GlobalTheory.MulVecTensorResolution
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MultiplicityMapValueKFiniteMemCuspForms
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.LiftRows GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

theorem GlobalTheory.ChainOnto.RealData.multiplicityMap_value_kFinite_mem_cuspForms : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D), V.SigOK → ∀ (S : D.what₂.Tau → SPar) (M : DSModel V S), ∃ cA : GlobalTheory.Mem.Th.CptF V, GlobalTheory.Cusp.IsCartanFrame V cA ∧ (∀ τ, IsCartanInv (gramAt D V τ) (cart M τ)) ∧ (∀ τ, cA τ * cart M τ = Formalism.UG.Jpq (V.sig (tauE D τ)).1 (V.sig (tauE D τ)).2 * cA τ) ∧ ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ U ∈ Mult θ M J χ, ∀ v : M.Vec, (∀ τ, (v τ : M.H τ) ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction.kfin M τ) → U v ∈ GlobalTheory.Cusp.A0 θ V cA := by
  intro D θ hθ V hV S M
  refine ⟨GlobalTheory.ChainOnto.RealData.sortedFrame M hV, GlobalTheory.ChainOnto.RealData.isCartanFrame_sortedFrame M hV,
    fun τ => GlobalTheory.ChainOnto.RealData.isCartanInv_cart M τ, fun τ => GlobalTheory.ChainOnto.RealData.sortedFrame_cart M hV τ, ?_⟩
  intro J χ U hU v hv
  induction hU using Submodule.span_induction with
  | mem T hT =>
    exact GlobalTheory.Cusp.mem_cuspForms.2 ⟨⟨hT.aut v, hT.cusp v⟩,
      GlobalTheory.ChainOnto.RealData.isKFinite_value θ hθ M hV hT v hv⟩
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul a x _ hx => exact (GlobalTheory.Cusp.A0 θ V _).smul_mem a hx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmZeroRat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SeeSaw.LiftSumProof

variable {D : D7}

theorem om_zero_rat {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hω : IsWeilDatumO ψ S T χS χT om) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) {γ : GA D S} (hγ : γ ∈ GQ S)
    {γ' : GA D T} (hγ' : γ' ∈ GQ T) (g : GA D S) (h : GA D T) : om (γ * g, γ' * h) f 0 = om (g, h) f 0 := by
  have e : ((γ * g, γ' * h) : GA D S × GA D T) = (γ, γ') * (g, h) := rfl
  rw [e, map_mul, Module.End.mul_apply]
  exact hω.om_aut γ hγ γ' hγ' _ (hω.om_pres _ _ hf)

theorem liftSum : ∀ D : D7, LiftSum D := by
  intro D ψ θ hθ S T x y hx hy k hk P
  obtain ⟨χS, χT, hω⟩ := hk.weil
  have hψ : IsStdChar D ψ (-1) := hk.vac.1
  have hvac : IsThetaFunO ψ S T k.vac := hk.vac.2.theta
  have hcomb : IsThetaFunO ψ S T (comb ψ S T k.c k.vac) :=
    GlobalTheory.FinTranslate.isTheta_sum_heisO_fin D ψ S T hψ.1 k.vac hvac (WO S T) k.c.support id k.c (fun u hu => hk.fin u hu)
  have hpt : IsThetaFunO ψ S T (k.pt ψ θ x y P) :=
    GlobalTheory.FockTheta.ptStable D ψ θ hψ hθ S T x.s y.s x.B y.B _ P hcomb

  have key : ∀ φ : GA D S → ℂ, IsContAut S φ →
      (∀ h, IntegrableOn (fun g => k.om (g, h) (k.pt ψ θ x y P) 0 * φ g) x.vol.𝓕 x.vol.μ) ∧
      Continuous fun h => ∫ g in x.vol.𝓕, k.om (g, h) (k.pt ψ θ x y P) 0 * φ g ∂x.vol.μ := by
    intro φ hφ
    have hc : Continuous (Function.uncurry fun (g : GA D S) (h : GA D T) => k.om (g, h) (k.pt ψ θ x y P) 0 * φ g) :=
      (hω.om_cont _ hpt 0).mul (hφ.2.comp continuous_fst)
    have hinv : ∀ γ ∈ GQ S, ∀ (g : GA D S) (h : GA D T),
        k.om (γ * g, h) (k.pt ψ θ x y P) 0 * φ (γ * g) = k.om (g, h) (k.pt ψ θ x y P) 0 * φ g := by
      intro γ hγ g h
      have e := om_zero_rat hω hpt hγ (one_mem (GQ T)) g h
      rw [one_mul] at e
      rw [e, hφ.1 γ hγ g]
    obtain ⟨h1, h2, -⟩ := GlobalTheory.T.continuous_integral_compactAutomorphicQuotient_param D S hx.cpt x.vol (GA D T) _ hc hinv
    exact ⟨h1, h2⟩
  refine ⟨hpt, fun φ hφ => ⟨fun γ' hγ' h => ?_, ?_⟩, fun I s a φ hφ => ?_⟩
  · show ∫ g in x.vol.𝓕, k.om (g, γ' * h) (k.pt ψ θ x y P) 0 * φ g ∂x.vol.μ =
      ∫ g in x.vol.𝓕, k.om (g, h) (k.pt ψ θ x y P) 0 * φ g ∂x.vol.μ
    congr 1
    funext g
    have e := om_zero_rat hω hpt (one_mem (GQ S)) hγ' g h
    rw [one_mul] at e
    rw [e]
  · exact (key φ hφ).2
  · funext h
    show ∫ g in x.vol.𝓕, k.om (g, h) (k.pt ψ θ x y P) 0 * (∑ i ∈ s, a i • φ i) g ∂x.vol.μ =
      (∑ i ∈ s, a i • fun h' => ∫ g in x.vol.𝓕, k.om (g, h') (k.pt ψ θ x y P) 0 * φ i g ∂x.vol.μ) h
    rw [Finset.sum_apply]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    have e : (fun g => ∑ i ∈ s, k.om (g, h) (k.pt ψ θ x y P) 0 * (a i * φ i g)) =
        fun g => ∑ i ∈ s, a i * (k.om (g, h) (k.pt ψ θ x y P) 0 * φ i g) := by
      funext g
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e, integral_finset_sum s (fun i hi => ((key (φ i) (hφ i hi)).1 h).const_mul (a i))]
    exact Finset.sum_congr rfl fun i _ => integral_const_mul (a i) _

end GlobalTheory.SeeSaw.LiftSumProof

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RealRepresentationMovesRieszVectorFrameStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realRepresentation_moves_rieszVector_frame : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (F : Formalism.L2.Forms.Forms0 D u) (tr : Formalism.L2.SG.ColDict.Transport X u F) (s : X.B.I.Ginf), s ∈ Hinf X u → ∀ z z' : Formalism.L2.Forms.Fr D 0 (Nat.zero_le _), Formalism.L2.Forms.IsTr (Formalism.L2.SG.ColDict.sTil X tr.wt s) z z' → X.piU u s (rieszJ tr z) = rieszJ tr z' := by
  first | exact @GlobalTheory.Core.Mi.piU_rieszJ | exact GlobalTheory.Core.Mi.piU_rieszJ | (intros; apply GlobalTheory.Core.Mi.piU_rieszJ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnfoldingIntegralTwistPrimeEqDeepFiniteSumStatement
section
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.TwBridge
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldingIntegral_twistPrime_eq_deep_finite_sum : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (W : TwData k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → cst.Ok → AtTwist (R := R) sel mu cst σ₀ P ι s W → SumAgree Ch sel mu cst σ₀ P ι s W ν := by
  first | exact @GlobalTheory.TwSumAgree.sumAgree | exact GlobalTheory.TwSumAgree.sumAgree | (intros; apply GlobalTheory.TwSumAgree.sumAgree <;> assumption)
end

