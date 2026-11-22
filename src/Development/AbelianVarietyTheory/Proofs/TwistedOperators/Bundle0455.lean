import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0432
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0235
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0430
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.IntegrableOnOfPeriodic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0293
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0447
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0312

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralConvergentDefinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefLiftSmooth

theorem hasDerivAt_integral_of_cocompact {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [MeasurableSpace H] [BorelSpace H] (Γ : Subgroup H) [Countable Γ] (μ : Measure H)
    [μ.IsMulLeftInvariant] [IsFiniteMeasureOnCompacts μ] (𝓕 C : Set H)
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hC : IsCompact C)
    (hcov : ∀ h : H, ∃ γ ∈ Γ, ∃ c ∈ C, h = γ * c) (K K' : ℝ → H → ℂ)
    (hK : ∀ t, Continuous (K t)) (hK' : Continuous fun p : ℝ × H => K' p.1 p.2)
    (hinv : ∀ γ ∈ Γ, ∀ t h, K t (γ * h) = K t h) (hinv' : ∀ γ ∈ Γ, ∀ t h, K' t (γ * h) = K' t h)
    (hd : ∀ t h, HasDerivAt (fun s => K s h) (K' t h) t) (t₀ : ℝ) :
    HasDerivAt (fun t => ∫ h in 𝓕, K t h ∂μ) (∫ h in 𝓕, K' t₀ h ∂μ) t₀ := by
  obtain ⟨M, hM⟩ := ((isCompact_closedBall t₀ 1).prod hC).exists_bound_of_continuousOn hK'.continuousOn
  have hconst : IntegrableOn (fun _ : H => (M : ℂ)) 𝓕 μ :=
    GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ continuous_const
      (fun _ _ _ => rfl)
  have hK'c : ∀ t, Continuous (K' t) := fun t => hK'.comp (Continuous.prodMk_right t)
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (bound := fun _ => ‖(M : ℂ)‖)
    (Metric.ball_mem_nhds t₀ one_pos) (Filter.Eventually.of_forall fun t => (hK t).aestronglyMeasurable)
    (GlobalTheory.CocompactIntegrable.integrableOn_of_cocompact Γ μ 𝓕 C h𝓕 hC hcov _ (hK t₀) (fun γ hγ h => hinv γ hγ t₀ h))
    (hK'c t₀).aestronglyMeasurable ?_ hconst.norm ?_).2
  · refine Filter.Eventually.of_forall fun h t ht => ?_
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hcov h
    rw [hinv' γ hγ]
    refine (hM (t, c) ⟨Metric.ball_subset_closedBall ht, hc⟩).trans ?_
    rw [Complex.norm_real]
    exact le_abs_self M
  · exact Filter.Eventually.of_forall fun h t _ => hd t h

theorem lift_smooth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), GlobalTheory.FunPr.Hypotheses₂ → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∀ (k : ℕ) (τs : Fin k → D.what₂.Tau) (Xs : Fin k → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ i, Xs i ∈ lieAt T (τs i)) → ∀ h : GA D T, ContDiff ℝ ∞ fun t : Fin k → ℝ => (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) (h * (List.ofFn fun i => oneP θ T (τs i) (Xs i) (t i)).prod) := by
  intro D ψ θ S T χS χT om Φ φ ν 𝓕 _ hω hθ hΦ hS _ hν h𝓕 hφ k τs Xs hX h
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D S
  obtain ⟨_, _, _, _, _, _, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hS
  have hK := GlobalTheory.Mem.Lift.isKerSys_thKer (θ := θ) hθ hω.std (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont
  set κ := GlobalTheory.Mem.Lift.thKer ψ S T om with hκ
  let L : GlobalTheory.RealWeil.thetaSub ψ S T → GA D T → ℂ := fun f h => ∫ g in 𝓕, κ f g h * φ g ∂ν
  have hkinv : ∀ f, ∀ γ ∈ GQ S, ∀ (g : GA D S) (h : GA D T), κ f (γ * g) h * φ (γ * g) = κ f g h * φ g := by
    intro f γ hγ g h
    have := hK.left f γ hγ 1 (one_mem _) g h
    rw [one_mul] at this
    rw [this, hφ.left γ hγ]
  have hcont : ∀ φ' ∈ Set.range L, Continuous φ' := by
    rintro _ ⟨f, rfl⟩
    exact GlobalTheory.DefLiftCont.continuous_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov
      (fun h g => κ f g h * φ g) (((hK.cont f).comp continuous_swap).mul (hφ.cont.comp continuous_snd))
      (fun γ hγ h g => hkinv f γ hγ g h)
  have hder : ∀ φ' ∈ Set.range L, ∀ τ, ∀ X ∈ lieAt T τ, ∃ φ'' ∈ Set.range L, ∀ h,
      HasDerivAt (fun t : ℝ => φ' (h * oneP θ T τ X t)) (φ'' h) 0 := by
    rintro _ ⟨f, rfl⟩ τ X hX
    obtain ⟨f', e⟩ := hK.derW τ X hX f
    refine ⟨L f', ⟨f', rfl⟩, fun h => ?_⟩
    have hoc := GlobalTheory.Mem.Lift.continuous_oneP (V := T) hθ hX
    have key := hasDerivAt_integral_of_cocompact (GQ S) ν 𝓕 C h𝓕 hC hcov
      (fun t g => κ f g (h * oneP θ T τ X t) * φ g) (fun t g => κ f' g (h * oneP θ T τ X t) * φ g)
      (fun t => ((hK.cont f).comp (continuous_id.prodMk continuous_const)).mul hφ.cont)
      (((hK.cont f').comp (continuous_snd.prodMk (continuous_const.mul (hoc.comp continuous_fst)))).mul
        (hφ.cont.comp continuous_snd))
      (fun γ hγ t g => hkinv f γ hγ g _) (fun γ hγ t g => hkinv f' γ hγ g _)
      (fun t g => (GlobalTheory.Mem.Lift.hasDerivAt_oneP (φ := fun h => κ f g h) (φ' := fun h => κ f' g h) hθ hX
        (fun h => e g h) h t).mul_const (φ g)) 0
    simpa only [GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one, L] using key
  have hsm := GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ T (Set.range L) hcont hder (L ⟨Φ, hΦ⟩) ⟨_, rfl⟩
  exact hsm k τs Xs hX h

end GlobalTheory.DefLiftSmooth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralMeasurableDefinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.DefiniteLiftZfin

open Matrix

theorem isCuspFun_of_posDef {D : D7} {V : HSp D} (hV : ∀ τ, (gramAt D V τ).PosDef) (φ : GA D V → ℂ) :
    IsCuspFun V φ := by
  intro r C ⟨hr, hli, h0⟩
  exfalso
  obtain ⟨τ0⟩ : Nonempty D.what₂.Tau := ⟨D.eTau.symm (Classical.arbitrary _)⟩
  have hτ : ∀ a, tauE D τ0 (star a) = starRingEnd ℂ (tauE D τ0 a) := D.sp.cm.cmUnram.2.1 (tauE D τ0)
  have h1 := congrArg (tauE D τ0) (congrFun (congrFun h0 ⟨0, hr⟩) ⟨0, hr⟩)
  have hx : star (fun i => tauE D τ0 (C i ⟨0, hr⟩)) ⬝ᵥ (gramAt D V τ0 *ᵥ fun i => tauE D τ0 (C i ⟨0, hr⟩)) = 0 := by
    rw [Matrix.zero_apply, map_zero] at h1
    rw [← h1, Matrix.mul_assoc]
    simp only [gramAt, Matrix.mul_apply, map_sum, map_mul, dotProduct, Matrix.mulVec, Matrix.map_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    exact (hτ _).symm
  have h2 : (fun i => tauE D τ0 (C i ⟨0, hr⟩)) = 0 := by
    by_contra hne
    have := (hV τ0).dotProduct_mulVec_pos hne
    rw [hx] at this
    exact lt_irrefl _ this
  refine hli.ne_zero ⟨0, hr⟩ (funext fun i => ?_)
  exact (tauE D τ0).injective ((congrFun h2 i).trans (map_zero (tauE D τ0)).symm)

theorem lift_zfin : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S))
    (𝓕 : Set (GA D S)), GlobalTheory.FunPr.Hypotheses₂ → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ →
    (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν →
    IsAutFunSm θ S φ → ∃ W : Submodule ℂ (GA D T → ℂ), FiniteDimensional ℂ W ∧
      (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) ∈ W ∧ ∀ τ k, ∀ f ∈ W, gelf θ T τ k f ∈ W := by
  intro D ψ θ S T χS χT om Φ φ ν 𝓕 hP hω hθ hΦ hS _ hH hF hφ
  have hK := GlobalTheory.Mem.Lift.isKerSys_thKer (θ := θ) hθ hω.std (GlobalTheory.Ker.isWeak_of_datum hω) hω.om_cont
  exact (hK.lift hP.cuspRapidDecay hθ ⟨hH, hF⟩ ⟨hφ, isCuspFun_of_posDef hS φ⟩ ⟨Φ, hΦ⟩).2.zfin

end GlobalTheory.DefiniteLiftZfin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralUnfoldingDefinite
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
open scoped ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LiftGrowthDef

theorem lift_growth : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (Φ : WO S T → ℂ) (φ : GA D S → ℂ) (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), GlobalTheory.FunPr.Hypotheses₂ → IsWeilDatumO ψ S T χS χT om → IsInfFam θ → IsThetaFunO ψ S T Φ → (∀ τ, (gramAt D S τ).PosDef) → (∀ τ, (gramAt D T τ).PosDef) → ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → IsAutFunSm θ S φ → ∃ N : ℕ, ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt T p.1) → ∀ x, ∃ C : ℝ, ∀ g ∈ GinfC T, ‖(l.foldr (fun p f => Rder θ T p.1 p.2 f) (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν)) (x * g)‖ ≤ C * normInf θ T g ^ N := by
  intro D ψ θ S T χS χT om Φ φ ν 𝓕 _ hom hθ hΦ hS hT hν h𝓕 hφ
  have key : ∀ l : List (D.what₂.Tau × Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ p ∈ l, p.2 ∈ lieAt T p.1) →
      ∃ L : ℂ →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L x)) ∧
        l.foldr (fun p f => Rder θ T p.1 p.2 f) (fun h : GA D T => ∫ g in 𝓕, thetaKO om g h Φ * φ g ∂ν) =
          GlobalTheory.DefLift.lift om ν 𝓕 (fun g => L (φ g)) := by
    intro l hl
    induction l with
    | nil =>
      refine ⟨LinearMap.toSpanSingleton ℂ _ Φ, fun x => ?_, ?_⟩
      · exact Formalism.IndefR.Fin.theta_smul S T x hΦ
      · funext h
        simp only [List.foldr_nil, GlobalTheory.DefLift.lift, LinearMap.toSpanSingleton_apply, thetaKO, map_smul,
          Pi.smul_apply, smul_eq_mul, mul_comm]
    | cons p l ih =>
      obtain ⟨L, hL, e⟩ := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq))
      obtain ⟨-, hd⟩ := GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ S T χS χT om hom θ hθ hS ℂ L hL φ
        hφ.cont hφ.left ν 𝓕 hν h𝓕
      obtain ⟨L', hL', -, hder⟩ := hd p.1 p.2 (hl p List.mem_cons_self)
      refine ⟨L', hL', ?_⟩
      rw [List.foldr_cons, e]
      funext g
      exact (hder g).deriv
  refine ⟨0, fun l hl x => ?_⟩
  obtain ⟨L, hL, e⟩ := key l hl
  obtain ⟨⟨hc, hinv⟩, -⟩ := GlobalTheory.DefLiftDer.lift_continuous_invariant_hasDerivAt D ψ S T χS χT om hom θ hθ hS ℂ L hL φ
    hφ.cont hφ.left ν 𝓕 hν h𝓕
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact T hT
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M, fun g _ => ?_⟩
  rw [e, pow_zero, mul_one]
  obtain ⟨γ, hγ, c, hc', hxc⟩ := hcov (x * g)
  rw [hxc, hinv γ hγ c]
  exact hM c hc'

end GlobalTheory.LiftGrowthDef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittTowerRestrictionUnipotentRadicalInvariant
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.UnipRes

theorem res_unip : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (n : NI V C) (f : WO V W → ℂ), IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω ((n : GA D V), 1) f) = res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ n f hf
  obtain ⟨C', h1, h2, h3⟩ := GlobalTheory.T.exists_isotropicDualFrame_of_splitEmbedding D V V' r C B hs
  obtain ⟨a, haQ, haC, haB, haC'⟩ := GlobalTheory.T.exists_rationalLevi_scaling_isotropicFrame D V V' r C C' B hs h1 h2 h3
  obtain ⟨l, hl⟩ := GlobalTheory.T.thetaRestriction_invariant_rationalLeviScaling D V V' W r C B hs a haQ haC haB ψ χS χT ω hω μ 𝓨 hμ
  have hp : ∀ p f, IsThetaFunO ψ V W f → IsThetaFunO ψ V W (ω p f) := hω.om_pres
  have hm : ∀ x y : GA D V, ∀ f, ω (x * y, 1) f = ω (x, 1) (ω (y, 1) f) := by
    intro x y f
    rw [show ((x * y, 1) : GA D V × GA D W) = (x, 1) * (y, 1) by simp, map_mul, Module.End.mul_apply]
  have key : ∀ g ∈ NI V C, ∀ f, IsThetaFunO ψ V W f →
      res V V' W C B μ 𝓨 (ω (g, 1) f) = res V V' W C B μ 𝓨 f := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨hx1, hx2, hx3⟩ := hx
      obtain ⟨m, hmN, rfl⟩ := GlobalTheory.T.unipotent_levi_matrix_action_identity D V V' r C C' B hs h1 h2 h3 a haC haB haC' x hx1 hx2 hx3
      obtain ⟨c, hc⟩ := GlobalTheory.T.unipotentRadical_stabiliser_scales_restriction D V V' W r C B hs ψ χS χT ω hω μ 𝓨 hμ m hmN
      intro f hf
      have e1 : res V V' W C B μ 𝓨 (ω (a, 1) (ω (a⁻¹, 1) (ω (m⁻¹, 1) f))) = res V V' W C B μ 𝓨 (ω (m⁻¹, 1) f) := by
        rw [← hm, mul_inv_cancel, show ((1 : GA D V), (1 : GA D W)) = 1 from rfl, map_one]; rfl
      have e2 : res V V' W C B μ 𝓨 (ω (m, 1) (ω (m⁻¹, 1) f)) = res V V' W C B μ 𝓨 f := by
        rw [← hm, mul_inv_cancel, show ((1 : GA D V), (1 : GA D W)) = 1 from rfl, map_one]; rfl
      rw [hm, hm, hm, hl _ (hp _ _ (hp _ _ (hp _ _ hf))), hc _ (hp _ _ (hp _ _ hf)), smul_smul, mul_comm,
        ← smul_smul, ← hl _ (hp _ _ (hp _ _ hf)), e1, ← hc _ (hp _ _ hf), e2]
    | one => intro f hf; rw [show ((1 : GA D V), (1 : GA D W)) = 1 from rfl, map_one]; rfl
    | mul x y _ _ hx hy => intro f hf; rw [hm, hx _ (hp _ _ hf), hy _ hf]
    | inv x _ hx =>
      intro f hf
      have := hx (ω (x⁻¹, 1) f) (hp _ _ hf)
      rw [← this, ← hm, mul_inv_cancel, show ((1 : GA D V), (1 : GA D W)) = 1 from rfl, map_one]; rfl
  exact key n n.2 f hf
end GlobalTheory.UnipRes
end

