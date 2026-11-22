import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsOpenKerUnramMulTame
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SameOrbEquivalence
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0302
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.FirstTermIdentity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsParamFunOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0326
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0318
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0259
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemberDatumOfFlagTie
import Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLw
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0143
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsIsFundU
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0194
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnisotropicTermsMeanZeroUnipotentRadical
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0027
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.DiagSmall
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0029
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ToGlob0
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0028
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CollSBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.Bundle0083
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0048
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0004
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingHypothesesHoldFamily
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0336
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PiEqOfFinPart
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceTwistSchwartzBruhat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawKernelChainLevelPrimeOperatorToStepZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0026
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.UnitRatio

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSplitPlaceGeometryExtensionCosetOrbitReps
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl GlobalTheory.QTw ValuativeRel
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.QTw.CosExt

set_option maxHeartbeats 4000000 in

theorem exists_qExt_cos : ∀ (D : D7) (c : Comm D) (v : VCom c) (B : GlobalTheory.Fam.Base c) (PP : Formalism.L2.DIV.Pl D.host.E) (G : QGeo v B PP) (χ : ℕ → (AE D)ˣ →* Circle), c.Is → ∀ (δ : G.kˣ →* ℂˣ) (hδ : IsTame δ) (η : ℕ → G.kˣ →* ℂˣ), (∀ j, IsUnram (η j)) → (∀ j, j ≤ G.s + 1 → (ofSplit G.q).IsComp (χ j)⁻¹ (η (j + 1) * δ)) → ∀ A, (G.T δ hδ η).IsRepSystem A G.ψk G.ν → ∀ M : ℕ, (G.T δ hδ η).Adapted A (box _ (G.ϖ ^ M)⁻¹) (box _ (G.ϖ ^ M)) → ∀ (C : Type) [Fintype C] (cs : C → XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) → G.k), (∀ y y', SameOrb ((G.T δ hδ η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ M)) (Submodule.Quotient.mk (cs y)) (Submodule.Quotient.mk (cs y')) → y = y') → (∀ z ∈ box (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1)) (G.ϖ ^ M)⁻¹, ∃ y, SameOrb ((G.T δ hδ η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ M)) (Submodule.Quotient.mk (cs y)) (Submodule.Quotient.mk z)) → ∃ E : QExt G χ, E.δ = δ ∧ E.η = η ∧ E.A = A ∧ E.M = M ∧ (∃ e : C ≃ E.Ch (G.s + 1), ∀ y, E.cos (e y) = Submodule.Quotient.mk (cs y)) ∧ ∀ j, G.s + 1 + 1 < j → Nonempty (Unique (E.Ch j)) := by
  intro D c v B PP G χ hc δ hδ η hη hμ A hA M hM C _ cs hinj hall
  obtain ⟨E, rfl, rfl, rfl, rfl, -⟩ := GlobalTheory.QTw.Inh.exists_ext_of_reps D c v B PP G χ hc δ hδ η hη hμ A hA M hM
  classical
  let Ch' : ℕ → Type := fun j => if j = G.s + 1 then C else if G.s + 1 + 1 < j then Unit else E.Ch j
  have eC : Ch' (G.s + 1) = C := if_pos rfl
  have eE : ∀ j, j ≤ G.s + 1 + 1 → j ≠ G.s + 1 → Ch' j = E.Ch j := fun j h1 h2 => by
    simp only [Ch', if_neg h2, if_neg (not_lt.2 h1)]
  have eU : ∀ j, G.s + 1 + 1 < j → Ch' j = Unit := fun j h1 => by
    simp only [Ch', if_neg (show j ≠ G.s + 1 by omega), if_pos h1]
  let fC : ∀ j, Fintype (Ch' j) := fun j => by
    simp only [Ch']; split_ifs <;> infer_instance
  let rep' : ∀ j d, j + d = G.s → Ch' j → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin (d + 1)) G.k :=
    fun j d h x => E.rep j d h (cast (eE j (by omega) (by omega)) x)
  let cos' : Ch' (G.s + 1) → (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1) → G.k) ⧸ box (XIx (Fin D.R.k) (Fin D.R.t) (G.s + 1)) (G.ϖ ^ E.M) :=
    fun y => Submodule.Quotient.mk (cs (cast eC y))
  have hpen : ∀ (α : Ch' G.s) (y : Ch' (G.s + 1)), ∃ e, (ofSplit G.q).IsCombAt c.ψ (G.FX G.s (by omega)) (G.FX (G.s + 1) le_rfl) e
      ((G.T E.δ E.tame E.η).xiPen (box _ (G.ϖ ^ E.M)) (rep' G.s 0 rfl α) (cos' y)) :=
    fun α y => GlobalTheory.LocMod.CombAt.exists_isCombAt _ hc.std _ _ _
  have htop : ∀ (y : Ch' (G.s + 1)), ∃ e, (ofSplit G.q).IsCombAt c.ψ (G.FX (G.s + 1) le_rfl) G.FM e
      ((G.T E.δ E.tame E.η).xiTop (box _ (G.ϖ ^ E.M)) G.ψk G.ν (-1) (cos' y)) :=
    fun y => GlobalTheory.LocMod.CombAt.exists_isCombAt _ hc.std _ _ _
  choose dPen hdPen using hpen
  choose dTop hdTop using htop
  let dL' : ∀ j, Ch' j → Ch' (j + 1) → WO (c.X j) (c.X (j + 1)) →₀ ℂ := fun j =>
    if h : j + 1 ≤ G.s then fun α γ => E.dL j (cast (eE j (by omega) (by omega)) α) (cast (eE (j + 1) (by omega) (by omega)) γ)
    else if h' : j = G.s then (by subst h'; exact dPen)
    else if h'' : j = G.s + 1 then (by subst h''; exact fun y _ => dTop y)
    else fun _ _ => 0
  let wt' : ∀ j, Ch' j → ℂ := fun j =>
    if h : j = G.s + 1 then (by subst h; exact fun y => (E.idx (G.s + 1) : ℂ) *
      (Nat.card {yb | SameOrb ((G.T E.δ E.tame E.η).lev (G.s + 1) 0 rfl).J (box _ (G.ϖ ^ E.M)) (cos' y) yb} : ℂ))
    else if h' : j ≤ G.s then fun α => E.wt j (cast (eE j (by omega) (by omega)) α)
    else fun _ => (E.idx (G.s + 1 + 1) : ℂ)
  let εL' : ∀ j, Ch' j → GA D (c.V j) →₀ ℂ := fun j =>
    if h : j ≤ G.s then fun α => E.εL j (cast (eE j (by omega) (by omega)) α) else fun _ => 0
  let E' : QExt G χ :=
    { δ := E.δ, tame := E.tame, η := E.η, unr := E.unr, mu_comp := E.mu_comp, A := E.A, reps := E.reps, Ch := Ch', fC := fC, rep := rep'
      rep_bij := fun j d h => (E.rep_bij j d h).comp
        ((Equiv.cast (eE j (by omega) (by omega))).bijective.bijOn_univ)
      M := E.M, adapt := E.adapt, cos := cos'
      cos_inj := fun y y' h => (Equiv.cast eC).injective (hinj _ _ h)
      cos_all := fun z hz => by
        obtain ⟨y, hy⟩ := hall z hz
        exact ⟨cast eC.symm y, by simpa [cos'] using hy⟩
      one := (Fintype.card_congr (Equiv.cast (eE (G.s + 1 + 1) le_rfl (by omega)))).trans E.one
      eL := E.eL, eLT := E.eLT, eL_at := E.eL_at, eLT_at := E.eLT_at, dL := dL'
      dL_mid := fun j d H α γ => by
        have := E.dL_mid j d H (cast (eE j (by omega) (by omega)) α) (cast (eE (j + 1) (by omega) (by omega)) γ)
        have e : dL' j α γ = E.dL j (cast (eE j (by omega) (by omega)) α) (cast (eE (j + 1) (by omega) (by omega)) γ) := by
          simp only [dL']; rw [dif_pos (show j + 1 ≤ G.s by omega)]
        rw [e]; exact this
      dL_pen := fun α y => by
        have e : dL' G.s α y = dPen α y := by
          simp only [dL']; rw [dif_neg (by omega), dif_pos trivial]
        rw [e]; exact hdPen α y
      dL_top := fun y u => by
        have e : dL' (G.s + 1) y u = dTop y := by
          simp only [dL']; rw [dif_neg (by omega), dif_neg (by omega), dif_pos trivial]
        rw [e]; exact hdTop y
      εL := εL'
      εL_at := fun j ρ hρ d h α => by
        obtain ⟨e, h1, h2⟩ := E.εL_at j ρ hρ d h (cast (eE j (by omega) (by omega)) α)
        refine ⟨e, h1, ?_⟩
        rw [← h2]; simp only [εL']; rw [dif_pos (show j ≤ G.s by omega)]
      εL_zero := fun α => by
        simp only [εL']; rw [dif_pos (Nat.zero_le _)]; exact E.εL_zero _
      idx := E.idx, idx_mid := E.idx_mid, idx_top := E.idx_top, m := E.m, haar := E.haar, wt := wt'
      wt_mid := fun j d h α => by
        rw [← E.wt_mid j d h (cast (eE j (by omega) (by omega)) α)]
        simp only [wt']; rw [dif_neg (show j ≠ G.s + 1 by omega), dif_pos (show j ≤ G.s by omega)]
      wt_pen := fun y => by simp only [wt']; rw [dif_pos trivial]
      wt_top := fun u => by simp only [wt']; rw [dif_neg (by omega), dif_neg (by omega)] }
  refine ⟨E', rfl, rfl, rfl, rfl, ⟨Equiv.cast eC.symm, fun y => ?_⟩, fun j hj => ⟨(Equiv.cast (eU j hj)).unique⟩⟩
  simp [E', cos']

end GlobalTheory.QTw.CosExt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FirstTermExistenceOfUniversal
section
noncomputable section

open scoped Matrix NNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RegSch.FirstTermCompare

variable {D : D7}

def trivDec (T : HSp D) : HypDec T T 0 where
  e := 0
  e' := 0
  i₀ := 1
  ee := Subsingleton.elim _ _
  e'e' := Subsingleton.elim _ _
  e'e := Subsingleton.elim _ _
  iso := by rw [Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  i₀e := Matrix.mul_zero _
  i₀e' := Matrix.mul_zero _
  rank_add := rfl

theorem hasIw_of_good {T T₀ : HSp D} {r : ℕ} (d : HypDec T T₀ r) {l : Lvl T} (hl : l.Good) :
    HasIw d l.K ∧ IsCompact (l.K : Set (GA D T)) := by
  have h := GlobalTheory.T.goodMajorantLevel_conj_unitaryAdelicMaximalCompact D T T₀ r d l.c hl.2.2
    (GlobalTheory.T.adelic_iwasawa_decomposition_wittIsotropicStabilizer D T T₀ r d l.c GlobalTheory.Core.Rk.IP.Model.isSplit_two hl.2.2) l hl
  exact ⟨h.1, h.2.1⟩

end GlobalTheory.RegSch.FirstTermCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FourierBesselThetaCharIntegrandLaws
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf GlobalTheory.Unf.FB

noncomputable section

namespace GlobalTheory.Unf.FB.ThLaws

variable {D : D7}

theorem heisO_zero_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (p : WO S T) (f : WO S T → ℂ) :
    heisO ψ S T p f 0 = f p := by
  rw [heisO, GlobalTheory.MixModel.symplOH_zero_left, AddChar.map_zero_eq_one, one_mul, zero_add]

theorem jacS_zero_apply (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (x : Mx D T.rank ρ) (n : GA D S) (f : WO S₀ T → ℂ) :
    jacS ψ d T x n f 0 = ψ (cenS d T x n) * f (ptS d T x n) := by
  rw [jacS, Pi.smul_apply, smul_eq_mul, heisO_zero_apply]

theorem jacS_nC (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D)
    (x : Mx D T.rank ρ) (c : skewA D ρ) (f : WO S₀ T → ℂ) : jacS ψ d T x (d.nC c) f = ψ (d.qS T c x) • f := by
  have h := ptS_nB_mul_nC d T x 0 c
  rw [d.nB_zero, one_mul, Matrix.mul_zero] at h
  rw [jacS, h, cenS_nC, heisO_zero]

theorem continuous_psiE {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) : Continuous (psiE ψ) := by
  have ht : Continuous (Algebra.trace (AF D.host.F) (AE D)) := IsModuleTopology.continuous_of_linearMap _
  exact hψ.comp ht

theorem continuous_upSum {X : Type} [TopologicalSpace X] {ρ : ℕ} {T : X → Mx D ρ ρ} (hT : Continuous T) :
    Continuous fun t => upSum (T t) := by
  unfold upSum
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  by_cases h : j.1 = i.1 + 1
  · simp only [h, if_true]; exact (continuous_apply j).comp ((continuous_apply i).comp hT)
  · simp only [h, if_false]; exact continuous_const

theorem continuous_psiFlag {ψ : AddChar (AF D.host.F) ℂ} (hψ : Continuous ψ) {S S₀ : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) : Continuous (psiFlag ψ d) := by
  unfold psiFlag blockX
  exact (continuous_psiE hψ).comp
    (continuous_upSum (continuous_const.matrix_mul ((GlobalTheory.MixModel.continuous_mt S).matrix_mul continuous_const)))

theorem continuous_ptS {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ) :
    Continuous (ptS d T x) := by
  unfold ptS
  exact (continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_mt S)).matrix_mul continuous_const

theorem continuous_cenS {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x : Mx D T.rank ρ) :
    Continuous (cenS d T x) := by
  unfold cenS
  exact GlobalTheory.OrientedHeis.continuous_symplOH continuous_const
    (continuous_const.matrix_mul (GlobalTheory.MixModel.continuous_mt S))

theorem exists_bound_quasi {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {S L : HSp D}
    {y : WO S L → ℂ} (hy : Quasi ψ S L y) : ∃ M : ℝ, ∀ w, ‖y w‖ ≤ M := by
  obtain ⟨-, -, -, -, -, K, hK, hKc⟩ := GlobalTheory.MixModel.lattice_Mx D L.rank S.rank
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hy.2.continuousOn
  refine ⟨C, fun w => ?_⟩
  obtain ⟨γ, ⟨γ0, rfl⟩, hγ⟩ := hKc w
  have h2 : ‖y w‖ = ‖y (ratW L S γ0 + w)‖ := by rw [hy.1 γ0 w, norm_mul, hψ.2.1, one_mul]
  rw [h2]
  exact hC _ hγ

theorem zl_rat {σ : ℕ} (B : BesLev D σ) :
    ∃ z0 : Matrix (Fin B.L.rank) (Fin (σ + 1)) D.host.E, zl B = rat z0 := by
  refine ⟨Matrix.vecMulVec B.ζ (fun i : Fin (σ + 1) => if i.1 + 1 = σ + 1 then (1 : D.host.E) else 0), ?_⟩
  funext i j
  simp only [zl, zEll, rat, Matrix.map_apply, Matrix.vecMulVec_apply, ell, map_mul, ratV]
  congr 1
  split_ifs <;> simp

theorem ptS_rat {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (T : HSp D) (x0 : Matrix (Fin T.rank) (Fin ρ) D.host.E)
    {γ : GA D S} (hγ : γ ∈ GQ S) : ∃ g0, ptS d T (rat x0) γ = ratW T S₀ g0 := by
  obtain ⟨g, hg⟩ := (GlobalTheory.MixModel.mem_GQ_iff S γ).1 hγ
  refine ⟨x0 * d.qX * g * d.i₀, ?_⟩
  rw [ratW_eq, ptS, HypDec.extX_apply, ← hg]
  simp only [rat_mul]
  rfl

theorem psi_cenS_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {S S₀ : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) (T : HSp D) (x0 : Matrix (Fin T.rank) (Fin ρ) D.host.E) {γ : GA D S} (hγ : γ ∈ GQ S) :
    ψ (cenS d T (rat x0) γ) = 1 := by
  obtain ⟨g, hg⟩ := (GlobalTheory.MixModel.mem_GQ_iff S γ).1 hγ
  have e : cenS d T (rat x0) γ = symplOH S T ((x0 * d.qX).map (incA D)) ((x0 * d.qX * g).map (incA D)) := by
    rw [cenS, HypDec.extX_apply, ← hg]
    change _ = symplOH S T (rat (x0 * d.qX)) (rat (x0 * d.qX * g))
    simp only [rat_mul]
    rfl
  rw [e]
  exact GlobalTheory.AnisoMean.psi_rat hψ S T _ _

theorem upSum_rat {ρ : ℕ} (M : Matrix (Fin ρ) (Fin ρ) D.host.E) :
    upSum (rat M : Mx D ρ ρ) = incA D (∑ i, ∑ j, if j.1 = i.1 + 1 then M i j else 0) := by
  simp only [upSum, map_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp [rat]

theorem psiE_incA {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) (t : D.host.E) : psiE ψ (incA D t) = 1 := by
  rw [psiE, show Algebra.trace (AF D.host.F) (AE D) (incA D t) =
    algebraMap D.host.F (AF D.host.F) (Algebra.trace D.host.F D.host.E t) from GlobalTheory.AnisoMean.trace_one_tmul (AF D.host.F) t]
  exact hψ.2.2.1 _

theorem psiFlag_rat {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsCharAF D.host.F ψ) {S S₀ : HSp D} {ρ : ℕ}
    (d : HypDec S S₀ ρ) {γ : GA D S} (hγ : γ ∈ GQ S) : psiFlag ψ d γ = 1 := by
  obtain ⟨g, hg⟩ := (GlobalTheory.MixModel.mem_GQ_iff S γ).1 hγ
  have e : blockX d γ = rat (d.qX * (g * d.e)) := by
    rw [blockX, ← hg]
    simp only [rat_mul]
    rfl
  rw [psiFlag, e, upSum_rat, psiE_incA hψ]

theorem psiFlag_nC (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (c : skewA D ρ) :
    psiFlag ψ d (d.nC c) = 1 := by
  rw [psiFlag, blockX_of_fix d (d.nC_jX c), upSum_one, psiE_zero]

theorem psiFlag_nB (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (b : Mx D ρ S₀.rank) :
    psiFlag ψ d (d.nB b) = 1 := by
  rw [psiFlag, blockX_of_fix d (d.nB_jX b), upSum_one, psiE_zero]

theorem psiFlag_levi (ψ : AddChar (AF D.host.F) ℂ) {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (u : GL (Fin ρ) (AE D)) :
    psiFlag ψ d (d.levi u) = psiUni ψ u := by
  rw [psiFlag_eq, psiBes_levi]

theorem th_laws : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (y : WO J.W₀ B.L → ℂ), Quasi ψ J.W₀ B.L y → Continuous (th J ψ B y) ∧ (∃ M : ℝ, (∀ w, ‖y w‖ ≤ M) ∧ ∀ n, ‖th J ψ B y n‖ ≤ M) ∧ (∀ γ ∈ flagN J.d, γ ∈ GQ J.W → ∀ n ∈ flagN J.d, th J ψ B y (γ * n) = th J ψ B y n) ∧ (∀ c, ∀ n ∈ flagN J.d, th J ψ B y (J.d.nC c * n) = star (ψ (J.d.qS B.L c (zl B))) * th J ψ B y n) ∧ (∀ n ∈ flagN J.d, ∀ u ∈ UX D (σ + 1), th J ψ B y (n * J.d.levi u) = th J ψ B y n * star (psiUni ψ u)) ∧ ∀ b, ∀ u ∈ UX D (σ + 1), th J ψ B y (J.d.nB b * J.d.levi u) = star (psiUni ψ u) * star (y (zl B ⬝ b)) := by
  intro D ψ hψs σ J B y hy
  have hψ : IsCharAF D.host.F ψ := hψs.1
  have hx : ∀ u ∈ UX D (σ + 1), zl B ⬝ u.1 = zl B := fun u hu => zEll_mul B.L B.ζ hu
  obtain ⟨hcen, hmul, hlevi, -⟩ := GlobalTheory.JacHom.jacS_hom D ψ J.W J.W₀ B.L (σ + 1) J.d (zl B) hx
  obtain ⟨M, hM⟩ := exists_bound_quasi hψ hy
  have hval : ∀ n, th J ψ B y n =
      star (ψ (cenS J.d B.L (zl B) n) * y (ptS J.d B.L (zl B) n)) * star (psiFlag ψ J.d n) := fun n => by
    rw [th, jacS_zero_apply]
  have hnorm : ∀ a, ‖ψ a‖ = 1 := hψ.2.1
  have hflag1 : ∀ n, ‖psiFlag ψ J.d n‖ = 1 := fun n => hnorm _
  refine ⟨?_, ⟨M, hM, fun n => ?_⟩, ?_, ?_, ?_, ?_⟩
  · have e : th J ψ B y = fun n =>
        star (ψ (cenS J.d B.L (zl B) n) * y (ptS J.d B.L (zl B) n)) * star (psiFlag ψ J.d n) := funext hval
    rw [e]
    exact (((hψ.1.comp (continuous_cenS _ _ _)).mul (hy.2.comp (continuous_ptS _ _ _))).star).mul
      (continuous_psiFlag hψ.1 _).star
  · rw [hval, norm_mul, norm_star, norm_star, norm_mul, hnorm, hflag1, one_mul, mul_one]
    exact hM _
  · intro γ hγN hγQ n hn
    obtain ⟨z0, hz0⟩ := zl_rat B
    have hp := hmul γ hγN n hn
    obtain ⟨g0, hg0⟩ := ptS_rat J.d B.L z0 hγQ
    rw [← hz0] at hg0
    have hc : ψ (cenS J.d B.L (zl B) γ) = 1 := by rw [hz0]; exact psi_cenS_rat hψ J.d B.L z0 hγQ
    rw [hval, hval, hp.1, hp.2.1, psiFlag_mul J.d ψ hγN hn, psiFlag_rat hψ J.d hγQ, one_mul, hg0, hy.1 g0]
    congr 2
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_neg_cancel_right, AddChar.map_add_eq_mul, hc, one_mul]
  · intro c n hn
    have hc : J.d.nC c ∈ flagN J.d := J.d.nC_mem_NFlag c
    rw [th, (hmul _ hc n hn).2.2, th, psiFlag_mul J.d ψ hc hn, psiFlag_nC, jacS_nC]
    simp only [Pi.smul_apply, smul_eq_mul, star_mul', one_mul, star_one]
    ring
  · intro n hn u hu
    have hl : J.d.levi u ∈ flagN J.d := J.d.levi_mem_NFlag hu
    rw [th, hlevi n hn u hu, psiFlag_mul J.d ψ hn hl, psiFlag_levi, th, star_mul', mul_assoc]
  · intro b u hu
    have hb : J.d.nB b ∈ flagN J.d := J.d.nB_mem_NFlag b
    have hl : J.d.levi u ∈ flagN J.d := J.d.levi_mem_NFlag hu
    have hp : ptS J.d B.L (zl B) (J.d.nB b) = zl B ⬝ b := by
      have := ptS_nB_mul_nC J.d B.L (zl B) b 0
      rwa [J.d.nC_zero, mul_one] at this
    have hc : cenS J.d B.L (zl B) (J.d.nB b) = 0 := by
      have := hcen b 0
      rw [J.d.nC_zero, mul_one] at this
      rw [this, HypDec.qS]
      simp [GlobalTheory.MixModel.symplOH_zero_right]
    rw [th, hlevi _ hb u hu, psiFlag_mul J.d ψ hb hl, jacS_zero_apply, hp, hc, AddChar.map_zero_eq_one, one_mul,
      psiFlag_nB, one_mul, psiFlag_levi]
    ring

end GlobalTheory.Unf.FB.ThLaws

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.GramPoincareHilbertSchmidtDeviationLeSplit
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Rk

theorem hsNormSq_add_le_three_halves {Wp Wq : Type*} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] (A B : Wq →L[ℂ] Wp) :
    hsNormSq (A + B) ≤ 3 / 2 * hsNormSq A + 3 * hsNormSq B := by
  rw [hsNormSq_eq, hsNormSq_eq, hsNormSq_eq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h := norm_add_le (A (stdOrthonormalBasis ℂ Wq i)) (B (stdOrthonormalBasis ℂ Wq i))
  have h0 := norm_nonneg (A (stdOrthonormalBasis ℂ Wq i) + B (stdOrthonormalBasis ℂ Wq i))
  rw [ContinuousLinearMap.add_apply]
  nlinarith [sq_nonneg (‖A (stdOrthonormalBasis ℂ Wq i)‖ - 2 * ‖B (stdOrthonormalBasis ℂ Wq i)‖)]

theorem hsDev_le_split_three_halves : ∀ (D : D7) (u : D.what₂.Word), GlobalTheory.Core.Rk.hsDev D u ≤
    3 / 2 * hsNormSq (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) + 3 * hsNormSq (AdmissibleBoundsFromSource.Kpp D u u) := by
  intro D u
  have e : Kmat D.s u u - ContinuousLinearMap.id ℂ (D.s.Cu u) =
      (Kmat D.s u u - AdmissibleBoundsFromSource.Kpp D u u - ContinuousLinearMap.id ℂ (D.s.Cu u)) + AdmissibleBoundsFromSource.Kpp D u u := by abel
  unfold GlobalTheory.Core.Rk.hsDev
  rw [e]
  exact hsNormSq_add_le_three_halves _ _

end GlobalTheory.Core.Rk
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HaarMeasureDisintegrationBesselGroupStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.haarMeasure_disintegration_besselGroup : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (u : D.what₂.Word) (ψ : AddChar (AF D.host.F) ℂ) (A : HSp D) (B : SBes X h u ψ A), ∃ c : ℝ, 0 < c ∧ ∀ G : X.B.I.GA → ENNReal, Measurable G → (∀ x, G x ≠ 0 → ∃ s ∈ SfinU X u, ∃ k ∈ X.K2, x.2 = s * X.xu u * k) → ∫⁻ x, G x ∂(X.B.I.muA X.B.μf) = ENNReal.ofReal c * ∫⁻ y, ∫⁻ s, ∫⁻ k in X.K2, G (iotaX X h s.1 * (y, X.xu u) * (1, k)) ∂X.B.μf ∂B.lev.μR ∂(X.nuQ u) := by
  first | exact @GlobalTheory.Core.Mi.Disint.disint | exact GlobalTheory.Core.Mi.Disint.disint | (intros; apply GlobalTheory.Core.Mi.Disint.disint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InertPlaceLocalTraceCharacterConductorIntegersStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep
open GlobalTheory.FinZeta (Gv embV Kv VacFin IsLocKer KerU)
open GlobalTheory.SphTheta (IsStd CayleyRule intMat liftPar)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke IsCommensurated Tj SatU ordL Ov)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.InertFrameLoc

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertPlace_localTraceCharacter_conductor_integers : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (v : HeightOneSpectrum (𝓞 D.host.F)) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : IsInertAt D.host.F D.host.E v w) (h : w.under (𝓞 D.host.F) = v) (c : w.adicCompletion D.host.E →+* w.adicCompletion D.host.E) (ϖ : w.adicCompletion D.host.E) (k : w.adicCompletion D.host.E), IsStdChar D ψ (-1) → IsConjAt D.sp.cm.sig h c → IsUnramInv ϖ c (qV D.host.F v) → GlobalTheory.InertLoc.IsGen D w k → ∀ z, (∀ u ∈ Formalism.UG.intL (w.adicCompletion D.host.E), thW ψ hw h (k * c k) (z * u) = 1) ↔ z ∈ Formalism.UG.intL (w.adicCompletion D.host.E) := by
  first | exact @GlobalTheory.InertFrameLoc.thW_cond | exact GlobalTheory.InertFrameLoc.thW_cond | (intros; apply GlobalTheory.InertFrameLoc.thW_cond <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LinearModelSplitPlaceTwistSchwartzBruhatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linearModel_splitPlace_twist_schwartzBruhat : ∀ D : D7, ForStepQ D fun c w k s s' p => ∀ PP ∈ w.Q, ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : SplitProj D v), IsProjAt φ PP → ∀ ι ι', IsChart s k φ ι → IsChart s' (k + 1) φ ι' → ∀ μS μT ξl : (Fv D.host.F v)ˣ →* ℂˣ, (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μS y = Circle.toUnits (c.chS (k + 1) x)) → (∀ (x : (AE D)ˣ) (y : (Fv D.host.F v)ˣ), (∃ e, IsIdemOf φ e ∧ (1 - e) * (x : AE D) = 1 - e ∧ rdA φ (x : AE D) = y) → μT y = Circle.toUnits (c.chT (k + 1) x)) → LiftsChar φ PP ξl (w.ξ PP) → ∀ P m X, IsCovolOne (ratL s'.V s.V) m X → ∃ (hW : ∀ g h, ∀ u ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v)), GlobalTheory.ParHecke.omTwo μS μT g h u ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v))) (hΦ : datum ξl⁻¹ ∈ GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v))) (T : GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v)) →ₗ[ℂ] (WO s.V s'.V → ℂ)), T ⟨_, hΦ⟩ = p.pt P ∧ (∀ u, IsThetaFunO c.ψ s.V s'.V (T u)) ∧ (∀ g h (u : GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v))), p.ω (ι g, ι' h) (T u) = T ⟨_, hW g h u u.2⟩) ∧ ∀ [MeasurableSpace (Fv D.host.F v)] [BorelSpace (Fv D.host.F v)] (ν : Measure (Fv D.host.F v)), GlobalTheory.SplitWeil.IsUnitVol ν → ∀ x : GA D s.V, gAt s.V (.inl v) x = 1 → ∃ C : ℂ, ∀ u u' : GlobalTheory.SplitWeil.SB (Matrix (Fin D.R.r ⊕ Blocks (k + 1) D.R.t) (Fin D.R.r ⊕ Blocks k D.R.t) (Fv D.host.F v)), ∫ z in X, p.ω (x, 1) (T u) z * conj (T u' z) ∂m = C * GlobalTheory.SplitWeil.ip ν u.1 u'.1 := by
  first | exact @GlobalTheory.TwistLinModel.linearModel_at_twist | exact GlobalTheory.TwistLinModel.linearModel_at_twist | (intros; apply GlobalTheory.TwistLinModel.linearModel_at_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LscSeminormThetaFunctionsLevelLeSobolevStatement
section
open scoped ComplexConjugate Matrix NNReal ENNReal TensorProduct Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.Eis GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.RegSch
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (RealMat IsFockVec)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (swSec sZero IsKFinVec delta ThetaClause)
open GlobalTheory.Core.Rk.SW (sch)
open GlobalTheory.Mem.AutSpace (SmFun)
open GlobalTheory.Size (sobO thetaLevel)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ThetaDens

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lsc_seminorm_thetaFunctionsLevel_le_sobolev : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ N : (WO S T → ℂ) → ℝ≥0∞, (∀ f ∈ thetaLevel ψ S T U, ∀ g ∈ thetaLevel ψ S T U, N (f + g) ≤ N f + N g) → (∀ (c : ℂ), ∀ f ∈ thetaLevel ψ S T U, N (c • f) = ‖c‖ₑ * N f) → (∀ f ∈ thetaLevel ψ S T U, N f ≠ ⊤) → (∀ (u : ℕ → WO S T → ℂ), (∀ j, u j ∈ thetaLevel ψ S T U) → ∀ f ∈ thetaLevel ψ S T U, (∀ d, Filter.Tendsto (fun j => sobO ψ θ μ 𝓕 d (u j - f)) Filter.atTop (nhds 0)) → N f ≤ Filter.liminf (fun j => N (u j)) Filter.atTop) → ∃ (d : ℕ) (C : ℝ≥0), ∀ f ∈ thetaLevel ψ S T U, N f ≤ C * sobO ψ θ μ 𝓕 d f := by
  first | exact @GlobalTheory.SobBaire.le_mul_sobO | exact GlobalTheory.SobBaire.le_mul_sobO | (intros; apply GlobalTheory.SobBaire.le_mul_sobO <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedCoordinateOriginUnipotentRadicalInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedCoordinate_origin_unipotentRadical_invariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ (μ : Measure (Mx D T.rank ρ)) (𝓕 : Set (Mx D T.rank ρ)), IsCovolOne (ratMx D T.rank ρ) μ 𝓕 → ∀ f, IsThetaFunO ψ S T f → (∀ b, d.mixS T ψ μ 𝓕 (om (d.nB b, 1) f) 0 = d.mixS T ψ μ 𝓕 (f) 0) ∧ ∀ c, d.mixS T ψ μ 𝓕 (om (d.nC c, 1) f) 0 = d.mixS T ψ μ 𝓕 (f) 0 := by
  first | exact @GlobalTheory.UnipZero.mixS_zero_unip | exact GlobalTheory.UnipZero.mixS_zero_unip | (intros; apply GlobalTheory.UnipZero.mixS_zero_unip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.NonemptyConcreteRowDataOfFinitenessBundle
section
open scoped Classical
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.PackageTie2 GlobalTheory.Core.Diag GlobalTheory.Core.Deg

namespace GlobalTheory.Core.Diag

theorem concK_of_finX : Formalism.L2.SG.Pf.WuDecayOfGap → ∀ (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT : ℝ) (S : Formalism.L2.SG.SpectralTiesReal.STies D), 29 ≤ C' → 29 ≤ Cl → FinX S.Y → Formalism.L2.SG.Pf.LocCP.LocTied D → TFrameAt D → StandingHypotheses D large₂ C' Cl Cg cb Cu cT CT → Nonempty (Formalism.L2.SG.ThmSOwn.ConcK D) := by
  intro hWu D large₂ C' Cl Cg cb Cu cT CT S hC' hCl hFX hL hTF hH
  have hG : Formalism.L2.SG.ConcreteSettingExists.GapHyp D := Formalism.L2.SG.ThmSOwn.gap_hypothesis_of_hypotheses hH (by linarith) hC'
  have hK := Formalism.L2.SG.Closed.level_subgroup_properties S.X
  exact ⟨Formalism.L2.SG.ThmSOwn.concKOf S ⟨hFX, hK, fun u => Formalism.L2.SG.Pf.RegroupPf.neatKu_K2Level D S.X S.Y u hK,
    (hWu D hG S.X).1, (hWu D hG S.X).2, hL, hTF⟩⟩

end GlobalTheory.Core.Diag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawKernelChainLevelPrimeOperatorToStepZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.FinPl GlobalTheory.SeeSaw ValuativeRel IsLocalRing
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.seeSawKernelChain_levelPrimeOperator_to_step_zero : ∀ (D : D7) (c : Comm D) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type) (o : TDat c k ι) (t : Tup c) (ε : ℕ → ι → 𝓀[k]ˣ) (S₀ : (ι → 𝓀[k]ˣ) → t.Col 0 → t.Col 0), t.Is → t.KBack → t.TailRd → LiftS o t → ReadS o t ε S₀ → CommX o t ε S₀ := by
  first | exact @GlobalTheory.SeeSaw.commX_of_laws | exact GlobalTheory.SeeSaw.commX_of_laws | (intros; apply GlobalTheory.SeeSaw.commX_of_laws <;> assumption)
end

