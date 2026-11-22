import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0250
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0019
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0265
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0090
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0081
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0327
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOfBasis
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0317
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZetaSumGLComplex
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0248
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CombAtSingleZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacua
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0023
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0080
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0185
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0251
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedThetaChainLValueQuotientFactorizationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedThetaChain_LValue_quotientFactorization : ∀ D : D7, LFull D := by
  first | exact @GlobalTheory.ChainTw.lFull_holds | exact GlobalTheory.ChainTw.lFull_holds | (intros; apply GlobalTheory.ChainTw.lFull_holds <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedDoublingIntegralSplitPlaceAdelic
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

open Formalism.UG (IsUnifV qV)
open GlobalTheory.LFun (KGL IsSatVecGL eulerFac UnrAt LvTw)
open GlobalTheory.LFun (locChar IsSplitChart IsInertChart KGL UnrAt toCompl locMat IsFrameAt IsSatVecU eulerFac LvTw dv Fam)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.Doubling (ioH_mem_KFin)

namespace GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 2000000 in

theorem localZetaOn_split : GlobalTheory.Published.UnramifiedDoublingGL →
    ∀ D : D7, LocalZetaOn D fun v => Formalism.MainNotions.SchurIrreducible.IsSplit (E := D.host.E) v := by
  intro hP D A L hL χ b hχ hb v hv hU μ hμH hK s hs φ hφ par c hc
  classical
  have hcm := isCMExt_host D
  have h2 : Module.finrank D.host.F D.host.E = 2 := hcm.2.2.1
  have hJ : IsHermND D.sp.cm.sig A.gram := GlobalTheory.Doubling.isHermND_gram A
  have hd : IsSelfDualAt D.sp.cm.sig A.gram L v :=
    (SelfDual.forall_isSelfDualAt_iff (σ := D.sp.cm.sig) (GlobalTheory.Doubling.isHermND_gram A).2 hL.1).2
      (fun y => hL.2 y) v
  obtain ⟨w, h⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hc' := hc
  obtain ⟨⟨C, hC⟩, V, _, _, ρ, x, ℓ, hpar, -, hcx⟩ := hc
  obtain ⟨w', hne, hall, hN, hN', -⟩ := GlobalTheory.LFun.SplitChart.exists_conj_place hcm h hv
  have h' : w'.under (𝓞 D.host.F) = v := (hall w').2 (Or.inr rfl)
  obtain ⟨e, he, hsat⟩ : ∃ e, IsSplitChart D.sp.cm.sig A.gram L h e ∧
      IsSatVecGL w (ρ.comp e.symm.toMonoidHom) x (par w) := by
    rcases hpar w h with ⟨-, e, he, hsat⟩ | ⟨hw, -⟩
    · exact ⟨e, he, hsat⟩
    · exact absurd hv (GlobalTheory.LFun.not_isSplit_of_isInertAt hw)
  have hB' : par w' = (par w).map (·⁻¹) :=
    GlobalTheory.LFun.ConjPlace.eq_map_inv_of_isParamVec hcm hJ hd hne (hpar w h) (hpar w' h')
  have hm : GlobalTheory.LFun.val χ w * GlobalTheory.LFun.val χ w' = 1 :=
    GlobalTheory.LFun.ResEta.val_mul_val h2 ((GlobalTheory.LFun.resEta_iff χ _).1 hb) hne h h' (hU w h) (hU w' h')
  have hfix : ∀ k ∈ stabLoc D.sp.cm.sig A.gram L v, ρ k x = x :=
    GlobalTheory.LGrp.mem_fixed.1 (hpar w h).mem_fixed
  have hz1 : ‖(((GlobalTheory.LFun.val χ w)⁻¹ : ℂˣ) : ℂ)‖ = 1 := by
    rw [Units.val_inv_eq_inv_val, norm_inv, GlobalTheory.LFun.norm_val, inv_one]
  have hker := GlobalTheory.T.sphericalSection_graph_splitPlace D A L hL χ b hb v hv hU s φ hφ w h e he
  have hbd : ℓ x ≠ 0 → ∀ β ∈ par w, ‖(β : ℂ)‖ ≤ (qV D.host.E w : ℝ) ^ ((A.rank : ℝ) / 2) ∧
      ‖((β⁻¹ : ℂˣ) : ℂ)‖ ≤ (qV D.host.E w : ℝ) ^ ((A.rank : ℝ) / 2) := by
    intro h0 β hβ
    have hc1 : c 1 ≠ 0 := by rw [hcx, map_one, Module.End.one_apply]; exact h0
    have Hb := GlobalTheory.T.sphericalParameterBound_split_place D A L hL v hv par c hc' hc1
    refine ⟨(Hb w h).2 β hβ, ?_⟩
    have H2 := (Hb w' h').2 β⁻¹ (hB' ▸ Multiset.mem_map_of_mem _ hβ)
    have e2 : ((Ideal.absNorm w'.asIdeal : ℕ) : ℝ) = (qV D.host.E w : ℝ) := by
      rw [hN', ← hN]; rfl
    rwa [e2] at H2
  have hsum := GlobalTheory.ZetaGL.zeta_sum_GL_complex hP D.host.E w A.rank s (by have : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _; linarith)
    (GlobalTheory.LFun.val χ w)⁻¹ (fun g => φ (ioAt A v (e.symm g))) hz1 hker V (ρ.comp e.symm.toMonoidHom) x (par w) hsat ℓ
    ⟨C, fun g => by have := hC (e.symm g); rwa [hcx] at this⟩ hbd
  have hval := GlobalTheory.LocValSplit.LvTw_div_dv_split D.host.F D.host.E par (GlobalTheory.LFun.val χ) v w w' A.rank b s hv
    (GlobalTheory.LFun.isUnram_of_isSplit h2 hv) hne hall hN hN' hB' hm
  have hinv : ∀ y, ∀ k ∈ stabLoc D.sp.cm.sig A.gram L v,
      φ (ioAt A v (y * k)) * c (y * k) = φ (ioAt A v y) * c y := by
    intro y k hk
    have e1 : ioAt A v (y * k) = ioAt A v y * ioAt A v k := by
      unfold ioAt
      rw [← map_mul]
      simp
    have hk' : ioAt A v k ∈ KFin D.sp.cm.sig (dblSp A).gram L v :=
      (ioH_mem_KFin (gram_hdbl A)).2 ⟨hk, one_mem _⟩
    rw [e1, hφ.2.1 _ hk', hcx, hcx, map_mul, Module.End.mul_apply, hfix k hk]
  have hsum' := GlobalTheory.T.hasSum_quotient_of_hasSum_mulEquiv_quotient _ _ e (stabLoc D.sp.cm.sig A.gram L v) (KGL w A.rank) he.2
    (fun y => φ (ioAt A v y) * c y) hinv _ (by
      refine hsum.congr_fun ?_
      intro a
      simp [hcx])
  haveI : Submodule.IsLattice D.host.E L := hL.1
  obtain ⟨hI, hE⟩ := GlobalTheory.T.integral_right_invariant_eq_sum_open_subgroup_cosets (Gv A v) μ (stabLoc D.sp.cm.sig A.gram L v)
    (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ v) hK (fun y => φ (ioAt A v y) * c y) _ hinv hsum'
  refine ⟨hI, ?_⟩
  rw [hE, hval, hcx, map_one, Module.End.one_apply]

end GlobalTheory.Core.Rk.IP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VacuumRestrictionRankZero
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil GlobalTheory.SeeSaw ValuativeRel IsLocalRing GlobalTheory.ChainOnto
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.RankZeroVac

variable {D : D7}

theorem incA_tmul' (e : D.host.E) : incA D e = (1 : AF D.host.F) ⊗ₜ[D.host.F] e := rfl

section
variable {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (T : HSp D)

theorem continuous_wittExtendByZero : Continuous (d.ext0 T) := continuous_id.matrix_mul continuous_const

theorem heisenbergOperator_wittExtendByZero (ψ : AddChar (AF D.host.F) ℂ) (u : WO W₀ T) (f : WO W T → ℂ) :
    heisO ψ W₀ T u (fun w => f (d.ext0 T w)) = fun w => heisO ψ W T (d.ext0 T u) f (d.ext0 T w) := by
  funext w
  simp only [heisO, map_add, d.wittDecomp_sympl_extAnisotropic_extAnisotropic]

theorem isThetaFunction_comp_wittExtendByZero {ψ : AddChar (AF D.host.F) ℂ} {f : WO W T → ℂ} (hf : IsThetaFunO ψ W T f) :
    IsThetaFunO ψ W₀ T (fun w => f (d.ext0 T w)) where
  quasi γ w := by
    have h := hf.quasi (γ * d.q0) (d.ext0 T w)
    have hr : ratW T W (γ * d.q0) = d.ext0 T (ratW T W₀ γ) := by
      rw [ratW_eq, ratW_eq, rat_mul, d.matrixExtendByZero_apply]; rfl
    rw [hr, d.wittDecomp_sympl_extAnisotropic_extAnisotropic] at h
    simp only [map_add]
    exact h
  level := by
    obtain ⟨U, hU, hfix⟩ := hf.level
    refine ⟨U.comap (d.ext0 T), hU.preimage (continuous_wittExtendByZero d T), fun u hu hinf => ?_⟩
    rw [heisenbergOperator_wittExtendByZero]
    have h0 : (d.ext0 T u).map (infPart D) = 0 := by
      rw [d.matrixExtendByZero_apply, Matrix.map_mul, hinf, Matrix.zero_mul]
    rw [hfix _ hu h0]
  cont := hf.cont.comp (continuous_wittExtendByZero d T)
  smooth k L hL hLf w := by
    have h := hf.smooth k ((d.ext0 T).comp L) ((continuous_wittExtendByZero d T).comp hL) (fun t => by
      show (d.ext0 T (L t)).map (finPart D) = 0
      rw [d.matrixExtendByZero_apply, Matrix.map_mul, hLf t, Matrix.zero_mul]) (d.ext0 T w)
    simpa only [AddMonoidHom.comp_apply, map_add] using h

theorem isHalf_wittHyperbolicExtendByZero_apply {e : AE D} {u : WO W₀ T} (h : IsHalf e u) : IsHalf e (d.ext0 T u) := by
  intro i j
  have hl : ∀ l, e * ((u : Matrix (Fin T.rank) (Fin W₀.rank) (AE D)) i l * d.p0 l j) =
      (u : Matrix (Fin T.rank) (Fin W₀.rank) (AE D)) i l * d.p0 l j := fun l => by rw [← mul_assoc, h i l]
  rw [d.matrixExtendByZero_apply, Matrix.mul_apply]
  show e * ∑ l, _ = _
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => hl l

end

end GlobalTheory.RankZeroVac

namespace GlobalTheory.RankZeroVac

variable {D : D7}

section
variable {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (T : HSp D)

theorem wittDecomposition_gram_projection_identity (s : Fin W₀.rank → D.host.E) (j : Fin W.rank) :
    ∑ l, (∑ k, star (s k) * W₀.gram k l) * d.q0 l j = ∑ m, star ((Matrix.mulVec d.i₀ s) m) * W.gram m j := by
  have h : Matrix.vecMul (Matrix.vecMul (star s) W₀.gram) d.q0 = Matrix.vecMul (star (Matrix.mulVec d.i₀ s)) W.gram := by
    rw [Matrix.vecMul_vecMul, HypDec.q0, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (gram_isUnit_det W₀),
      Matrix.one_mul, ← Matrix.vecMul_vecMul, Matrix.star_mulVec]
  have hj := congrFun h j
  simpa only [Matrix.vecMul, dotProduct, Pi.star_apply] using hj

end

end GlobalTheory.RankZeroVac

namespace GlobalTheory.RankZeroVac

variable {D : D7}

section
variable {W W₀ : HSp D} {ρ : ℕ} (d : HypDec W W₀ ρ) (T : HSp D)

end

end GlobalTheory.RankZeroVac
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorSourceRealPointCommuteHeisenbergCombStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_sourceRealPoint_commute_heisenbergComb : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ z ∈ GinfC S, ∀ c : WO S T →₀ ℂ, IsFinComb c → ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → om (z, 1) (comb ψ S T c g) = comb ψ S T c (om (z, 1) g) := by
  first | exact @GlobalTheory.SeeSaw.RealComm.om_comb | exact GlobalTheory.SeeSaw.RealComm.om_comb | (intros; apply GlobalTheory.SeeSaw.RealComm.om_comb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilOperatorThetaFunSupModerateGrowthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
open scoped ComplexOrder ENNReal NNReal ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilOperator_thetaFun_sup_moderate_growth : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : Om S T), IsWeilDatumO ψ S T χS χT om → ∀ f, IsThetaFunO ψ S T f → ∃ (C : ℝ) (A : ℕ), ∀ g h w, ‖om (g, h) f w‖ ≤ C * (height S g * height T h) ^ A := by
  first | exact @GlobalTheory.SupThetaGrowth.om_sup_growth | exact GlobalTheory.SupThetaGrowth.om_sup_growth | (intros; apply GlobalTheory.SupThetaGrowth.om_sup_growth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilRepSourceLineEqOppositeTargetLineStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_sourceLine_eq_opposite_targetLine : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (L L' S : HSp D) (τ : Matrix (Fin L.rank) (Fin L'.rank) D.host.E), L.rank = L'.rank → τᴴ ⬝ (L.gram ⬝ τ) = (((-1 : ℤ) : D.host.E) * (D.host.xi0 * star D.host.xi0)) • L'.gram → ∀ (χz χ χ' : ((AE D)ˣ →* Circle)) (om : Om L S) (om' : Om S L'), IsWeilDatumO ψ L S χz χ om → IsWeilDatumO ψ S L' χ' χz⁻¹ om' → ∀ f, IsThetaFunO ψ L S f → IsThetaFunO ψ S L' (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) ∧ ∀ h, om' (h, 1) (fun w => f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w))) = fun w => om (1, h) f (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.ofAdj L S ((rat τ : Mx D L.rank L'.rank) ⬝ w)) := by
  first | exact @GlobalTheory.ConjLine.weil_source_line_opposite | exact GlobalTheory.ConjLine.weil_source_line_opposite | (intros; apply GlobalTheory.ConjLine.weil_source_line_opposite <;> assumption)
end

