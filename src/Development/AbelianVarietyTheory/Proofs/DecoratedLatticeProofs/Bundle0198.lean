import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0181
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0174
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0031
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicTransportMeasureSecond
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0405
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0342
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.RegUnitary
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0014
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0125
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ContinuesConst
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0173
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0182
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0011
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0005
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0406
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0365
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0262
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.UnitaryPointsRankZeroSubsingleton
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0020
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjDoublingIsotropicUnipotentMemSiegelStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_doubling_isotropic_unipotent_mem_siegel : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → ∀ (r : ℕ) (K : Matrix (Fin V.rank) (Fin r) D.host.E), diagSnd γi * K = 0 → IsIsoFrame V (leviMat finSumFinEquiv γi * K) → ∀ n ∈ NI V (leviMat finSumFinEquiv γi * K), ∃ p : siegel V, γ * io V (n, 1) = p * γ ∧ aP V p = 1 := by
  first | exact @GlobalTheory.Core.Rk.Dich.conj_io_unip_siegel | exact GlobalTheory.Core.Rk.Dich.conj_io_unip_siegel | (intros; apply GlobalTheory.Core.Rk.Dich.conj_io_unip_siegel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjIntertwinerPointValueSobolevContinuous
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjRowCont

theorem reg_star {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (g : X.B.I.GA) (φ : L2X X) :
    X.B.R g (star φ) = star (X.B.R g φ) := by
  have := X.B.sf
  have := X.B.haar
  have := Formalism.MainNotions.LeviCoordinates.rr_muA_left X.B.I X.B.μf
  obtain ⟨-, hr, -⟩ := GlobalTheory.AdelicUnimod.adelic_unimodular X.B.I X.B.μf
  have hP : ∀ a : X.B.I.GA, Formalism.L2.SG.Pf.RPres (X.B.I.muA X.B.μf) a := fun a => ⟨measurable_mul_const a, hr a⟩
  obtain ⟨h1, h2⟩ := Formalism.L2.SG.Pf.rp_map (Formalism.MainNotions.LeviCoordinates.rr_FD_of X.B.I X.B.μf X.B.fund X.B.fund_spec) (hP g) (hP g⁻¹)
  have e1 := X.B.R_spec g (star φ)
  have e2 := X.B.R_spec g φ
  have e3 : ∀ᵐ x ∂(muX X), ((star φ : L2X X) : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * g)) =
      star ((φ : X.B.I.GA → ℂ) (X.B.I.rep X.B.fund (x * g))) := by
    refine ae_of_ae_map (p := fun y => ((star φ : L2X X) : X.B.I.GA → ℂ) y = star ((φ : X.B.I.GA → ℂ) y)) h1 ?_
    rw [h2]
    filter_upwards [Lp.coeFn_star φ] with y hy
    rw [hy]
    rfl
  apply Lp.ext
  filter_upwards [e1, e2, e3, Lp.coeFn_star (X.B.R g φ)] with x a1 a2 a3 a4
  rw [a1, a4, Pi.star_apply, a2]
  exact a3

theorem iotaX_rat_iff {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (g : GA D (D.sp.Y 0)) : g ∈ GQ (D.sp.Y 0) ↔ iotaX X h g ∈ X.B.I.GFset := by
  have k : ∀ {I I' : Formalism.MainNotions.S.AutInst} (e : I = I') (x : I.GA), x ∈ I.GFset ↔ castGA e x ∈ I'.GFset := by
    intro I I' e x
    subst e; rfl
  exact (Formalism.IndefR.RationalEmbedding.iota_rat D g).trans (k h.symm _)

theorem exists_conj_multilinear {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) {S : D.what₂.Tau → SPar}
    (M : DSModel (D.sp.Y 0) S) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)) (Φ : X.B.Hs →L[ℂ] L2X X) :
    ∃ Ψ : ContinuousMultilinearMap ℂ M.H (L2X X), ∀ y,
      Ψ y = star (Φ (X.B.tens (Equiv.piCongrLeft X.B.H X.pl.symm fun τ => c τ (y τ)))) := by
  obtain ⟨m, hm, -⟩ := GlobalTheory.exists_continuousMultilinearMap_of_inner_prod (H := X.B.H) X.B.tens
    X.B.tens_spec.1 X.B.tens_spec.2.2
  let C : (∀ τ, M.H τ) → ∀ v, X.B.H v := fun y => Equiv.piCongrLeft X.B.H X.pl.symm (fun τ => c τ (y τ))
  have hC : ∀ y τ, C y (X.pl.symm τ) = c τ (y τ) := fun y τ => Equiv.piCongrLeft_apply_apply _ _ _ _
  have hCu : ∀ y τ a, C (Function.update y τ a) = Function.update (C y) (X.pl.symm τ) (c τ a) := by
    intro y τ a
    rw [← GlobalTheory.ConjRowMult.piCongrLeft_update]
    refine congrArg (Equiv.piCongrLeft X.B.H X.pl.symm) (funext fun τ' => ?_)
    exact Function.apply_update (fun i (s : M.H i) => c i s) y τ a τ'
  have hCc : Continuous C := by
    refine continuous_pi fun v => ?_
    obtain ⟨τ, rfl⟩ := X.pl.symm.surjective v
    simp only [hC]
    exact (c τ).continuous.comp (continuous_apply τ)
  let Ψ₀ : MultilinearMap ℂ M.H (L2X X) := MultilinearMap.mk' (fun y => conjL (muX X) (Φ (m (C y))))
    (fun y τ a b => by rw [hCu, hCu, hCu, map_add, m.map_update_add, map_add, map_add])
    (fun y τ a b => by
      rw [hCu, hCu, LinearIsometryEquiv.map_smulₛₗ, m.map_update_smul, map_smul, LinearIsometryEquiv.map_smulₛₗ,
        starRingEnd_self_apply])
  refine ⟨⟨Ψ₀, (conjL (muX X)).continuous.comp (Φ.continuous.comp (m.cont.comp hCc))⟩, fun y => ?_⟩
  show star (Φ (m (C y))) = _
  rw [hm]

set_option maxHeartbeats 1000000 in

theorem conjMap_cont : GlobalTheory.Published.DiscreteSeriesClassification → ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D) (θ : InfFam D) (S : D.what₂.Tau → SPar) (M : DSModel (D.sp.Y 0) S) (J : Set (GA D (D.sp.Y 0))) (χ : GA D (D.sp.Y 0) → ℂ) (t : GA D (D.sp.Y 0)) (c : ∀ τ, M.H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), S = parB (Ptw D) 0 → IsInfFam θ → GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → IdE X → Matches X h J χ t → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ (M.rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : M.Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u))) ψ) → ∀ (τ : D.what₂.Tau) (v : M.Vec) (x : GA D (D.sp.Y 0)), ∃ ℓ : M.H τ →ₗ[ℂ] ℂ, Sobolev₂ (lieAt (D.sp.Y 0) τ) (M.rep τ) ℓ ∧ ∀ w : M.sm τ, ℓ w = GlobalTheory.ConjRowMult.conjMap X M c Φ h t (Function.update v τ w) x := by
  intro _ D X h θ S M J χ t c _ hθ _ hE _ hc Φ hΦ hrep τ₀ v₀ x₀
  obtain ⟨_, _, _, _, _, -, _⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D (D.sp.Y 0)
  obtain ⟨hf, -, hat, -⟩ := GlobalTheory.Core.Mi.SeeReal.realSplit_of_idE D X h θ hθ hE
  obtain ⟨-, hcomm, g, hg, hfix⟩ := GlobalTheory.IdemProj.re_orth_proj X.B
  have := X.B.sf
  have := X.B.haar
  let T : GA D (D.sp.Y 0) ≃* X.B.I.GA := (iotaX X h).toMulEquiv
  have hT : Continuous T := (iotaX X h).continuous
  have hT' : Continuous T.symm := (iotaX X h).symm.continuous
  obtain ⟨μ, ρ, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ :=
    GlobalTheory.TensRep.exists_transport X.B.I X.B.μf X.B.fund X.B.fund_spec X.B.R X.B.R_spec T hT hT'
  obtain ⟨U, hU, hUg⟩ := h11 g hg
  have hA : Φ ∈ X.B.I.HomS X.B.σs X.B.μf X.B.fund X.B.R := by
    obtain ⟨A, hA, rfl⟩ := hΦ
    intro g
    show (X.B.Re.comp A).comp (X.B.σs g) = (X.B.R (g, 1)).comp (X.B.Re.comp A)
    rw [ContinuousLinearMap.comp_assoc, hA g, ← ContinuousLinearMap.comp_assoc, hcomm g,
      ContinuousLinearMap.comp_assoc]
  have hlev : ∀ k ∈ X.B.I.Kg g, ∀ w, X.B.R (1, k) (Φ w) = Φ w := by
    obtain ⟨A, -, rfl⟩ := hΦ
    intro k hk w
    exact congrArg (fun C : L2X X →L[ℂ] L2X X => C (A w)) (hfix k hk)
  obtain ⟨Ψ, hΨ⟩ := exists_conj_multilinear X M c Φ
  obtain ⟨N, hN1, hN2, hN3⟩ := GlobalTheory.TensRep.exists_mmap (ι := fun v x => X.B.I.ext v (T x)) hθ M h1 h2 h5 h6 h7 h8 h9
    (fun γ hγ v => h10 γ ((iotaX_rat_iff X h γ).1 hγ) v) hU Ψ
    (fun τ a ha y => by
      obtain ⟨q1, q2, -⟩ := hat τ a ha
      rw [h3, hΨ, hΨ, reg_star]
      congr 1
      refine GlobalTheory.TensRep.hom_tens X.B.I X.B.tens_spec hA q1 _ _ fun v => ?_
      obtain ⟨τ', rfl⟩ := X.pl.symm.surjective v
      rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]
      by_cases e : τ' = τ
      · subst e
        rw [Function.update_self]
        exact hc _ a ha _
      · rw [Function.update_of_ne e]
        have q : (iotaX X h (atTau θ (D.sp.Y 0) τ a)).1 (X.pl.symm τ') = 1 := q2 _ (X.pl.symm.injective.ne e)
        rw [q]
        have : X.B.σ (X.pl.symm τ') 1 = 1 := (X.ds _).2.2.1.1.1
        show _ = X.B.σ (X.pl.symm τ') 1 _
        rw [this]
        rfl)
    (fun y k hk hk' => by
      rw [h3, hΨ, reg_star]
      have e : T k = (1, (T k).2) := Prod.ext ((hf k).1 hk') rfl
      rw [e, hlev _ (hUg k hk)])
  have key : ∀ (u : M.Vec) y, GlobalTheory.ConjRowMult.conjMap X M c Φ h t u y = N u (y * t⁻¹) := by
    intro u y
    have r1 : GlobalTheory.Dec.IsContRep X.B (Ψ fun τ => (u τ : M.H τ)) (fun z => N u (T.symm z)) := by
      refine GlobalTheory.RepSmooth.isContRep_of_ae X.B ((hN2 u).3.comp hT') (fun γ hγ z => ?_) ?_
      · rw [map_mul]
        refine (hN2 u).1 _ ((iotaX_rat_iff X h _).2 ?_) _
        have : iotaX X h (T.symm γ) = γ := T.apply_symm_apply γ
        rwa [this]
      · filter_upwards [h4 _ (hN1 u)] with z hz
        rw [← hz, T.apply_symm_apply]
    have r2 : Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)))
        (fun z => star (N u (T.symm z))) := by
      refine ⟨r1.1.star, fun γ hγ z => congrArg star (r1.2.1 γ hγ z), ?_⟩
      have r3 := r1.2.2
      rw [hΨ] at r3
      filter_upwards [r3, Lp.coeFn_star (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X M c u)))] with z a1 a2
      rw [← a1]
      exact (star_star _).symm.trans (congrArg star a2.symm)
    rw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.contRepL_spec X r2, star_star]
    exact congrArg (N u) (T.symm_apply_apply _)
  obtain ⟨ℓ, hℓ1, hℓ2⟩ := hN3 τ₀ v₀ (x₀ * t⁻¹)
  exact ⟨ℓ, hℓ1, fun w => (hℓ2 w).trans (key _ _).symm⟩

end GlobalTheory.ConjRowCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjugateHalfAnnihilatorMemCompletedHomLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.SeeSaw GlobalTheory.LocMod
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitVacAnnih

open GlobalTheory.FinPl.FrameLat

theorem trace_rankOne {k m n Y Y' : Type} [Field k] [Fintype m] [DecidableEq m] [Fintype n] [Fintype Y] [Fintype Y']
    (A G : Matrix m m k) (hAG : G * A = 1) (N : Matrix m n k) (B : Matrix n n k) (βT : Matrix n Y k) (βS : Matrix m Y' k)
    (γS : Matrix Y' m k) (hS : βS * γS = 1) (c : Y → k) (x : m → k) :
    Matrix.trace (A * N * B * (βT * vecMulVec c ((x ᵥ* G) ᵥ* βS) * γS)) = x ⬝ᵥ (N * B) *ᵥ (βT *ᵥ c) := by
  rw [Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, hS,
    Matrix.mul_one, Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mul_assoc A, ← Matrix.mul_assoc G, hAG, Matrix.one_mul]

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem int_of_char {ψk : AddChar k Circle} (h : HasConductor ψk 1) {b : k} (hb : ∀ a ∈ 𝒪[k], ψk (a * b) = 1) :
    b ∈ 𝒪[k] := by
  by_cases h0 : b = 0
  · rw [h0]; exact zero_mem _
  have h1 := (h b).1 fun t ht => by
    have := hb (t / b) (by
      rw [Valuation.mem_integer_iff, map_div₀]
      exact div_le_one_of_le₀ ht zero_le)
    rwa [div_mul_cancel₀ _ h0] at this
  rw [Valuation.mem_integer_iff]
  simpa using h1

theorem annihilator_mem_latO : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (S T : HSp D) (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), IsStdChar D ψ (-1) → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ y : WO S T, IsHalf (cA D q.e) y → (∀ x : Matrix Y Y' k, (∀ r s, x r s ∈ 𝒪[k]) → ψ (symplO S T ((ofSplit q).up FS FT x) y) = 1) → y ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = q.v) := by
  intro D k _ _ _ _ q hU Y Y' _ _ _ _ S T FS FT LS LT hS hT hFS hFT ψ ψk _ hχ hc y hy hann
  have hce : cA D q.e ∈ GlobalTheory.FinPl.intAt D (· = q.v) := by
    rw [← sec_one q]
    exact ⟨csec_mem_idAt 1, (cA_int_iff _).2 (sec_mem_intAt q 1 (one_mem _)).2⟩
  have hcs : ∀ a : AE D, cA D (q.sec (q.pr (cA D a))) = cA D q.e * a := fun a => by
    rw [q.sec_pr, RingHom.map_mul, GlobalTheory.LocSympl.conj_conj]
  have hgram : ∀ (V : HSp D) i j, q.pr (cA D (incA D (V.gram i j))) = (V.gram.map (q.pr.comp (incA D))) j i :=
    fun V i j => by rw [cA_incA, GlobalTheory.LatVac.gram_star]; rfl
  rw [GlobalTheory.FinPl.LatMem.mem_latO_iff D S T LS LT hS hT, hU.2 T LT]
  refine ⟨fun i j => ?_, fun x hx => ?_⟩
  · rw [← hy i j]
    exact Ideal.mul_mem_right _ _ hce.1
  set N : Matrix (Fin S.rank) (Fin T.rank) k := Matrix.of fun b c => q.pr (cA D (y c b)) with hN
  set x' : Fin S.rank → k := fun j => q.pr (cA D (x j)) with hx'
  have hyN : y = N.transpose.map fun a => cA D ((ofSplit q).ι a) := by
    ext i j
    exact ((hcs _).trans (hy i j)).symm
  have hx1 : (fun j => cA D (q.sec (x' j))) ∈ GlobalTheory.FinPl.latV S LS (· = q.v) := by
    have := smul_mem hS hx hce
    convert this using 1
    funext j
    exact hcs _
  have hyx : (y : Matrix _ _ (AE D)) *ᵥ x = fun i => cA D (q.sec ((x' ᵥ* N) i)) := by
    funext i
    have : (x' ᵥ* N) i = q.pr (cA D (((y : Matrix _ _ (AE D)) *ᵥ x) i)) := by
      simp only [Matrix.vecMul, Matrix.mulVec, dotProduct, map_sum, RingHom.map_mul, hN, hx', Matrix.of_apply]
      exact Finset.sum_congr rfl fun j _ => mul_comm _ _
    rw [this, hcs]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [← mul_assoc, hy i j]
  show (y : Matrix _ _ (AE D)) *ᵥ x ∈ _
  rw [hyx, csec_mem_iff hT]
  intro u hu
  have huc : FT.β *ᵥ (FT.γ *ᵥ u) = u := by rw [Matrix.mulVec_mulVec, FT.βγ, Matrix.one_mulVec]
  have hcint : ∀ i, (FT.γ *ᵥ u) i ∈ 𝒪[k] := (hFT _).2 (by rw [huc]; exact hu)
  set f := q.pr.comp (incA D) with hf
  have hrow : ∀ s, ((x' ᵥ* S.gram.map f) ᵥ* FS.β) s ∈ 𝒪[k] := fun s => by
    have h1 := (csec_mem_iff hS x').1 hx1 _ ((hFS (Pi.single s 1)).1 fun i => by
      by_cases h : i = s
      · subst h; rw [Pi.single_eq_same]; exact one_mem _
      · rw [Pi.single_eq_of_ne h]; exact zero_mem _)
    convert h1 using 1
    simp only [hgram, Matrix.mulVec_single_one, Matrix.vecMul, dotProduct, Finset.sum_mul, Matrix.col, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  refine int_of_char hc fun a ha => ?_
  have h2 := hann (vecMulVec (a • (FT.γ *ᵥ u)) ((x' ᵥ* S.gram.map f) ᵥ* FS.β)) fun r s =>
    mul_mem (mul_mem ha (hcint r)) (hrow s)
  have hA : S.gram.map f * (S.gram⁻¹).map f = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ (GlobalTheory.LatVac.gram_det_isUnit S),
      Matrix.map_one _ (map_zero f) (map_one f)]
  rw [GlobalTheory.LocSympl.psi_sympl_up _ FS FT ψ ψk hχ, hyN, GlobalTheory.LocSympl.pi_hO_up] at h2
  have h3 := trace_rankOne _ _ hA N (T.gram.map f) FT.β FS.β FS.γ FS.βγ (a • (FT.γ *ᵥ u)) x'
  rw [Matrix.mulVec_smul, huc, Matrix.mulVec_smul, dotProduct_smul, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec] at h3
  have h4 : ∑ i, ∑ j, u i * q.pr (cA D (incA D (T.gram i j))) * (x' ᵥ* N) j = (x' ᵥ* N) ⬝ᵥ T.gram.map f *ᵥ u := by
    rw [Finset.sum_comm]
    simp only [hgram, Matrix.mulVec, dotProduct, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [h4, ← smul_eq_mul, ← h3]
  exact Circle.ext h2

end GlobalTheory.SplitVacAnnih

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuesWithModerateGrowthShiftTranslatePowStatement
section
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuesWithModerateGrowth_shift_translate_pow : ∀ (D : D7) (T : HSp D) (e e' : ℂ → GA D T → ℂ) (x : GA D T) (c : ℝ≥0) (s₁ s₂ : ℂ), 0 < c → (∀ s g, e' s g = npow c (s₁ - s) * e (s + s₂) (g * x)) → ContMod T e → ContMod T e' := by
  first | exact @GlobalTheory.EisCont.Shift.contMod_shift | exact GlobalTheory.EisCont.Shift.contMod_shift | (intros; apply GlobalTheory.EisCont.Shift.contMod_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspidalModerateGrowthRapidDecayStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta MeasureTheory NumberField Matrix GlobalTheory.CuspGeo
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_moderateGrowth_rapidDecay : GlobalTheory.Published.CuspDecayBound := by
  first | exact @GlobalTheory.CuspGeo.cuspDecayBound | exact GlobalTheory.CuspGeo.cuspDecayBound | (intros; apply GlobalTheory.CuspGeo.cuspDecayBound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteUnitaryQuotientCompactFundamentalDomainStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec)
open GlobalTheory.Mem.Th (CptF)
open GlobalTheory.Core.Rk.IP
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.Exh GlobalTheory.RegSW
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definite_unitary_quotient_compact_fundamentalDomain : ∀ (D : D7) (A : HSp D), HSpace.SigOK A → HSpace.IsPosDef A → ∀ m : Measure (GA D A), m.IsHaarMeasure → GlobalTheory.Unf.CoCpt A ∧ ∃ (X K : Set (GA D A)), MeasurableSet X ∧ IsFundamentalDomain (GQ A) X m ∧ IsCompact K ∧ X ⊆ K := by
  first | exact @GlobalTheory.DefFund.coCpt_and_fundamentalDomain_subset_compact | exact GlobalTheory.DefFund.coCpt_and_fundamentalDomain_subset_compact | (intros; apply GlobalTheory.DefFund.coCpt_and_fundamentalDomain_subset_compact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DiscreteSeriesTestDataOfNoncompactGaps
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.Core.Rk GlobalTheory.Core.Mi
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Core.Mi

private theorem isHCParam_comp_fin_cast {n m : ℕ} (h : n = m) {f : Fin m → ℝ} (hf : Formalism.QuantumDeterminants.IsHCParam f) :
    Formalism.QuantumDeterminants.IsHCParam (fun i : Fin n => f (Fin.cast h i)) := by
  subst h
  exact hf

theorem isHCParam_lam_of_setting {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (v : InfinitePlace X.B.I.F) :
    Formalism.QuantumDeterminants.IsHCParam (X.B.lam v) := by
  rw [show X.B.lam v = _ from funext (X.lam_eq v)]
  exact isHCParam_comp_fin_cast X.n_eq (Formalism.MainNotions.S.Inh.aut_isHCParam_lamS D.R (D.hc (X.pl v)))

private theorem card_filter_true_add_card_filter_false {n : ℕ} (ε : Fin n → Bool) :
    (Finset.univ.filter fun a : Fin n => ε a = true).card +
      (Finset.univ.filter fun a : Fin n => ε a = false).card = n := by
  rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
  have h1 : ∀ a : Fin n, ((if ε a = true then 1 else 0) + (if ε a = false then 1 else 0) : ℕ) = 1 := by
    intro a
    cases ε a <;> simp
  simp only [h1, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

theorem two_mul_rkR_le {n : ℕ} (ε : Fin n → Bool) : 2 * GlobalTheory.Count.rkR ε ≤ n := by
  have h1 : GlobalTheory.Count.rkR ε ≤ (Finset.univ.filter fun a : Fin n => ε a = true).card := min_le_left _ _
  have h2 : GlobalTheory.Count.rkR ε ≤ (Finset.univ.filter fun a : Fin n => ε a = false).card := min_le_right _ _
  have h3 := card_filter_true_add_card_filter_false ε
  omega

private theorem natCast_rpow_three_halves_le_sq (q : ℕ) : (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]
    positivity
  · have h1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    calc (q : ℝ) ^ ((3 : ℝ) / 2) ≤ (q : ℝ) ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
      _ = (q : ℝ) ^ 2 := Real.rpow_two _

private theorem mul_rpow_three_halves_le_pow_four (q n : ℕ) (h : 2 * q ≤ n) :
    120 * (n : ℝ) * ((q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (n : ℝ) ^ 4 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rw [Nat.cast_zero, Real.zero_rpow (by norm_num), mul_zero]
    positivity
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have hq2 : 2 * (q : ℝ) ≤ n := by exact_mod_cast h
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hsq : 4 * (q : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by nlinarith
    calc 120 * (n : ℝ) * (q : ℝ) ^ ((3 : ℝ) / 2) ≤ 120 * (n : ℝ) * (q : ℝ) ^ 2 :=
          mul_le_mul_of_nonneg_left (natCast_rpow_three_halves_le_sq q) (by positivity)
      _ ≤ 30 * (n : ℝ) ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hsq hn0]
      _ ≤ 100 * (n : ℝ) ^ 4 := by
          nlinarith [mul_le_mul_of_nonneg_left (show (30 : ℝ) ≤ 100 * n by linarith) (pow_nonneg hn0 3)]

theorem rkR_bound {n : ℕ} (ε : Fin n → Bool) :
    120 * (n : ℝ) * ((GlobalTheory.Count.rkR ε : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (n : ℝ) ^ 4 :=
  mul_rpow_three_halves_le_pow_four _ _ (two_mul_rkR_le ε)

private theorem mul_sq_mul_sqrt_le_pow_four (q n : ℕ) (h : 2 * q ≤ n) :
    40 * (n : ℝ) ^ 2 * Real.sqrt (q : ℝ) ≤ 100 * (n : ℝ) ^ 4 := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    rw [Nat.cast_zero, Real.sqrt_zero, mul_zero]
    positivity
  · have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
    have hq2 : 2 * (q : ℝ) ≤ n := by exact_mod_cast h
    have hs : Real.sqrt (q : ℝ) ≤ q := by
      have h' := Real.sqrt_le_sqrt (show (q : ℝ) ≤ (q : ℝ) ^ 2 by nlinarith)
      rwa [Real.sqrt_sq (by linarith)] at h'
    calc 40 * (n : ℝ) ^ 2 * Real.sqrt (q : ℝ) ≤ 40 * (n : ℝ) ^ 2 * q :=
          mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ 20 * (n : ℝ) ^ 3 := by nlinarith [mul_le_mul_of_nonneg_left hq2 (sq_nonneg (n : ℝ))]
      _ ≤ 100 * (n : ℝ) ^ 4 := by
          nlinarith [mul_le_mul_of_nonneg_left (show (20 : ℝ) ≤ 100 * n by linarith) (pow_nonneg hn0 3)]

theorem rkR_bound_sqrt {n : ℕ} (ε : Fin n → Bool) :
    40 * (n : ℝ) ^ 2 * Real.sqrt (GlobalTheory.Count.rkR ε) ≤ 100 * (n : ℝ) ^ 4 :=
  mul_sq_mul_sqrt_le_pow_four _ _ (two_mul_rkR_le ε)

theorem seeData_of_gap : ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D), GlobalTheory.Count.GapGe X.B (100 * (D.R.r : ℝ) ^ 4) → GlobalTheory.Count.IsDSData X.B X.dv ∧ GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) ∧ GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) ∧ (∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ 100 * (D.R.r : ℝ) ^ 4) ∧ Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧ ∀ v, Integrable (Formalism.L2.SG.ProjRows.phLoc (ε := X.B.I.ε v) (X.B.σ v) (X.B.w v) (X.dv v)) (Formalism.REAL.muG (X.B.I.ε v)) := by
  intro D X hg
  have hDS : GlobalTheory.Count.IsDSData X.B X.dv := fun v =>
    ⟨isHCParam_lam_of_setting X v, X.ds v, X.low v, GlobalTheory.LowestVectorDegree.isFdeg_fdegOf_lowest D X v⟩
  have hb : ∀ v, 120 * (X.B.I.n : ℝ) * ((GlobalTheory.Count.rkR (X.B.I.ε v) : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤
      100 * (D.R.r : ℝ) ^ 4 := by
    intro v
    have e : (X.B.I.n : ℝ) = (D.R.r : ℝ) := by exact_mod_cast X.n_eq
    calc _ ≤ 100 * (X.B.I.n : ℝ) ^ 4 := rkR_bound (X.B.I.ε v)
      _ = 100 * (D.R.r : ℝ) ^ 4 := by rw [e]
  have hL : GlobalTheory.Dec.LocDec X.B (100 * (D.R.r : ℝ) ^ 4) :=
    GlobalTheory.Dec.locDec_of_decGap_gapGe (GlobalTheory.DecGapBound.decGap_of_formulaGap GlobalTheory.Jet.FormGapFree.formulaGap)
      X.B X.dv _ hDS hg hb
  have hI : Integrable X.ph (Formalism.L2.SG.ProjRows.muInf X.B.I) :=
    (GlobalTheory.Dec.ProjCuspGap.projector_rank_cuspidal X.B X.dv _ hDS hg hb).1
  have hH : GlobalTheory.Dec.HBig X.B 40 (100 * (D.R.r : ℝ) ^ 4) := by
    unfold GlobalTheory.Dec.HBig
    intro v
    have e : (X.B.I.n : ℝ) = (D.R.r : ℝ) := by exact_mod_cast X.n_eq
    calc _ ≤ 100 * (X.B.I.n : ℝ) ^ 4 := rkR_bound_sqrt (X.B.I.ε v)
      _ = 100 * (D.R.r : ℝ) ^ 4 := by rw [e]
  exact ⟨hDS, hL, hH, hb, hI, GlobalTheory.ProdFactor.integrable_phLoc_of_integrable_ph D X hI⟩

end GlobalTheory.Core.Mi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledLagrangianTransverseInOpenOrbitStatement
section
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.Dich
open Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubled_lagrangian_transverse_in_open_orbit : ∀ (D : D7) (V : HSp D), ∀ γ ∈ GQ (dblSp V), ∀ γi : Matrix (Fin (V.rank + V.rank)) (Fin (V.rank + V.rank)) D.host.E, (matHom (dblSp V) γ⁻¹).1 = γi.map (incA D) → (∀ x : Fin V.rank → D.host.E, diagSnd γi *ᵥ x = 0 → x = 0) → ∃ δ ∈ GQ V, γ * (io V (δ, 1))⁻¹ ∈ siegel V := by
  first | exact @GlobalTheory.Core.Rk.Dich.exists_mem_siegel_of_diagSnd | exact GlobalTheory.Core.Rk.Dich.exists_mem_siegel_of_diagSnd | (intros; apply GlobalTheory.Core.Rk.Dich.exists_mem_siegel_of_diagSnd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoubledSpaceMaximalLevelLatticeStatement
section
open scoped NNReal Matrix TensorProduct Topology
open Filter NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.RegSW GlobalTheory.EisCont GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine
open GlobalTheory.Core.Rk.SWLaw (dblDec zeroSp)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem _root_.GlobalTheory.T.doubled_space_maximal_level_lattice : ∀ (D : D7) (V : HSp D), siegel V = stab (dblDec V) ∧ (∀ (p : GA D (dblSp V)) (h : p ∈ siegel V) (h' : p ∈ stab (dblDec V)), aP V ⟨p, h⟩ = Matrix.GeneralLinearGroup.det (onX (dblDec V) ⟨p, h'⟩)) ∧ IsAniso (zeroSp D) ∧ ∀ a : GL (Fin V.rank) (AE D), IsMaj V a → ∃ (L : Submodule (𝓞 D.host.E) (Fin (dblSp V).rank → D.host.E)) (b : GL (Fin (dblSp V).rank) (AE D)), IsLevel (dblSp V) L b ∧ Khat V a = lev (dblSp V) L b := by
  first | exact @GlobalTheory.EisCont.siegel_eq_stab_dblDec | exact GlobalTheory.EisCont.siegel_eq_stab_dblDec | (intros; apply GlobalTheory.EisCont.siegel_eq_stab_dblDec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIntegerSubConjNotMemSelfConjugatePlace
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ConjMovesResidue

theorem exists_sub_star_notMem : ∀ (D : D7) (Q : Pl D.host.E), IsConjPl (D := D) Q Q →
    ∃ δ δ' : 𝓞 D.host.E, (δ' : D.host.E) = star (δ : D.host.E) ∧ δ - δ' ∉ Q.asIdeal := by
  intro D Q _
  obtain ⟨θ, t, h1, h2⟩ := Formalism.BasicNotions.Examples₂.unram_at D.host Q.asIdeal Q.isMaximal
  refine ⟨θ, t, ?_, h2⟩
  change algebraMap (𝓞 D.host.E) D.host.E t = _
  rw [h1, Formalism.BasicNotions.Examples₂.star_eq_conj]

end GlobalTheory.ConjMovesResidue
end

