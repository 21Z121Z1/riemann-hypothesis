import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyEqOfIsZetaCont
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0293
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0287
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0102
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0295
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0271
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0024
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0289
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0024
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.TransvectionAction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0009
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0117
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0285
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentMulAddOneSubInverse
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0128

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainOccurringParamsNormHalfRankBound
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainOnto

theorem parBoundW_of_parBound {D : D7} (h : ParBound D) : ParBoundW D := by
  intro c hc j hj s hs u B hu
  exact GlobalTheory.LiftPole.Bounded.mono (h c hc j hj s hs u B hu) (by linarith)

theorem parBoundW (hP : GlobalTheory.Published.CuspRapidDecay) (D : D7) (hL : LevFacts D) : ParBoundW D :=
  parBoundW_of_parBound (GlobalTheory.T.thetaChain_heckeParams_trivialBound_rapidDecay hP D hL)

end GlobalTheory.ChainOnto
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrivialAtPlaceCommSeeSawCombinationKeepsVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.OffPlaceWeil

theorem vac_off {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : Om S T}
    (hW : IsWeilDatumO ψ S T χS χT om) {LS : Lat S} {LT : Lat T} {P : GlobalTheory.FinPl.Pl D → Prop} {f : WO S T → ℂ}
    (hf : Vac ψ S T LS LT P f) {g : GA D S} {h : GA D T} (hg : g ∈ grpOff S P) (hh : h ∈ grpOff T P) :
    Vac ψ S T LS LT P (om (g, h) f) := by
  have key : ∀ u ∈ latO S T (LS : Set _) (LT : Set _) P, heisO ψ S T u f = f →
      heisO ψ S T u (om (g, h) f) = om (g, h) f := by
    intro u hu hfix
    have e := hW.om_heis g h u f hf.1
    rw [hfix, GlobalTheory.DisjComb.actO_off hg hh (GlobalTheory.FinPl.LatMem.latO_mxAt hu)] at e
    exact e.symm
  exact ⟨hW.om_pres _ f hf.1, fun u hu => key _ (AddSubgroup.nsmul_mem _ hu 2) (hf.2.1 u hu),
    fun e he u hu hh' => key u hu (hf.2.2 e he u hu hh')⟩

theorem combAt_eg {D : D7} {c : Comm D} {v : VCom c} (Gi : GLoc v) (j : ℕ) (hj : j + 1 < D.R.m) :
    CombAt (· = Gi.q.v) (Gi.eg j) := by
  have hs := Gi.hs
  intro u hu a b
  have h1 := (Gi.eg_is j (Gi.s - j) (by omega)).1 u hu a b
  obtain ⟨ε, hε, hsum⟩ := Gi.q.above
  exact ((GlobalTheory.FinPl.placeIdem_acts D Gi.q.v ε hε).1 _).2 (hsum ▸ h1)

theorem main : ∀ {D : D7} {c : Comm D} {v : VCom c}, c.Is → v.Is → ∀ (Gi : GLoc v) (j : ℕ), j + 1 < D.R.m → ∀ (χS χT : (AE D)ˣ →* Circle) (om : Om (c.V j) (c.V (j + 1))), IsWeilDatumO c.ψ _ _ χS χT om → ∀ (F : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) F → ∀ y ∈ grpOff (c.V (j + 1)) (· = Gi.q.v), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = Gi.q.v) (om (1, y) F) ∧ om (1, y) (comb c.ψ _ _ (Gi.eg j) F) = comb c.ψ _ _ (Gi.eg j) (om (1, y) F) := by
  intro D c v hc _ Gi j hj χS χT om hW F hF y hy
  exact ⟨vac_off hW hF (one_mem _) hy,
    (GlobalTheory.DisjComb.main D c.ψ hc.std _ _ (· = Gi.q.v) (fun _ => False) (fun _ _ h => h)).2.2.1 χS χT om hW _
      (combAt_eg Gi j hj) 1 (one_mem _) y hy F hF.1⟩

end GlobalTheory.OffPlaceWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceCouplingIndexFiniteLevelStableStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlace_couplingIndex_finite_level_stable : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ), (Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂)).Finite ∧ (∀ yb, SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb) ∧ (∀ yb yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb) ∧ (∀ yb yb' yb'', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb' yb'' → SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb'') ∧ ∀ yb ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂), ∀ yb', SameOrb (Q.T.lev (Q.s + 1) 0 rfl).J (box _ Q.c₂) yb yb' → yb' ∈ Q.T.coupIdx Q.A (box _ Q.c₁) (box _ Q.c₂) := by
  first | exact @GlobalTheory.QPl.CoupStab.coupIdx_stab | exact GlobalTheory.QPl.CoupStab.coupIdx_stab | (intros; apply GlobalTheory.QPl.CoupStab.coupIdx_stab <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoLevelIndicesNeZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlace_last_two_level_indices_ne_zero : ∀ (D : D7) (c : Comm D) (v : VCom c) (χ : ℕ → (AE D)ˣ →* Circle) (Q : QAt v χ), Q.idx (Q.s + 1) ≠ 0 ∧ Q.idx (Q.s + 1 + 1) ≠ 0 := by
  first | exact @GlobalTheory.QPl.QAt.idx_last_ne_zero | exact GlobalTheory.QPl.QAt.idx_last_ne_zero | (intros; apply GlobalTheory.QPl.QAt.idx_last_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoStepEntriesSchwartzBruhatStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ) α yb, Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb ∈ SB _ ∧ Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb ∈ SB _ := by
  first | exact @GlobalTheory.QPl.LastTwo.entries_mem_SB | exact GlobalTheory.QPl.LastTwo.entries_mem_SB | (intros; apply GlobalTheory.QPl.LastTwo.entries_mem_SB <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceNormalisedCombinationsPreserveThetaFunStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlace_normalisedCombinations_preserve_thetaFunctions : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → F.Pins w → ∀ j (h : j + 2 * 0 + 2 = D.R.m) (Ψ₁ : WO (c.V j) (c.V (j + 1)) → ℂ) (Ψ₂ : WO (c.V (j + 1)) c.T → ℂ), IsThetaFunO c.ψ _ _ Ψ₁ → IsThetaFunO c.ψ _ _ Ψ₂ → IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQ j) Ψ₁) ∧ IsThetaFunO c.ψ _ _ (comb c.ψ _ _ (w.eQT j h) Ψ₂) := by
  first | exact @GlobalTheory.QPl.pins_keep_theta | exact GlobalTheory.QPl.pins_keep_theta | (intros; apply GlobalTheory.QPl.pins_keep_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UniformCauchySeqOnHeisenbergWordSobolevCauchyStatement
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
theorem _root_.GlobalTheory.T.uniformCauchySeqOn_heisenbergWord_sobolevCauchy : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ θ : InfFam D, IsInfFam θ → ∀ S T : HSp D, ∀ (μ : Measure (WO S T)) (𝓕 : Set (WO S T)), IsCovolOne (ratL T S) μ 𝓕 → ∀ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) → ∀ u : ℕ → WO S T → ℂ, (∀ j, u j ∈ thetaLevel ψ S T U) → (∀ d, ∀ ε : ℝ≥0∞, 0 < ε → ∃ J, ∀ i ≥ J, ∀ j ≥ J, sobO ψ θ μ 𝓕 d (u i - u j) < ε) → ∀ l : List (D.what₂.Tau × Fin T.rank × Fin S.rank × Bool), UniformCauchySeqOn (fun j => GlobalTheory.Size.wordAct (GlobalTheory.Size.heisDer ψ θ) l (u j)) Filter.atTop Set.univ := by
  first | exact @GlobalTheory.ThetaDensCauchy.uniformCauchySeqOn_word | exact GlobalTheory.ThetaDensCauchy.uniformCauchySeqOn_word | (intros; apply GlobalTheory.ThetaDensCauchy.uniformCauchySeqOn_word <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodularStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryAdelic_inf_fin_split_periods_unimodular : ∀ (D : D7) (V : HSp D), IsClosed (GinfC V : Set (GA D V)) ∧ IsClosed (GfC V : Set (GA D V)) ∧ (∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b = b * a) ∧ (∃ e : (GinfC V × GfC V) ≃ₜ GA D V, ∀ p, e p = p.1 * p.2) ∧ (∀ μ : Measure (GfC V), μ.IsHaarMeasure → μ.IsMulRightInvariant) ∧ ∀ (V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ), ((∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ jacGrp d → a ∈ jacGrp d ∧ b ∈ jacGrp d) ∧ (∀ μ : Measure (jacGrp d), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ μ : Measure ((jacGrp d).subgroupOf (GfC V)), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ (A L : HSp D) (o : OrthDec V₀ A L), (∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ besGrp d o → a ∈ besGrp d o ∧ b ∈ besGrp d o) ∧ (∀ μ : Measure (besGrp d o), μ.IsHaarMeasure → μ.IsInvInvariant) ∧ ∀ μ : Measure ((besGrp d o).subgroupOf (GfC V)), μ.IsHaarMeasure → μ.IsInvInvariant := by
  first | exact @GlobalTheory.AdelicSplit.adelic_split | exact GlobalTheory.AdelicSplit.adelic_split | (intros; apply GlobalTheory.AdelicSplit.adelic_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryIdempotentCutMemFourierJacobiBesselGroup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.SetCut

theorem smul_add_one_sub_smul_sub_one {R : Type} [CommRing R] {n : ℕ} (c : R) (M : Matrix (Fin n) (Fin n) R) :
    c • M + (1 - c) • (1 : Matrix (Fin n) (Fin n) R) - 1 = c • (M - 1) := by
  rw [sub_smul, one_smul, smul_sub]; abel

theorem smul_add_one_sub_smul_block {R : Type} [CommRing R] {n m : ℕ} (c : R) (P Q : Matrix (Fin n) (Fin n) R)
    (j : Matrix (Fin n) (Fin m) R) (p : Matrix (Fin m) (Fin n) R) (M : Matrix (Fin m) (Fin m) R)
    (h : P + j * p + Q = 1) :
    c • (P + j * M * p + Q) + (1 - c) • (1 : Matrix (Fin n) (Fin n) R) =
      P + j * (c • M + (1 - c) • (1 : Matrix (Fin m) (Fin m) R)) * p + Q := by
  rw [← h]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, smul_add, sub_smul,
    one_smul, Matrix.mul_sub, Matrix.sub_mul]
  abel

theorem smul_add_one_sub_smul_block₂ {R : Type} [CommRing R] {n m k : ℕ} (c : R)
    (j : Matrix (Fin n) (Fin m) R) (p : Matrix (Fin m) (Fin n) R) (M : Matrix (Fin m) (Fin m) R)
    (j' : Matrix (Fin n) (Fin k) R) (p' : Matrix (Fin k) (Fin n) R)
    (h : j * p + j' * p' = 1) :
    c • (j * M * p + j' * (1 : Matrix (Fin k) (Fin k) R) * p') + (1 - c) • (1 : Matrix (Fin n) (Fin n) R) =
      j * (c • M + (1 - c) • (1 : Matrix (Fin m) (Fin m) R)) * p + j' * (1 : Matrix (Fin k) (Fin k) R) * p' := by
  have := smul_add_one_sub_smul_block c 0 (j' * p') j p M (by rw [zero_add, h])
  simpa only [zero_add, Matrix.mul_one] using this

variable {D : D7}

theorem jac_subOne_cutG (V : HSp D) (ε : AF D.host.F) (hε : ε * ε = ε) (g : GA D V) :
    Formalism.L2.Theta.subOne V (cutG V ε hε g) = algebraMap (AF D.host.F) (AE D) ε • Formalism.L2.Theta.subOne V g :=
  smul_add_one_sub_smul_sub_one (algebraMap (AF D.host.F) (AE D) ε) (Formalism.L2.Theta.mt V g)

theorem jac_cutG_map_NFlag (V : HSp D) {ρ : ℕ} (e : Matrix (Fin V.rank) (Fin ρ) D.host.E) (ε : AF D.host.F)
    (hε : ε * ε = ε) : (NFlag V e).map (cutG V ε hε) ≤ NFlag V e := by
  unfold NFlag
  rw [MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨g, ⟨h1, h2⟩, rfl⟩
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨a, ha, hb⟩ := h1 i
    refine ⟨algebraMap (AF D.host.F) (AE D) ε • a, fun j hj => ?_, ?_⟩
    · rw [Pi.smul_apply, ha j hj, smul_zero]
    · rw [jac_subOne_cutG, Matrix.smul_mulVec, hb, Matrix.mulVec_smul]
  · obtain ⟨a, hb⟩ := h2 x hx
    refine ⟨algebraMap (AF D.host.F) (AE D) ε • a, ?_⟩
    rw [jac_subOne_cutG, Matrix.smul_mulVec, hb, Matrix.mulVec_smul]

theorem unitaryIdempotentCut_wittHyperbolicEmbedding_comm {V V₀ : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (ε : AF D.host.F) (hε : ε * ε = ε) (h : GA D V₀) :
    cutG V ε hε (d.emb0 h) = d.emb0 (cutG V₀ ε hε h) := by
  apply GlobalTheory.MixModel.mt_injective V
  change Formalism.L2.Theta.mt V (cutG V ε hε (d.emb0 h)) = Formalism.L2.Theta.mt V (d.emb0 (cutG V₀ ε hε h))
  rw [mt_cutG, HypDec.unitaryMatrix_wittCoreEmbedding, HypDec.unitaryMatrix_wittCoreEmbedding, mt_cutG]
  exact smul_add_one_sub_smul_block _ _ _ _ _ _ d.sum_eq_one

theorem jac_cutG_emb_inl {V₀ A L : HSp D} (o : OrthDec V₀ A L) (ε : AF D.host.F) (hε : ε * ε = ε) (h : GA D A) :
    cutG V₀ ε hε (o.emb (h, 1)) = o.emb (cutG A ε hε h, 1) := by
  apply GlobalTheory.MixModel.mt_injective V₀
  change Formalism.L2.Theta.mt V₀ (cutG V₀ ε hε (o.emb (h, 1))) = Formalism.L2.Theta.mt V₀ (o.emb (cutG A ε hε h, 1))
  rw [mt_cutG, OrthDec.mt_emb, OrthDec.mt_emb, mt_cutG, mt_one]
  exact smul_add_one_sub_smul_block₂ _ _ _ _ _ _ o.sum_eq_one

theorem cutG_mem_jacGrp_besGrp (D : D7) (V V₀ : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (ε : AF D.host.F) (hε : ε * ε = ε) :
    (∀ g ∈ jacGrp d, cutG V ε hε g ∈ jacGrp d) ∧
      ∀ (A L : HSp D) (o : OrthDec V₀ A L), ∀ g ∈ besGrp d o, cutG V ε hε g ∈ besGrp d o := by
  refine ⟨fun g hg => ?_, fun A L o g hg => ?_⟩
  · have H : (jacGrp d).map (cutG V ε hε) ≤ jacGrp d := by
      unfold jacGrp
      rw [Subgroup.map_sup]
      refine sup_le_sup (jac_cutG_map_NFlag V d.e ε hε) ?_
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      exact ⟨cutG V₀ ε hε h, (unitaryIdempotentCut_wittHyperbolicEmbedding_comm d ε hε h).symm⟩
    exact H ⟨g, hg, rfl⟩
  · have H : (besGrp d o).map (cutG V ε hε) ≤ besGrp d o := by
      unfold besGrp
      rw [Subgroup.map_sup]
      refine sup_le_sup (jac_cutG_map_NFlag V d.e ε hε) ?_
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      refine ⟨cutG A ε hε h, ?_⟩
      rw [embA_apply, embA_apply, unitaryIdempotentCut_wittHyperbolicEmbedding_comm, jac_cutG_emb_inl]
    exact H ⟨g, hg, rfl⟩

end GlobalTheory.FinPl.SetCut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitarySupportedSplitPlacesEqProdLocalPartsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitarySupported_splitPlaces_eq_prod_local_parts : ∀ (D : D7) (V : HSp D) (n : ℕ) (k : Fin n → Type) [∀ i, Field (k i)] [∀ i, ValuativeRel (k i)] [∀ i, TopologicalSpace (k i)] [∀ i, IsNonarchimedeanLocalField (k i)] (q : ∀ i, GlobalTheory.FinPl.SplitPt D (k i)), Function.Injective (fun i => (q i).v) → ∀ g ∈ GlobalTheory.FinPl.grpAt V (fun p => ∃ i, p = (q i).v), ∃ h : Fin n → GA D V, (∀ i, SuppAt (q i).e V (h i)) ∧ g = ((List.finRange n).map h).prod := by
  first | exact @GlobalTheory.SplitDecomp.prod_of_grpAt | exact GlobalTheory.SplitDecomp.prod_of_grpAt | (intros; apply GlobalTheory.SplitDecomp.prod_of_grpAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumDescendsToWittCore
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.Desc

theorem weil_data_descend : ∀ D : D7, Descent D :=
  fun D => GlobalTheory.T.weilDatumDescendsToWittCore_of_exists D (GlobalTheory.T.exists_weilDatum_hermitianPair D)

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilHomActionFixOfTrivialAtSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.SplitWeil ValuativeRel
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.OffFix

open scoped TensorProduct

variable {D : D7}

theorem idOff_mul_eq_zero {v : Pl D} {ε : AF D.host.F} (hε : IsPlaceIdem D v ε) {x y : AE D}
    (hx : x ∈ idOff D (· = v)) (hy : algebraMap (AF D.host.F) (AE D) ε * y = y) : x * y = 0 := by
  classical
  obtain ⟨α, hεα, hv, hw⟩ := hε
  obtain ⟨h0, hc⟩ := placeIdempotent_infinite_and_finite_components D v ε α hεα
  have hc' : ∀ w, compAt D w (algebraMap (AF D.host.F) (AE D) ε) = if w = v then 1 else 0 := by
    intro w
    rw [hc w]
    by_cases h : w = v
    · subst h; rw [if_pos rfl, hv]; rfl
    · rw [if_neg h, hw w h, TensorProduct.zero_tmul]
  have hx0 := (SetCut.mem_idOff_iff_mul (· = v) _ h0 hc' x).1 hx
  rw [← hy, ← mul_assoc, mul_comm x, hx0, zero_mul]

theorem supp_of_mem {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) {ε : AF D.host.F} (hε : IsPlaceIdem D p.v ε)
    (hsum : p.e + cA D p.e = algebraMap (AF D.host.F) (AE D) ε) (S T : HSp D) (LS : Lat S) (LT : Lat T) (u : WO S T)
    (hu : u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) ∨
      IsHalf p.e u ∨ IsHalf (cA D p.e) u) :
    ∀ i j, algebraMap (AF D.host.F) (AE D) ε * u i j = u i j := by
  rcases hu with hu | hu | hu
  · intro i j
    induction hu using AddSubgroup.closure_induction with
    | mem w hw =>
      obtain ⟨α, -, hα0, a, -, s, -, t, -, rfl⟩ := hw
      have hmem : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) ∈ idAt D (· = p.v) := by
        obtain ⟨h0, hc⟩ := placeIdempotent_infinite_and_finite_components D p.v _ α rfl
        rw [mem_supportedOnPlacesIdeal_iff_components_zero_elsewhere]
        exact ⟨h0, fun w hw => by rw [hc w, hα0 w hw, TensorProduct.zero_tmul]⟩
      rw [Matrix.of_apply]
      have hfac : (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) =
          algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) *
            ((1 : AF D.host.F) ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j)) := by
        rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
          Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hfac]
      exact ((placeIdem_acts D p.v ε hε).1 _).1 (Ideal.mul_mem_right _ _ hmem)
    | zero => simp
    | add x y _ _ hx hy => simp only [Matrix.add_apply, mul_add, hx, hy]
    | neg x _ hx => simp only [Matrix.neg_apply, mul_neg, hx]
  · intro i j
    have hce : algebraMap (AF D.host.F) (AE D) ε * p.e = p.e := by
      rw [← hsum, add_mul, p.split.1, mul_comm (cA D p.e), p.split.2.1, add_zero]
    rw [← hu i j, ← mul_assoc, hce]
  · intro i j
    have hce : algebraMap (AF D.host.F) (AE D) ε * cA D p.e = cA D p.e := by
      rw [← hsum, add_mul, p.split.2.1, zero_add, ← map_mul, p.split.1]
    rw [← hu i j, ← mul_assoc, hce]

theorem actO_eq_of_grpOff : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : SplitPt D k) (S T : HSp D) (LS : Lat S) (LT : Lat T) (g : GA D S) (h : GA D T),
    g ∈ grpOff S (· = p.v) → h ∈ grpOff T (· = p.v) → ∀ u : WO S T,
    (u ∈ latO S T (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E)) (· = p.v) ∨ IsHalf p.e u ∨
      IsHalf (cA D p.e) u) → actO S T g h u = u := by
  intro D k _ _ _ _ p S T LS LT g h hg hh u hu
  obtain ⟨ε, hε, hsum⟩ := p.above
  have hsupp := supp_of_mem p hε hsum S T LS LT u hu
  have hA : ∀ i j, (Formalism.L2.Theta.mt T h - 1) i j ∈ idOff D (· = p.v) :=
    (SetCut.mem_congGrp_iff T (idOff D (· = p.v)) h).1 hh
  have hB : ∀ i j, (Formalism.L2.Theta.mt S g⁻¹ - 1) i j ∈ idOff D (· = p.v) :=
    (SetCut.mem_congGrp_iff S (idOff D (· = p.v)) g⁻¹).1 (inv_mem hg)
  let U : Matrix (Fin T.rank) (Fin S.rank) (AE D) := u
  have hU : ∀ i j, algebraMap (AF D.host.F) (AE D) ε * U i j = U i j := hsupp
  have h1 : HMul.hMul (Formalism.L2.Theta.mt T h - 1) U = (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun l _ => idOff_mul_eq_zero hε (hA i l) (hU l j)
  have h2 : HMul.hMul U (Formalism.L2.Theta.mt S g⁻¹ - 1) = (0 : Matrix (Fin T.rank) (Fin S.rank) (AE D)) := by
    ext i j
    rw [Matrix.mul_apply, Matrix.zero_apply]
    exact Finset.sum_eq_zero fun l _ => by rw [mul_comm]; exact idOff_mul_eq_zero hε (hB l j) (hU i l)
  have e1 : HMul.hMul (Formalism.L2.Theta.mt T h) U = U := by rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1; exact h1
  have e2 : HMul.hMul U (Formalism.L2.Theta.mt S g⁻¹) = U := by rw [Matrix.mul_sub, Matrix.mul_one, sub_eq_zero] at h2; exact h2
  show HMul.hMul (HMul.hMul (Formalism.L2.Theta.mt T h) U) (Formalism.L2.Theta.mt S g⁻¹) = U
  rw [e1, e2]

end GlobalTheory.FinPl.OffFix

end
end

