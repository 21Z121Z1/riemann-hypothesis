import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3651
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0001
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0048
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0038
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0009
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0022
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0096
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0016
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0066
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0071
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0832
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedQuotientReal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.Bundle0095
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalMatchingOfHoweDualityStatement

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.EvaluationGridOfJoin
section
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.Mem.Top GlobalTheory.Mem.LiteralAutomorphy
namespace GlobalTheory.Mem.LiteralAutomorphy
theorem evaluation_grid_of_join : GlobalTheory.Published.HoweDualityReal → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → ∃ CF0 : ℝ, ∀ CF, CF0 ≤ CF → EvLgG (GridA CF) :=
  fun hw hm P hJ ht K WC LM TA FS =>
    GlobalTheory.Mem.LiteralAutomorphy.evLgG_gridA_of_exGrid
      (GlobalTheory.Mem.LiteralAutomorphy.exGrid_of (_root_.GlobalTheory.Mem.LiteralAutomorphy.exists_weilDeligne_of_localInputs P)
        (isEx_of_separates FS (_root_.GlobalTheory.RowEx.twisted_linear_bound P (_root_.GlobalTheory.PairLift.thetaPairLift_cuspidal_of_hypotheses P)) (_root_.GlobalTheory.RowEx.twisted_base_existence P (_root_.GlobalTheory.RowEx.twisted_constant_existence hw hm P K WC LM TA)))
        (nfAll_of GlobalTheory.RowEx.nfChars nfRoot (GlobalTheory.RowEx.nfPhase_of_sumOKK (_root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt P))
          (GlobalTheory.NFJetProof.nfJet_holds (_root_.GlobalTheory.RowClaim.rowSum_of_hypotheses_alt P) GlobalTheory.NormSum.inp_all (_root_.GlobalTheory.DictFree.twisted_dictionary_eventually_large P GlobalTheory.NormSum.inp_all))
          (_root_.GlobalTheory.RowEx.RatioField.twistRatio_mem_numberField P
            (GlobalTheory.ToricTransport.toricRatioConjugates_of_transport
              hJ.2.2.1)
            GlobalTheory.SqTop.fieldDat
            (GlobalTheory.SqTop.lNe_of_functionalEquation (GlobalTheory.Published.HeckeTateFunctionalEquation.abs ht) GlobalTheory.HeckeStrip.completedLBoundedInStrips
              GlobalTheory.SqTop.fieldDat))
          (_root_.GlobalTheory.RowEx.bottomField_isNumberField P GlobalTheory.NormSum.inp_all))
        (GlobalTheory.Mem.LiteralAutomorphy.nfSq_of_fieldDat GlobalTheory.NormSum.intSt_and_archSt.1 GlobalTheory.SqTop.fieldDat
          (GlobalTheory.ToricExist.torEx hJ.2.1 GlobalTheory.SqTop.fieldDat
            (GlobalTheory.SqTop.lNe_of_functionalEquation (GlobalTheory.Published.HeckeTateFunctionalEquation.abs ht) GlobalTheory.HeckeStrip.completedLBoundedInStrips
              GlobalTheory.SqTop.fieldDat))
          GlobalTheory.SqTop.BotSmallProof.botSmall_holds)
        CarryGrid.carryG (GlobalTheory.RowEx.carryW_of_weil P.weilRepresentationUnitaryPair) GlobalTheory.RowEx.carryS trEasy
        (PhaseCarry.trPhase_of_trFlip GlobalTheory.RowEx.Carry.flippedTensorsTransferToGrid_proof) (Jet.trJet_of_trFlip GlobalTheory.RowEx.Carry.flippedTensorsTransferToGrid_proof) GlobalTheory.RowEx.trBot_holds
        GlobalTheory.Mem.LiteralAutomorphy.trSq_holds keyFin_holds GlobalTheory.Mem.LiteralAutomorphy.gKeyFin)
end GlobalTheory.Mem.LiteralAutomorphy
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedSquareLocalMatching
section
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
namespace GlobalTheory.SquareLM
theorem twisted_square_local_matching : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.LocalMatching := by
  intro hH hP hT hL D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨Pr, ρ, q, q', hq, hq', hrk, hirr, hfac⟩ := _root_.GlobalTheory.T.twisted_quotient_real hH hP hT hL D ψ θ hψ hθ W W₁ X A A₁ B a b
  let ι := {x : D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ // x.2 ∈ lieAt X x.1}
  have hirr' : ∀ N : Submodule ℂ Pr, (∀ i : ι, ∀ x ∈ N, ρ i.1.1 i.1.2 x ∈ N) → N = ⊥ ∨ N = ⊤ :=
    fun N hN => hirr N fun τ Y hY x hx => hN ⟨(τ, Y), hY⟩ x hx
  have hS := GlobalTheory.dixmier_commutant_scalar ι Pr (fun i => ρ i.1.1 i.1.2) hrk hirr'
  obtain ⟨h0, hadd, hsmul, hfadd, hfsmul⟩ := GlobalTheory.FinFockLin.finF_lin D ψ θ hψ hθ true W X A B
  obtain ⟨h0', hadd', hsmul', hfadd', hfsmul'⟩ := GlobalTheory.FinFockLin.finF_lin D ψ θ hψ hθ false W₁ X A₁ B
  refine ⟨Pr, q, q', hq, hq', fun α β htr hexp => ⟨_root_.GlobalTheory.T.twist_triple_matches hH hP hT hL D ψ θ hψ hθ W W₁ X A A₁ B α β htr, ?_⟩⟩
  intro ωA ωB Pi rf rl p p' hm
  obtain ⟨hfa, hfb⟩ := hfac α β htr hexp ωA ωB Pi rf rl p p' hm
  let S : Submodule ℂ (WO W X → ℂ) :=
    { carrier := {f | IsFinF ψ θ true A B f}, add_mem' := fun hf hg => hadd _ _ hf hg, zero_mem' := h0,
      smul_mem' := fun c _ hf => hsmul c _ hf }
  let S' : Submodule ℂ (WO W₁ X → ℂ) :=
    { carrier := {f | IsFinF ψ θ false A₁ B f}, add_mem' := fun hf hg => hadd' _ _ hf hg, zero_mem' := h0',
      smul_mem' := fun c _ hf => hsmul' c _ hf }
  let βA : S →ₗ[ℂ] PolF D X.rank W.rank →ₗ[ℂ] Pi :=
    LinearMap.mk₂ ℂ (fun f P => p (fockF ψ θ true A B f.1 P)) (fun f g P => by
        rw [Submodule.coe_add, hfadd _ _ _ f.2 g.2, map_add])
      (fun c f P => by rw [Submodule.coe_smul, hfsmul _ _ _ f.2, map_smul]) (fun f P P' => by rw [map_add, map_add])
      (fun c f P => by rw [map_smul, map_smul])
  let βB : S' →ₗ[ℂ] PolF D X.rank W₁.rank →ₗ[ℂ] Pi :=
    LinearMap.mk₂ ℂ (fun f P => p' (fockF ψ θ false A₁ B f.1 P)) (fun f g P => by
        rw [Submodule.coe_add, hfadd' _ _ _ f.2 g.2, map_add])
      (fun c f P => by rw [Submodule.coe_smul, hfsmul' _ _ _ f.2, map_smul]) (fun f P P' => by rw [map_add, map_add])
      (fun c f P => by rw [map_smul, map_smul])
  have hspan : ∀ {M : HSp D} {ε : Bool} {A' : Fr M} {P : Type} [AddCommGroup P] [Module ℂ P] (pp : (WO M X → ℂ) →ₗ[ℂ] P),
      (algF ψ θ ε A' B).map pp = ⊤ →
      Submodule.span ℂ {y | ∃ f : {f // IsFinF ψ θ ε A' B f}, ∃ Q, y = pp (fockF ψ θ ε A' B f.1 Q)} = ⊤ := by
    intro M ε A' P _ _ pp h
    rw [← h, algF, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨f, Q, rfl⟩; exact ⟨_, ⟨f.1, Q, f.2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨f, Q, hf, rfl⟩, rfl⟩; exact ⟨⟨f, hf⟩, Q, rfl⟩
  obtain ⟨Pf, r, r', e, hr, hr', he, he'⟩ := GlobalTheory.SquareLM.productForm ι Pr Pi _ _ _ _ (fun i => ρ i.1.1 i.1.2) (fun i => rl i.1.1 i.1.2)
    q q' βA βB ⊤ ⊤ hq hq' hirr' hS
    (fun f _ => by
      obtain ⟨φ, h1, h2⟩ := hfa f.1 f.2
      exact ⟨φ, fun i => h1 i.1.1 i.1.2 i.2, LinearMap.ext fun P => h2 P⟩)
    (fun f _ => by
      obtain ⟨φ, h1, h2⟩ := hfb f.1 f.2
      exact ⟨φ, fun i => h1 i.1.1 i.1.2 i.2, LinearMap.ext fun P => h2 P⟩)
    (by
      rw [← hspan p hm.mapA.onto]
      congr 1; ext y
      exact ⟨fun ⟨f, _, Q, h⟩ => ⟨⟨f.1, f.2⟩, Q, h⟩, fun ⟨f, Q, h⟩ => ⟨⟨f.1, f.2⟩, trivial, Q, h⟩⟩)
    (by
      rw [← hspan p' hm.mapB.onto]
      congr 1; ext y
      exact ⟨fun ⟨f, _, Q, h⟩ => ⟨⟨f.1, f.2⟩, Q, h⟩, fun ⟨f, Q, h⟩ => ⟨⟨f.1, f.2⟩, trivial, Q, h⟩⟩)
  obtain ⟨r₀, hr₀⟩ := LinearMap.exists_extend r
  obtain ⟨r₀', hr₀'⟩ := LinearMap.exists_extend r'
  have e₁ : ∀ f (hf : IsFinF ψ θ true A B f), r₀ f = r ⟨f, hf⟩ := fun f hf => LinearMap.congr_fun hr₀ ⟨f, hf⟩
  have e₂ : ∀ f (hf : IsFinF ψ θ false A₁ B f), r₀' f = r' ⟨f, hf⟩ := fun f hf => LinearMap.congr_fun hr₀' ⟨f, hf⟩
  refine ⟨Pf, r₀, r₀', e, fun x => ?_, fun x => ?_, fun f hf P => ?_, fun f hf P => ?_⟩
  · obtain ⟨f, _, h⟩ := hr x; exact ⟨f.1, f.2, by rw [e₁ f.1 f.2]; exact h⟩
  · obtain ⟨f, _, h⟩ := hr' x; exact ⟨f.1, f.2, by rw [e₂ f.1 f.2]; exact h⟩
  · rw [e₁ f hf]; exact he ⟨f, hf⟩ trivial P
  · rw [e₂ f hf]; exact he' ⟨f, hf⟩ trivial P
end GlobalTheory.SquareLM
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_local_factors_match : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.LocalMatching := by
  first | exact @_root_.GlobalTheory.SquareLM.twisted_square_local_matching | exact _root_.GlobalTheory.SquareLM.twisted_square_local_matching | (intros; apply _root_.GlobalTheory.SquareLM.twisted_square_local_matching <;> assumption)
end
end

