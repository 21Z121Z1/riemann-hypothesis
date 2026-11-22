import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0817
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0831
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0810
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0351
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LsumMapDomainSome
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0374

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstantTermExistenceFromHowe
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowEx

theorem constEx_of : GlobalTheory.Published.HoweDualityReal → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.SquareSt.WeilConvergence → GlobalTheory.SquareSt.LocalMatching → GlobalTheory.SquareSt.ThetaIntegralsAgree → ConstEx := by
  intro hw hm h1 h2 h3 h4 h5
  obtain ⟨C1, H1⟩ := GlobalTheory.T.matched_theta_integral_value h1 h2 h3 h4 h5
  obtain ⟨C2, H2⟩ := GlobalTheory.T.polynomial_route_submodule hw h1 h2 hm h3 h4 h5
  refine ⟨max C1 C2, fun ε CF hCF => ?_⟩
  obtain ⟨x1, K1⟩ := H1 ε CF (le_trans (le_max_left _ _) hCF)
  obtain ⟨x2, K2⟩ := H2 ε CF (le_trans (le_max_right _ _) hCF)
  refine ⟨max x1 x2, fun D large₂ he hx Γ _ _ Pl0 T A Ks _ _ _ R F hS => ?_⟩
  have k1 := K1 D large₂ he (le_trans (le_max_left _ _) hx) Γ Pl0 T A Ks R F hS
  have k2 := K2 D large₂ he (le_trans (le_max_right _ _) hx) Γ Pl0 T A Ks R F hS
  intro G W hW B
  obtain ⟨rm, hrm⟩ := GlobalTheory.RowTest.exists_match_over hS.core.lev hS.core.chain hW
  choose r hr1 hr2 hr3 hr4 using k2 G W hW B rm hrm
  let rel' : ∀ i j : ℕ, Submodule ℂ (PolRoute G (.grid i (j + 1)) (.grid (i + 1) (j + 1)) (.grid (i + 1) j) ×
      PolRoute G (.grid i (j + 1)) (.grid i j) (.grid (i + 1) j)) := fun i j =>
    if h : i < D.R.m ∧ j < D.R.m then r ⟨i, h.1⟩ ⟨j, h.2⟩ else rm.rel i j
  have e : ∀ i j : Fin D.R.m, rel' i j = r i j := fun i j => dif_pos ⟨i.2, j.2⟩
  let ρ : RealMatch W := { rm with
    rel := rel'
    onto_big := fun i j a => by
      by_cases h : i < D.R.m ∧ j < D.R.m
      · simp only [rel', dif_pos h]; exact hr1 ⟨i, h.1⟩ ⟨j, h.2⟩ a
      · simp only [rel', dif_neg h]; exact rm.onto_big i j a
    onto_small := fun i j b => by
      by_cases h : i < D.R.m ∧ j < D.R.m
      · simp only [rel', dif_pos h]; exact hr2 ⟨i, h.1⟩ ⟨j, h.2⟩ b
      · simp only [rel', dif_neg h]; exact rm.onto_small i j b
    proper := fun i j => by
      by_cases h : i < D.R.m ∧ j < D.R.m
      · simp only [rel', dif_pos h]; exact hr3 ⟨i, h.1⟩ ⟨j, h.2⟩
      · simp only [rel', dif_neg h]; exact rm.proper i j }
  have hρ : ρ.Over R := hrm
  have hc : ∀ i j t, ∃ c, IsSquareConst W B ρ t i j c := by
    intro i j t
    obtain ⟨c, hc⟩ := hr4 i j ρ rfl rfl (e i j) t
    refine ⟨c, fun M hM Θ Θ' hΘ z g g₁ hz => ?_⟩
    obtain ⟨J, hJ⟩ := k1 G W hW B ρ hρ t i j M hM Θ Θ' hΘ g g₁
    obtain ⟨z₀, hz₀, hconv₀, hid⟩ := hc M hM Θ Θ' hΘ g g₁
    rw [hJ z₀ hconv₀.2] at hid
    have hI : ∫ u in M.fd _, kerBig W Θ g g₁ u ∂M.ν _ = c * J := by
      apply mul_left_cancel₀ hz₀; rw [hid]; ring
    rw [hJ z hz.2, hI]; ring
  choose c hc using hc
  exact ⟨ρ, fun i j t => c i j t, hρ, fun i j t => hc i j t⟩

end GlobalTheory.RowEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalMatchingOfHoweDuality
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

theorem localMatching : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.LocalMatching := by
  intro hH hP hT hL D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨Pr, ρ, q, q', hq, hq', hrk, hirr, hfac⟩ := GlobalTheory.T.polynomial_representation_triple hH hP hT hL D ψ θ hψ hθ W W₁ X A A₁ B a b
  let ι := {x : D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ // x.2 ∈ lieAt X x.1}
  have hirr' : ∀ N : Submodule ℂ Pr, (∀ i : ι, ∀ x ∈ N, ρ i.1.1 i.1.2 x ∈ N) → N = ⊥ ∨ N = ⊤ :=
    fun N hN => hirr N fun τ Y hY x hx => hN ⟨(τ, Y), hY⟩ x hx
  have hS := GlobalTheory.dixmier_commutant_scalar ι Pr (fun i => ρ i.1.1 i.1.2) hrk hirr'
  obtain ⟨h0, hadd, hsmul, hfadd, hfsmul⟩ := GlobalTheory.FinFockLin.finF_lin D ψ θ hψ hθ true W X A B
  obtain ⟨h0', hadd', hsmul', hfadd', hfsmul'⟩ := GlobalTheory.FinFockLin.finF_lin D ψ θ hψ hθ false W₁ X A₁ B
  refine ⟨Pr, q, q', hq, hq', fun α β htr hexp => ⟨GlobalTheory.T.weil_triple_matching_exists hH hP hT hL D ψ θ hψ hθ W W₁ X A A₁ B α β htr, ?_⟩⟩
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

