import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0533
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0240
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0238
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralNormSqEqToL2
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0421
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0141
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0559
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0534
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1897
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0565
import Formalism.LocalToGlobal.InertKernelTheory.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0217
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0523
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0404
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0304
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0542
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0560
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactUnitaryRealPointsOfGramEqOneStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCompact_unitaryRealPoints_of_gram_eq_one : ∀ (D : D7) (V : HSp D), V.gram = 1 → IsCompact (GinfC V : Set (GA D V)) := by
  first | exact @GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one | exact GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one | (intros; apply GlobalTheory.GramOneCompact.isCompact_GinfC_of_gram_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocSubLocGen
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.CuspGKId

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

structure IsLocSub (τ : D.what₂.Tau) (B : Submodule ℂ (GA D V → ℂ)) : Prop where
  k : ∀ g, GlobalTheory.CuspGK.InK M τ g → ∀ f ∈ B, rTr V (atTau θ V τ g) f ∈ B
  lie : ∀ X ∈ lieAt V τ, ∀ f ∈ B, Rder θ V τ X f ∈ B

def locGen (τ : D.what₂.Tau) (ψ : GA D V → ℂ) : Submodule ℂ (GA D V → ℂ) :=
  sInf {B | ψ ∈ B ∧ IsLocSub θ M τ B}

theorem mem_locGen (τ : D.what₂.Tau) (ψ : GA D V → ℂ) : ψ ∈ locGen θ M τ ψ :=
  Submodule.mem_sInf.2 fun _ h => h.1

theorem isLocSub_locGen (τ : D.what₂.Tau) (ψ : GA D V → ℂ) : IsLocSub θ M τ (locGen θ M τ ψ) where
  k g hg f hf := Submodule.mem_sInf.2 fun B hB => hB.2.k g hg f (Submodule.mem_sInf.1 hf B hB)
  lie X hX f hf := Submodule.mem_sInf.2 fun B hB => hB.2.lie X hX f (Submodule.mem_sInf.1 hf B hB)

theorem locGen_le {τ : D.what₂.Tau} {ψ : GA D V → ℂ} {B : Submodule ℂ (GA D V → ℂ)} (hψ : ψ ∈ B)
    (hB : IsLocSub θ M τ B) : locGen θ M τ ψ ≤ B :=
  sInf_le ⟨hψ, hB⟩

end GlobalTheory.CuspGKId

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsNonzeroFockVacuumConjUnitVacuumNegSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNonzeroFockVacuum_conj_unitVacuum_negSpace : ∀ {D : D7} (S T : GlobalTheory.Grid.Node D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (f : WO S.V T.V → ℂ), GlobalTheory.Grid.IsVac ψ θ true S T f → GlobalTheory.Chain.IsVacVec ψ θ S.M T.M (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj id f) := by
  first | exact @GlobalTheory.VacCjNeg.isVacVec_cj_of_isVac_neg | exact GlobalTheory.VacCjNeg.isVacVec_cj_of_isVac_neg | (intros; apply GlobalTheory.VacCjNeg.isVacVec_cj_of_isVac_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSchrodingerThetaDatumAddAdelicSchwartz
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section

namespace GlobalTheory.SquareAgree

theorem isDatum_add : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ {Z : Type} [AddCommGroup Z]
    (crd : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE F E) → Z) (Φ Φ' : (Fin n × Fin d → AF F) → ℂ) (f f' : Z → ℂ),
    IsDatum M ψ crd Φ f → IsDatum M ψ crd Φ' f' → IsDatum M ψ crd (Φ + Φ') (f + f') := by
  intro F E _ _ _ _ _ σ n d Y Wd M ψ hψ Z _ crd Φ Φ' f f' h h'
  refine ⟨add_mem h.1 h'.1, fun u => ?_⟩
  have e : M.co.rho ψ u (Φ + Φ') = M.co.rho ψ u Φ + M.co.rho ψ u Φ' := by
    funext x
    simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.add_apply]
    ring
  rw [e, GlobalTheory.WeilM.thetaSum_add F (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ u Φ h.1)
    (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ u Φ' h'.1), h.2 u, h'.2 u]
  rfl

end GlobalTheory.SquareAgree
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsWeilDatumComplexConjugateOfNegHermitianSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.ChiGrid GlobalTheory.GridJoin
open scoped Pointwise TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chain GlobalTheory.ChainFr GlobalTheory.Chain.RealIt GlobalTheory.PairLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isWeilDatum_complexConjugate_of_negHermitianSpace : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GlobalTheory.Grid.WRep S T), GlobalTheory.Grid.IsWeil ψ true S T χS χT ω → IsWeilDatumO ψ S T χS⁻¹ χT⁻¹ (GlobalTheory.AdjTr.conjRep ω) := by
  first | exact @GlobalTheory.ConjWeilBack.weil_conjRep_of_neg | exact GlobalTheory.ConjWeilBack.weil_conjRep_of_neg | (intros; apply GlobalTheory.ConjWeilBack.weil_conjRep_of_neg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.JetKapIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC

noncomputable section

namespace GlobalTheory.RatMoveJets

def RatCoord {D : D7} (V : HSp D) (fr : GL (Fin V.rank) D.host.E) (g : GfC V)
    (U : Matrix.unitaryGroup (Fin V.rank) D.host.E) : Prop :=
  ∃ γ ∈ GQ V, finHom V γ = finHom V (g : GA D V) ∧
    Formalism.L2.Theta.mt V γ = (fr.1 * U.1 * (fr⁻¹ : GL (Fin V.rank) D.host.E).1).map (incA D)

section
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GlobalTheory.ChiGrid.GridData L sc}

def srcU : ∀ p : GlobalTheory.ChiGrid.Pair T, Matrix.unitaryGroup (Fin (G.V p.small).rank) D.host.E →
    Matrix.unitaryGroup (Fin (G.V p.big).rank) D.host.E → Matrix.unitaryGroup (Fin (G.pS p).rank) D.host.E
  | .chi _ _, _, U' => U'
  | .mu _ _ _, U, _ => U
  | .core _, _, U' => U'
  | .top _ _, U, _ => U

def tgtU : ∀ p : GlobalTheory.ChiGrid.Pair T, Matrix.unitaryGroup (Fin (G.V p.small).rank) D.host.E →
    Matrix.unitaryGroup (Fin (G.V p.big).rank) D.host.E → Matrix.unitaryGroup (Fin (G.pT p).rank) D.host.E
  | .chi _ _, U, _ => U
  | .mu _ _ _, _, U' => U'
  | .core _, U, _ => U
  | .top _ _, _, U' => U'

end

section
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def JetTh (ch : Choice R) (p : Pair T) (x : FinPt ch.G p.small) (y : FinPt ch.G p.big)
    (Θ : VC D (ch.G.pS p).rank (ch.G.pT p).rank → ℂ) : Prop :=
  ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) Θ)

theorem jetKap_iff (ch : Choice R) (p : Pair T) (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ : ℂ) :
    GlobalTheory.MovedKappaEx.JetKap ch p x y κ ↔ JetTh ch p x y (fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ)
      (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ)
        (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) :=
  Iff.rfl

end

end GlobalTheory.RatMoveJets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFiniteDecompositionAssembleRealPlaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Classical

noncomputable section

namespace GlobalTheory.KFinDecomp

theorem assemble_finset {ι : Type} [DecidableEq ι] {U : ι → Type} [∀ τ, AddCommGroup (U τ)] [∀ τ, Module ℂ (U τ)]
    {E : Type} [AddCommGroup E] [Module ℂ E] (𝒞 : Set E) (Ty : ι → E → Prop)
    (R : ∀ τ, U τ → U τ → (E → E) → Prop) (m : ι → ℕ) (a : ∀ τ, Fin (m τ) → U τ)
    (A : ∀ τ, Fin (m τ) → U τ → E → E)
    (hadd : ∀ τ j u, ∀ f ∈ 𝒞, ∀ f' ∈ 𝒞, A τ j u (f + f') = A τ j u f + A τ j u f')
    (hsmul : ∀ τ j u (c : ℂ), ∀ f ∈ 𝒞, A τ j u (c • f) = c • A τ j u f)
    (hmaps : ∀ τ j u, ∀ f ∈ 𝒞, A τ j u f ∈ 𝒞)
    (hkeep : ∀ τ j u τ', τ' ≠ τ → ∀ f ∈ 𝒞, Ty τ' f → Ty τ' (A τ j u f))
    (hcomm : ∀ τ j u τ', τ' ≠ τ → ∀ x y Φ, R τ' x y Φ → ∀ f ∈ 𝒞, A τ j u (Φ f) = Φ (A τ j u f))
    (hadd' : ∀ τ j, ∀ f ∈ 𝒞, ∀ u u', A τ j (u + u') f = A τ j u f + A τ j u' f)
    (hsmul' : ∀ τ j, ∀ f ∈ 𝒞, ∀ (c : ℂ) u, A τ j (c • u) f = c • A τ j u f)
    (hR : ∀ τ j, ∀ f ∈ 𝒞, ∀ u w Φ, R τ u w Φ → A τ j w f = Φ (A τ j u f))
    (hsum : ∀ τ, ∀ f ∈ 𝒞, Ty τ f → f = ∑ j, A τ j (a τ j) f)
    (ψ : E) (hψ : ψ ∈ 𝒞) (hTy : ∀ τ, Ty τ ψ) (s : Finset ι) :
    ∃ (κ : Type) (_ : Fintype κ) (T : κ → (∀ τ, U τ) → E) (u : κ → ∀ τ, U τ),
      (∀ k v, T k v ∈ 𝒞) ∧ (∀ k v, ∀ τ ∉ s, Ty τ (T k v)) ∧
      (∀ k v, ∀ τ ∉ s, ∀ w, T k (Function.update v τ w) = T k v) ∧
      (∀ k v, ∀ τ ∈ s, ∀ x y, T k (Function.update v τ (x + y)) =
        T k (Function.update v τ x) + T k (Function.update v τ y)) ∧
      (∀ k v, ∀ τ ∈ s, ∀ (c : ℂ) x, T k (Function.update v τ (c • x)) = c • T k (Function.update v τ x)) ∧
      (∀ k v, ∀ τ ∈ s, ∀ w Φ, R τ (v τ) w Φ → T k (Function.update v τ w) = Φ (T k v)) ∧
      ψ = ∑ k, T k (u k) := by
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Unit, inferInstance, fun _ _ => ψ, fun _ _ => 0, fun _ _ => hψ, fun _ _ τ _ => hTy τ,
      fun _ _ _ _ _ => rfl, ?_, ?_, ?_, ?_⟩
    · intro _ _ τ hτ; exact absurd hτ (Finset.notMem_empty τ)
    · intro _ _ τ hτ; exact absurd hτ (Finset.notMem_empty τ)
    · intro _ _ τ hτ; exact absurd hτ (Finset.notMem_empty τ)
    · simp
  | @insert τ₀ s hτ₀ ih =>
    obtain ⟨κ, hκ, T, u, hT𝒞, hTTy, hTfix, hTadd, hTsmul, hTR, hψs⟩ := ih

    refine ⟨κ × Fin (m τ₀), inferInstance, fun p v => A τ₀ p.2 (v τ₀) (T p.1 v),
      fun p => Function.update (u p.1) τ₀ (a τ₀ p.2), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p v
      exact hmaps _ _ _ _ (hT𝒞 _ _)
    · intro p v τ hτ
      have hne : τ ≠ τ₀ := fun h => hτ (h ▸ Finset.mem_insert_self τ₀ s)
      have hs : τ ∉ s := fun h => hτ (Finset.mem_insert_of_mem h)
      exact hkeep τ₀ p.2 (v τ₀) τ hne _ (hT𝒞 _ _) (hTTy _ _ τ hs)
    · intro p v τ hτ w
      have hne : τ ≠ τ₀ := fun h => hτ (h ▸ Finset.mem_insert_self τ₀ s)
      have hs : τ ∉ s := fun h => hτ (Finset.mem_insert_of_mem h)
      show A τ₀ p.2 (Function.update v τ w τ₀) (T p.1 (Function.update v τ w)) = A τ₀ p.2 (v τ₀) (T p.1 v)
      rw [Function.update_of_ne hne.symm, hTfix p.1 v τ hs w]
    · intro p v τ hτ x y
      show A τ₀ p.2 (Function.update v τ (x + y) τ₀) (T p.1 (Function.update v τ (x + y))) =
        A τ₀ p.2 (Function.update v τ x τ₀) (T p.1 (Function.update v τ x)) +
          A τ₀ p.2 (Function.update v τ y τ₀) (T p.1 (Function.update v τ y))
      by_cases h : τ = τ₀
      · subst h
        simp only [Function.update_self]
        rw [hTfix p.1 v τ hτ₀, hTfix p.1 v τ hτ₀, hTfix p.1 v τ hτ₀]
        exact hadd' τ p.2 _ (hT𝒞 _ _) x y
      · have hs : τ ∈ s := (Finset.mem_insert.1 hτ).resolve_left h
        rw [Function.update_of_ne (Ne.symm h), Function.update_of_ne (Ne.symm h),
          Function.update_of_ne (Ne.symm h), hTadd p.1 v τ hs x y]
        exact hadd τ₀ p.2 (v τ₀) _ (hT𝒞 _ _) _ (hT𝒞 _ _)
    · intro p v τ hτ c x
      show A τ₀ p.2 (Function.update v τ (c • x) τ₀) (T p.1 (Function.update v τ (c • x))) =
        c • A τ₀ p.2 (Function.update v τ x τ₀) (T p.1 (Function.update v τ x))
      by_cases h : τ = τ₀
      · subst h
        simp only [Function.update_self]
        rw [hTfix p.1 v τ hτ₀, hTfix p.1 v τ hτ₀]
        exact hsmul' τ p.2 _ (hT𝒞 _ _) c x
      · have hs : τ ∈ s := (Finset.mem_insert.1 hτ).resolve_left h
        rw [Function.update_of_ne (Ne.symm h), Function.update_of_ne (Ne.symm h),
          hTsmul p.1 v τ hs c x]
        exact hsmul τ₀ p.2 (v τ₀) c _ (hT𝒞 _ _)
    · intro p v τ hτ w Φ hRw
      show A τ₀ p.2 (Function.update v τ w τ₀) (T p.1 (Function.update v τ w)) =
        Φ (A τ₀ p.2 (v τ₀) (T p.1 v))
      by_cases h : τ = τ₀
      · subst h
        rw [Function.update_self, hTfix p.1 v τ hτ₀]
        exact hR τ p.2 _ (hT𝒞 _ _) (v τ) w Φ hRw
      · have hs : τ ∈ s := (Finset.mem_insert.1 hτ).resolve_left h
        rw [Function.update_of_ne (Ne.symm h), hTR p.1 v τ hs w Φ hRw]
        exact (hcomm τ₀ p.2 (v τ₀) τ h (v τ) w Φ hRw _ (hT𝒞 _ _)).symm ▸ rfl
    ·
      have hterm : ∀ k, T k (u k) = ∑ j, A τ₀ j (a τ₀ j) (T k (u k)) := fun k =>
        hsum τ₀ _ (hT𝒞 _ _) (hTTy _ _ τ₀ hτ₀)
      rw [Fintype.sum_prod_type, hψs]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hterm k]
      refine Finset.sum_congr rfl fun j _ => ?_
      show A τ₀ j (a τ₀ j) (T k (u k)) =
        A τ₀ j (Function.update (u k) τ₀ (a τ₀ j) τ₀) (T k (Function.update (u k) τ₀ (a τ₀ j)))
      rw [Function.update_self, hTfix k (u k) τ₀ hτ₀]

theorem assemble_places : ∀ (D : D7) (θ : InfFam D) (N : GlobalTheory.Grid.Node D) (𝒞 : Set (GA D N.V → ℂ)) (Ty : D.what₂.Tau → (GA D N.V → ℂ) → Prop), (∀ f ∈ 𝒞, Continuous f) → (∀ τ, GlobalTheory.KFinDecomp.DecompAt θ N 𝒞 Ty τ) → ∀ ψ ∈ 𝒞, (∀ τ, Ty τ ψ) → ∃ (n : ℕ) (T₀ : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M) (u : Fin n → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M), (∀ j v, T₀ j v ∈ 𝒞) ∧ (∀ j, ∀ τ, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = N.M.rep τ k (v τ) → T₀ j (Function.update v τ w) = rTr N.V (atTau θ N.V τ k) (T₀ j v)) ∧ (∀ j, ∀ τ, ∀ X ∈ lieAt N.V τ, ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KVec N.M) (w : GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ), (w : N.M.H τ) = dRep (N.M.rep τ) X (v τ) → T₀ j (Function.update v τ w) = Rder θ N.V τ X (T₀ j v)) ∧ ψ = ∑ j, T₀ j (u j) := by
  intro D θ N 𝒞 Ty hcont hdec ψ hψ hTy
  unfold GlobalTheory.KFinDecomp.DecompAt at hdec
  choose m a A hop hlin hsum using hdec

  have hK : ∀ τ, ∀ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, k ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := by
    intro τ k hk
    have hu : IsUnit (N.M.fr τ).det := (Matrix.isUnit_iff_isUnit_det _).1 (N.M.fr_unit τ)
    have h := (GlobalTheory.Chain.RealLine.Semi.conj_compact N.M τ (k := N.M.fr τ * k * (N.M.fr τ)⁻¹) hk).1
    have he : (N.M.fr τ)⁻¹ * (N.M.fr τ * k * (N.M.fr τ)⁻¹) * N.M.fr τ = k :=
      calc (N.M.fr τ)⁻¹ * (N.M.fr τ * k * (N.M.fr τ)⁻¹) * N.M.fr τ
          = ((N.M.fr τ)⁻¹ * N.M.fr τ) * k * ((N.M.fr τ)⁻¹ * N.M.fr τ) := by simp only [mul_assoc]
        _ = k := by rw [Matrix.nonsing_inv_mul _ hu, one_mul, mul_one]
    rwa [he] at h

  let R : ∀ τ, GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ →
      ((GA D N.V → ℂ) → (GA D N.V → ℂ)) → Prop := fun τ x y Φ =>
    (∃ k ∈ GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.maxCpt N.M τ, (y : N.M.H τ) = N.M.rep τ k x ∧
        Φ = fun f => rTr N.V (atTau θ N.V τ k) f) ∨
      (∃ X ∈ lieAt N.V τ, (y : N.M.H τ) = dRep (N.M.rep τ) X x ∧ Φ = fun f => Rder θ N.V τ X f)
  have hcomm : ∀ τ j u τ', τ' ≠ τ → ∀ x y Φ, R τ' x y Φ → ∀ f ∈ 𝒞, A τ j u (Φ f) = Φ (A τ j u f) := by
    rintro τ j u τ' hne x y Φ (⟨k, hk, -, rfl⟩ | ⟨X, hX, -, rfl⟩) f hf
    · exact (hop τ j u).tr τ' hne k (hK τ' k hk) f hf
    · exact (hop τ j u).lie τ' hne X hX f hf
  have hRel : ∀ τ j, ∀ f ∈ 𝒞, ∀ x y Φ, R τ x y Φ → A τ j y f = Φ (A τ j x f) := by
    rintro τ j f hf x y Φ (⟨k, hk, hy, rfl⟩ | ⟨X, hX, hy, rfl⟩)
    · exact (hlin τ j f hf).2.2.1 k hk x y hy
    · exact (hlin τ j f hf).2.2.2 X hX x y hy
  obtain ⟨κ, hκ, T, u, hT𝒞, -, -, hTadd, hTsmul, hTR, hψT⟩ :=
    GlobalTheory.KFinDecomp.assemble_finset (U := fun τ => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ) 𝒞 Ty R m a A
      (fun τ j x f hf f' hf' => (hop τ j x).add f f' (hcont f hf) (hcont f' hf'))
      (fun τ j x c f hf => (hop τ j x).smul c f (hcont f hf))
      (fun τ j x f hf => (hop τ j x).maps f hf)
      (fun τ j x τ' hne f hf h' => (hop τ j x).keep τ' hne f hf h')
      hcomm
      (fun τ j f hf x x' => (hlin τ j f hf).1 x x')
      (fun τ j f hf c x => (hlin τ j f hf).2.1 c x)
      hRel hsum ψ hψ hTy Finset.univ

  let e := Fintype.equivFin κ
  let T₀ : Fin (Fintype.card κ) → GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.KMap N.M := fun j =>
    (⟨T (e.symm j),
      fun v τ x y => by convert hTadd (e.symm j) v τ (Finset.mem_univ τ) x y,
      fun v τ c x => by convert hTsmul (e.symm j) v τ (Finset.mem_univ τ) c x⟩ :
      MultilinearMap ℂ (fun τ => GlobalTheory.IndefiniteRowSideFullHecke.KTypeExtension.kFin N.M τ) (GA D N.V → ℂ))
  refine ⟨Fintype.card κ, T₀, fun j => u (e.symm j), fun j v => hT𝒞 (e.symm j) v, ?_, ?_, ?_⟩
  · intro j τ k hk v w hw
    exact hTR (e.symm j) v τ (Finset.mem_univ τ) w _ (Or.inl ⟨k, hk, hw, rfl⟩)
  · intro j τ X hX v w hw
    exact hTR (e.symm j) v τ (Finset.mem_univ τ) w _ (Or.inr ⟨X, hX, hw, rfl⟩)
  · rw [hψT]
    exact (Equiv.sum_comp e.symm (fun k => T k (u k))).symm

end GlobalTheory.KFinDecomp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.KStableOfIsGKSub
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.KTypeProj

section Gen

variable {M ι : Type} [AddCommGroup M] [Module ℂ M]

def typeSpan (ρ : ι → M →ₗ[ℂ] M) (Y₀ G : Submodule ℂ M) : Submodule ℂ M :=
  ⨆ (T : M →ₗ[ℂ] M) (_ : Y₀.map T ≤ G ∧ ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)), Y₀.map T

theorem typeSpan_le (ρ : ι → M →ₗ[ℂ] M) (Y₀ G : Submodule ℂ M) : typeSpan ρ Y₀ G ≤ G :=
  iSup₂_le fun _ h => h.1

theorem le_typeSpan (ρ : ι → M →ₗ[ℂ] M) {Y₀ G : Submodule ℂ M} (h : Y₀ ≤ G) : Y₀ ≤ typeSpan ρ Y₀ G := by
  have h1 : Y₀.map LinearMap.id ≤ typeSpan ρ Y₀ G :=
    le_iSup₂_of_le (f := fun (T : M →ₗ[ℂ] M) (_ : Y₀.map T ≤ G ∧ ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)) => Y₀.map T)
      LinearMap.id ⟨by rwa [Submodule.map_id], fun _ _ _ => rfl⟩ le_rfl
  rwa [Submodule.map_id] at h1

theorem map_le_typeSpan (ρ : ι → M →ₗ[ℂ] M) {Y₀ G : Submodule ℂ M} (T : M →ₗ[ℂ] M) (hT : Y₀.map T ≤ G)
    (hc : ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)) : Y₀.map T ≤ typeSpan ρ Y₀ G :=
  le_iSup₂_of_le (f := fun (T : M →ₗ[ℂ] M) (_ : Y₀.map T ≤ G ∧ ∀ i, ∀ w ∈ Y₀, T (ρ i w) = ρ i (T w)) => Y₀.map T)
    T ⟨hT, hc⟩ le_rfl

end Gen

variable {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) {V : HSp D} {S : D.what₂.Tau → SPar}
  (M : Formalism.IndefR.Mult.DSModel V S)

def rTrL (k : GA D V) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) where
  toFun := rTr V k
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem rTrL_apply (k : GA D V) (f : GA D V → ℂ) : rTrL k f = rTr V k f := rfl

def KIdx : Type := {p : D.what₂.Tau × Matrix (Fin V.rank) (Fin V.rank) ℂ // GlobalTheory.CuspGK.InK M p.1 p.2}

def rhoK (i : KIdx M) : (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ) := rTrL (atTau θ V i.1.1 i.1.2)

def KStable (Y : Submodule ℂ (GA D V → ℂ)) : Prop :=
  ∀ τ g, GlobalTheory.CuspGK.InK M τ g → ∀ f ∈ Y, rTr V (atTau θ V τ g) f ∈ Y

theorem kStable_iff (Y : Submodule ℂ (GA D V → ℂ)) : KStable θ M Y ↔ ∀ i, ∀ y ∈ Y, rhoK θ M i y ∈ Y :=
  ⟨fun h i y hy => h i.1.1 i.1.2 i.2 y hy, fun h τ g hg y hy => h ⟨(τ, g), hg⟩ y hy⟩

theorem kStable_inf {Y Y' : Submodule ℂ (GA D V → ℂ)} (h : KStable θ M Y) (h' : KStable θ M Y') :
    KStable θ M (Y ⊓ Y') :=
  fun τ g hg f hf => ⟨h τ g hg f hf.1, h' τ g hg f hf.2⟩

theorem kStable_gkGen (ψ : GA D V → ℂ) : KStable θ M (GlobalTheory.CuspGK.gkGen θ M ψ) :=
  (GlobalTheory.CuspGK.isGKSub_gkGen θ M ψ).k

theorem kStable_of_isGKSub {A : Submodule ℂ (GA D V → ℂ)} (h : GlobalTheory.CuspGK.IsGKSub θ M A) : KStable θ M A := h.k

end GlobalTheory.KTypeProj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelInductionFromPairsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_induction_from_pairs : GlobalTheory.FunPr.Hypotheses₂ → PairEx → RowModels → RowStep := by
  first | exact @GlobalTheory.RowArrow.rowStep | exact GlobalTheory.RowArrow.rowStep | (intros; apply GlobalTheory.RowArrow.rowStep <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedTensorFactorMemCoeffFieldStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest Formalism.IndefR.WeilFull GlobalTheory.RowClaim
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedTensorFactor_mem_coeffField : ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A) (CF b : ℝ), HidaSetting large₂ R F → ch.Is → ch.AtScale CF b → ch.FieldOK → ∀ (t : T) (Φ : ch.G.Datum), ch.S.SumOK t Φ → ∀ β ∈ ch.S.supp t Φ, ∀ (w : locPl ch.G t) (S : (locGrid ch.G t w).Args → ℂ), (∀ z, S z ∈ Set.range D.what₂.embLL) → ∀ z, moved (locGrid ch.G t w) (keepAt ch.G w) ((repsAt ch.G t w).elt (β w)) S z ∈ Set.range D.what₂.embLL := by
  first | exact @GlobalTheory.MovedField.moved_mem | exact GlobalTheory.MovedField.moved_mem | (intros; apply GlobalTheory.MovedField.moved_mem <;> assumption)
end

