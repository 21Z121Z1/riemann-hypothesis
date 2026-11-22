import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0779
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0517
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0538
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0550
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0562
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0780
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0563
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0127
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0482
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0778
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0714
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLocalGroupsNormalFramesSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0681
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0777

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitModulusScalarLocalStatement
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

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_modulus_scalar_local : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ₀ : ℂ, Mod1All κ₀ ∧
    (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ₀‖ = 1) ∧
    ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ₀ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  first | exact @GlobalTheory.MovedKappaEx.exists_kappa | exact GlobalTheory.MovedKappaEx.exists_kappa | (intros; apply GlobalTheory.MovedKappaEx.exists_kappa <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantInnerVertexLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} in

theorem colMapV_congr (S : GridChoice W U) (t : T)
    (v v' : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ) (x x' : ∀ j, FinPt G (.top j))
    (h : ∀ j (hj : j < D.R.m), fockComp W S.N.frC (.top t j) (v ⟨j, hj⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) =
      fockComp W S.N.frC (.top t j) (v' ⟨j, hj⟩) (x' j * S.N.u _) (x' (j + 1) * S.N.u _)) :
    colMapV S t v x = colMapV S t v' x' := by
  have e : (fun j => if hj : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (v ⟨j, hj⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) else 0) =
      (fun j => if hj : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (v' ⟨j, hj⟩) (x' j * S.N.u _) (x' (j + 1) * S.N.u _) else 0) := by
    funext j
    by_cases hj : j < D.R.m
    · rw [dif_pos hj, dif_pos hj, h j hj]
    · rw [dif_neg hj, dif_neg hj]
  unfold colMapV
  rw [e]

theorem pairPts_update_top : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (j : ℕ) (hj : 0 < j) (hjm : j < D.R.m) (k : FinPt G (.top j)),
      finG (G.V (.top j)) k ∈ S.levTop t Φ β j hjm →
      pairPts S τ (Function.update x j (x j * k)) y (Ψ (Function.update x j (x j * k) 0)) (F (y 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  intro D T L sc G W U S t Φ β τ μ₀ hL hde hc ht hβ hτ hv Ψ F x y j hj hjm k hk
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  have hx0 : Function.update x (j + 1) (x (j + 1) * k) 0 = x 0 := Function.update_of_ne (by omega) _ _
  rw [hx0, pairPts_eq_pairV, pairPts_eq_pairV]
  set u := S.N.u (.top (j + 1)) with hu
  set g : FinPt G (.top (j + 1)) := u⁻¹ * k * u with hg
  have thv : ∀ d ∈ τ.support, ∀ j' : Fin D.R.m, IsThetaFunO W.ψ (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) (S.Z.vec (d.1 j')) :=
    fun d hd j' => GlobalTheory.VecThetaDef.vec_isThetaFunO S.Z (d.1 j') (show j'.1 + 1 ≤ D.R.m by omega) (by simp [Pair.InRange, Node.InRange]; try omega) ((hv d hd).1 j')
  have hcol : ∀ d ∈ τ.support, colMapV S t (fun j' => S.Z.vec (d.1 j')) (Function.update x (j + 1) (x (j + 1) * k)) =
      colMapV S t (movedCol S d j hjm g) x := by
    intro d hd
    refine colMapV_congr S t _ _ _ _ fun j' hj' => ?_
    by_cases h1 : j = j'
    · subst h1
      have hA := GlobalTheory.FockTranslate.fockComp_translate W S.N.frC t j (by omega) _ (thv d hd ⟨j, hj'⟩) (x j * S.N.u _) 1 (x (j + 1) * u) g
      rw [mul_one] at hA
      have e1 : x (j + 1) * k * u = x (j + 1) * u * g := by rw [hg]; group
      have m1 : (⟨j, hj'⟩ : Fin D.R.m) ≠ ⟨j + 1, hjm⟩ := by intro h; simp [Fin.ext_iff] at h
      rw [Function.update_of_ne (by omega : j ≠ j + 1), Function.update_self, e1, hA, movedCol,
        Function.update_of_ne m1, Function.update_self]
      try simp only [OneMemClass.coe_one]
      all_goals rfl
    · by_cases h2 : j + 1 = j'
      · subst h2
        have hA := GlobalTheory.FockTranslate.fockComp_translate W S.N.frC t (j + 1) (by omega) _ (thv d hd ⟨j + 1, hj'⟩) (x (j + 1) * u) g (x (j + 1 + 1) * S.N.u _) 1
        rw [mul_one] at hA
        have e1 : x (j + 1) * k * u = x (j + 1) * u * g := by rw [hg]; group
        rw [Function.update_self, Function.update_of_ne (by omega : j + 1 + 1 ≠ j + 1), e1, hA, movedCol, Function.update_self]
        try simp only [OneMemClass.coe_one]
        all_goals rfl
      · have m1 : (⟨j', hj'⟩ : Fin D.R.m) ≠ ⟨j + 1, hjm⟩ := by intro h; simp [Fin.ext_iff] at h; omega
        have m2 : (⟨j', hj'⟩ : Fin D.R.m) ≠ ⟨j, by omega⟩ := by intro h; simp [Fin.ext_iff] at h; omega
        rw [Function.update_of_ne (by omega : j' ≠ j + 1), Function.update_of_ne (by omega : j' + 1 ≠ j + 1), movedCol,
          Function.update_of_ne m1, Function.update_of_ne m2]
  have key : pairV S t τ (fun d j' => S.Z.vec (d.1 j')) (fun d i => S.Z.vec (d.2 i)) (Function.update x (j + 1) (x (j + 1) * k)) y =
      pairV S t τ (fun d => movedCol S d j hjm g) (fun d i => S.Z.vec (d.2 i)) x y := by
    unfold pairV
    refine Finsupp.sum_congr fun d hd => ?_
    rw [hcol d hd]
  rw [key]
  refine congrArg (fun φ => φ (Ψ (x 0)) (F (y 0))) (GlobalTheory.ExpansionInvariance.pairV_eq_of_prodFun_eq S t τ _ _ _ _ ?_ ?_ (GlobalTheory.T.expansion_product_invariant_inner_vertex_level S hL hde hc ht hβ hτ hv j hjm k hk) x y)
  · intro d hd j'
    refine ⟨?_, thv d hd j'⟩
    by_cases h2 : j' = ⟨j + 1, hjm⟩
    · subst h2
      rw [movedCol, Function.update_self]
      exact (W.om_is _ (by simp [Pair.InRange, Node.InRange]; try omega)).om_pres _ _ (thv d hd _)
    · by_cases h1 : j' = ⟨j, by omega⟩
      · subst h1
        rw [movedCol, Function.update_of_ne h2, Function.update_self]
        exact (W.om_is _ (by simp [Pair.InRange, Node.InRange]; try omega)).om_pres _ _ (thv d hd _)
      · rw [movedCol, Function.update_of_ne h2, Function.update_of_ne h1]
        exact thv d hd j'
  · intro d hd i
    have h := GlobalTheory.VecThetaDef.vec_isThetaFunO S.Z (d.2 i) (show i.1 + 1 ≤ D.R.m ∧ D.R.m = D.R.m by omega) (show i.1 + 1 ≤ D.R.m ∧ D.R.m ≤ D.R.m by omega) ((hv d hd).2 i)
    exact ⟨h, h⟩

end GlobalTheory.ExpansionInvariance

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExpansionPairingInvariantInnerVertexLevelTer
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansionPairing_invariant_innerVertex_level : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T} {Φ : G.Datum} {β : CosFam G t} {τ : PureDat G t →₀ ℂ} {μ₀ : T},
    L.Is μ₀ → (Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q)) → (∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) → t ∈ U → β ∈ S.supp t Φ → S.IsExpansion t Φ β τ →
    (∀ d ∈ τ.support, (∀ j, S.Z.HasVec (d.1 j)) ∧ ∀ i, S.Z.HasVec (d.2 i)) →
    ∀ (Ψ : FinPt G (.top 0) → VV ℂ (wt G (.top 0))) (F : FinPt G (.grid 0 D.R.m) → VV ℂ (listedWt G (.grid 0 D.R.m))),
    ∀ (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) (i : ℕ) (hi : 0 < i) (him : i < D.R.m) (k : FinPt G (.grid i D.R.m)),
      finG (G.V (.grid i D.R.m)) k ∈ S.levRow t i him.le →
      pairPts S τ x (Function.update y i (y i * k)) (Ψ (x 0)) (F (Function.update y i (y i * k) 0)) = pairPts S τ x y (Ψ (x 0)) (F (y 0)) := by
  first | exact @GlobalTheory.RowVertexInv.pairPts_update_row | exact GlobalTheory.RowVertexInv.pairPts_update_row | (intros; apply GlobalTheory.RowVertexInv.pairPts_update_row <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstColumnVectorSumFormulaStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.first_column_vector_sum_formula : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
    ∀ (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J)
      (xs : ∀ j : Fin D.R.m, WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)))
      (ys : ∀ i : Fin D.R.m, WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T))),
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) *
        (τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) *
          ∏ i, Function.update (fun i => ch.S.Z.vec (d.2 i)) (GlobalTheory.FirstRowVertex.firstIx D)
            (GlobalTheory.FirstRowVertex.rowShift0 ch.S.toGridChoice k (ch.S.Z.vec (d.2 (GlobalTheory.FirstRowVertex.firstIx D)))) i (ys i)) =
      τ.sum fun d c => c * (∏ j, ch.S.Z.vec (d.1 j) (xs j)) * ∏ i, ch.S.Z.vec (d.2 i) (ys i) := by
  first | exact @GlobalTheory.FirstRowDatum.main_law | exact GlobalTheory.FirstRowDatum.main_law | (intros; apply GlobalTheory.FirstRowDatum.main_law <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiBasePointCharacterTrivialDepthLattiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobi_basePoint_character_trivial_depthLattice : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m) (a' : Mx D (G.V (.grid (2 * σ + 2) 0)).rank (σ + 1)), (F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a' ∈ latRow G (2 * σ + 2) → W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX (G.V (.grid (2 * σ + 2) 0)) (xFB F σ h')) ((F.dJ (σ + 1) h).extY (G.V (.grid (2 * σ + 2) 0)) a')) = 1 := by
  first | exact @GlobalTheory.CharXFB.charx_fb | exact GlobalTheory.CharXFB.charx_fb | (intros; apply GlobalTheory.CharXFB.charx_fb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselPiecesMutualAnnihilatorsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierJacobiToBessel_pieces_mutual_annihilators : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), FinLat (pcFB W F σ h h').A₂ ∧ (∀ a, MxAt (fun _ => True) a → (a ∈ (pcFB W F σ h h').A₁ ↔ ∀ a' ∈ (pcFB W F σ h h').A₂, W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX _ a) ((F.dJ (σ + 1) h).extY _ a')) = 1)) ∧ (∀ a', MxAt (fun _ => True) a' → (a' ∈ (pcFB W F σ h h').A₂ ↔ ∀ a ∈ (pcFB W F σ h h').A₁, W.ψ (symplO _ _ ((F.dJ (σ + 1) h).extX _ a) ((F.dJ (σ + 1) h).extY _ a')) = 1)) := by
  first | exact @GlobalTheory.AscFin.AnnPieces.pcFB_dualA | exact GlobalTheory.AscFin.AnnPieces.pcFB_dualA | (intros; apply GlobalTheory.AscFin.AnnPieces.pcFB_dualA <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GenericCharacterTrivialBesselStepUnitriangular
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.AscFin.UniBF

private theorem psiE_add_mul {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (a b : AE D) :
    psiE ψ (a + b) = psiE ψ a * psiE ψ b := by
  simp only [psiE, map_add, AddChar.map_add_eq_mul]

private theorem psiE_zero_one {D : D7} (ψ : AddChar (AF D.host.F) ℂ) : psiE ψ (0 : AE D) = 1 := by
  simp only [psiE, map_zero, AddChar.map_zero_eq_one]

theorem psiUni_pcBF : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u : UX D ρ,
    MxAt (fun _ => True) (u.1.1 - 1) → xZero (F.dJ ρ h) ⬝ u.1.1 - xZero (F.dJ ρ h) ∈ (pcBF W F ρ h).A₁ →
    psiUni W.ψ u.1 = 1 := by
  intro D hq T L μ0 hL sc G W Mv hM F hF ρ h u hu hx
  have hA := GlobalTheory.T.genericCharacter_trivial_superdiagonal_off_exceptional D hq T L μ0 hL sc G W Mv hM F hF ρ h
  have hB := GlobalTheory.T.additive_character_superdiag_trivial D hq T L μ0 hL sc G W Mv hM F hF ρ h
  set N : Mx D ρ ρ := u.1.1 - 1 with hNdef
  have hx' : (F.dB ρ h).extX _ ((F.dJ ρ h).jX ⬝ N) ∈ latRow G (2 * ρ + 1) := by
    have e : xZero (F.dJ ρ h) ⬝ u.1.1 - xZero (F.dJ ρ h) = (F.dJ ρ h).jX ⬝ N := by
      rw [hNdef, Matrix.mul_sub, Matrix.mul_one]; rfl
    rw [← e]; exact hx
  have hN : (F.dJ ρ h).pX ⬝ ((F.dB ρ h).extX _ ((F.dJ ρ h).jX ⬝ N) ⬝ (F.dB ρ h).jX) = N := by
    rw [HypDec.extX_apply, Matrix.mul_assoc, HypDec.pX_jX, Matrix.mul_one, ← Matrix.mul_assoc, HypDec.pX_jX,
      Matrix.one_mul]
  have key : ∀ i j : Fin ρ, j.1 = i.1 + 1 → psiE W.ψ (u.1.1 i j) = 1 := fun i j hij => by
    have hne : i ≠ j := fun e => by rw [e] at hij; omega
    have e1 : u.1.1 i j = N i j := by rw [hNdef, Matrix.sub_apply, Matrix.one_apply_ne hne, sub_zero]
    rw [e1]
    refine GlobalTheory.FinPl.PsiUnit.psiE_eq_one_of_local W.ψ W.ψ_std.1.1 (hu i j) fun v _ => ?_
    have ho := GlobalTheory.FinPlLoc.idem_mem_intAt (D := D) (· = v)
    by_cases hv : v ∈ G.pl.S0
    · have := hB _ hx' i j hij v hv _ ho
      rwa [hN] at this
    · have := hA _ hx' i j hij v hv _ ho
      rwa [hN] at this
  unfold psiUni upSum
  refine Finset.sum_induction _ (fun x => psiE W.ψ x = 1) (fun a b ha hb => by rw [psiE_add_mul, ha, hb, one_mul])
    (psiE_zero_one W.ψ) fun i _ => ?_
  refine Finset.sum_induction _ (fun x => psiE W.ψ x = 1) (fun a b ha hb => by rw [psiE_add_mul, ha, hb, one_mul])
    (psiE_zero_one W.ψ) fun j _ => ?_
  split_ifs with hij
  · exact key i j hij
  · exact psiE_zero_one W.ψ

example : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u : UX D ρ, MxAt (fun _ => True) (u.1.1 - 1) →
    xZero (F.dJ ρ h) ⬝ u.1.1 - xZero (F.dJ ρ h) ∈ (pcBF W F ρ h).A₁ → psiUni W.ψ u.1 = 1 := psiUni_pcBF

end GlobalTheory.AscFin.UniBF

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemBesselGroupOfLocalMatrixGridNode
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowRepBes
open GlobalTheory.LocGrp GlobalTheory.LocMod

theorem mem_bes {D : D7} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (p : Place D k)
    {A B : HSp D} {σ : ℕ} (d : HermitianOrthogonalExtensionData A B (2 * σ + 1) (-1)) (l : Fin σ → D.host.E) (hl : ∀ a, l a ≠ 0)
    {b b' : Matrix (Fin A.rank) (Fin A.rank) k} (hb : b * b' = 1) (hb' : b' * b = 1) {u : Fin (2 * σ + 1) → k}
    {Γ : Matrix (Fin A.rank ⊕ Fin (2 * σ + 1)) (Fin B.rank) k} (h1 : Γ * sumCols d p.π b u = 1) (h2 : sumCols d p.π b u * Γ = 1)
    {g : GA D B} (hg : SuppAt p.e B g) {x : GL (Fin A.rank ⊕ Fin (2 * σ + 1)) k}
    (e : x.val = Γ * ((mt B g).map p.π * sumCols d p.π b u)) (hx : x ∈ symR k (Fin A.rank) (2 * σ + 1)) :
    g ∈ besGrp (diagDec (besDec d rfl) l hl) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  have hσ : σ ≤ 2 * σ + 1 := by omega
  have hσ' : σ < 2 * σ + 1 := by omega
  let E : Fin A.rank ⊕ Fin 1 ≃ Fin (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)).rank := finSumFinEquiv
  let φ : D.host.E →+* k := p.π.comp (incA D)
  set dd := diagDec (besDec d rfl) l hl with hdd
  set o := GlobalTheory.OrthSumExists.orthDecHsum D A (GlobalTheory.SeeSaw.Model.nLine D) with ho
  let F : Frame k B.rank (Fin A.rank ⊕ Fin (2 * σ + 1)) := { β := sumCols d p.π b u, γ := Γ, βγ := h2, γβ := h1 }
  let FA : Frame k A.rank (Fin A.rank) := { β := b, γ := b', βγ := hb, γβ := hb' }
  let F₀ : Frame k (GlobalTheory.Doubling.hsum A (GlobalTheory.SeeSaw.Model.nLine D)).rank (Fin A.rank ⊕ Fin 1) :=
    { β := (fromBlocks b 0 0 (1 : Matrix (Fin 1) (Fin 1) k)).submatrix E.symm id
      γ := (fromBlocks b' 0 0 (1 : Matrix (Fin 1) (Fin 1) k)).submatrix id E.symm
      βγ := by
        refine (submatrix_mul_equiv _ _ _ (Equiv.refl _) _).trans ?_
        rw [fromBlocks_multiply]
        simp [hb]
      γβ := by
        refine (submatrix_mul_equiv _ _ _ E.symm _).trans ?_
        rw [fromBlocks_multiply]
        simp [hb'] }
  have hloc : p.IsLoc F g x := by
    refine ⟨hg, ?_⟩
    change _ = sumCols d p.π b u * x.val * Γ
    rw [e, ← Matrix.mul_assoc, h2, Matrix.one_mul, Matrix.mul_assoc, h2, Matrix.mul_one]
  have vX : ∀ r (i : Fin σ), φ (d.a r (Fin.castLE hσ i)) = φ (l i)⁻¹ * (dd.jX.map p.π) r i := fun r i => by
    change _ = _ * φ (((besDec d rfl).e * diagonal l) r i)
    rw [mul_diagonal, ← map_mul, mul_left_comm, inv_mul_cancel₀ (hl i), mul_one]; rfl
  have vY : ∀ r (i : Fin σ), φ (d.a r (Fin.castLE hσ i).rev) = φ (star (l i)) * (dd.jY.map p.π) r i :=
    fun r i => by
      change _ = _ * φ (((besDec d rfl).e' * diagonal fun a => (star (l a))⁻¹) r i)
      rw [mul_diagonal, ← map_mul, mul_left_comm, mul_inv_cancel₀ (star_ne_zero.2 (hl i)), mul_one]; rfl
  have core : ∀ {Z : Type} (X : Matrix (Fin A.rank ⊕ Fin 1) Z k), dd.j0.map p.π *
      X.submatrix E.symm id = fromCols ((frameMat B A d.ι).map φ) ((midCol d rfl).map φ) * X := fun X => by
    have e : dd.j0.map p.π = (fromCols ((frameMat B A d.ι).map φ) ((midCol d rfl).map φ)).submatrix id E.symm := by
      rw [← fromCols_map]; rfl
    exact (congrArg (· * X.submatrix E.symm id) e).trans (submatrix_mul_equiv _ _ _ E.symm _)
  have jA : dd.j0.map p.π * o.jA.map p.π = (frameMat B A d.ι).map φ := by
    have e : o.jA.map p.π = (fromRows (1 : Matrix (Fin A.rank) (Fin A.rank) k) (0 : Matrix (Fin 1) (Fin A.rank) k)).submatrix E.symm id := by
      rw [← Matrix.map_one φ (map_zero _) (map_one _), ← Matrix.map_zero φ (map_zero _), ← fromRows_map]; rfl
    rw [e, core, fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, add_zero]
  have jB : dd.j0.map p.π * o.jB.map p.π = (midCol d rfl).map φ := by
    have e : o.jB.map p.π = (fromRows (0 : Matrix (Fin A.rank) (Fin 1) k) (1 : Matrix (Fin 1) (Fin 1) k)).submatrix E.symm id := by
      rw [← Matrix.map_one φ (map_zero _) (map_one _), ← Matrix.map_zero φ (map_zero _), ← fromRows_map]; rfl
    refine (congrArg (dd.j0.map p.π * ·) e).trans ((core _).trans ?_)
    rw [fromCols_mul_fromRows, Matrix.mul_one, Matrix.mul_zero, zero_add]
  have fX : ∀ (i : Fin σ) r, F.β r (Sum.inr (Fin.castLE hσ i)) = u (Fin.castLE hσ i) * φ (l i)⁻¹ * (dd.jX.map p.π) r i :=
    fun i r => (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans ((congrArg (u _ * ·) (vX r i)).trans (mul_assoc _ _ _).symm))
  have fY : ∀ (i : Fin σ) r, F.β r (Sum.inr (Fin.castLE hσ i).rev) =
      u (Fin.castLE hσ i).rev * φ (star (l i)) * (dd.jY.map p.π) r i :=
    fun i r => (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans ((congrArg (u _ * ·) (vY r i)).trans (mul_assoc _ _ _).symm))
  have fZ : ∀ r, F.β r (Sum.inr ⟨σ, hσ'⟩) = u ⟨σ, hσ'⟩ * (dd.j0.map p.π * o.jB.map p.π) r (0 : Fin 1) := fun r =>
    (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans (congrArg (u _ * ·) (congrFun (congrFun jB r) (0 : Fin 1)).symm))
  have ec := core (fromBlocks b 0 0 (1 : Matrix (Fin 1) (Fin 1) k))
  rw [fromCols_mul_fromBlocks, Matrix.mul_zero, Matrix.mul_zero, add_zero, zero_add, Matrix.mul_one] at ec
  obtain ⟨Φ, hΦ⟩ := exists_hom p F
  have hN : N k (Fin A.rank) (2 * σ + 1) (σ + 1) ≤ (besGrp dd o).comap Φ := by
    refine (Subgroup.closure_le _).2 fun y hy => Subgroup.mem_sup_left (flag_of_strict p dd F₀ F
      (Sum.elim (Sum.map id fun _ => ⟨σ, hσ'⟩)
        (Sum.elim (fun i : Fin σ => Sum.inr (Fin.castLE hσ i)) fun i : Fin σ => Sum.inr (Fin.castLE hσ i).rev)) ?_
      (Sum.elim (Sum.elim (fun _ => 1) fun _ => u ⟨σ, hσ'⟩)
        (Sum.elim (fun i => u (Fin.castLE hσ i) * φ (l i)⁻¹) fun i => u (Fin.castLE hσ i).rev * φ (star (l i)))) ?_
      (GlobalTheory.RootEx.lev (σ + 1)) ?_ (hΦ y) fun r s hrs => by rw [Matrix.sub_apply, hy r s hrs, sub_self])
    · rintro (a | j)
      · exact ⟨Sum.inl (Sum.inl a), rfl⟩
      · rcases lt_trichotomy j.val σ with h | h | h
        · exact ⟨Sum.inr (Sum.inl ⟨j.val, h⟩), rfl⟩
        · exact ⟨Sum.inl (Sum.inr 0), congrArg Sum.inr (Fin.ext h.symm)⟩
        · exact ⟨Sum.inr (Sum.inr ⟨2 * σ - j.val, by omega⟩), congrArg Sum.inr (Fin.ext (by
            simp only [Fin.val_rev, Fin.val_castLE]; omega))⟩
    · rintro r ((a | a) | i | i)
      · exact (congrFun (congrFun ec r) (Sum.inl a)).symm.trans (one_mul _).symm
      · exact (mul_diagonal u _ _ _).trans ((mul_comm _ _).trans (congrArg (u _ * ·) (congrFun (congrFun ec r) (Sum.inr a)).symm))
      · exact fX i r
      · exact fY i r
    · rintro ((a | a) | i | i)
      · rfl
      · rfl
      · rfl
      · have := i.2
        simp only [GlobalTheory.RootEx.lev, wlev, Sum.elim_inr, Fin.val_rev, Fin.val_castLE]
        omega
  have hle : symR k (Fin A.rank) (2 * σ + 1) ≤ (besGrp dd o).comap Φ := by
    rw [symR, symN_odd]
    refine sup_le ?_ hN
    rintro _ ⟨g₀, rfl⟩
    obtain ⟨h, hh⟩ := Witness.exists_isLoc p FA g₀
    have eA : mt B (dd.emb0 (o.emb (h, 1))) ⬝ (dd.j0 ⬝ o.jA) = dd.j0 ⬝ o.jA ⬝ mt A h := by
      rw [cancel₂ (dd.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, o.emb_jA, Matrix.mul_assoc]
    have eB : mt B (dd.emb0 (o.emb (h, 1))) ⬝ (dd.j0 ⬝ o.jB) = dd.j0 ⬝ o.jB := by
      rw [cancel₂ (dd.wittDecomp_anisotropicEmbedding_inclAnisotropic _), Matrix.mul_assoc, o.emb_jB, GlobalTheory.MixModel.mt_one, Matrix.mul_one]
    have eZ := map_fix p eB
    rw [Matrix.map_mul] at eZ
    have hm : p.IsLoc F (dd.emb0 (o.emb (h, 1))) (embX (2 * σ + 1) g₀) := by
      refine ⟨suppAt_wittLeviEmbedding dd (suppAt_emb o hh.1), eq_embX F _ g₀ ((dd.j0 ⬝ o.jA).map p.π * FA.β) (fun r a => ?_)
        (intertwine p eA hh) fun j => ?_⟩
      · change ((frameMat B A d.ι).map φ * b) r a = _
        rw [Matrix.map_mul, jA]
      · rcases lt_trichotomy j.val σ with hj | hj | hj
        · exact fix_col (map_fix p (dd.wittDecomp_anisotropicEmbedding_inclX _)) _ ⟨j.val, hj⟩ (fX ⟨j.val, hj⟩)
        · obtain rfl : j = ⟨σ, hσ'⟩ := Fin.ext hj
          exact fix_col eZ _ (0 : Fin 1) fZ
        · obtain ⟨q, rfl⟩ : ∃ q : Fin σ, j = (Fin.castLE hσ q).rev :=
            ⟨⟨2 * σ - j.1, by omega⟩, Fin.ext (by simp only [Fin.val_rev, Fin.val_castLE]; omega)⟩
          exact fix_col (map_fix p (dd.wittDecomp_anisotropicEmbedding_inclY _)) _ q (fY q)
    change Φ _ ∈ besGrp _ _
    rw [isLoc_unique p (hΦ _) hm]
    exact Subgroup.mem_sup_right ⟨h, rfl⟩
  rw [isLoc_unique p hloc (hΦ x)]
  exact hle hx

end GlobalTheory.RowRepBes

namespace GlobalTheory.RowRepBes
open GlobalTheory.LocMod

theorem mem_besGrp_of_symR {D : D7} {A B : HSp D} {c σ : ℕ} (d : HermitianOrthogonalExtensionData A B c (-1)) (h : c = 2 * σ + 1)
    (l : Fin σ → D.host.E) (hl : ∀ a, l a ≠ 0) (w : Pl D.host.E) (β : GL (Fin A.rank) (Lev.EAf D))
    (β' : GL (Fin B.rank) (Lev.EAf D)) (u : Fin c → Kw w) (hF : IsSumFrame d w β β' u) {a b : ℕ} (ha : a = A.rank)
    (hb : b = B.rank) (hab : a + c = b) (p : Place D (Kw w)) (hp : piAt w = p.π) (g : GA D B) (hg : SuppAt p.e B g)
    (hx : frameGL hab (inBasis hb β' w (Lev.finE B g)) ∈ symR (Kw w) (Fin a) c) :
    g ∈ besGrp (diagDec (besDec d h) l hl) (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  subst h ha hb
  obtain ⟨Γ, h1, h2, e⟩ := frame_val d w hF
  rw [hp] at h1 h2 e
  exact mem_bes p d l hl (GlobalTheory.StdFrames.loc w β).mul_inv (GlobalTheory.StdFrames.loc w β).inv_mul h1 h2 hg (e g) hx

theorem mem_besGrp_of_locAt : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ {w : Pl D.host.E}, w ∈ locPl G t → ∀ (ew : AE D), Formalism.L2.NTheta.IsIdemAt ew w → ∀ {j σ : ℕ} (hj : j ≤ D.R.m) (hj' : j < D.R.m) (h' : j + 2 * σ + 2 = D.R.m) (h : GA D (G.V (.grid D.R.m j))), SuppAt ew _ h → GlobalTheory.RowRep.locAt S.B t w j hj h ∈ rowR (G := locGrid G t w) one_le_sLen (j := j) hj' → h ∈ besGrp (besDecAt G j σ h') (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  intro D T L sc G W U S t ht w hw ew hew j σ hj hj' h' h hs hx
  have he : IsIdemSum ew {w} := ⟨⟨fun _ => ew, fun PP hPP => by rw [Finset.mem_singleton.1 hPP]; exact hew,
    (Finset.sum_singleton (fun _ => ew) w).symm⟩, hew.1.2.1⟩
  obtain ⟨p, hp, rfl⟩ := GlobalTheory.PlcAtW.exists_plc D w ew he
  exact mem_besGrp_of_symR (G.rowDec j hj') (by omega) _ _ w _ _ _ (S.row t ht w hw j hj') (topRank_eq G t w hj)
    (rank_vertex G t w (X := (D.R.m, j)) ⟨le_rfl, hj⟩) _ p (RingHom.ext fun x => (hp.2.1 x).symm) h hs hx

end GlobalTheory.RowRepBes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelFourthStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negative_theta_level_fourth : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → ∀ τ, IsTypeAt R.θ (G.V (i + 1) j).V τ ((G.V (i + 1) j).S τ) (fun h => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) := by
  first | exact @GlobalTheory.ThetaLiftTypeX.lift_isTypeAt | exact GlobalTheory.ThetaLiftTypeX.lift_isTypeAt | (intros; apply GlobalTheory.ThetaLiftTypeX.lift_isTypeAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelThirdStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.negative_theta_level_third : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i < D.R.m → j ≤ D.R.m → ∀ Φ, IsThetaFunO R.ψ (GlobalTheory.Grid.neg (G.V (i + 1) j).V) (G.V i j).V Φ → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i j) φ → (∀ h, IntegrableOn (fun g => thetaKO (G.X i j).ω h g Φ * φ g) (G.meas t i j).fd (G.meas t i j).ν) → IsCuspFun (G.V (i + 1) j).V (fun h => ∫ g in (G.meas t i j).fd, thetaKO (G.X i j).ω h g Φ * φ g ∂(G.meas t i j).ν) := by
  first | exact @GlobalTheory.XArrowCusp.lift_isCuspFun | exact GlobalTheory.XArrowCusp.lift_isCuspFun | (intros; apply GlobalTheory.XArrowCusp.lift_isCuspFun <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalMapColumnsMemLatGIffMovedFinitePartStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj Formalism.IndefR.Datum ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.ChartRestriction.G.Geo.Tor
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalMap_columns_mem_latG_iff_moved_finitePart : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks),
    R.toLevCh.Is A.μ0 → ∀ (i : Fin D.R.m) (b : Matrix (Fin (Vc D i).rank) (Fin (Vc D i).rank) D.host.E),
    GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.IsONLatBasis (Vc D i) b → ∀ (y : GA D (Wc D i)) (Yr : Matrix (Fin (Wc D i).rank) (Fin (Vc D i).rank) D.host.E),
      (∀ a, (fun m => ∑ n, Yr m n * b n a) ∈ latG (Wc D i) y) ↔
        actO (Vc D i) (Wc D i) 1 y⁻¹ (ratW (Wc D i) (Vc D i) Yr - GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.realPt (Vc D i) (Wc D i) Yr) ∈
          latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True := by
  first | exact @GlobalTheory.ColSplit.cols_mem_iff | exact GlobalTheory.ColSplit.cols_mem_iff | (intros; apply GlobalTheory.ColSplit.cols_mem_iff <;> assumption)
end
end

