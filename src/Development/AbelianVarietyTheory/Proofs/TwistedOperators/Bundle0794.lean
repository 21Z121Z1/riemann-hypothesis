import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0792
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsCoreLat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0012
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0521
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0547
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0617
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0646
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0571
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0793
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0600
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EpsVEqOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0697
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0698
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0700
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0696
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0699
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0715
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0717
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0674
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0776
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0705
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0707

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetFockVacuumDatumStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows GlobalTheory.CoreOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cosetFockVacuumDatum : DatumEx := by
  first | exact @GlobalTheory.CoreOnto.datumEx | exact GlobalTheory.CoreOnto.datumEx | (intros; apply GlobalTheory.CoreOnto.datumEx <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDegreeBoundFourierLiftedStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degree_bound_fourier_lifted : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X →
    ∃ n : D.what₂.Tau → ℕ, ∀ (κ : Measure (GinfC A')), κ.IsMulLeftInvariant → IsProbabilityMeasure κ →
      ∀ (t : T), ∀ x ∈ GfC A', ∀ h ∈ GfC WW, ∀ k : FVar D WW.rank A'.rank →₀ ℕ,
        ∃ (m : ℕ) (r : Fin m → ℂ) (U : Fin m → GlobalTheory.NormSum.Tup D A'.rank WW.rank n), (∀ p, IsAlgebraic ℚ (r p)) ∧
          ∫ g, X.ker' W.ψ W.θ t (MvPolynomial.monomial k 1) h (x * (g : GA D A')) ∂κ =
            ∑ p, r p * X.ker' W.ψ W.θ t (GlobalTheory.NormSum.minorPol D (U p)) h x := by
  first | exact @GlobalTheory.RealProj.avg_monomial | exact GlobalTheory.RealProj.avg_monomial | (intros; apply GlobalTheory.RealProj.avg_monomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticesEntireIntertwining
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

namespace GlobalTheory.MovedDict

theorem movedVacuum_dict : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (p : Pair _), DefPair D.R.m p →
    ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ∃ (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.pS p).rank → D.host.E))
    (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.pT p).rank → D.host.E)) (κ : ℂ), SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧
    Differentiable ℂ (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) ∧
    (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) →
      EqAt D q Ls (stdL D _) ∧ EqAt D q Lt (stdL D _) ∧ ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) ∧
    IsVacO ch.W.ψ ch.W.θ _ _ (ch.G.cartS ch.W.cart p) (ch.G.onT ch.W.cart p) (inV (frS ch.S.N p) Ls) (inV (frT ch.S.N p) Lt)
      (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p)) ∧
    (∀ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True),
      actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w ∈
        latO _ _ (inV (frS ch.S.N p) Ls) (inV (frT ch.S.N p) Lt) (fun _ => True)) ∧
    ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ *
            Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _)
              (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p) z) := by
  intro hPr hInp
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch hIs _ => ?_⟩⟩
  intro p hp x y
  obtain ⟨hSs, hSt⟩ := GlobalTheory.T.lattices_self_dual_moved_pair hPr hInp ch hIs p hp x y
  obtain ⟨κ, hκ, hu, hj⟩ := GlobalTheory.T.exists_unit_modulus_local_factor hPr hInp ch hIs p hp x y
  refine ⟨_, _, κ, hSs, hSt, hκ, GlobalTheory.T.differentiable_intertwining_pair hPr hInp ch hIs p hp x y, ?_, GlobalTheory.T.vacuum_vector_moved_pair hPr hInp ch hIs p hp x y,
    (GlobalTheory.T.lattice_orbit_vectors_moved_pair hPr hInp ch hIs p hp x y).1, hj⟩
  intro q _ hx hy
  refine ⟨?_, ?_, hu q hx hy⟩
  · rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩ <;> first | exact hy | exact hx
  · rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩ <;> first | exact hx | exact hy

end GlobalTheory.MovedDict
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPeriodGroupPointLiftingRowGroupLocalElemenStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_periodGroup_point_lifting_rowGroup_localElements : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (s : ℤˣ) t, ∀ j ∈ idx D, ∀ (hj : j ≤ D.R.m) (hj' : j < D.R.m)
    (δ : GA D (ch.G.V (.grid D.R.m j))), IsTilt ch.G j δ →
    ∀ l : ∀ w : locPl ch.G t, GL (Fin ((locGrid ch.G t w.1).rank (D.R.m, j))) (Kw w.1),
      (∀ w, l w ∈ rowR (G := locGrid ch.G t w.1) one_le_sLen (j := j) hj') →
      ∃ y, HasLoc t ch.S.B hj y (fun w => sgnAt ch.G t s w.1 j * l w * (sgnAt ch.G t s w.1 j)⁻¹) ∧
        δ * y * δ⁻¹ ∈ rowGrp ch.G j := by
  first | exact @GlobalTheory.RowLift.lift_rowR | exact GlobalTheory.RowLift.lift_rowR | (intros; apply GlobalTheory.RowLift.lift_rowR <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsScalarThetaRationalExpansion
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.RatVacAlg

theorem om_rat_vac_eq_smul_algComb : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∀ γ ∈ Formalism.L2.Theta.GQ A, ∀ a ∈ GinfC A, ∀ γ' ∈ Formalism.L2.Theta.GQ WW, ∀ a' ∈ GinfC WW,
      γ * a ∈ GfC A → γ' * a' ∈ GfC WW →
      ∃ (κ : ℂ) (F : WO (GlobalTheory.Grid.neg A) WW → ℂ), GlobalTheory.MovedAlg.IsAlgComb W.ψ (GlobalTheory.Grid.neg A) WW X.vac F ∧
        X.ω t (γ, γ') X.vac = κ • F := by
  intro D T _ L μ₀ sc G W i j A A' WW X hP hN hL hX t γ hγ a ha γ' hγ' a' ha' hfa hfa'
  have hI := hX.is
  have hom := hI.weil t
  have cS : ∀ τ, IsCartanInv (gramAt D (GlobalTheory.Grid.neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hI.rigW.2.2 τ).1
  have hsdS : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hI.rigA.1
  have hx : (GlobalTheory.Grid.ofSgn true A).symm (γ * a) ∈ GfC (GlobalTheory.Grid.neg A) := by
    show (GlobalTheory.Grid.ofSgn true A) ((GlobalTheory.Grid.ofSgn true A).symm (γ * a)) ∈ GfC A
    rw [MulEquiv.apply_symm_apply]
    exact hfa
  obtain ⟨κ₁, F, hF, hκ₁⟩ := GlobalTheory.T.weilDatum_finite_pair_vacuum_algebraic_combination hI.isVac hsdS hI.rigW.1 cS cT hom _ hx _ hfa'
  obtain ⟨C, -, hC⟩ := GlobalTheory.T.realPoint_acts_on_vacuum_by_algebraicScalar hX t γ hγ a ha γ' hγ' a' ha' hfa hfa'
  have e1 : X.ω t (γ * a, γ' * a') X.vac = κ₁ • F := hκ₁
  have e2 : X.ω t (γ * a, γ' * a') X.vac = C • X.ω t (γ, γ') X.vac := by
    rw [show ((γ * a, γ' * a') : GA D A × GA D WW) = (γ, γ') * (a, a') from rfl, map_mul, Module.End.mul_apply, hC,
      map_smul]
  have hv : X.vac ≠ 0 := by
    intro h0
    obtain ⟨⟨p, hp⟩, hn⟩ := hI.isVac.2.norm
    have h1 := hn p hp
    simp [h0, nrm2] at h1
  have hC0 : C ≠ 0 := by
    rintro rfl
    apply hv
    have h2 := congrArg (X.ω t (a, a')⁻¹) hC
    rw [zero_smul, map_zero, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2
    exact h2
  refine ⟨C⁻¹ * κ₁, F, hF, ?_⟩
  rw [mul_smul, ← e1, e2, smul_smul, inv_mul_cancel₀ hC0, one_smul]

end GlobalTheory.RatVacAlg

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSignFlatDictionaryAtOnePlaceLargeDepth
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FlatPlace GlobalTheory.LocMod GlobalTheory.SplitWeil
open GlobalTheory.SplitFlip (Grid Edge oppositePath)

namespace GlobalTheory.FlatPlace

theorem prod_range_pairs (g : ℕ → ℂ) (n : ℕ) : ∏ j ∈ Finset.range (2 * n), g j = ∏ l ∈ Finset.range n, g (2 * l) * g (2 * l + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.mul_succ, Finset.prod_range_succ, Finset.prod_range_succ, ih, Finset.prod_range_succ, mul_assoc]

theorem prod_fin_pairs {m : ℕ} (hm : Even m) (g : Fin m → ℂ) :
    ∏ j, g j = ∏ l : Fin (m / 2), g ⟨2 * l, by have := l.2; omega⟩ * g ⟨2 * l + 1, by have := l.2; omega⟩ := by
  have h2 : m = 2 * (m / 2) := by obtain ⟨a, ha⟩ := hm; omega
  let g' : ℕ → ℂ := fun j => if h : j < m then g ⟨j, h⟩ else 1
  have e1 : ∏ j, g j = ∏ j ∈ Finset.range m, g' j := by
    rw [Finset.prod_range]
    exact Finset.prod_congr rfl fun j _ => by simp only [g', dif_pos j.2]
  rw [e1, congrArg Finset.range h2, prod_range_pairs, Finset.prod_range]
  refine Finset.prod_congr rfl fun l _ => ?_
  have := l.2
  simp only [g']
  rw [dif_pos (by omega), dif_pos (by omega)]

theorem exists_unpair {Y : ℕ → Type} [∀ j, Nonempty (Y j)] {n : ℕ} (q : ∀ l : Fin n, Y (2 * l) × Y (2 * l + 1)) :
    ∃ x : ∀ j, Y j, ∀ l : Fin n, (x (2 * l), x (2 * l + 1)) = q l := by
  have h : ∀ j, ∃ y : Y j, ∀ l : Fin n, (j = 2 * l → HEq y (q l).1) ∧ (j = 2 * l + 1 → HEq y (q l).2) := fun j => by
    by_cases h1 : ∃ l : Fin n, j = 2 * l
    · obtain ⟨l, rfl⟩ := h1
      refine ⟨(q l).1, fun l' => ⟨fun e => ?_, fun e => by omega⟩⟩
      obtain rfl : l = l' := Fin.ext (by omega)
      rfl
    · by_cases h2 : ∃ l : Fin n, j = 2 * l + 1
      · obtain ⟨l, rfl⟩ := h2
        refine ⟨(q l).2, fun l' => ⟨fun e => by omega, fun e => ?_⟩⟩
        obtain rfl : l = l' := Fin.ext (by omega)
        rfl
      · exact ⟨Classical.arbitrary _, fun l => ⟨fun e => absurd ⟨l, e⟩ h1, fun e => absurd ⟨l, e⟩ h2⟩⟩
  choose x hx using h
  exact ⟨x, fun l => Prod.ext (eq_of_heq ((hx _ l).1 rfl)) (eq_of_heq ((hx _ l).2 rfl))⟩

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (Γ : Grid k)

theorem pureTensor_phiM (keep : Bool) (ε g : Γ.VertexGroup)
    (φ : ∀ b : Edge, Matrix (Fin (Γ.rank b.tgt)) (Fin (Γ.rank b.src)) k → ℂ) (z : Γ.Args) :
    Γ.lines₂ (oppositePath Γ.m) (phiM Γ (ε * g) g φ) z =
      zetaLoc Γ keep ε g * moved Γ keep g (Γ.lines₂ (oppositePath Γ.m) φ) z := by
  have h1 : Γ.edgeFactor .one (ε * g) = fun e => Γ.edgeFactor .one ε e * Γ.edgeFactor .one g e := by
    funext e
    simp only [Grid.edgeFactor, Pi.mul_apply, map_mul, GlobalTheory.SplitFlip.apow_mul, _root_.mul_inv_rev, Units.val_mul]
    ring
  have h2 : Γ.lines₂ (oppositePath Γ.m) (phiM Γ (ε * g) g φ) z = ((oppositePath Γ.m).map (Γ.edgeFactor .one ε)).prod *
      Γ.pathAct .one (oppositePath Γ.m) g (Γ.lines₂ (oppositePath Γ.m) φ) z := by
    simp only [Grid.lines₂, Grid.pathAct, phiM, h1, List.prod_map_mul, mul_assoc]
    rfl
  rw [h2, zetaLoc, moved]
  cases keep
  · simp only [Bool.false_eq_true, if_false, mul_assoc, Units.mul_inv_cancel_left]
  · simp only [if_true, mul_one, one_mul]

theorem flatTensor_phiM [MeasurableSpace k] [BorelSpace k] (hs : 1 ≤ Γ.s) (ψ : AddChar k Circle) (ν : Measure k) (keep : Bool)
    (ε g : Γ.VertexGroup) (φ : ∀ b : Edge, Matrix (Fin (Γ.rank b.tgt)) (Fin (Γ.rank b.src)) k → ℂ) (x : ColArgs Γ) (y : RowArgs Γ) :
    flatTensor hs ψ ν (Γ.lines₂ (oppositePath Γ.m) (phiM Γ (ε * g) g φ)) x y =
      zetaLoc Γ keep ε g * flatTensor hs ψ ν (moved Γ keep g (Γ.lines₂ (oppositePath Γ.m) φ)) x y := by
  simp only [flatTensor, flatIntegrand, pureTensor_phiM Γ keep, mul_assoc, integral_const_mul]

end Local

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem gv_row (t : T) (w : Pl D.host.E) (β : Cosets (G := locGrid ch.G t w) one_le_sLen (givenLevel ch.G t w)) (i : ℕ) :
    (epsV ch.G t w * (repsAt ch.G t w).elt β) (i, D.R.m) = 1 := by
  rw [Pi.mul_apply]
  by_cases hi : i = D.R.m
  · subst hi
    rw [epsV_eq_one t w (by omega), elt_eq_one t w β (by omega), mul_one]
  · have e1 : epsV ch.G t w (i, D.R.m) = 1 := dif_neg hi
    have e2 : (repsAt ch.G t w).elt β (i, D.R.m) = 1 := dif_neg hi
    rw [e1, e2, mul_one]

theorem colAt_up {t : T} {w : Pl D.host.E} {p : Place D (Kw w)} (hp : IsPlc w p) (x : ColArgs (locGrid ch.G t w)) (j : ℕ)
    (hj : j < D.R.m) : ch.S.toGridChoice.colAt t w (fun j => p.up (frTop ch.S.toGridChoice t w j j.2.le)
      (frTop ch.S.toGridChoice t w (j + 1) j.2) (x j)) j = x j := by
  rw [GridChoice.colAt, dif_pos hj]
  refine Eq.trans ?_ (Witness.down_up p (frTop ch.S.toGridChoice t w j hj.le) (frTop ch.S.toGridChoice t w (j + 1) hj) (x j))
  have e : p.π = (cpt w).comp (toEAf D) := RingHom.ext hp.2.1
  rw [Place.down, e]
  rfl

theorem placeAt_of (hc : ChrP ch) (ha : ArrP ch) (hl : LocP ch) (hd : DblP ch) (hz : LastP ch) (hb : CombP ch) (hs : ScalP ch) :
    PlaceAt ch (-1) := by
  obtain ⟨κ, z, h1, h2, h3⟩ := hs
  refine ⟨κ, z, h1, h2, fun t w hw β => ⟨_, h3 t w hw β, ?_⟩⟩
  intro e he M hM r r₀ h hr hr₀ hh φ hφ v f hv hf I S x d c hdc hx u
  obtain ⟨p, hp, rfl⟩ := GlobalTheory.T.exists_completionPlaceData D w e he
  have hm := D.R.two_le_m
  have hev : Even D.R.m := D.R.m_even
  have hP : IsPts ch t w β p.e r r₀ h := ⟨hr, hr₀, hh⟩
  have hV : ∀ j : Fin D.R.m, IsArrVec ch t w p.e φ j j.2 (v j) (f j) := fun j => ⟨hv j, hf j⟩
  have hcond := (hc t w hw p hp).2.1
  have hE : ∀ j (hj : j + 1 < D.R.m), Even j →
      Expands p j hj (facAt ch t w β φ j) (conAt ch.W hM f (h * r) j) (conAt ch.W hM v (h * r₀) j) := fun j hj hj' => by
    by_cases h2 : j + 2 = D.R.m
    · exact hz t w hw p hp β r r₀ h hP M hM φ v f hV j h2
    · exact hd t w hw p hp β r r₀ h hP M hM φ v f hV j hj' (by omega)
  have hΞ : ∀ (i : I) (j : Fin D.R.m), ∃ Ξ : SB (Matrix _ _ (Kw w)), i ∈ S →
      (∀ y, Ξ.1 y = (d i j).fn (p.up (frTop ch.S.toGridChoice t w j j.2.le) (frTop ch.S.toGridChoice t w (j + 1) j.2) y)) ∧
      p.IsCombAt ch.W.ψ (frTop ch.S.toGridChoice t w j j.2.le) (frTop ch.S.toGridChoice t w (j + 1) j.2) ((c i).1 j) Ξ.1 :=
    fun i j => by
      by_cases hi : i ∈ S
      · obtain ⟨Ξ, hΞ⟩ := hb t w hw p hp j j.2 (d i j) ((c i).1 j) (hdc i hi j).1 (hdc i hi j).2
        exact ⟨Ξ, fun _ => hΞ⟩
      · exact ⟨0, fun h => absurd h hi⟩
  choose Ξ hΞ using hΞ
  have hlt : ∀ l : Fin (D.R.m / 2), 2 * l.1 + 1 < D.R.m := fun l => by have := l.2; omega
  have hSB : ∀ j < D.R.m - 1, phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ
      (.theta D.R.m j) ∈ SB _ := fun j hj => by
    obtain ⟨-, -, -, Φ, hΦ, -⟩ := ha t w hw p hp φ j (by omega) _ _ (hV ⟨j, by omega⟩) _ _ (epsV_mem t w) 1 _ 1 _
      (hl t w hw p hp β r r₀ h hP j (by omega)).1 (hl t w hw p hp β r r₀ h hP (j + 1) (by omega)).1 _ _ (Equiv.refl _) (Equiv.refl _)
    obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := Kw w)
    have key : ∀ {A B : Type}, Topology.IsClosedEmbedding fun z : Matrix A B (Kw w) => zᵀ :=
      Function.LeftInverse.isClosedEmbedding (f := fun z => zᵀ) (fun z => rfl) continuous_id.matrix_transpose
        continuous_id.matrix_transpose
    have e : phiM (locGrid ch.G t w) (epsV ch.G t w * (repsAt ch.G t w).elt β) ((repsAt ch.G t w).elt β) φ (.theta D.R.m j) =
        Φ.1 ∘ fun z => zᵀ := funext fun z => (hΦ zᵀ).symm
    rw [e]
    exact ⟨Φ.2.1.comp_continuous key.continuous, Φ.2.2.comp_isClosedEmbedding key⟩
  have key := GlobalTheory.T.prod_eq_sum_of_factorwise_linear_expansion (Fin (D.R.m / 2)) _ I S
    (fun i => zetaLoc (locGrid ch.G t w) (keepAt ch.G w) (epsV ch.G t w) ((repsAt ch.G t w).elt β) * x i)
    (fun l i q => (Ξ i ⟨2 * l, by have := hlt l; omega⟩).1 q.1 * (Ξ i ⟨2 * l + 1, hlt l⟩).1 q.2)
    (fun l i => combC ch.W (c i) (conAt ch.W hM v (h * r₀)) (2 * l) (u (2 * l)) (u (2 * l + 1)))
    (fun l => facAt ch t w β φ (2 * l)) (fun l => conAt ch.W hM f (h * r) (2 * l) (u (2 * l)) (u (2 * l + 1)))
    (fun l y hy => by
      have := congrFun (congrFun ((hE (2 * l) (hlt l) (even_two_mul _) I S y _ _ (fun i => (c i).1 (2 * l))
        (fun i => (c i).1 (2 * l + 1)) fun i hi => ⟨(hΞ i ⟨2 * l, by have := hlt l; omega⟩ hi).2, (hΞ i ⟨2 * l + 1, hlt l⟩ hi).2⟩).1
        fun q₁ q₂ => hy (q₁, q₂)) (u (2 * l))) (u (2 * l + 1))
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, combC] using this)
    (fun l y hy => by
      have := congrFun (congrFun ((hE (2 * l) (hlt l) (even_two_mul _) I S y _ _ (fun i => (c i).1 (2 * l))
        (fun i => (c i).1 (2 * l + 1)) fun i hi => ⟨(hΞ i ⟨2 * l, by have := hlt l; omega⟩ hi).2, (hΞ i ⟨2 * l + 1, hlt l⟩ hi).2⟩).2
        hy) (u (2 * l))) (u (2 * l + 1))
      simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, combC] using this)
    (fun q => by
      obtain ⟨y, hy⟩ := exists_unpair (Y := fun j => Matrix (Fin (topRank (locGrid ch.G t w) (j + 1)))
        (Fin (topRank (locGrid ch.G t w) j)) (Kw w)) q
      have e1 := hx (fun j => p.up (frTop ch.S.toGridChoice t w j j.2.le) (frTop ch.S.toGridChoice t w (j + 1) j.2) (y j))
        fun j => Witness.up_half p _ _ _
      have e2 := GlobalTheory.T.flatTensor_pureTensor_eq_prod_localFactors (Kw w) (locGrid ch.G t w) one_le_sLen hm hev (psiAt ch.W w) (unitVol w) hcond.continuous hcond.ne_one
        (isUnitVol_unitVol w).1 _ hSB (ch.S.toGridChoice.colAt t w fun j => p.up (frTop ch.S.toGridChoice t w j j.2.le)
          (frTop ch.S.toGridChoice t w (j + 1) j.2) (y j)) 0
      replace e2 := ((flatTensor_phiM (locGrid ch.G t w) one_le_sLen (psiAt ch.W w) (unitVol w) (keepAt ch.G w) (epsV ch.G t w)
        ((repsAt ch.G t w).elt β) φ _ 0).trans (congrArg _ e1.symm)).symm.trans e2
      rw [Finset.prod_eq_one (s := Finset.range (locGrid ch.G t w).m) (fun i _ => by
        simp only [phiM, hφ, Grid.edgeFactor, mul_one]
        change ((_ : ℂˣ) : ℂ) * _ * _ * _ = 1
        rw [show (epsV ch.G t w * (repsAt ch.G t w).elt β) (Edge.ex i (locGrid ch.G t w).m).src = 1 from gv_row ch t w β i,
          show (epsV ch.G t w * (repsAt ch.G t w).elt β) (Edge.ex i (locGrid ch.G t w).m).tgt = 1 from gv_row ch t w β (i + 1)]
        simp), one_mul, Finset.prod_range] at e2
      refine Eq.trans (Finset.prod_congr rfl fun l _ => ?_) (e2.symm.trans ?_)
      · rw [colAt_up ch hp y _ (by have := hlt l; omega), colAt_up ch hp y _ (hlt l), hy l]
      · rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [← mul_assoc, prod_fin_pairs hev]
        congr 1
        refine Finset.prod_congr rfl fun l _ => ?_
        rw [(hΞ i _ hi).1, (hΞ i _ hi).1, ← hy l])
    fun l => ⟨0⟩
  simp only [evT, Pi.one_apply, Finset.prod_const_one, mul_one, Finset.prod_range]
  rw [key, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _

theorem big_placeAt : Big fun ch => ∃ s, PlaceAt ch s :=
  big_mono (fun ch ⟨⟨⟨⟨⟨⟨⟨⟨⟨lat, chr⟩, loc⟩, bes⟩, jac⟩, scal⟩, arr⟩, comb⟩, dbl⟩, last⟩ =>
    ⟨-1, placeAt_of ch chr (arr lat chr) loc (dbl chr (arr lat chr) loc bes jac) (last chr (arr lat chr) loc bes jac) (comb lat) scal⟩)
  (((((((((GlobalTheory.T.frameLattice_points_eq_integralMatrices_largeDepth.and GlobalTheory.T.localCharacterComponents_largeDepth).and GlobalTheory.T.dictionaryPoints_localMatrices_largeDepth).and GlobalTheory.T.besselFrameOfGridLattice_largeDepth).and GlobalTheory.T.jacobiFrameOfGridLattice_largeDepth).and GlobalTheory.T.flatDictionaryScalar_largeDepth).and
    GlobalTheory.T.arrowLocalModel_movedFrames).and GlobalTheory.T.latticeVacuumCombination_localModel).and GlobalTheory.T.flatDictionary_doubleStep_at_place).and GlobalTheory.T.flatDictionary_lastTwoSteps_at_place)

end GlobalTheory.FlatPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlippedFiniteTensorLatticeFixedLargeDepth
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowKFix

theorem key {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks]
    [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R) (large₂ : SizeData₂ D) (F : Face D A)
    (hS : HidaSetting large₂ R F) (hch : ch.Is) (hsh : ShapeAt ch) : KFix ch := by
  intro t Φ τ hτ J hJ k hk y v
  have hJ' : 1 ≤ J ∧ J + 1 < D.R.m := by
    simp only [idx, List.mem_range'_1] at hJ
    omega
  obtain ⟨j, rfl⟩ : ∃ j, J = j + 1 := ⟨J - 1, by omega⟩
  have hj : j + 1 + 1 < D.R.m := hJ'.2
  obtain ⟨c₁, c₂, h1, h2, h3⟩ := GlobalTheory.T.lastRowInnerVertex_vacua_scaled_localProduct ch large₂ F hS hch hsh t Φ j hj k hk
  exact GlobalTheory.T.weilRep_pair_fixes_flippedTensorSum ch large₂ F hS hch t Φ τ hτ j hj k hk c₁ c₂ h1 h2 h3 y v

theorem kfix : Big fun ch => KFix ch := by
  obtain ⟨CF0, h⟩ := GlobalTheory.T.lastRowLatticesGoodPosition_large_depth
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := h ε CF hCF
  exact ⟨x₀, fun D large₂ he hx' Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hch hsc =>
    key ch large₂ F hS hch (hx D large₂ he hx' Γ Pl0 T A Ks R F hS ch hch hsc)⟩

end GlobalTheory.RowKFix
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableScalarActionMultiplicityMapValuesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integrable_scalar_action_multiplicityMap_values : GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ t ∈ MultT θ M J χ, ∀ (w : M.Vec) (m : Measure (GinfC V)), m.IsHaarMeasure → ∀ (α : GinfC V → ℂ) (c : ℂ), Integrable α m → (∀ b : ∀ τ, M.H τ, ∫ h, α h * coefR θ M b (fun τ => w τ) h ∂m = c * ∏ τ, ⟪b τ, (w τ : M.H τ)⟫_ℂ) → ∀ x, ∫ h, α h * t (PiTensorProduct.tprod ℂ w) (x * h) ∂m = c * t (PiTensorProduct.tprod ℂ w) x := by
  first | exact @GlobalTheory.ValAct.integral_mul_multT_eq | exact GlobalTheory.ValAct.integral_mul_multT_eq | (intros; apply GlobalTheory.ValAct.integral_mul_multT_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftHorizontalCuspType
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspFormApprox

theorem th_formApprox_of (hU : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (φ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ → ∀ (A : ℕ) (ε : ℝ), 0 < ε → ∃ (n : ℕ) (F : Fin n → N.Maps) (v : Fin n → Formalism.IndefR.Links.SmT N.M), (∀ l, F l ∈ N.Cusp θ) ∧ ∀ g, ‖φ g - ∑ l, F l (v l) g‖ * GlobalTheory.Grow.quotHeight N.V g ^ A ≤ ε) : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → ∀ b : ℕ, IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (Fs : Fin n → (G.V i (j + 1)).Maps) (vs : Fin n → SmT (G.V i (j + 1)).M), (∀ k, Fs k ∈ (G.V i (j + 1)).Cusp R.θ) ∧ IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∫ g in (G.meas t i (j + 1)).fd, GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖ ∂(G.meas t i (j + 1)).ν ≤ ε := by
  intro _ hP D _ G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG t i j hi hj φ hφ b
  obtain ⟨hμ, h𝓕⟩ := GlobalTheory.PairLift.haar_vert hR hG t hi (j := j + 1) hj
  exact ⟨integrableOn_quotHeight_pow_mul_norm hP.cuspRapidDecay hR.inf hμ h𝓕 hφ b,
    weighted_uniform_approx_cusp_forms hμ h𝓕 hφ.1.cont b (hU D R.θ hR.inf hP _ φ hφ b)⟩

theorem th_formApprox : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D → ∀ (G₀ : Type) [Group G₀] [Fintype G₀] (Pl0 T : Type) (A : FamIn D.what₂.LL G₀ Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (G : GlobalTheory.Grid.GridPre R), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.RowBase R → G.Is → ∀ t i j, i ≤ D.R.m → j < D.R.m → ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType R.θ (G.V i (j + 1)) φ → ∀ b : ℕ, IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∀ ε : ℝ, 0 < ε → ∃ (n : ℕ) (Fs : Fin n → (G.V i (j + 1)).Maps) (vs : Fin n → SmT (G.V i (j + 1)).M), (∀ k, Fs k ∈ (G.V i (j + 1)).Cusp R.θ) ∧ IntegrableOn (fun g => GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖) (G.meas t i (j + 1)).fd (G.meas t i (j + 1)).ν ∧ ∫ g in (G.meas t i (j + 1)).fd, GlobalTheory.Grow.quotHeight (G.V i (j + 1)).V g ^ b * ‖(∑ k, Fs k (vs k) g) - φ g‖ ∂(G.meas t i (j + 1)).ν ≤ ε :=
  th_formApprox_of GlobalTheory.T.cusp_form_uniform_height_approx

end GlobalTheory.CuspFormApprox

end
end

