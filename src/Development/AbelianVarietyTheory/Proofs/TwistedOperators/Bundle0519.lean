import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0506
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0508
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeHomApproxIntegralMatrixMod
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0029
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0438
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0509
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ChainParSucc
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0017
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0018
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

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfThetaDistributionHeisenbergTranslatesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_thetaDistribution_heisenbergTranslates : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Wd : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ Y Wd)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ → ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d),
    (∀ u, GlobalTheory.WeilM.thetaSum F (M.co.rho ψ u Φ) = 0) → Φ = 0 := by
  first | exact @GlobalTheory.ThetaSeparates.eq_zero_of_thetaSum_rho | exact GlobalTheory.ThetaSeparates.eq_zero_of_thetaSum_rho | (intros; apply GlobalTheory.ThetaSeparates.eq_zero_of_thetaSum_rho <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExFieldOfKeyFinExKey
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

noncomputable section

namespace GlobalTheory.RowEx

theorem exField_of_keyFin_exKey : KeyFin → ExKey → ExField := by
  classical
  intro h2 h1
  obtain ⟨c, h1⟩ := h1
  refine ⟨c, fun ε CF hC => ?_⟩
  obtain ⟨x, h1⟩ := h1 ε CF hC
  refine ⟨x, fun s e hx P f Ξ hΞ => ?_⟩
  obtain ⟨𝒦, hK, H⟩ := h2 P Ξ hΞ
  choose S hS HS using h1 s e hx P f
  refine ⟨hK.toFinset.biUnion S, fun z hz => ?_, fun Y f' hP hf large₂ hs Γ _ _ Pl0 U A Ks _ _ _ R F st hC ho hc hz => ?_⟩
  · obtain ⟨κ, -, hz⟩ := Finset.mem_biUnion.1 hz
    exact hS κ z hz
  · obtain ⟨κ, hκ, hk⟩ := H Y U R.toLevCh A.μ0 hP st.core.lev hc
    exact HS κ Y f' hP hf large₂ hs Γ Pl0 U A Ks R F st hC ho hk fun z hz' =>
      hz z (Finset.mem_biUnion.2 ⟨κ, hK.mem_toFinset.2 hκ, hz'⟩)

end GlobalTheory.RowEx

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExKeyOf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open GlobalTheory.Mem GlobalTheory.Mem.Top
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.RowEx

set_option maxHeartbeats 1600000 in

theorem exKey_of (h1 : GridEx) (h2 : IsEx) (h3 : NFAll) (cG : CarryG) (cW : CarryW) (cS : CarryS)
    (t1 : TrEasy) (t2 : TrPhase) (t3 : TrJet) (t4 : TrBot) : ExKey := by
  classical
  obtain ⟨a1, h1⟩ := h1
  obtain ⟨a2, h2⟩ := h2
  obtain ⟨a3, h3⟩ := h3
  refine ⟨max a1 (max a2 a3), fun ε CF hC => ?_⟩
  obtain ⟨x1, h1⟩ := h1 ε CF (le_of_max_le_left hC)
  obtain ⟨x2, h2⟩ := h2 ε CF (le_of_max_le_left (le_of_max_le_right hC))
  obtain ⟨x3, h3⟩ := h3 ε CF (le_of_max_le_right (le_of_max_le_right hC))
  refine ⟨max x1 (max x2 x3), fun s he hx P f κ => ?_⟩
  have hx1 := le_of_max_le_left hx
  have hx2 := le_of_max_le_left (le_of_max_le_right hx)
  have hx3 := le_of_max_le_right (le_of_max_le_right hx)
  by_cases H : ∃ (X : Stages) (f' : Fr X.B.toPre) (_ : X.B.toPre = P) (_ : HEq f' f) (large₂ : SizeData₂ X.toD7) (_ : large₂.sc = s)
      (Γ : Type) (_ : Group Γ) (_ : Fintype Γ) (Pl0 T : Type)
      (A : FamIn X.toD7.what₂.LL Γ Pl0 T X.toD7.R.m) (Ks : Type) (_ : Field Ks) (_ : NumberField Ks) (_ : Algebra Ks X.toD7.what₂.LL)
      (R : RealDat X.toD7 A Ks) (F : Face X.toD7 A), HidaSetting large₂ R F ∧ R.C = Fr.at X f' ∧ TwistPlacesOffPrimeQZero R.toLevCh ∧ HEq (keyOf R.toLevCh) κ
  swap
  · exact ⟨∅, by simp, fun X f' a b large₂ c Γ _ _ Pl0 T A Ks _ _ _ R F d e g i _ =>
      absurd ⟨X, f', a, b, large₂, c, Γ, _, _, Pl0, T, A, Ks, _, _, _, R, F, d, e, g, i⟩ H⟩
  obtain ⟨X0, f0, a0, b0, Lg0, rfl, Γ0, _, _, Pl00, T0, A0, Ks0, _, _, _, R0, F0, d0, e0, g0, i0⟩ := H
  obtain ⟨G0, W0, hW0, ⟨S0⟩⟩ := h1 _ Lg0 he hx1 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 g0
  obtain ⟨M, ρ, ξ, cv, rm, S, rp, n, e, c, hS, hIs⟩ := h2 _ Lg0 he hx2 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 G0 W0 hW0 S0
  obtain ⟨N, hN, hAll⟩ := h3 _ Lg0 he hx3 Γ0 Pl00 T0 A0 Ks0 R0 F0 d0 _ hIs rfl
  obtain ⟨b⟩ : Nonempty (Module.Basis (Fin (Module.finrank ℚ N)) ℚ N) := ⟨Module.finBasis ℚ N⟩
  refine ⟨Finset.univ.image fun i => ((b i : N) : ℂ), ?_, ?_⟩
  · intro z hz
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hz
    exact IntermediateField.isAlgebraic_iff.1 (Algebra.IsAlgebraic.isAlgebraic _)
  intro X f' a b' large₂ hs Γ _ _ Pl0 T A Ks _ _ _ R F d e' g i hz
  have hk : HEq (keyOf R.toLevCh) (keyOf R0.toLevCh) := i.trans i0.symm
  have hpre : X.B.toPre = X0.B.toPre := a.trans a0.symm
  have key : ∀ (P P' : Pre) (_ : P = P') (k : Key P) (k' : Key P'), HEq k k' → ∀ x ∈ k, ∃ y ∈ k', HEq x.1 y.1 ∧ HEq x.2 y.2 := by
    rintro P _ rfl k k' h x hx
    obtain rfl := eq_of_heq h
    exact ⟨x, hx, HEq.rfl, HEq.rfl⟩
  have hι : ∀ t : T, ∃ t0 : T0, HEq (R.xiH t) (R0.xiH t0) ∧ HEq (R.Q t) (R0.Q t0) := fun t => by
    obtain ⟨_, ⟨t0, rfl⟩, h⟩ := key _ _ hpre _ _ hk _ ⟨t, rfl⟩
    exact ⟨t0, h⟩
  choose ι hι using hι
  have one : ∀ (P P' : Pre) (_ : P = P'), HEq (1 : HChar P.host.E) (1 : HChar P'.host.E) := by rintro P _ rfl; rfl
  have hb : ι A.μ0 = A0.μ0 := d0.core.lev.xi_inj (by
    rw [d0.core.lev.xi_base]
    have := (hι A.μ0).1
    rw [d.core.lev.xi_base] at this
    exact eq_of_heq (this.symm.trans (one _ _ hpre)))
  have hL : LAgree R0.toLevCh R.toLevCh A0.μ0 A.μ0 ι :=
    ⟨hpre, d0.core.lev, d.core.lev, ⟨f0, f', b'.trans b0.symm, e0, e'⟩, hb, fun t => (hι t).1, fun t => (hι t).2, d0.betaX, d.betaX⟩
  obtain ⟨G, hG⟩ := cG _ _ _ _ _ _ _ _ _ hL _ G0
  obtain ⟨W, hW, hWA⟩ := cW _ _ _ _ _ Γ Pl0 A Ks R _ ι hL d.core.chain d.core.models _ G0 G hG W0
  obtain ⟨S', hS'⟩ := cS _ _ _ _ _ _ _ _ _ hL _ G0 G hG W0 W hWA S.toGridChoice
  have hA : Agree S.toGridChoice S' A0.μ0 A.μ0 ι := ⟨hL, hG, hWA, hS'⟩
  have h2' := h2 _ large₂ (hs ▸ he) (hs ▸ hx2) Γ Pl0 T A Ks R F d
  rw [hs] at h2'
  obtain ⟨M', ρ', ξ', cv', rm', S2, rp', n', e2, c', hS2, hIs'⟩ := h2' G W hW S'
  refine ⟨_, hIs', rfl, ?_⟩
  obtain ⟨u1, u2, u3⟩ := t1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N (algebraMap N ℂ)
  have hAll' : AllIn (algebraMap N ℂ) S' A.μ0 := ⟨u1 hAll.chars, u2 hAll.root, t2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.phase,
    t3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.jet, u3 hAll.ratios, t4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA N _ hAll.bot⟩
  subst hS2
  refine hAll'.numbersIn.mono ?_
  rintro _ ⟨y, rfl⟩
  rw [← b.sum_repr y, map_sum]
  refine X.toD7.what₂.embLL.fieldRange.sum_mem fun i _ => ?_
  rw [Rat.smul_def, map_mul, map_ratCast]
  exact X.toD7.what₂.embLL.fieldRange.mul_mem (SubfieldClass.ratCast_mem _ _) (hz _ (Finset.mem_image_of_mem _ (Finset.mem_univ i)))

end GlobalTheory.RowEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsChainPols
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FlipStart

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

def colPure (W : G.Weil) (t : T) (f : ∀ j : Fin D.R.m, Sch G (.down t 0 j))
    (q : ∀ j : Fin D.R.m, PolF D (G.pT (.mu t 0 j)).rank (G.pS (.mu t 0 j)).rank) : PureT G (downPath t 0 D.R.m) :=
  downFam t 0 D.R.m fun j => W.fock (.mu t 0 j) (f j) (q j)

def givenFin (W : G.Weil) (t : T) (f : ∀ j : Fin D.R.m, Sch G (.down t 0 j)) (Φ : G.Datum) : PureT G (givenPath t D.R.m) :=
  Path.Fam.append (downFam t 0 D.R.m f) (rowFam 0 D.R.m fun i => W.cosVec i (Φ i))

def gPol (ρ : G.RealVec) (q : ∀ j : ℕ, PolF D (G.V (.grid 0 (j + 1))).rank (G.V (.grid 0 j)).rank) : PolE G
  | .ex i 0 => if h : i < D.R.m then ρ ⟨i, h⟩ else 0
  | .ex _ (_ + 1) => 0
  | .theta 0 j => q j
  | .theta (_ + 1) _ => 0

variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}

def ChainVecs (ch : Choice R) (t : T) (f : ∀ j : Fin D.R.m, Sch ch.G (.down t 0 j)) : Prop :=
  ∀ j : Fin D.R.m, ((j : ℕ) + 1 < D.R.m → HEq (f j) (R.vY t j)) ∧ ((j : ℕ) + 1 = D.R.m → HEq (f j) (R.vX t))

def ChainPols (ch : Choice R) (q : ∀ j : ℕ, PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank) : Prop :=
  ∀ j : ℕ, (j + 1 < D.R.m → HEq (q j) (ch.cv.polY j)) ∧ (j + 1 = D.R.m → HEq (q j) ch.cv.polX)

theorem exists_heq_fun (Y Y' : LSp D) (S S' : HSp D) (Λ Λ') (hY : Y = ⟨S, Λ⟩) (hY' : Y' = ⟨S', Λ'⟩) (f : WO S S' → ℂ) :
    ∃ f' : WO Y.sp Y'.sp → ℂ, HEq f' f := by
  subst hY hY'; exact ⟨f, HEq.rfl⟩

theorem exists_heq_pol {a b a' b' : ℕ} (ha : a' = a) (hb : b' = b) (P : PolF D a b) : ∃ P' : PolF D a' b', HEq P' P := by
  subst ha hb; exact ⟨P, HEq.rfl⟩

theorem rank_col_lt (L : LevCh D T) {j : ℕ} (h : j < D.R.m) : (columnBlock L j).sp.rank = (Yc D j).rank := by
  rw [colY_lt L h]

theorem rank_col_m (L : LevCh D T) : (columnBlock L D.R.m).sp.rank = D.sp.X'.rank := by
  rw [colY_m L]

theorem exists_chainVecs (ch : Choice R) (t : T) : ∃ f, ChainVecs ch t f := by
  have H : ∀ j : Fin D.R.m, ∃ f : Sch ch.G (.down t 0 j),
      ((j : ℕ) + 1 < D.R.m → HEq f (R.vY t j)) ∧ ((j : ℕ) + 1 = D.R.m → HEq f (R.vX t)) := fun ⟨j, hj⟩ => by
    by_cases h : j + 1 < D.R.m
    · obtain ⟨f, e⟩ := exists_heq_fun (columnBlock R.toLevCh j) (columnBlock R.toLevCh (j + 1)) _ _ _ _ (colY_lt _ (by omega))
        (colY_lt _ h) (R.vY t j)
      exact ⟨f, fun _ => e, fun h' => by simp at h'; omega⟩
    · have e1 : j = D.R.m - 1 := by omega
      subst e1
      have e2 : columnBlock R.toLevCh (D.R.m - 1 + 1) = ⟨D.sp.X', R.ΛX⟩ := by
        rw [Nat.sub_add_cancel (by omega)]; exact colY_m _
      obtain ⟨f, e⟩ := exists_heq_fun (columnBlock R.toLevCh (D.R.m - 1)) (columnBlock R.toLevCh (D.R.m - 1 + 1)) _ _ _ _
        (colY_lt _ (by omega)) e2 (R.vX t)
      exact ⟨f, fun h' => absurd h' h, fun _ => e⟩
  choose f hf using H
  exact ⟨f, hf⟩

theorem exists_chainPols (ch : Choice R) : ∃ q, ChainPols ch q := by
  have H : ∀ j : ℕ, ∃ q : PolF D (ch.G.V (.grid 0 (j + 1))).rank (ch.G.V (.grid 0 j)).rank,
      (j + 1 < D.R.m → HEq q (ch.cv.polY j)) ∧ (j + 1 = D.R.m → HEq q ch.cv.polX) := fun j => by
    by_cases h : j + 1 < D.R.m
    · obtain ⟨q, e⟩ := exists_heq_pol (rank_col_lt R.toLevCh h) (rank_col_lt R.toLevCh (by omega)) (ch.cv.polY j)
      exact ⟨q, fun _ => e, fun h' => by omega⟩
    · by_cases h' : j + 1 = D.R.m
      · have e1 : j = D.R.m - 1 := by omega
        subst e1
        have e2 : (columnBlock R.toLevCh (D.R.m - 1 + 1)).sp.rank = D.sp.X'.rank := by
          rw [Nat.sub_add_cancel (by omega)]; exact rank_col_m _
        obtain ⟨q, e⟩ := exists_heq_pol e2 (rank_col_lt R.toLevCh (by omega)) ch.cv.polX
        exact ⟨q, fun h'' => absurd h'' h, fun _ => e⟩
      · exact ⟨0, fun h'' => absurd h'' h, fun h'' => absurd h'' h'⟩
  choose q hq using H
  exact ⟨q, hq⟩

end GlobalTheory.FlipStart

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCompactMeetsBesselTopRationalOrbitsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_meets_besselTopRationalOrbits : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∃ Ω : Set (GA D (G.V (.grid D.R.m 0))), IsCompact Ω ∧ ∀ (h : GA D (G.V (.top 0))) (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e),
      ∃ γ ∈ GQ (G.V (.grid D.R.m 0)), γ * ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h) ∈ Ω := by
  first | exact @GlobalTheory.BesCover.bplus_cover | exact GlobalTheory.BesCover.bplus_cover | (intros; apply GlobalTheory.BesCover.bplus_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsCosetSameLocalCosetSetsOtherBaseLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw GlobalTheory.FunObj.borelSpaceKw

noncomputable section

open scoped TensorProduct nonZeroDivisors Pointwise

namespace GlobalTheory.FunObj.CosFlip

open Matrix GlobalTheory.FunObj.Comparison₂ GlobalTheory.SplitFlip GlobalTheory.StdFrames ValuativeRel Formalism.L2.DIV

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts}

theorem v_le_cosExp (G : GridData L sc) {s : OA D} (hs : s ∈ idS D.host.F G.modul) (w : Pl D.host.E) :
    Valued.v (cpt (D := D) w s.1) ≤ WithZero.exp (-(cosExp G w : ℤ)) := by
  by_cases hw : w ∈ G.pl.W0
  · exact (mem_idS_modul G s).1 hs w hw
  · rw [(depthAt_of_notMem G hw).1, Nat.cast_zero, neg_zero, WithZero.exp_zero]
    exact (mem_OA_iff _).1 s.2 w

theorem coord_sub_mem (G : GridData L sc) (B : Frames G) (t : T) (w : Pl D.host.E) (h : 0 < D.R.m)
    (h0 : IsFrame (B.β 0 0) (G.Λ (.grid 0 0))) (h1 : IsFrame (B.β 1 0) (G.Λ (.grid 1 0)))
    {y y₀ : homLat (G.Λ (.grid 1 0)) (G.Λ (.grid 0 0))} (hy : Cos.mk G.modul y = Cos.mk G.modul y₀) :
    B.coord t w (X := (0, 0)) (Y := (1, 0)) ⟨h.le, Nat.zero_le _⟩ ⟨h, Nat.zero_le _⟩
        (y.1.map (algebraMap D.host.E (Kw w))) -
      B.coord t w (X := (0, 0)) (Y := (1, 0)) ⟨h.le, Nat.zero_le _⟩ ⟨h, Nat.zero_le _⟩
        (y₀.1.map (algebraMap D.host.E (Kw w))) ∈ matLat (Fin ((locGrid G t w).rank (1, 0))) (unifAt w ^ cosExp G w • SplitFlip.stdLat (Kw w) (Fin ((locGrid G t w).rank (0, 0)))) := by
  rw [mem_matLat_pow, map_algebraMap, map_algebraMap, coord_map, coord_map]
  intro a b
  obtain ⟨s, hs, e⟩ := fr_mem_idS h1 h0 (sub_mem_of_mk_eq hy)
    (Fin.cast (rank_vertex G t w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
    (Fin.cast (rank_vertex G t w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a)
  simp only [Matrix.sub_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.map_apply]
  rw [← RingHom.map_sub, ← Matrix.sub_apply, ← fr_sub, ← Matrix.map_sub _ (map_sub (eToEAf D)), ← e]
  exact v_le_cosExp G hs w

theorem cosetSet_mk (G : GridData L sc) (B : Frames G) (t : T) (w : Pl D.host.E) (h : 0 < D.R.m)
    (h0 : IsFrame (B.β 0 0) (G.Λ (.grid 0 0))) (h1 : IsFrame (B.β 1 0) (G.Λ (.grid 1 0)))
    (y₀ : homLat (G.Λ (.grid 1 0)) (G.Λ (.grid 0 0))) :
    cosetSet t w B h (Cos.mk G.modul y₀) = {x | x - B.coord t w (X := (0, 0)) (Y := (1, 0)) ⟨h.le, Nat.zero_le _⟩
      ⟨h, Nat.zero_le _⟩ (y₀.1.map (algebraMap D.host.E (Kw w))) ∈
        matLat (Fin ((locGrid G t w).rank (1, 0))) (unifAt w ^ cosExp G w • SplitFlip.stdLat (Kw w) (Fin ((locGrid G t w).rank (0, 0))))} := by
  ext x
  constructor
  · rintro ⟨y, hy, hx⟩
    have := add_mem hx (coord_sub_mem G B t w h h0 h1 hy)
    rwa [sub_add_sub_cancel] at this
  · intro hx
    exact ⟨y₀, rfl, hx⟩

end GlobalTheory.FunObj.CosFlip

namespace GlobalTheory.FunObj.CosFlip

open Matrix GlobalTheory.FunObj.Comparison₂ GlobalTheory.SplitFlip GlobalTheory.StdFrames ValuativeRel Formalism.L2.DIV

theorem sub_mem_iff_of_sub_mem {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (S : Submodule R M) {a b : M}
    (h : a - b ∈ S) (x : M) : x - a ∈ S ↔ x - b ∈ S := by
  constructor
  · intro hx
    have := add_mem hx h
    rwa [sub_add_sub_cancel] at this
  · intro hx
    have := sub_mem hx h
    rwa [sub_sub_sub_cancel_right] at this

theorem exists_cos_cosetSet_eq : ∀ {D : D7} {T T' : Type} {L : LevCh D T} {L' : LevCh D T'} {sc : Consts} (G : GridData L sc) (G' : GridData L' sc)
    (B : GlobalTheory.FunObj.Frames G) (B' : GlobalTheory.FunObj.Frames G'),
    IsSDFrame (Yc D 0) (L.βY 0) (L.ΛY 0) (D.host.g 0 * D.host.g 1) →
    IsSDFrame (Yc D 0) (L'.βY 0) (L'.ΛY 0) (D.host.g 0 * D.host.g 1) →
    G'.pl.v0 = G.pl.v0 → G'.pl.w = G.pl.w → G'.sp.Vs 1 0 = G.sp.Vs 1 0 → HEq (B'.βs 1 0) (B.βs 1 0) →
    ∀ (h : 0 < D.R.m) (κ' : G'.CosAt 0), ∃ κ : G.CosAt 0, ∀ (t : T') (t₀ : T) (w : Pl D.host.E),
      GlobalTheory.FunObj.cosetSet t w B' h κ' = GlobalTheory.FunObj.cosetSet t₀ w B h κ := by
  intro D T T' L L' sc G G' B B' hY hY' hv0 hw _ _ h κ'
  have h0 : IsFrame (B.β 0 0) (G.Λ (.grid 0 0)) := hY.choose_spec.1
  have h0' : IsFrame (B'.β 0 0) (G'.Λ (.grid 0 0)) := hY'.choose_spec.1
  have h1 : IsFrame (B.β 1 0) (G.Λ (.grid 1 0)) := B.isFrame 1 0 le_rfl h (Nat.zero_le _)
  have h1' : IsFrame (B'.β 1 0) (G'.Λ (.grid 1 0)) := B'.isFrame 1 0 le_rfl h (Nat.zero_le _)
  have hW0 : G'.pl.W0 = G.pl.W0 := by
    unfold Places.W0 Places.S0
    rw [hv0, hw]
  have hdep : ∀ v, G'.pl.depth sc v = G.pl.depth sc v := fun v => by
    unfold Places.depth
    rw [hv0]
  have hexp : ∀ w, cosExp G' w = cosExp G w := fun w => by
    by_cases hm : w ∈ G.pl.W0
    · rw [cosExp, cosExp, if_pos (by rw [hW0]; exact hm), if_pos hm, hdep]
    · rw [cosExp, cosExp, if_neg (by rw [hW0]; exact hm), if_neg hm]
  obtain ⟨y', hy'⟩ := Submodule.Quotient.mk_surjective _ κ'
  have hint : ∀ i j, ∃ s ∈ idS D.host.F ⊤, s.1 = fr (B'.β 0 0) (B'.β 1 0) (y'.1.map (eToEAf D)) i j :=
    fr_mem_idS h1' h0' (by rw [Submodule.top_smul]; exact y'.2)
  choose N _ hN using hint
  have hr : (G.V (.grid 1 0)).rank = (G'.V (.grid 1 0)).rank := by
    show (G.sp.Vs 1 0).sp.rank = (G'.sp.Vs 1 0).sp.rank
    rw [‹G'.sp.Vs 1 0 = G.sp.Vs 1 0›]
  obtain ⟨x₀, hx₀, hs⟩ := HatFrame.homLat_approx_mod (G.Λ (.grid 1 0)) (G.Λ (.grid 0 0)) (B.β 1 0) (B.β 0 0) h1 h0
    G.modul (G.pl.modul_ne_bot sc) (fun i j => N i (Fin.cast hr j))
  refine ⟨Cos.mk G.modul ⟨x₀, hx₀⟩, fun t t₀ w => ?_⟩
  have hk : Cos.mk G'.modul y' = κ' := hy'
  rw [← hk, cosetSet_mk G' B' t w h h0' h1' y', cosetSet_mk G B t₀ w h h0 h1 ⟨x₀, hx₀⟩, hexp]
  have key : @id (Matrix (Fin ((locGrid G t₀ w).rank (1, 0))) (Fin ((locGrid G t₀ w).rank (0, 0))) (Kw w))
        (B'.coord t w (X := (0, 0)) (Y := (1, 0)) ⟨h.le, Nat.zero_le _⟩ ⟨h, Nat.zero_le _⟩
          (y'.1.map (algebraMap D.host.E (Kw w)))) -
      B.coord t₀ w (X := (0, 0)) (Y := (1, 0)) ⟨h.le, Nat.zero_le _⟩ ⟨h, Nat.zero_le _⟩
        (x₀.map (algebraMap D.host.E (Kw w))) ∈ matLat (Fin ((locGrid G t₀ w).rank (1, 0)))
        (unifAt w ^ cosExp G w • SplitFlip.stdLat (Kw w) (Fin ((locGrid G t₀ w).rank (0, 0)))) := by
    rw [mem_matLat_pow]
    dsimp only [id]
    rw [Comparison₂.map_algebraMap, Comparison₂.map_algebraMap, coord_map, coord_map]
    intro a b
    obtain ⟨s, hs1, hs2⟩ := hs (Fin.cast (rank_vertex G t₀ w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
      (Fin.cast (rank_vertex G t₀ w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a)
    have e1 : (N (Fin.cast (rank_vertex G t₀ w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
        (Fin.cast hr (Fin.cast (rank_vertex G t₀ w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a)) : EAf D) =
        fr (B'.β 0 0) (B'.β 1 0) (y'.1.map (eToEAf D))
          (Fin.cast (rank_vertex G' t w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
          (Fin.cast (rank_vertex G' t w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a) := hN _ _
    have e2 : fr (B'.β 0 0) (B'.β 1 0) (y'.1.map (eToEAf D))
          (Fin.cast (rank_vertex G' t w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
          (Fin.cast (rank_vertex G' t w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a) -
        fr (B.β 0 0) (B.β 1 0) (x₀.map (eToEAf D))
          (Fin.cast (rank_vertex G t₀ w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
          (Fin.cast (rank_vertex G t₀ w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a) = -(s : EAf D) := by
      rw [hs2, ← e1]
      exact (neg_sub _ _).symm
    show Valued.v (cpt (D := D) w (fr (B'.β 0 0) (B'.β 1 0) (y'.1.map (eToEAf D))
          (Fin.cast (rank_vertex G' t w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
          (Fin.cast (rank_vertex G' t w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a)) -
        cpt (D := D) w (fr (B.β 0 0) (B.β 1 0) (x₀.map (eToEAf D))
          (Fin.cast (rank_vertex G t₀ w (X := (0, 0)) ⟨h.le, Nat.zero_le _⟩) b)
          (Fin.cast (rank_vertex G t₀ w (X := (1, 0)) ⟨h, Nat.zero_le _⟩) a))) ≤ _
    rw [← RingHom.map_sub, e2, RingHom.map_neg, Valuation.map_neg]
    exact v_le_cosExp G hs1 w
  ext x
  exact sub_mem_iff_of_sub_mem _ key x

end GlobalTheory.FunObj.CosFlip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsHeckeElementLatticeBetweenPrimeMulSplitStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_heckeElement_lattice_between_prime_mul_split : ∀ (D : D7) (V : HSp D) (P : Formalism.L2.DIV.Pl D.host.E) (e : AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (g : GA D V)
    (M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    Formalism.L2.NTheta.IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 →
    P.asIdeal • latG V g ≤ M → M ≤ latG V g →
    M.toAddSubgroup.relIndex (latG V g).toAddSubgroup = Ideal.absNorm P.asIdeal ^ k →
    ∃ a₀ : GA D V, Formalism.L2.NTheta.IsHeckeElt V e (ϖ : D.host.E) k a₀ ∧ latG V (g * a₀) ⊓ latG V g = M ∧
      (Formalism.L2.Col.conjPrime₂ P).asIdeal • latG V (g * a₀) ≤ latG V g := by
  first | exact @GlobalTheory.HeckeLocStep.exists_hecke | exact GlobalTheory.HeckeLocStep.exists_hecke | (intros; apply GlobalTheory.HeckeLocStep.exists_hecke <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRealIntertwinersUpwardThetaPairStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_realIntertwiners_upwardThetaPair : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → ∀ (D : D7) (t : ℕ) (V W : HSp D) (S S' : D.what₂.Tau → SPar) (M : DSModel V S) (M' : DSModel W S') (aS aT : D.what₂.Tau → ℚ) (θ : InfFam D) (ψ : AddChar (AF D.host.F) ℂ), IsInfFam θ → (∀ τ, UpPair t (S τ) (S' τ) (aS τ) (aT τ)) → (∃ It : PolF D W.rank V.rank →ₗ[ℂ] SmT M' →ₗ[ℂ] SmT M, ∀ ω f, GlobalTheory.PairLift.IsWeilExp ψ V W aS aT ω → GlobalTheory.Chain.IsVacVec ψ θ M M' f → IsItW θ M M' ω (GlobalTheory.Chain.ptOf ψ θ M M' f) It) ∧ ∃ It : PolF D V.rank W.rank →ₗ[ℂ] SmT M →ₗ[ℂ] SmT M', ∀ ω f, GlobalTheory.PairLift.IsWeilExp ψ W V aT aS ω → GlobalTheory.Chain.IsVacVec ψ θ M' M f → IsItW θ M' M ω (GlobalTheory.Chain.ptOf ψ θ M' M f) It := by
  first | exact @GlobalTheory.EvenOnto.upPair_itW | exact GlobalTheory.EvenOnto.upPair_itW | (intros; apply GlobalTheory.EvenOnto.upPair_itW <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaTripleBaseDataCharactersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaTriple_baseData_characters : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (W W₁ X : HSp D) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ ωA : WRep W X, IsWeil ψ true W X β (β / α) ωA →
    ∃ (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E),
      Bs.ψ = ψ ∧ Xc.α = α ∧ Xc.β = β ∧ Bs.IsGood D.sp.cm.sig ∧ Xc.IsGood Bs W.rank W₁.rank ∧
      (∀ w, ∃ τ, ∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧
      ∀ w, ((W.rank + W₁.rank : ℕ) : ℤ) < Bs.mα w - Bs.mβ w := by
  first | exact @GlobalTheory.TripleBaseChars.exists_base_chars | exact GlobalTheory.TripleBaseChars.exists_base_chars | (intros; apply GlobalTheory.TripleBaseChars.exists_base_chars <;> assumption)
end

