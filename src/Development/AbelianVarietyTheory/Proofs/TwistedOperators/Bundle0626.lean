import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0609
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0457
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightBelow
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0607
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0608
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0022
import Formalism.LocalToGlobal.ProjectiveLattices.LevelPb
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0122
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0574
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0596
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0017
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0617
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0018
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0022
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1904
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1439
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagOneNegOneConjAntidiagonalStabilizerMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrix

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactChainTopPairMovedVectorRowCharacter
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.IndefiniteRowSideFullHecke.MinorOrderedEntries
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowReal

section EigTop

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem cart_eq_one_of_posOnb (W : G.Weil) {X : Node} (hX : X.InRange D.R.m) (hP : PosOnb W X) (τ : D.what₂.Tau) :
    W.cart X τ = 1 := by
  obtain ⟨ε, h1, h2⟩ := W.onb_is X hX τ
  rw [hP τ] at h1
  rw [← h1, Matrix.mul_one] at h2
  have hd : IsUnit (W.onb X τ).det := Matrix.isUnit_det_of_left_inverse (hP τ)
  calc W.cart X τ = W.cart X τ * W.onb X τ * (W.onb X τ)⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.mul_one]
    _ = 1 := by rw [h2, Matrix.mul_nonsing_inv _ hd]

theorem compAt_mt_eq_archM (θ : InfFam D) (V : HSp D) (k : GA D V) (τ : D.what₂.Tau) :
    compAt θ τ (mt V k) = Formalism.L2.Pj.archM V (θ τ) k := by
  have e := GlobalTheory.RealType.realFr_coe θ V 1 k τ
  rw [GlobalTheory.RealType.realFr_one] at e
  rw [show compAt θ τ (mt V k) = ((GlobalTheory.CoefModel.realGL θ V k τ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) from rfl, e]
  simp

theorem det_conj_submatrix {a b : ℕ} (h : a = b) {B : Matrix (Fin b) (Fin b) ℂ} (hB : IsUnit B.det)
    (u : Matrix (Fin a) (Fin a) ℂ) :
    (B * u.submatrix (Fin.cast h.symm) (Fin.cast h.symm) * B⁻¹).det = u.det := by
  subst h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', mul_comm, ← mul_assoc,
    inv_mul_cancel₀ hB.ne_zero, one_mul]
  rfl

end EigTop

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section EigTop2

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem det_compAt_ptTop (W : G.Weil) (μ0 : T) (hL : L.Is μ0) {U : Set T} (N : Std G U)
    (g : Gc D.what₂.Tau (rowSizes D)) (n : Fin (D.R.m + 1)) (τ : D.what₂.Tau) :
    (compAt W.θ τ (mt (G.V (.top n)) (ptTop W g n))).det =
      (rowComp (rowSizes D) g n τ).1.det := by
  induction n using Fin.lastCases with
  | last =>
    show (compAt W.θ τ (mt (G.V (.top D.R.m)) (ptTop W g D.R.m))).det = _
    have hP : PosOnb W (.grid D.R.m D.R.m) :=
      posOnb_of_defNode W μ0 hL (X := .grid D.R.m D.R.m) ⟨le_rfl, rfl⟩
    have hd := fun τ => Matrix.isUnit_det_of_left_inverse (hP τ)
    rw [ptTop_m, kappaTop_apply, compAt_mt_eq_archM]
    have e1 : ∀ (X : Node) (k : GA D (G.V X)), (Formalism.L2.Pj.archM (G.V X) (W.θ τ) k).det =
        ((GlobalTheory.RealType.realAt W.θ N X k τ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ).det :=
      fun X k => by rw [GlobalTheory.RealType.realAt, GlobalTheory.RealType.realFr_coe, Matrix.det_units_conj']
    rw [e1, (GlobalTheory.RealType.isBlock_realAt W.θ_is N _ τ).det, mul_one, ← e1, ← compAt_mt_eq_archM]
    have e2 := compAt_kappa_snd g (Fin.last _) hP τ
    erw [e2, det_conj_submatrix (rank_gridM G le_rfl).symm (hd τ)]
    have e : rowComp (rowSizes D) g (Fin.last D.R.m) = embed (rowSizes D).nC_succ (g.2 (Fin.last D.R.m)) := by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]
      exact Fin.snoc_last (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j)) _ _
    erw [e]
    show _ = (Matrix.reindex (finSumFinEquiv.trans (finCongr (rowSizes D).nC_succ)) (finSumFinEquiv.trans (finCongr (rowSizes D).nC_succ))
      (Matrix.fromBlocks (g.2 (Fin.last D.R.m) τ).1 0 0 (1 : Matrix (Fin 1) (Fin 1) ℂ))).det
    rw [Matrix.det_reindex_self]
    exact ((Matrix.det_fromBlocks_zero₂₁ _ _ _).trans (by rw [Matrix.det_one, mul_one]; rfl)).symm
  | cast j =>
    show (compAt W.θ τ (mt (G.V (.top j)) (ptTop W g j))).det = _
    have hP : PosOnb W (.top j) := posOnb_of_defNode W μ0 hL (X := .top j) j.2.le
    rw [ptTop_lt W g j.2, compAt_kappa_fst g j hP τ, det_conj_submatrix (rank_top G j.2.le).symm (Matrix.isUnit_det_of_left_inverse (hP τ))]
    have e : rowComp (rowSizes D) g j.castSucc = g.1 j := by
      simp only [rowComp, MonoidHom.coe_mk, OneHom.coe_mk]
      exact Fin.snoc_castSucc (α := fun j : Fin ((rowSizes D).m + 1) => UG D.what₂.Tau ((rowSizes D).nR j)) _ _ j
    rw [e]

end EigTop2

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

section EigTop3

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem movedVec_theta_fock (W : G.Weil) (μ0 : T) (hL : L.Is μ0) {U : Set T} (S : GridChoice W U) (t : T) {j : ℕ}
    (hj : j + 1 ≤ D.R.m) (d : FinDatum G t (.top t j)) (hd : S.Z.HasVec d) :
    IsThetaFunO W.ψ (G.pS (.top t j)) (G.pT (.top t j)) (movedVec t S d) ∧
      ∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.top t j)) (G.pT (.top t j))) W.θ τ (cplxO 1 1) (movedVec t S d) := by
  have hr : (Pair.top t j : Pair T).InRange D.R.m := hj
  have hW := W.om_is _ hr
  have hX0 : DefNode D.R.m (.top j) := by show j ≤ D.R.m; omega
  have hX1 : DefNode D.R.m (.top (j + 1)) := hj
  have hc0 := cart_eq_one_of_posOnb W hX0.inRange (posOnb_of_defNode W μ0 hL hX0)
  have hc1 := cart_eq_one_of_posOnb W hX1.inRange (posOnb_of_defNode W μ0 hL hX1)
  obtain ⟨hv1, hv2⟩ := GlobalTheory.FockRealVec.vec_theta_fock W S.Z (p := .top t j) hj d hd
  have hv : ∀ τ, IsFockVacAt (heisO W.ψ (G.pS (.top t j)) (G.pT (.top t j))) W.θ τ (cplxO 1 1) (S.Z.vec d) := fun τ => by
    have := hv2 τ
    rwa [show G.cartS W.cart (.top t j) τ = 1 from hc0 τ, show G.onT W.cart (.top t j) τ = 1 from hc1 τ] at this
  refine ⟨hW.om_pres _ _ hv1, fun τ z => ?_⟩
  unfold movedVec
  generalize G.toPair (.top t j) (S.N.u (Pair.top t j).small).1 (S.N.u (Pair.top t j).big).1 = q
  obtain ⟨a, b⟩ := q
  obtain ⟨z₀, rfl⟩ : ∃ z₀ : Matrix (Fin (G.pT (.top t j)).rank) (Fin (G.pS (.top t j)).rank) ℂ, z = compAt W.θ τ (mt _ b) * z₀ * compAt W.θ τ (mt _ a⁻¹) := by
    refine ⟨compAt W.θ τ (mt _ b⁻¹) * z * compAt W.θ τ (mt _ a), ?_⟩
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.one_mul, Matrix.mul_assoc,
      GlobalTheory.OrientedHeis.compAt_mt_mul_inv, Matrix.mul_one]
  have h0 := congrArg (W.om _ (a, b)) (hv τ z₀)
  rw [GlobalTheory.FockMove.om_annih hW W.θ_is a b τ (by rw [Matrix.one_mul, Matrix.mul_one])
    (by rw [Matrix.one_mul, Matrix.mul_one]) z₀ hv1, map_zero] at h0
  exact h0

theorem cast_half {K : Type} [Field K] [CharZero K] {n : ℕ} (hn : Even n) : (((n / 2 : ℕ) : ℤ) : K) = (n : K) / 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [show (k + k) / 2 = k by omega]
  push_cast
  ring

end EigTop3

end GlobalTheory.RowReal

namespace GlobalTheory.RowReal

theorem om_ptTop_movedVec : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ0 : T}, L.Is μ0 →
    ∀ (W : G.Weil) {U : Set T} (S : GridChoice W U) (g : Gc D.what₂.Tau (GlobalTheory.RowReal.rowSizes D)) (t : T) (j : Fin D.R.m)
    (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    W.om (.top t j) (G.toPair (.top t j) (GlobalTheory.RowReal.ptTop W g j) (GlobalTheory.RowReal.ptTop W g (j + 1))) (movedVec t S d) =
      GlobalTheory.RowReal.rowScal (GlobalTheory.RowReal.rowEntries D sc.cGap) j g • movedVec t S d := by
  intro D T L sc G μ0 hL W U S g t j d hd
  have hj : (j : ℕ) + 1 ≤ D.R.m := j.2
  have hr : (Pair.top t (j : ℕ) : Pair T).InRange D.R.m := hj
  have hW := W.om_is _ hr
  have hX0 : DefNode D.R.m (.top j) := j.2.le
  have hX1 : DefNode D.R.m (.top ((j : ℕ) + 1)) := hj
  have hc0 := cart_eq_one_of_posOnb W hX0.inRange (posOnb_of_defNode W μ0 hL hX0)
  have hc1 := cart_eq_one_of_posOnb W hX1.inRange (posOnb_of_defNode W μ0 hL hX1)
  have hS : ∀ τ, IsCartanInv (gramAt D (G.V (.top j)) τ) 1 := fun τ => by
    have := W.cart_is _ hX0.inRange τ
    rwa [hc0 τ] at this
  have hT : ∀ τ, IsCartanInv (gramAt D (G.V (.top ((j : ℕ) + 1))) τ) 1 := fun τ => by
    have := W.cart_is _ hX1.inRange τ
    rwa [hc1 τ] at this
  obtain ⟨hm, hv⟩ := movedVec_theta_fock W μ0 hL S t hj d hd
  have ev0 : Even (G.V (.top j)).rank := by rw [rank_top G j.2.le]; exact even_nR _
  have ev1 : Even (G.V (.top ((j : ℕ) + 1))).rank := by rw [rank_top G hj]; exact even_nR _
  have hχS : G.chrS (.top t j) = L.mu t ((j : ℕ) + 1) := by
    show Formalism.IndefR.Lift.attChr (L.mu t ((j : ℕ) + 1)) L.eta (G.V (.top j)).rank = _
    simp [Formalism.IndefR.Lift.attChr, Nat.not_odd_iff_even.2 ev0]
  have hχT : G.chrT (.top t j) = L.mu t ((j : ℕ) + 1) := by
    show Formalism.IndefR.Lift.attChr (L.mu t ((j : ℕ) + 1)) L.eta (G.V (.top ((j : ℕ) + 1))).rank = _
    simp [Formalism.IndefR.Lift.attChr, Nat.not_odd_iff_even.2 ev1]
  have hexp : ∀ τ, HasInfExp D (L.mu t ((j : ℕ) + 1)) τ (-(((rowEntries D sc.cGap τ).e j : ℤ) : ℚ)) := fun τ => by
    have h := GlobalTheory.GridJoin.ColIt.hasInfExp_mu L hL t j τ
    have e : (((rowEntries D sc.cGap τ).e j : ℤ) : ℚ) = (D.hc τ).e j := by
      show (((num D sc.cGap τ).e ((j : ℕ) + 1) : ℤ) : ℚ) = _
      rw [num_e D sc.cGap τ (by omega) hj]
      rfl
    rwa [e]
  have key := GlobalTheory.VacuumCharacter.vacuum_character D W.ψ W.θ (G.V (.top j)) (G.V (.top ((j : ℕ) + 1)))
    (G.chrS (.top t j)) (G.chrT (.top t j)) (W.om (.top t j)) hW W.θ_is (hX0.sigOK G) (hX1.sigOK G) (fun _ => 1) hS hT
    (fun τ => -(((rowEntries D sc.cGap τ).e j : ℤ) : ℚ)) (fun τ => -(((rowEntries D sc.cGap τ).e j : ℤ) : ℚ))
    (fun τ => by rw [hχS]; exact hexp τ) (fun τ => by rw [hχT]; exact hexp τ)
    (fun τ => -(rowEntries D sc.cGap τ).e j + ((rowSizes D).nR j.castSucc / 2 : ℕ))
    (fun τ => -(rowEntries D sc.cGap τ).e j - ((rowSizes D).nR j.castSucc / 2 : ℕ))
    (fun τ => (rowEntries D sc.cGap τ).e j - ((rowSizes D).nR j.succ / 2 : ℕ))
    (fun τ => by
      rw [Int.cast_add, Int.cast_neg, Fin.val_castSucc, cast_half (even_nR (S := rowSizes D) j), rank_top G j.2.le])
    (fun τ => by
      rw [Int.cast_sub, Int.cast_neg, Fin.val_castSucc, cast_half (even_nR (S := rowSizes D) j), rank_top G j.2.le])
    (fun τ => by
      rw [Matrix.trace_one, Fintype.card_fin, rank_top G hj, Int.cast_sub, Fin.val_succ,
        cast_half (even_nR (S := rowSizes D) ((j : ℕ) + 1))]
      push_cast
      ring)
    (movedVec t S d) hm hv (ptTop W g j) (ptTop_mem W g j) (ptTop W g ((j : ℕ) + 1)) (ptTop_mem W g _)
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
  rw [show G.toPair (.top t j) (ptTop W g j) (ptTop W g ((j : ℕ) + 1)) = (ptTop W g j, ptTop W g ((j : ℕ) + 1)) from rfl, key]
  congr 1
  clear key hexp hχS hχT ev0 ev1 hm hv hS hT hc0 hc1 hW hr hd
  have a1 : (1 / 2 : ℂ) • ((1 : Matrix (Fin (G.V (.top ((j : ℕ) + 1))).rank) (Fin (G.V (.top ((j : ℕ) + 1))).rank) ℂ) + 1) = 1 := by
    module
  simp only [a1, sub_self, smul_zero, Matrix.zero_mul, Matrix.one_mul, add_zero, zero_add, Matrix.det_one, one_zpow, mul_one]
  have hg : ∀ τ, (compAt W.θ τ (mt (G.V (.top j)) (ptTop W g j))).det = (rowComp (rowSizes D) g j.castSucc τ).1.det :=
    fun τ => det_compAt_ptTop W μ0 hL S.N g j.castSucc τ
  have hh : ∀ τ, (compAt W.θ τ (mt (G.V (.top ((j : ℕ) + 1))) (ptTop W g ((j : ℕ) + 1)))).det =
      (rowComp (rowSizes D) g j.succ τ).1.det :=
    fun τ => det_compAt_ptTop W μ0 hL S.N g j.succ τ
  simp only [hg, hh]
  simp [rowScal, detChar, detU, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun τ _ => mul_comm _ _

end GlobalTheory.RowReal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryAdelicSchwartzArchimedeanReplaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complementaryAdelicSchwartz_archimedean_replace : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (r : (κ → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r → f ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
  first | exact @GlobalTheory.TwistRest.restTr | exact GlobalTheory.TwistRest.restTr | (intros; apply GlobalTheory.TwistRest.restTr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CosetDatumVectorFiniteHeisenbergCombinationStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cosetDatumVector_finite_heisenbergCombination : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {W : G.Weil} (S : GridChoice W Set.univ) (t : T) (p : Pair T), DefPair D.R.m p → ∀ (k : ℕ) (d : FinDatum G t p), 0 < k → IsCosetDatum k d → d.z = 1 → d.P = locPl G t → ∃ (n : ℕ) (c : Fin n → Formalism.MainNotions.TaylorLogMetric.Qbar) (w : Fin n → WO (G.pS p) (G.pT p)), (∀ i, k • w i ∈ latO (G.pS p) (G.pT p) (S.N.latS p : Set _) (S.N.latT p : Set _) fun _ => True) ∧ (∀ i, (w i).map (infPart D) = 0) ∧ (∀ i, IsIntegral ℤ ((k : Formalism.MainNotions.TaylorLogMetric.Qbar) ^ (D.R.f * (G.pS p).rank * (G.pT p).rank) * c i)) ∧ (∀ ρ : Formalism.MainNotions.TaylorLogMetric.Qbar →+* ℂ, ∑ i, ‖ρ (c i)‖ ≤ 1) ∧ S.Z.vec d = ∑ i, (c i : ℂ) • heisO W.ψ (G.pS p) (G.pT p) (w i) (S.Z.vac p) := by
  first | exact @GlobalTheory.RowEx.fourierVec | exact GlobalTheory.RowEx.fourierVec | (intros; apply GlobalTheory.RowEx.fourierVec <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CoverFieldOfContainsRayField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TwistField

theorem coverField_of_containsRayField : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F), LawsJ T → R.toLevCh.Is A.μ0 → QGuard R → (∀ t, GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.ContainsRayField (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t)) → GlobalTheory.TwistField.CoverField T R := by
  intro D G _ _ Pl0 T0 A T _ R hT hL hQ hray
  unfold GlobalTheory.TwistField.CoverField
  intro i t l₂ hdvd hM hA Xo₂ c₂ hc
  obtain ⟨hHost, hLev, -, -⟩ := hT.pins
  unfold Par.PinHost at hHost
  unfold Par.PinLevel at hLev

  have hn : GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t = l₂.M := by
    rw [hM, hLev.1]
    rfl

  have hsq : ∃ a : D.host.K, a ^ 2 = -(T.Q.H.d : D.host.K) := by
    refine ⟨⟨D.host.sqrtMinusD, Formalism.L2.Pj.LPb.sqrtMinusD_mem_K D⟩, ?_⟩
    rw [hHost.1]
    apply Subtype.ext
    push_cast
    exact Formalism.BasicNotions.Host.sqrtMinusD_sq D.host
  have h3 : 3 ≤ GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t := hn ▸ l₂.three_le

  have hW := (GlobalTheory.T.weberValues_mem_of_containsRayField D.host.E T.Q.H D.host.K D.what₂.LL (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.embK D) D.what₂.embLL
    (Formalism.L2.Pj.LPb.finrank_K D) hsq _ h3 (hray t)).1
  refine GlobalTheory.T.geometricallyIrreducible_components_weberValues D T.Q hT.pins ((i : ℕ) + 1) ⟨by omega, by omega⟩ l₂ Xo₂ c₂
    (GlobalTheory.IndefiniteRowSideFullHecke.RayFieldTheta.tupLevel R t) (by omega) ?_ (Or.inl (hc ▸ hW))
  show Nat.lcm l₂.M l₂.A ∣ _
  rw [hA, Nat.lcm_one_right, hn]

end GlobalTheory.TwistField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormOfTypeEqFiniteSum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open Classical

namespace GlobalTheory.DefiniteDecomp

open Formalism.IndefR.Mult Matrix GlobalTheory.Grid

theorem cusp_decomp : GlobalTheory.FunPr.Hypotheses₂ → ∀ {D : D7} (θ : InfFam D) (N : GlobalTheory.Grid.Node D), IsInfFam θ → N.V.SigOK → N.V.IsDefinite →
    ∀ φ, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N φ →
      ∃ (n : ℕ) (F : Fin n → N.Cusp θ) (w : Fin n → SmT N.M), φ = ∑ i, (F i).1 (w i) := by
  intro hP D θ N hθ hs hd φ hφ
  obtain ⟨hAut, -, hType⟩ := hφ
  haveI hfd : ∀ τ, FiniteDimensional ℂ (N.M.H τ) := fun τ => GlobalTheory.DefiniteEnd.finiteDimensional_model hs hd N.M τ
  have hmulK : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ),
      g * h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) := fun τ g hg h hh => GlobalTheory.PointAtPlaceHom.mul_mem_UH hg hh
  have hρ : ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ),
      (N.M.rep τ (g * h) : N.M.H τ →ₗ[ℂ] N.M.H τ) =
        (N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ (N.M.rep τ h : N.M.H τ →ₗ[ℂ] N.M.H τ) := by
    intro τ g hg h hh
    rw [rep_mul N.M τ hg hh]
    rfl
  have hframe : ∀ τ, ∃ (m : ℕ) (k : Fin m → Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ)
      (B : Fin m → (N.M.H τ →ₗ[ℂ] N.M.H τ)), (∀ j, k j ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) ∧
      (∀ A : N.M.H τ →ₗ[ℂ] N.M.H τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ),
        LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ A) =
          ∑ j, LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ (k j) : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ A) *
            LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ B j)) ∧
      (∀ i, ∀ h ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), B i ∘ₗ (N.M.rep τ h : N.M.H τ →ₗ[ℂ] N.M.H τ) =
        ∑ j, LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ (k j) : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ
          (B i ∘ₗ (N.M.rep τ h : N.M.H τ →ₗ[ℂ] N.M.H τ))) • B j) :=
    fun τ => GlobalTheory.T.exists_dual_frame_span_unitary_representation (Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) (fun g => (N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ))
      (hmulK τ) (hρ τ) (fun g hg => ⟨g⁻¹, (GlobalTheory.T.discreteSeriesModel_adjoint_eq_inv_finiteDimensional N.M τ hg).1, (GlobalTheory.T.discreteSeriesModel_adjoint_eq_inv_finiteDimensional N.M τ hg).2⟩)
  choose m k B hk hB1 hB2 using hframe
  have hexp : ∀ τ x, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ), φ (x * atTau θ N.V τ g) =
      ∑ j, φ (x * atTau θ N.V τ (k τ j)) *
        LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ B τ j) :=
    fun τ x g hg => GlobalTheory.T.modelType_form_expands_along_dualFrame hP.discreteSeriesHermitianUnique θ N.M τ (k τ) (hk τ) (B τ) (hB1 τ) (hType τ) x hg

  let F : GA D N.V → (D.what₂.Tau → Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ) → ℂ :=
    fun x g => φ (x * realProd θ N.V g)
  have hsplit : ∀ x (g : D.what₂.Tau → Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ),
      (∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) → ∀ τ₀ g', g' ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ₀) →
      F x (Function.update g τ₀ g') = φ ((x * realProd θ N.V (Function.update g τ₀ 1)) * atTau θ N.V τ₀ g') := by
    intro x g hg τ₀ g' hg'
    show φ (x * realProd θ N.V (Function.update g τ₀ g')) = _
    rw [realProd_update hθ hg τ₀ hg', (realProd_commute hθ hg τ₀ hg').eq, mul_assoc]
  have hFexp : ∀ x τ₀ (g : D.what₂.Tau → Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ),
      (∀ τ, g τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) → F x g = ∑ j, F x (Function.update g τ₀ (k τ₀ j)) *
        LinearMap.trace ℂ (N.M.H τ₀) ((N.M.rep τ₀ (g τ₀) : N.M.H τ₀ →ₗ[ℂ] N.M.H τ₀) ∘ₗ B τ₀ j) := by
    intro x τ₀ g hg
    have e0 : F x g = F x (Function.update g τ₀ (g τ₀)) := by rw [Function.update_eq_self]
    rw [e0, hsplit x g hg τ₀ _ (hg τ₀), hexp τ₀ _ _ (hg τ₀)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsplit x g hg τ₀ _ (hk τ₀ j)]

  let bH : ∀ τ, Module.Basis (Fin (Module.finrank ℂ (N.M.H τ))) ℂ (N.M.H τ) := fun τ => Module.finBasis ℂ (N.M.H τ)
  let ℓ : (∀ τ, Fin (Module.finrank ℂ (N.M.H τ))) → ∀ τ, Fin (m τ) → (N.M.sm τ →ₗ[ℂ] ℂ) :=
    fun a τ j => (bH τ).coord (a τ) ∘ₗ B τ j ∘ₗ (N.M.sm τ).subtype
  let T : (∀ τ, Fin (Module.finrank ℂ (N.M.H τ))) → MMap N.M := fun a =>
    ∑ J : (∀ τ, Fin (m τ)), ((MultilinearMap.mkPiAlgebra ℂ D.what₂.Tau ℂ).compLinearMap
      (fun τ => ℓ a τ (J τ))).smulRight (fun x => F x (fun τ => k τ (J τ)))
  have hT : ∀ a v x, T a v x = ∑ J : (∀ τ, Fin (m τ)), (∏ τ, ℓ a τ (J τ) (v τ)) * F x (fun τ => k τ (J τ)) := by
    intro a v x
    simp only [T, MultilinearMap.sum_apply, Finset.sum_apply, MultilinearMap.smulRight_apply,
      MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply, Pi.smul_apply, smul_eq_mul]
  have hMult : ∀ a, IsMultMap θ N.M ∅ 1 (T a) := by
    intro a
    refine ⟨fun v => ?_, fun v => GlobalTheory.DefiniteEnd.isCuspFun_of_definite hs hd _,
      fun v k' hk' => absurd hk' (Set.notMem_empty k'), fun τ₀ h hh v w hw => ?_, fun τ v x => ?_⟩
    · have e : T a v = ∑ J : (∀ τ, Fin (m τ)), (∏ τ, ℓ a τ (J τ) (v τ)) •
          rTr N.V (realProd θ N.V (fun τ => k τ (J τ))) φ := by
        funext x
        rw [hT, Finset.sum_apply]
        rfl
      rw [e]
      refine Finset.sum_induction _ (IsAutFunSm θ N.V) (fun f g hf hg => GlobalTheory.MultMem.isAutFunSm_add hf hg) ?_
        (fun J _ => GlobalTheory.MultMem.isAutFunSm_smul _ (isAutFunSm_realProd hθ _ hAut))
      exact Formalism.L2.Theta.isAutFunSm_const (θ := θ) (V := N.V) (c := (0 : ℂ))
    · funext x
      have hkJ : ∀ J : (∀ τ, Fin (m τ)), ∀ τ, (fun τ => k τ (J τ)) τ ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ) :=
        fun J τ => hk τ (J τ)
      have hF' : ∀ J : (∀ τ, Fin (m τ)), F (x * atTau θ N.V τ₀ h) (fun τ => k τ (J τ)) =
          F x (Function.update (fun τ => k τ (J τ)) τ₀ (h * k τ₀ (J τ₀))) := by
        intro J
        show φ (x * atTau θ N.V τ₀ h * realProd θ N.V _) = φ (x * realProd θ N.V _)
        have e1 := realProd_update hθ (hkJ J) τ₀ (hmulK τ₀ h hh _ (hk τ₀ (J τ₀)))
        have e2 := realProd_update hθ (hkJ J) τ₀ (hk τ₀ (J τ₀))
        rw [Function.update_eq_self] at e2
        rw [e1, e2, GlobalTheory.PointAtPlaceHom.atTau_mul hθ N.V τ₀ hh (hk τ₀ (J τ₀))]
        simp only [mul_assoc]
      show T a (Function.update v τ₀ w) x = T a v (x * atTau θ N.V τ₀ h)
      rw [hT, hT]
      simp only [hF']
      have key := GlobalTheory.T.sum_prod_update_regroup_of_update_eq (X := fun _ => Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ) (W := fun τ => N.M.sm τ)
        k (ℓ a) τ₀ (F x) (fun g => F x (Function.update g τ₀ (h * g τ₀))) (v τ₀) w ?_ v
      · rw [Function.update_eq_self] at key
        exact key
      intro J
      simp only [Function.update_idem, Function.update_self]
      have hf : ∀ g' ∈ Formalism.QuantumDeterminants.UH (gramAt D N.V τ₀), F x (Function.update (fun τ => k τ (J τ)) τ₀ g') =
          ∑ j, F x (Function.update (fun τ => k τ (J τ)) τ₀ (k τ₀ j)) *
            LinearMap.trace ℂ (N.M.H τ₀) ((N.M.rep τ₀ g' : N.M.H τ₀ →ₗ[ℂ] N.M.H τ₀) ∘ₗ B τ₀ j) := by
        intro g' hg'
        rw [hsplit x _ (hkJ J) τ₀ g' hg', hexp τ₀ _ g' hg']
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hsplit x _ (hkJ J) τ₀ _ (hk τ₀ j)]
      have := equiv_one (Formalism.QuantumDeterminants.UH (gramAt D N.V τ₀)) (fun g => (N.M.rep τ₀ g : N.M.H τ₀ →ₗ[ℂ] N.M.H τ₀))
        (hρ τ₀) (k τ₀) (hk τ₀) (B τ₀) (hB2 τ₀) _ hf (hmulK τ₀) ((bH τ₀).coord (a τ₀)) (v τ₀ : N.M.H τ₀) hh
      simp only [ℓ, LinearMap.comp_apply, Submodule.subtype_apply, hw]
      exact this
    · exact GlobalTheory.DefiniteEnd.exists_sobCont N.M τ (T a) v x
  have hmem : ∀ a, PiTensorProduct.lift (T a) ∈ N.Cusp θ := fun a =>
    (mem_multT θ N.M ∅ 1 _).2 (by rw [LinearEquiv.symm_apply_apply]; exact Submodule.subset_span (hMult a))
  let e : ∀ τ, Fin (Module.finrank ℂ (N.M.H τ)) → N.M.sm τ := fun τ i => ⟨bH τ i, by rw [sm_eq_top N.M τ]; trivial⟩
  have htr : ∀ τ j, LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ 1 : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ B τ j) =
      ∑ i, (bH τ).coord i (B τ j (bH τ i)) := by
    intro τ j
    rw [rep_one N.M τ, ContinuousLinearMap.toLinearMap_one, Module.End.one_eq_id, LinearMap.id_comp,
      LinearMap.trace_eq_matrix_trace ℂ (bH τ), Matrix.trace]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.coord_apply]
  have hrep : ∀ x, φ x = ∑ a : (∀ τ, Fin (Module.finrank ℂ (N.M.H τ))), T a (fun τ => e τ (a τ)) x := by
    intro x
    have h1 : φ x = F x (fun _ => 1) := by
      show φ x = φ (x * realProd θ N.V _)
      rw [realProd_one hθ, mul_one]
    have h2 := GlobalTheory.T.eq_sum_prod_of_expansion_in_each_coordinate (X := fun _ => Matrix (Fin N.V.rank) (Fin N.V.rank) ℂ)
      (fun τ => Formalism.QuantumDeterminants.UH (gramAt D N.V τ)) m k hk
      (fun τ j g => LinearMap.trace ℂ (N.M.H τ) ((N.M.rep τ g : N.M.H τ →ₗ[ℂ] N.M.H τ) ∘ₗ B τ j)) (F x)
      (fun τ₀ g hg => hFexp x τ₀ g hg) (fun _ => 1) (fun τ => GlobalTheory.PointAtPlaceHom.one_mem_UH _)
    rw [h1, h2]
    simp only [hT]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [← Finset.sum_mul, mul_comm]
    congr 1
    simp only [htr]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
    rfl
  let eqv := Fintype.equivFin (∀ τ, Fin (Module.finrank ℂ (N.M.H τ)))
  refine ⟨Fintype.card _, fun i => ⟨PiTensorProduct.lift (T (eqv.symm i)), hmem _⟩,
    fun i => PiTensorProduct.tprod ℂ (fun τ => e τ (eqv.symm i τ)), ?_⟩
  funext x
  rw [hrep x, Finset.sum_apply]
  simp only [PiTensorProduct.lift.tprod]
  exact (Equiv.sum_comp eqv.symm (fun a => T a (fun τ => e τ (a τ)) x)).symm

end GlobalTheory.DefiniteDecomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagonalFixingDoublingMatrixMemIntegralSiegelParStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_parD_matD_eq_diagonalFixingDoublingMatrix : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d) (v : Pl F), (2 : 𝓞 F) ∉ v.asIdeal →
    ∀ c : AE F E, cA σ c = -c → At (evFin F v) c → (∀ z ∈ GlobalTheory.InertSph.latAt W v, c • z ∈ GlobalTheory.InertSph.latAt W v) →
    ∃ p ∈ GlobalTheory.InertDbl.ParD σ W v, GlobalTheory.InertDbl.matD p = GlobalTheory.SplitDblGen.diagonalFixingDoublingMatrix c d := by
  first | exact @GlobalTheory.SplitDblPar.diagonalFixingDoublingMatrix_mem_integralSiegelParabolic | exact GlobalTheory.SplitDblPar.diagonalFixingDoublingMatrix_mem_integralSiegelParabolic | (intros; apply GlobalTheory.SplitDblPar.diagonalFixingDoublingMatrix_mem_integralSiegelParabolic <;> assumption)
end

