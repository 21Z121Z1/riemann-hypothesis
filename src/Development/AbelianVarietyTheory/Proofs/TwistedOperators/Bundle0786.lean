import Mathlib
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0559
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0256
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1852
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0841
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.OddnessConditionHolds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0783
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0113
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0333
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0290
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0760
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0677
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0428
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0390
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0407
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0106
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0575
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0698
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0700
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0782
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0699
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RepresentationAtEveryPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0714
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0778
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeriodLocalGroupsNormalFramesSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupClosedEmbeddingIntegral
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBessel
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0202
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalBlockDetBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0784
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0174
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0360
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0381
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0703

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierCoeffScalarInvariant
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

namespace GlobalTheory.MovedKappaArith

theorem selfDualIntertwiner_baseVector_ne_zero {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} (hC : Crv D cc δ)
    (ht : GL3Theta.IsTwoTorsionPointUnkilled D (lamOf D cc δ) t0) {N N' : ℕ} {e0 : VC D N N' → ℂ} (he : oddE0 D cc δ t0 N N' e0)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hL : SD D L) (hL' : SD D L') :
    Iop D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L') e0 ≠ 0 := by
  have s0 := GlobalTheory.MovedVacuum.sd_stdL D N
  have s0' := GlobalTheory.MovedVacuum.sd_stdL D N'
  have k0 : KLat D (tor0 D cc δ) (La0 D (tor0 D cc δ) N N') := Or.inr ⟨_, _, s0, s0', rfl⟩
  have k1 : KLat D (tor0 D cc δ) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D cc δ) L L') := Or.inr ⟨_, _, hL, hL', rfl⟩
  have huni := GlobalTheory.theta_translation_intertwiner_unitary D cc δ hC N N' _ _ k0 k1
  intro h
  exact GlobalTheory.TrueTheta.ne_zero_of_like hC ht s0 s0' he.2.2.2.1
    (by rw [← (huni e0 he.1).2.2.2, h, GlobalTheory.VacuumScalar.Iop_zero])

theorem applyAt0_monomial (D : D7) {N N' : ℕ} (α : Mono D N N') (G : VC D N N' → ℂ) :
    Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial α 1) G
      = (α.prod fun _ n => (n.factorial : ℂ)) * Formalism.MainNotions.TaylorLogMetric.taylor D G α := by
  classical
  unfold Formalism.MainNotions.GL3Theta.applyAt0
  rw [MvPolynomial.support_monomial, if_neg one_ne_zero, Finset.sum_singleton, MvPolynomial.coeff_monomial,
    if_pos rfl, one_mul]

end GlobalTheory.MovedKappaArith

namespace GlobalTheory.MovedKappaArith

theorem kappa_unique : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∀ κ κ' : ℂ, (∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z)) → (∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ' * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z)) → κ = κ' := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y κ κ' h1 h2
  set F := Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) with hFdef
  have hF : Differentiable ℂ F :=
    GlobalTheory.MovedDict.Entire.differentiable_intertwining_moved hPr hInp ch hIs p hp x y
  obtain ⟨hsd, hsd'⟩ := GlobalTheory.MovedSD.sd_srcLat_tgtLat hPr hInp ch hIs p hp x y
  have hF0 : F ≠ 0 := selfDualIntertwiner_baseVector_ne_zero ch.S.Z.crv ch.S.Z.pt0 (ch.S.Z.e0_is p hp) hsd hsd'
  obtain ⟨α, hα⟩ := GlobalTheory.NatFamily.exists_taylor_ne D hF hF0
  have e := (h1 α).symm.trans (h2 α)
  rw [applyAt0_monomial, applyAt0_monomial, GlobalTheory.ProdThetaConj.taylor_const_mul hF,
    GlobalTheory.ProdThetaConj.taylor_const_mul hF] at e
  have e' := (opp p).injective (mul_left_cancel₀ (ch.S.Z.c0 p).ne_zero e)
  have hP : (α.prod fun v e => period ch.S.Z.δ v.1 ^ e) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (GlobalTheory.FunObj.period_ne_zero (GlobalTheory.TwoTorsionPt.delta_ne ch.S.Z.crv) v.1)
  have hfac : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have e'' := mul_left_cancel₀ (mul_ne_zero hP hfac) (by simpa only [mul_assoc] using e')
  exact mul_right_cancel₀ hα e''

end GlobalTheory.MovedKappaArith

namespace GlobalTheory.MovedKappaArith

theorem kappa_arith : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∀ κ : ℂ, (∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z)) →
    Mod1All κ ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y κ hj
  obtain ⟨κ₀, hm, hu, hj₀⟩ := GlobalTheory.T.exists_unit_modulus_scalar_local hPr hInp ch hIs p hp x y
  obtain rfl := kappa_unique hPr hInp ch hIs p hp x y κ κ₀ hj hj₀
  exact ⟨hm, hu⟩

end GlobalTheory.MovedKappaArith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FourierJacobiToBesselLatticeSplits
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section
namespace GlobalTheory.AscFin.SplitsFB

theorem inv_neg_mat {D : D7} {n : ℕ} (A : Matrix (Fin n) (Fin n) D.host.E) : (-A)⁻¹ = -A⁻¹ := by
  by_cases h : IsUnit A.det
  · exact Matrix.inv_eq_left_inv (by rw [neg_mul_neg, Matrix.nonsing_inv_mul A h])
  · have h' : ¬ IsUnit (-A).det := by
      rw [Matrix.det_neg]
      intro hu
      exact h (isUnit_of_mul_isUnit_right hu)
    rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h', neg_zero]

theorem symplO_negSp {D : D7} (S T : HSp D) (x y : WO S T) : symplO (negSp S) T x y = -symplO S T x y := by
  have e : hO (negSp S) T x y = -hO S T x y := by
    unfold hO
    rw [negSp_gram, inv_neg_mat]
    simp only [Matrix.neg_apply, map_neg, neg_mul, Finset.sum_neg_distrib]
  unfold symplO
  rw [e, mul_neg, map_neg]

theorem symplO_zero_left' {D : D7} (S T : HSp D) (y : WO S T) : symplO S T 0 y = 0 := by
  unfold symplO hO
  simp

section
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc)

theorem sd_grid (i : ℕ) (h1 : 1 ≤ i) (h : i ≤ D.R.m) : IsSelfDualC (G.V (.grid i 0)) (G.Λ (.grid i 0)) :=
  (G.isV (X := .grid i 0) (by show _ ∧ _; constructor <;> omega) (by intro j hj; injection hj with h2; omega)).sd

theorem latRow_mxAt (i : ℕ) (h1 : 1 ≤ i) (h : i + 1 ≤ D.R.m) {u} (hu : u ∈ latRow G i) : MxAt (fun _ => True) u :=
  ((GlobalTheory.T.mem_homLatticeCompletion_iff_supported_maps D _ _ _ _ (isSelfDualC_neg (sd_grid G (i + 1) (by omega) h)) (sd_grid G i h1 (by omega)) (fun _ => True) u).1
    hu.1).1

theorem latRow_pair (W : G.Weil) (i : ℕ) (h1 : 1 ≤ i) (h : i + 1 ≤ D.R.m) {u u'} (hu : u ∈ latRow G i) (hu' : u' ∈ latRow G i) :
    W.ψ (symplO (G.V (.grid (i + 1) 0)) (G.V (.grid i 0)) u u') = 1 := by
  have := (GlobalTheory.T.homLatticeCompletion_self_annihilator_atPlaces D W.ψ W.ψ_std _ _ _ _ (isSelfDualC_neg (sd_grid G (i + 1) (by omega) h)) (sd_grid G i h1 (by omega))
    (fun _ => True) u (latRow_mxAt G i h1 h hu)).1 hu.1 u' hu'.1
  rwa [symplO_negSp, AddChar.map_neg_eq_inv, inv_eq_one] at this

theorem mxAt_mul {P : GlobalTheory.FinPl.Pl D → Prop} {m n k : ℕ} {x : Mx D m n} (hx : MxAt P x) (y : Mx D n k) : MxAt P (x ⬝ y) :=
  fun i j => by
    show (x * y) i j ∈ _
    rw [Matrix.mul_apply]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_right _ _ (hx i l)

end

set_option maxHeartbeats 2000000 in

theorem splits_FB : OnStd fun {D} _ _ {sc} {G} W F => ∀ σ (h : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m),
    Splits (F.dJ (σ + 1) h) (F.dB σ h') (pcFB W F σ h h') (xFB F σ h') 0 W.ψ (latRow G (2 * σ + 2)) := by
  intro D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hS := GlobalTheory.T.depthLatticeGridRow_stable_witt_projections D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hT := GlobalTheory.T.depthLatticeGridRow_stable_wittTargetProjections D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hC := GlobalTheory.T.fourierJacobi_basePoint_character_trivial_depthLattice D hq T L μ0 hL sc G W M hM F hF σ h h'
  have hB := GlobalTheory.T.depthLatticeGridRow_le_selfDualHomLatticeShift D hq T L μ0 hL sc G W M hM (2 * σ + 2) (by omega) (by omega)
  refine ⟨fun u hu => ?_⟩
  set dV := F.dJ (σ + 1) h with hdV
  set dW := F.dB σ h' with hdW
  obtain ⟨hX, hY⟩ := hS u hu
  have e1 := dV.sum_eq_one
  have e2 := dW.sum_eq_one
  have h0 : u ⬝ (dV.j0 ⬝ dV.p0) ∈ latRow G (2 * σ + 2) := by
    have s : u ⬝ (dV.jX ⬝ dV.pX) + u ⬝ (dV.j0 ⬝ dV.p0) + u ⬝ (dV.jY ⬝ dV.pY) = u := by
      rw [← Matrix.mul_add, ← Matrix.mul_add, e1, Matrix.mul_one]
    have e : u ⬝ (dV.j0 ⬝ dV.p0) = u - u ⬝ (dV.jX ⬝ dV.pX) - u ⬝ (dV.jY ⬝ dV.pY) := by
      rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq]
      conv_rhs => rw [← s]
      abel
    rw [e]
    exact sub_mem (sub_mem hu hX) hY
  set w := u ⬝ (dV.j0 ⬝ dV.p0) with hw
  obtain ⟨gX, gY⟩ := hT w h0
  have g0 : (dW.j0 ⬝ dW.p0) ⬝ w ∈ latRow G (2 * σ + 2) := by
    have s : (dW.jX ⬝ dW.pX) ⬝ w + (dW.j0 ⬝ dW.p0) ⬝ w + (dW.jY ⬝ dW.pY) ⬝ w = w := by
      rw [← Matrix.add_mul, ← Matrix.add_mul, e2, Matrix.one_mul]
    have e : (dW.j0 ⬝ dW.p0) ⬝ w = w - (dW.jX ⬝ dW.pX) ⬝ w - (dW.jY ⬝ dW.pY) ⬝ w := by
      rw [eq_sub_iff_add_eq, eq_sub_iff_add_eq]
      conv_rhs => rw [← s]
      abel
    rw [e]
    exact sub_mem (sub_mem h0 gX) gY
  have hA1 : dV.extX (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jX) ∈ latRow G (2 * σ + 2) := by
    rw [HypDec.extX_apply, Matrix.mul_assoc]; exact hX
  have hA2 : dV.extY (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jY) ∈ latRow G (2 * σ + 2) := by
    rw [HypDec.extY_apply, Matrix.mul_assoc]; exact hY
  have hB1 : dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.incX _ (dW.pX ⬝ (u ⬝ dV.j0))) = (dW.jX ⬝ dW.pX) ⬝ w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.incX_apply, hw]; simp only [Matrix.mul_assoc]
  have hB2 : dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.incY _ (dW.pY ⬝ (u ⬝ dV.j0))) = (dW.jY ⬝ dW.pY) ⬝ w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.incY_apply, hw]; simp only [Matrix.mul_assoc]
  have hG0 : dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.inc0 _ (dW.p0 ⬝ (u ⬝ dV.j0))) = (dW.j0 ⬝ dW.p0) ⬝ w := by
    rw [HypDec.matrixExtendByZero_apply, HypDec.wittDecomp_inclAnisotropicHom_apply, hw]; simp only [Matrix.mul_assoc]
  have heq : u = dV.extX (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jX) + dV.extY (G.V (.grid (2 * σ + 2) 0)) (u ⬝ dV.jY) +
      dV.ext0 (G.V (.grid (2 * σ + 2) 0)) (dW.incX _ (dW.pX ⬝ (u ⬝ dV.j0)) + dW.incY _ (dW.pY ⬝ (u ⬝ dV.j0)) +
        dW.inc0 _ (dW.p0 ⬝ (u ⬝ dV.j0))) := by
    rw [map_add, map_add, hB1, hB2, hG0, HypDec.extX_apply, HypDec.extY_apply, ← Matrix.add_mul, ← Matrix.add_mul,
      show dW.jX ⬝ dW.pX + dW.jY ⬝ dW.pY + dW.j0 ⬝ dW.p0 = 1 from (add_right_comm _ _ _).trans e2, Matrix.one_mul, hw,
      Matrix.mul_assoc, Matrix.mul_assoc]
    have s : u ⬝ (dV.jX ⬝ dV.pX) + u ⬝ (dV.j0 ⬝ dV.p0) + u ⬝ (dV.jY ⬝ dV.pY) = u := by
      rw [← Matrix.mul_add, ← Matrix.mul_add, e1, Matrix.mul_one]
    conv_lhs => rw [← s]
    abel
  refine ⟨u ⬝ dV.jX, hA1, u ⬝ dV.jY, AddSubgroup.subset_closure
      ⟨mxAt_mul (latRow_mxAt G (2 * σ + 2) (by omega) (by omega) hu) _,
        fun a ha => latRow_pair G W (2 * σ + 2) (by omega) (by omega) ha hA2⟩,
    dW.pX ⬝ (u ⬝ dV.j0), ?_, dW.pY ⬝ (u ⬝ dV.j0), ?_, dW.p0 ⬝ (u ⬝ dV.j0), ?_, heq, hC _ hA2, ?_⟩
  · show dV.ext0 _ (dW.incX _ (dW.pX ⬝ (u ⬝ dV.j0))) ∈ latBig G (2 * σ + 2)
    rw [hB1]; exact hB gX
  · show dV.ext0 _ (dW.incY _ (dW.pY ⬝ (u ⬝ dV.j0))) ∈ latBig G (2 * σ + 2)
    rw [hB2]; exact hB gY
  · show dV.ext0 _ (dW.inc0 _ (dW.p0 ⬝ (u ⬝ dV.j0))) ∈ latRow G (2 * σ + 2)
    rw [hG0]; exact g0
  · rw [map_zero, symplO_zero_left', AddChar.map_zero_eq_one]

end GlobalTheory.AscFin.SplitsFB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridRowZeroBasePointCarriesLattice
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal GlobalTheory.FinPl
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RowShape

theorem moves_of_forall {D : D7} (S : HSp D) (g : GA D S) (L M : GlobalTheory.FinPl.Lat S) (hL : Submodule.IsLattice D.host.E L)
    (hM : Submodule.IsLattice D.host.E M) (h : ∀ v : GlobalTheory.FinPl.Pl D, GlobalTheory.FinPl.Moves S g L M (· = v)) :
    GlobalTheory.FinPl.Moves S g L M (fun _ => True) := by
  intro y hy
  have hT := fun (N : GlobalTheory.FinPl.Lat S) (hN : Submodule.IsLattice D.host.E N) (z : Fin S.rank → AE D) =>
    ((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun _ => True)).2 S).2.2.2 N z hN
  have hmy : ∀ i, (Formalism.L2.Theta.mt S g *ᵥ y) i ∈ idAt D (fun _ => True) := fun i => by
    simp only [Matrix.mulVec, dotProduct]
    exact Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)
  rw [hT L hL y, hT M hM _]
  refine ⟨fun ⟨_, h2⟩ => ⟨hmy, fun v _ e he => ?_⟩, fun ⟨_, h2⟩ => ⟨hy, fun v _ e he => ?_⟩⟩
  · have hs : ∀ i, (e • y) i ∈ idAt D (· = v) := fun i => Ideal.mul_mem_right _ _ he.1
    have := (h v (e • y) hs).1 (h2 v trivial e he)
    rwa [Matrix.mulVec_smul] at this
  · have hs : ∀ i, (e • y) i ∈ idAt D (· = v) := fun i => Ideal.mul_mem_right _ _ he.1
    refine (h v (e • y) hs).2 ?_
    rw [Matrix.mulVec_smul]
    exact h2 v trivial e he

theorem moves0_of_selfDual : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => IsSelfDualC _ (GlobalTheory.RowShape.rowN ch.G 0) → ∀ (t : T) (b : Pts ch.G), IsBase t ch.S.B b → GlobalTheory.FinPl.Moves _ (b 0) (ch.G.Λ (.grid D.R.m 0)) (GlobalTheory.RowShape.rowN ch.G 0) fun _ => True := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro hN t b hb
  have hL : R.toLevCh.Is A.μ0 := s.core.lev
  have hde := GlobalTheory.FlipIntegrand.pde_ne_q_of_setting s
  have hc := hch.guard t
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hΛ : IsSelfDualC _ (ch.G.Λ (.grid D.R.m 0)) :=
    (ch.G.isV (X := .grid D.R.m 0) ⟨le_rfl, Nat.zero_le _⟩ (fun j e => by injection e with h1 h2; omega)).sd
  apply moves_of_forall _ _ _ _ hΛ.1 hN.1
  intro v
  classical
  by_cases hv : ∃ w ∈ locPl ch.G t, w.under (𝓞 D.host.F) = v
  · obtain ⟨w, hw, rfl⟩ := hv
    obtain ⟨e, ⟨⟨es, hes, -⟩, -⟩, -, -⟩ := hb.1
    obtain ⟨p, hpe, hpv, hpr⟩ := GlobalTheory.T.exists_cmSplitPoint_at_place_over_split D w (es w) (hes w hw) s.hF
    have key := GlobalTheory.T.gridBasePoint_carries_lattice_to_movedLattice hL hde ch.G ch.W Set.univ ch.S.toGridChoice t trivial hc b hb w hw p (hpe ▸ hes w hw) hpr
    rw [← hpv, ← GlobalTheory.Core.Mi.LatMatch.sMoves_one]
    refine GlobalTheory.T.normOneHomothety_carries_selfDual_of_splitComponent D _ p _ _ _ 1 (b 0) hΛ hN (GlobalTheory.Core.Mi.LatMatch.normOneAt_one _) fun x => ?_
    rw [map_one, one_smul]
    exact key x
  · push_neg at hv
    have hv0 : v ∉ ch.G.pl.S0 := fun h0 => hv (ch.G.pl.w v)
      (Finset.mem_union_left _ (by simpa [Places.W0] using ⟨v, h0, rfl⟩)) (ch.G.pl.under_w h0)
    intro y hy
    rw [GlobalTheory.T.gridBasePoint_trivial_offTensorPlaces ch.G t ch.S.B b hb v hv y hy]
    exact GlobalTheory.T.lattice_off_S0_last_level_iff ch.G v hv0 y hy

theorem moves0 : Big fun {D} {Γ} _ _ {Pl0 T} {A} {Ks} _ _ _ {R} ch => ∀ (t : T) (b : Pts ch.G), IsBase t ch.S.B b → GlobalTheory.FinPl.Moves _ (b 0) (ch.G.Λ (.grid D.R.m 0)) (GlobalTheory.RowShape.rowN ch.G 0) fun _ => True :=
  big_mono (fun _ h => h.1 (h.2 0 (Nat.zero_le _))) (Big.and moves0_of_selfDual GlobalTheory.T.isSelfDual_gridRowMovedLattice_largeDepth)

end GlobalTheory.RowShape
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemBesselGroupOfLocalMatrixGridNodeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_besselGroup_of_localMatrix_gridNode : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ {w : Pl D.host.E}, w ∈ locPl G t → ∀ (ew : AE D), Formalism.L2.NTheta.IsIdemAt ew w → ∀ {j σ : ℕ} (hj : j ≤ D.R.m) (hj' : j < D.R.m) (h' : j + 2 * σ + 2 = D.R.m) (h : GA D (G.V (.grid D.R.m j))), SuppAt ew _ h → GlobalTheory.RowRep.locAt S.B t w j hj h ∈ rowR (G := locGrid G t w) one_le_sLen (j := j) hj' → h ∈ besGrp (besDecAt G j σ h') (GlobalTheory.OrthSumExists.orthDecHsum D _ _) := by
  first | exact @GlobalTheory.RowRepBes.mem_besGrp_of_locAt | exact GlobalTheory.RowRepBes.mem_besGrp_of_locAt | (intros; apply GlobalTheory.RowRepBes.mem_besGrp_of_locAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSubgroupOfLocalComponentsSplitPlacesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_subgroup_of_localComponents_splitPlaces : ∀ {D : D7} (V : HSp D) (P : Finset (Pl D.host.E)) (e : AE D), IsIdemSum e P → ∀ (H : Subgroup (GA D V)) (r : GA D V), SuppAt e V r → (∀ w ∈ P, ∀ ew : AE D, Formalism.L2.NTheta.IsIdemAt ew w → ∃ h ∈ H, SuppAt ew V h ∧ GlobalTheory.StdFrames.loc w (Lev.finE V h) = GlobalTheory.StdFrames.loc w (Lev.finE V r)) → r ∈ H := by
  first | exact @GlobalTheory.RowAssemble.mem_of_loc | exact GlobalTheory.RowAssemble.mem_of_loc | (intros; apply GlobalTheory.RowAssemble.mem_of_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialMatchZeroIffPureTensorImageZero
section
open NumberField IsDedekindDomain
open scoped TensorProduct

namespace GlobalTheory.PolKer

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels in

theorem polMatch_zero_iff_polZero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a')
    (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf → ∀ Φ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.PolMatch Bs G Xc R Rf Φ 0 ↔ GlobalTheory.PolKer.PolZero Bs G Xc R Rf (Φ) := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM Φ
  constructor
  · rintro ⟨T, hX, m, m', f, φ, f', φ', h1, h1', hΦ, h0, he⟩
    refine ⟨T, hX, m, f, φ, h1, hΦ, ?_⟩
    rw [he]
    exact GlobalTheory.T.tmul_sum_eq_zero_of_pureTensor_function_zero G.M'.vac (fun v => (hM.triple.geo.hM'.vac v).2.1) hM.triple.geo.hM'.std R.p' Rf.Pi Rf.p' T m' f' φ'
      (fun j => (h1' j).2.2) h0.symm
  · rintro ⟨T, hX, m, f, φ, h1, hΦ, hz⟩
    refine ⟨T, hX, m, 0, f, φ, Fin.elim0, Fin.elim0, h1, fun j => j.elim0, hΦ, ?_, ?_⟩
    · simp
    · rw [hz]; simp

end GlobalTheory.PolKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowTestMemFourierJacobiGroupOfSumFrameSymmetricStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section
open GlobalTheory.RootEx GlobalTheory.RowRep
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowTest_mem_fourierJacobiGroup_of_sumFrame_symmetric : ∀ {D : D7} {A B : HSp D} {c σ : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε) (h : c = 2 * σ), 1 ≤ σ → ∀ (w : Pl D.host.E) (β : GL (Fin A.rank) (Lev.EAf D)) (β' : GL (Fin B.rank) (Lev.EAf D)) (u : Fin c → Kw w), IsSumFrame d w β β' u → (∀ p, u p ≠ 0) → ∀ {a b : ℕ} (_ : a = A.rank) (hb : b = B.rank) (hab : a + c = b) (q : GlobalTheory.FinPl.SplitPt D (Kw w)), (∀ x, q.pr x = GlobalTheory.RowRep.piAt w x) → ∀ g : GA D B, SuppAt q.e B g → frameGL hab (inBasis hb β' w (Lev.finE B g)) ∈ symR (Kw w) (Fin a) c → g ∈ jacGrp (jacDec d h) := by
  first | exact @GlobalTheory.RowRepLoc.mem_jacGrp_of_symR | exact GlobalTheory.RowRepLoc.mem_jacGrp_of_symR | (intros; apply GlobalTheory.RowRepLoc.mem_jacGrp_of_symR <;> assumption)
end
end

