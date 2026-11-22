import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0505
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0273
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1759
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0263
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ParRowZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0497
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0253
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0500
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0506
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0032
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0012
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0014
import Formalism.ThetaLiftIndependence.FinalThetaLiftAMFKIndep
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0026
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0213
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0153
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0878
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeOnMemGoodPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1048
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0515
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanHeisenbergLineContinuousFiniteZeroStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.VacTransfer
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedeanHeisenbergLine_continuous_finite_zero : ∀ (D : D7) (S X : HSp D) {d : ℕ} (e : Fin X.rank ≃ Fin d) (g : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
    (cS : Matrix (Fin S.rank) (Fin d) (AE D) ≃+ WO S X),
    (∀ u, cS u = (HMul.hMul (uᵀ.submatrix e id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM g) : Matrix (Fin X.rank) (Fin S.rank) (AE D))) →
    ∀ u : Matrix (Fin S.rank) (Fin d) (AE D),
      Continuous (GlobalTheory.VacTransfer.archLine cS u) ∧ ∀ t, (GlobalTheory.VacTransfer.archLine cS u t).map (finPart D) = 0 := by
  first | exact @GlobalTheory.ArchLineCont.archLine_continuous_finPart | exact GlobalTheory.ArchLineCont.archLine_continuous_finPart | (intros; apply GlobalTheory.ArchLineCont.archLine_continuous_finPart <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AtRealPlaceMemUnipotentFlagAdelicStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.atRealPlace_mem_unipotentFlag_adelic : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (B : HSp D) {ρ : ℕ} (e : Matrix (Fin B.rank) (Fin ρ) D.host.E) (τ : D.what₂.Tau)
    (u : Matrix (Fin B.rank) (Fin B.rank) ℂ), u ∈ GlobalTheory.RealBessel.unipRad (gramAt D B τ) (e.map (tauE D τ)) →
    atTau θ B τ u ∈ NFlag B e := by
  first | exact @GlobalTheory.FlagRealUnip.atTau_mem_NFlag | exact GlobalTheory.FlagRealUnip.atTau_mem_NFlag | (intros; apply GlobalTheory.FlagRealUnip.atTau_mem_NFlag <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.AutCuspOfMemCusp
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

open Formalism.IndefR.Mult GlobalTheory.Grid

namespace GlobalTheory.FinLift

variable {D : D7}

theorem autCusp_of_mem_cusp (N : Node D) (θ : InfFam D) {Φ : N.Maps} (hΦ : Φ ∈ N.Cusp θ) (v : SmT N.M) :
    IsAutFun N.V (Φ v) ∧ IsCuspFun N.V (Φ v) := by
  obtain ⟨T, hT, rfl⟩ := Submodule.mem_map.1 hΦ
  replace hT := (GlobalTheory.MultMem.mem_mult_iff D θ N.V N.S N.M ∅ 1 T).1 hT
  induction v using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    simp only [map_smul, LinearEquiv.coe_coe, PiTensorProduct.lift.tprod]
    exact ⟨(GlobalTheory.MultMem.isAutFunSm_smul r (hT.aut f)).toIsAutFun, GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp f)⟩
  | add x y hx hy =>
    rw [map_add]
    exact ⟨GlobalTheory.RowLift.isAutFun_add hx.1 hy.1, GlobalTheory.MultMem.isCuspFun_add hx.1 hy.1 hx.2 hy.2⟩

theorem autCusp_sum (V : HSp D) {ι : Type} (s : Finset ι) (φ : ι → GA D V → ℂ) (h : ∀ i ∈ s, IsAutFun V (φ i) ∧ IsCuspFun V (φ i)) :
    IsAutFun V (∑ i ∈ s, φ i) ∧ IsCuspFun V (∑ i ∈ s, φ i) :=
  Finset.sum_induction φ (fun ψ => IsAutFun V ψ ∧ IsCuspFun V ψ)
    (fun a b ha hb => ⟨GlobalTheory.RowLift.isAutFun_add ha.1 hb.1, GlobalTheory.MultMem.isCuspFun_add ha.1 hb.1 ha.2 hb.2⟩)
    ⟨GlobalTheory.RowLift.isAutFun_zero V, fun r C hC μ 𝓕 hμ h𝓕 g => by simp⟩ h

end GlobalTheory.FinLift

namespace GlobalTheory.FinLift

variable {D : D7}

theorem thetaKO_sum {S T : HSp D} (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (g : GA D S) (h : GA D T)
    {ι : Type} (s : Finset ι) (x : ι → WO S T → ℂ) : thetaKO om g h (∑ i ∈ s, x i) = ∑ i ∈ s, thetaKO om g h (x i) := by
  simp only [thetaKO, map_sum, Finset.sum_apply]

theorem lift_finSum {θ : InfFam D} {A B : Node D} {P : Type} {m : A.MeasDat} {n : ℕ}
    (K : Fin n → P → GA D B.V → GA D A.V → ℂ) (It : P → SmT A.M → SmT B.M)
    (hK : ∀ l, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsMult θ m (K l) It) (ps : Fin n → P) {n' : ℕ} (Fs : Fin n' → A.Maps)
    (vs : Fin n' → SmT A.M) (hF : ∀ k, Fs k ∈ A.Cusp θ) :
    (∀ h, IntegrableOn (fun g => (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g) m.fd m.ν) ∧
    IsAutFun B.V (fun h => ∫ g in m.fd, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g ∂m.ν) ∧
    IsCuspFun B.V (fun h => ∫ g in m.fd, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g ∂m.ν) := by
  choose F' hF' hI using fun l k => hK l (Fs k) (hF k)
  have hsplit : ∀ h g, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g = ∑ l, ∑ k, K l (ps l) h g * Fs k (vs k) g :=
    fun h g => by rw [Finset.sum_mul_sum]
  have hint : ∀ h, IntegrableOn (fun g => (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g) m.fd m.ν := fun h => by
    simp_rw [hsplit]
    exact integrable_finset_sum _ fun l _ => integrable_finset_sum _ fun k _ => (hI l k (ps l) (vs k) h).1
  have heq : (fun h => ∫ g in m.fd, (∑ l, K l (ps l) h g) * ∑ k, Fs k (vs k) g ∂m.ν) =
      ∑ l, ∑ k, F' l k (It (ps l) (vs k)) := by
    funext h
    simp_rw [hsplit]
    rw [integral_finset_sum _ fun l _ => integrable_finset_sum _ fun k _ => (hI l k (ps l) (vs k) h).1]
    simp only [Finset.sum_apply]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [integral_finset_sum _ fun k _ => (hI l k (ps l) (vs k) h).1]
    exact Finset.sum_congr rfl fun k _ => (hI l k (ps l) (vs k) h).2
  rw [heq]
  exact ⟨hint, autCusp_sum B.V _ _ fun l _ => by
    simpa only [Finset.sum_apply] using autCusp_sum B.V _ _ fun k _ => autCusp_of_mem_cusp B θ (hF' l k) _⟩

end GlobalTheory.FinLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselColumnScalarFunctionContinuousLeftInvarianStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselColumnScalarFunction_continuous_leftInvariant : Big fun ch => ∀ a, Continuous (colFn ch a) ∧
    ∀ γ ∈ GQ (ch.G.V (.top 0)), ∀ g, colFn ch a (γ * g) = colFn ch a g := by
  first | exact @GlobalTheory.RowClaim.colFn_cont_left | exact GlobalTheory.RowClaim.colFn_cont_left | (intros; apply GlobalTheory.RowClaim.colFn_cont_left <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneAdditiveBoundedCompactStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriodCorankOne_additive_bounded_compact : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ Ω : Set (GA D (G.V (.grid D.R.m 0))), IsCompact Ω → (∀ (h : GA D (G.V (.top 0))) (n : NFlag (G.V (.grid D.R.m 0)) G.besTop.e),
      ∃ γ ∈ GQ (G.V (.grid D.R.m 0)), γ * ((n : GA D (G.V (.grid D.R.m 0))) * embTop G h) ∈ Ω) →
    ∀ φ ∈ contLeft (G.V (.top 0)), ∃ C : ℝ,
      (∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ F' ∈ contLeft (G.V (.grid D.R.m 0)), Bplus W M φ (F + F') = Bplus W M φ F + Bplus W M φ F') ∧
      (∀ φ' ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), Bplus W M (φ + φ') F = Bplus W M φ F + Bplus W M φ' F) ∧
      ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ K : ℝ, (∀ x ∈ Ω, ‖F x‖ ≤ K) → ‖Bplus W M φ F‖ ≤ C * K := by
  first | exact @GlobalTheory.BplusLaws.bplus_add_bound | exact GlobalTheory.BplusLaws.bplus_add_bound | (intros; apply GlobalTheory.BplusLaws.bplus_add_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneRightTranslateUnipotentStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriodCorankOne_rightTranslate_unipotent : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ (φ : GA D (G.V (.top 0)) → ℂ), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ u ∈ NFlag (G.V (.grid D.R.m 0)) G.besTop.e,
      Bplus W M φ (rTr _ u F) = besChar W.ψ G.besTop u * Bplus W M φ F := by
  first | exact @GlobalTheory.BplusUnip.bplus_rTr_unip | exact GlobalTheory.BplusUnip.bplus_rTr_unip | (intros; apply GlobalTheory.BplusUnip.bplus_rTr_unip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BesselPeriodCorankOneSimultaneousRightTranslateStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.SepRows
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Mi.SepPer (contLeft)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselPeriodCorankOne_simultaneous_rightTranslate : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (M : Vol G), M.IsRow →
    ∀ φ ∈ contLeft (G.V (.top 0)), ∀ F ∈ contLeft (G.V (.grid D.R.m 0)), ∀ a : GA D (G.V (.top 0)),
      Bplus W M (rTr _ a φ) (rTr _ (embTop G a) F) = Bplus W M φ F := by
  first | exact @GlobalTheory.BplusShift.bplus_rTr | exact GlobalTheory.BplusShift.bplus_rTr | (intros; apply GlobalTheory.BplusShift.bplus_rTr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColMapEqColMapV
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.ExpansionInvariance

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

def colMapV (S : GridChoice W U) (t : T) (v : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
    (x : ∀ j, FinPt G (.top j)) : VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (wt G (.top D.R.m)) :=
  chainTo (V := fun j => VV ℂ (wt G (.top j)))
    (fun j => if h : j < D.R.m then S.Z.scal 1 (.top t j) •
      fockComp W S.N.frC (.top t j) (v ⟨j, h⟩) (x j * S.N.u _) (x (j + 1) * S.N.u _) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.top 0))⁻¹

def rowMapV (S : GridChoice W U) (v : ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
    (y : ∀ i, FinPt G (.grid i D.R.m)) : VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] VV ℂ (wt G (.grid D.R.m D.R.m)) :=
  chainTo (V := fun i => VV ℂ (wt G (.grid i D.R.m)))
    (fun i => if h : i < D.R.m then S.Z.scal 1 (.chi i D.R.m : Pair T) •
      fockComp W S.N.frC (.chi i D.R.m : Pair T) (v ⟨i, h⟩) (y i * S.N.u _) (y (i + 1) * S.N.u _) else 0) D.R.m ∘ₗ
    rhoVr (tauE D) _ (S.N.fr (.grid 0 D.R.m))⁻¹ ∘ₗ funOf (listedWt G (.grid 0 D.R.m))

def pairV (S : GridChoice W U) (t : T) {δ : Type} (τ : δ →₀ ℂ)
    (c : δ → ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) → ℂ)
    (r : δ → ∀ i : Fin D.R.m, WO (G.pS (.chi i D.R.m : Pair T)) (G.pT (.chi i D.R.m : Pair T)) → ℂ)
    (x : ∀ j, FinPt G (.top j)) (y : ∀ i, FinPt G (.grid i D.R.m)) :
    VV ℂ (wt G (.top 0)) →ₗ[ℂ] VV ℂ (listedWt G (.grid 0 D.R.m)) →ₗ[ℂ] ℂ :=
  τ.sum fun d a => a • (brPair (listedWt G (.grid D.R.m D.R.m)) G.sp.topDec.rank.symm (wt G (.top D.R.m))).compl₁₂
    (colMapV S t (c d) x) (rowMapV S (r d) y)

theorem pairPts_eq_pairV (S : GridChoice W U) {t : T} (τ : PureDat G t →₀ ℂ) (x : ∀ j, FinPt G (.top j))
    (y : ∀ i, FinPt G (.grid i D.R.m)) :
    pairPts S τ x y = pairV S t τ (fun d j => S.Z.vec (d.1 j)) (fun d i => S.Z.vec (d.2 i)) x y := rfl

def movedCol (S : GridChoice W U) {t : T} (d : PureDat G t) (j : ℕ) (hj : j + 1 < D.R.m) (g : FinPt G (.top (j + 1))) :
    ∀ j' : Fin D.R.m, WO (G.pS (.top t j' : Pair T)) (G.pT (.top t j' : Pair T)) → ℂ :=
  Function.update (Function.update (fun j' => S.Z.vec (d.1 j')) ⟨j, by omega⟩
      (W.om (.top t j) (1, (g : GA D (G.V (.top (j + 1))))) (S.Z.vec (d.1 ⟨j, by omega⟩))))
    ⟨j + 1, hj⟩ (W.om (.top t (j + 1)) ((g : GA D (G.V (.top (j + 1)))), 1) (S.Z.vec (d.1 ⟨j + 1, hj⟩)))

end GlobalTheory.ExpansionInvariance

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnMemLatticeIffIdealStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.ChiGrid
open scoped TensorProduct nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.column_mem_lattice_iff_ideal : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : GlobalTheory.ChiGrid.HermitianOrthogonalExtensionData A B c ε), ε ≠ 0 → ∀ (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → GlobalTheory.SeeSaw.FI D) (v : GlobalTheory.FinPl.Pl D) (q : Fin c) (b : AE D), (fun k => b * incA D (d.a k q)) ∈ GlobalTheory.FinPl.latV B (d.lat Λ 𝔟) (· = v) ↔ b ∈ GlobalTheory.SeeSaw.idV (𝔟 q) v := by
  first | exact @GlobalTheory.UnitaryEmbeddingColumns.mem_latV_iff | exact GlobalTheory.UnitaryEmbeddingColumns.mem_latV_iff | (intros; apply GlobalTheory.UnitaryEmbeddingColumns.mem_latV_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConclOfDownIntertwines
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.KappaLambdaEmbedding
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.KappaLevels

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

variable {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H]

omit [FiniteDimensional ℂ E] [FiniteDimensional ℂ H] in

theorem inner_of_normSq (u : E →ₗ[ℂ] H) (n : ℝ) (h : ∀ x, ‖u x‖ ^ 2 = n * ‖x‖ ^ 2) (x y : E) :
    ⟪u x, u y⟫_ℂ = (n : ℂ) * ⟪x, y⟫_ℂ := by
  have h' : ∀ z, ((‖u z‖ : ℝ) : ℂ) ^ 2 = (n : ℂ) * ((‖z‖ : ℝ) : ℂ) ^ 2 := fun z => by exact_mod_cast h z
  have e1 := inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) (u x) (u y)
  have e2 := inner_eq_sum_norm_sq_div_four (𝕜 := ℂ) x y
  rw [← map_smul, ← map_add, ← map_add, ← map_sub, ← map_sub] at e1
  rw [e1, e2]
  have h1 := h' (x + y)
  have h2 := h' (x - y)
  have h3 := h' (x - (RCLike.I : ℂ) • y)
  have h4 := h' (x + (RCLike.I : ℂ) • y)
  simp only [Complex.coe_algebraMap]
  rw [h1, h2, h3, h4]
  ring

theorem iota_adjoint_transport {E' H' : Type} [NormedAddCommGroup E'] [InnerProductSpace ℂ E'] [FiniteDimensional ℂ E']
    [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (Θ : E →ₗ[ℂ] H) (ι : E' →ₗ[ℂ] H')
    (V : Submodule ℂ E') (uA : E' →ₗ[ℂ] E) (uE : H' →ₗ[ℂ] H) {n : ℝ} (hn : 0 < n) (nA : ∀ x, ‖uA x‖ ^ 2 = n * ‖x‖ ^ 2)
    (nE : ∀ x, ‖uE x‖ ^ 2 = n * ‖x‖ ^ 2) (hι : ∀ x ∈ V, uE (ι x) = Θ (uA x)) (y : H')
    (hy : LinearMap.adjoint Θ (uE y) ∈ V.map uA) {a : ℂ} (ha : Θ (LinearMap.adjoint Θ (uE y)) = a • uE y) :
    (ι.domRestrict (V ⊓ (V ⊓ LinearMap.ker ι)ᗮ) ∘ₗ LinearMap.adjoint (ι.domRestrict (V ⊓ (V ⊓ LinearMap.ker ι)ᗮ))) y = a • y := by
  have hne : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  obtain ⟨z, hz, hzw⟩ := hy
  have key : ∀ u ∈ V, ⟪u, z⟫_ℂ = ⟪ι u, y⟫_ℂ := fun u hu => by
    apply mul_left_cancel₀ hne
    rw [← inner_of_normSq uA _ nA, ← inner_of_normSq uE _ nE, hzw, hι u hu, LinearMap.adjoint_inner_right]
  have hQ : z ∈ V ⊓ (V ⊓ LinearMap.ker ι)ᗮ := by
    refine ⟨hz, (Submodule.mem_orthogonal _ _).2 fun u hu => ?_⟩
    rw [key u hu.1, LinearMap.mem_ker.1 hu.2, inner_zero_left]
  have hb : LinearMap.adjoint (ι.domRestrict (V ⊓ (V ⊓ LinearMap.ker ι)ᗮ)) y = ⟨z, hQ⟩ := by
    refine ext_inner_left ℂ fun u => ?_
    rw [LinearMap.adjoint_inner_right, Submodule.coe_inner]
    exact (key u u.2.1).symm
  have hinj : Function.Injective uE := (injective_iff_map_eq_zero uE).2 fun y hy => by
    have := nE y
    rw [hy, norm_zero, zero_pow two_ne_zero] at this
    exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 ((mul_eq_zero.1 this.symm).resolve_left hn.ne'))
  apply hinj
  rw [LinearMap.comp_apply, hb, map_smul, ← ha, ← hzw]
  exact hι z hz

end Abstract

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)

def DownIntertwines (t : T) : Prop :=
  ∀ g κ, IsLevelLift D.sp.X' R.βX (R.datXt t) (R.eG g) κ → ∀ y y' : (R.HX t).H,
    (∀ h, (R.HX t).e y' h = (levChi _ R.βX (flagL (R.datXt t)) κ)⁻¹ • (R.HX t).e y (h * (finHom _).rangeRestrict κ)) →
      R.Th t y' = R.gE g (R.Th t y)

def UpKeepsLevel (t : T) : Prop :=
  ∀ P, ∀ x ∈ rowsAt R P, LinearMap.adjoint (R.Th t) x ∈ goodAt R t P

variable {R F}

def SchurOnChain : Prop :=
  ∀ (D : D7) (θ : Datum.InfFam D) (j : ℕ), j < D.R.m → ∀ (M : DSModel (Yc D j) (parB (Ptw D) (min j D.R.m)))
    (β : GL (Fin (Yc D j).rank) (Lev.EAf D)) (L : LevDat D.host.E ℂ (Yc D j).rank) (μ : Measure (GA D (Yc D j))) (𝓕 : Set (GA D (Yc D j))),
    SchurMult θ M (levS _ β L) (levChi _ β L) μ 𝓕

end GlobalTheory.KappaLevels

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruenceLevelOfEmbedding
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace nonZeroDivisors Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevRestrict

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem map_hatL {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) {Λ : Submodule (𝓞 E) (Fin n → E)}
    {Λ' : Submodule (𝓞 E) (Fin m → E)} (hM : ∀ y ∈ Λ, M *ᵥ y ∈ Λ') :
    ∀ x ∈ Formalism.L2.Herm.hatL (F := F) Λ,
      (M.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) Λ' := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨M *ᵥ y, hM y hy, ?_⟩
    funext i
    exact RingHom.map_mulVec _ M y i
  | zero => rw [mulVec_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [mulVec_add]; exact add_mem hx hy
  | smul s x _ hx =>
    have := Submodule.smul_mem _ s hx
    rw [Subring.smul_def, ← mulVec_smul] at this
    rw [Subring.smul_def]
    exact this

theorem map_smul {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) {Λ : Submodule (𝓞 E) (Fin n → E)}
    {Λ' : Submodule (𝓞 E) (Fin m → E)} (hM : ∀ y ∈ Λ, M *ᵥ y ∈ Λ') (𝔪 : Ideal (𝓞 E)) :
    ∀ y ∈ 𝔪 • Λ, M *ᵥ y ∈ 𝔪 • Λ' := by
  have : 𝔪 • Λ ≤ (𝔪 • Λ').comap ((Matrix.mulVecLin M).restrictScalars (𝓞 E)) := by
    rw [Submodule.smul_le]
    intro r hr z hz
    show M *ᵥ (r • z) ∈ 𝔪 • Λ'
    rw [mulVec_smul]
    exact Submodule.smul_mem_smul hr (hM z hz)
  exact fun y hy => this hy

theorem map_hatL_smul {m n : ℕ} (M : Matrix (Fin m) (Fin n) E) {Λ : Submodule (𝓞 E) (Fin n → E)}
    {Λ' : Submodule (𝓞 E) (Fin m → E)} (hM : ∀ y ∈ Λ, M *ᵥ y ∈ Λ') (𝔪 : Ideal (𝓞 E)) :
    ∀ x ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ),
      (M.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))) *ᵥ x ∈ Formalism.L2.Herm.hatL (F := F) (𝔪 • Λ') :=
  map_hatL M (map_smul M hM 𝔪)

end General

open GlobalTheory.UnitaryEmbeddingProperties

variable {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E}

theorem qM_mul_a (d : HermitianOrthogonalExtensionData A B c ε) : qM d * d.a = 0 := by
  rw [qM, Matrix.mul_assoc, d.perp, Matrix.mul_zero]

theorem qM_lat (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ∀ x ∈ d.lat Λ 𝔟, qM d *ᵥ x ∈ Λ := by
  intro x hx
  obtain ⟨y, hy, u, -, rfl⟩ := hx
  rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, qM_mul, qM_mul_a, one_mulVec, zero_mulVec, add_zero]
  exact hy

theorem frameMat_lat (d : HermitianOrthogonalExtensionData A B c ε) (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E))
    (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) : ∀ y ∈ Λ, frameMat B A d.ι *ᵥ y ∈ d.lat Λ 𝔟 :=
  fun y hy => ⟨y, hy, 0, fun p => (𝔟 p).zero_mem, by simp⟩

set_option maxHeartbeats 2000000 in

theorem finE_mem_congLev : ∀ {D : D7} {A B : HSp D} {c : ℕ} {ε : D.host.E} (d : HermitianOrthogonalExtensionData A B c ε)
    (Λ : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (𝔟 : Fin c → FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)
    (𝔪 : Ideal (𝓞 D.host.E)) (h : GA D A), Lev.finE B (stabilizerEmbedding d h) ∈ congLev D.sp.cm B.gram (d.lat Λ 𝔟) 𝔪 →
      Lev.finE A h ∈ congLev D.sp.cm A.gram Λ 𝔪 := by
  intro D A B c ε d Λ 𝔟 𝔪 h hg
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin B.rank) (Fin A.rank) (Lev.EAf D),
      P = (frameMat B A d.ι).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : Matrix (Fin A.rank) (Fin B.rank) (Lev.EAf D),
      Q = (qM d).map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g, g = Lev.finE B (stabilizerEmbedding d h) := ⟨_, rfl⟩
  obtain ⟨k, hkdef⟩ : ∃ k, k = Lev.finE A h := ⟨_, rfl⟩
  rw [← hgdef] at hg
  rw [← hkdef]
  have hQP : HMul.hMul Q P = (1 : Matrix (Fin A.rank) (Fin A.rank) (Lev.EAf D)) := by
    rw [hP, hQ]; exact qM_mul_map _ d
  have e : ∀ {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E),
      (M.map (incA D)).map (GlobalTheory.LevSplit.finSw D) =
        M.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) := fun M => by
    ext i j; exact GlobalTheory.LevSplit.finSw_incA _
  have hG : g.1 = ex P Q k.1 := by
    rw [hgdef, hkdef, GlobalTheory.LevSplit.finE_val, GlobalTheory.LevSplit.finE_val, hP, hQ]
    show ((matHom B (stabilizerEmbedding d h)).1).map _ = ex _ _ (((matHom A h).1).map _)
    rw [unitaryEmbedding_matrix_formula, ex_map, e, e]
  have hGP : HMul.hMul g.1 P = HMul.hMul P k.1 := by rw [hG]; exact ex_mul_P P Q hQP _
  have hk : k.1 = HMul.hMul (HMul.hMul Q g.1) P := by
    rw [Matrix.mul_assoc, hGP, ← Matrix.mul_assoc, hQP, Matrix.one_mul]
  have hPl : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ, P *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ 𝔟) :=
    by subst hP; exact map_hatL (F := D.host.F) (frameMat B A d.ι) (frameMat_lat d Λ 𝔟)
  have hQl : ∀ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) (d.lat Λ 𝔟), Q *ᵥ x ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    by subst hQ; exact map_hatL (F := D.host.F) (qM d) (qM_lat d Λ 𝔟)
  rw [mem_congLev] at hg
  have g2 := hg.2.1
  have g3 := hg.2.2
  rw [mem_congLev]
  refine ⟨?_, fun x => ⟨fun hx => ?_, fun hx => ?_⟩, fun x hx => ?_⟩
  · rw [hkdef]; exact GlobalTheory.LevSplit.finE_mem_UA A h
  · rw [hk, ← mulVec_mulVec, ← mulVec_mulVec]; exact hQl _ ((g2 _).1 (hPl x hx))
  · have h1 := hPl _ hx
    rw [mulVec_mulVec, ← hGP, ← mulVec_mulVec] at h1
    have h2 := hQl _ ((g2 _).2 h1)
    rwa [mulVec_mulVec, hQP, one_mulVec] at h2
  · have e2 : k.1 *ᵥ x - x = Q *ᵥ (g.1 *ᵥ (P *ᵥ x) - P *ᵥ x) := by
      rw [mulVec_sub, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hQP, one_mulVec, hk]
    rw [e2, hQ]
    exact map_hatL_smul (F := D.host.F) (qM d) (qM_lat d Λ 𝔟) 𝔪 _ (g3 _ (hPl x hx))

end GlobalTheory.LevRestrict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstantTermLiftIsotropicSubspaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantTermLift_isotropicSubspace : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.TowerConstTerm D := by
  first | exact @GlobalTheory.TowerConstTermObj.towerConstTerm | exact GlobalTheory.TowerConstTermObj.towerConstTerm | (intros; apply GlobalTheory.TowerConstTermObj.towerConstTerm <;> assumption)
end

