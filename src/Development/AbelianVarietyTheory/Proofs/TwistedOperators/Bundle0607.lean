import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0526
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0586
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0603
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0296
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1710
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0510
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0578
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0591
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1805
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0376
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieActionFockOperatorsScalarsTrace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0114
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0513
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsAllTiedNotStable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesHermitianUniqueOfClassification
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0007
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0091
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0020
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0577
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0340
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0233
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0216
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0247
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0596
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0589
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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0554
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0576
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0594

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColAtFirstPt
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.TopZeroInv GlobalTheory.TopLevelInv GlobalTheory.StdFrames
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.TopZeroFirst
variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}

theorem zero_lt_m (D : D7) : 0 < D.R.m := by
  have h2 := D.R.two_le_m
  omega

private theorem inBasis_val_eq_submatrix_conj {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E) :
    (inBasis h β w x).val = ((loc w β)⁻¹ * loc w x * loc w β).val.submatrix (Fin.cast h) (Fin.cast h) := by
  rw [← map_inv, ← map_mul, ← map_mul]
  rfl

def kapTop0 (S : GridChoice W U) (t : T) (k : FinPt G (.top 0)) (w : Pl D.host.E) :
    GL (Fin (topRank (locGrid G t w) 0)) (Kw w) :=
  inBasis (topRank_eq G t w (Nat.zero_le _)) (S.βp 0) w (finG (G.V (.top 0)) k)

def firstPt (t : T) (g : FinPt G (.top 0)) (x : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :
    ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T)) :=
  Function.update x ⟨0, zero_lt_m D⟩ (actO _ _ (g : GA D (G.V (.top 0)))⁻¹ 1⁻¹ (x ⟨0, zero_lt_m D⟩))

def datFn {t : T} (d : PureDat G t) : ∀ l : Arr D, WO (G.pS (arrP t l)) (G.pT (arrP t l)) → ℂ
  | .inl j => (d.1 j).fn
  | .inr i => (d.2 i).fn

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

theorem colAt_firstPt (S : GridChoice W U) {t : T} (ht : t ∈ U) (k : FinPt G (.top 0)) {w : Pl D.host.E}
    (hw : w ∈ locPl G t) (x : ∀ j : Fin D.R.m, WO (G.pS (.top t j : Pair T)) (G.pT (.top t j : Pair T))) :
    S.colAt t w (firstPt t ((S.N.u (.top 0))⁻¹ * k * S.N.u (.top 0)) x) =
      Function.update (S.colAt t w x) 0 (S.colAt t w x 0 * (kapTop0 S t k w).val) := by
  funext j
  by_cases hj : j < D.R.m
  · by_cases h0 : j = 0
    · subst h0
      have hu := loc_finE_u_colCoord S ht (X := .top 0) (Nat.zero_le _) hw
      rw [Function.update_self, colAt_eq S t w _ hj, colAt_eq S t w _ hj]
      unfold firstPt
      rw [Function.update_self, frAt_actO_colCoord]
      simp only [inv_one, map_one, mul_one, inv_mul_cancel, Units.val_one, Matrix.one_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, map_mul, map_inv, hu, _root_.inv_inv, _root_.mul_inv_rev, one_mul]
      unfold kapTop0
      rw [inBasis_val_eq_submatrix_conj, submatrix_cast_mul_colCoord]
      simp only [_root_.mul_assoc]
      rfl
    · rw [Function.update_of_ne h0, colAt_eq S t w _ hj, colAt_eq S t w _ hj]
      unfold firstPt
      rw [Function.update_of_ne (fun h => h0 (congrArg Fin.val h))]
  · have h0 : j ≠ 0 := by
      have := zero_lt_m D
      omega
    rw [Function.update_of_ne h0]
    simp only [GridChoice.colAt, dif_neg hj]

end GlobalTheory.TopZeroFirst

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ColumnArrowKernelRealEqDetCharMulFockKernel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FockFrameChange GlobalTheory.FockReal

noncomputable section

namespace GlobalTheory.ColKer

open GlobalTheory.Chain.StepVac in

theorem mu_exp {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T} (hL : L.Is μ₀) (t : T) (j : ℕ) (hj : j < D.R.m)
    (τ : D.what₂.Tau) : HasInfExp D (L.mu t (j + 1)) τ (-(D.hc τ).e ⟨j, hj⟩) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h0 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 ⟨j, hj⟩) (hasInfQ_tau (L.C.isMu0 ⟨j, hj⟩).inf) τ
  obtain ⟨θ, hθ⟩ : ∃ θ, IsInfFam (D := D) θ := by
    obtain ⟨_, _, hθ, _⟩ := h0
    exact hθ
  have := hasInfExp_mul h0 (hasInfExp_of_order hθ (hL.xi t) hn ho τ)
  rw [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this
  exact this

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem realGL_fin (θ : InfFam D) (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : GlobalTheory.CoefModel.realGL θ V g = 1 := by
  funext τ
  show Formalism.UG.bc (θ τ) (infHom V g) = 1
  rw [show infHom V g = 1 from hg, map_one]

theorem realGL_infOf (θ : InfFam D) (V : HSp D) (h : GA D V) :
    GlobalTheory.CoefModel.realGL θ V (infOf V h : GA D V) = GlobalTheory.CoefModel.realGL θ V h := by
  conv_rhs => rw [← infOf_mul_finOf V h]
  rw [map_mul, realGL_fin θ V (finOf V h).2, mul_one]

theorem det_realIn (θ : InfFam D) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (g : GA D (G.V X))
    (τ : D.what₂.Tau) :
    ((realIn θ fr X g τ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ).det =
      ((GlobalTheory.CoefModel.realGL θ (G.V X) g τ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ).det := by
  simp only [realIn, MonoidHom.pi_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Pi.evalMonoidHom_apply, Units.val_mul, Matrix.det_mul, inv_inv]
  rw [mul_comm, ← mul_assoc, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, one_mul]

theorem conj_frame {n : ℕ} (O F c : GL (Fin n) ℂ) :
    ((O : Matrix (Fin n) (Fin n) ℂ)⁻¹ * (F : Matrix (Fin n) (Fin n) ℂ)) *
      ((F⁻¹ * c * F : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *
      ((O : Matrix (Fin n) (Fin n) ℂ)⁻¹ * (F : Matrix (Fin n) (Fin n) ℂ))⁻¹ =
        (O : Matrix (Fin n) (Fin n) ℂ)⁻¹ * (c : Matrix (Fin n) (Fin n) ℂ) * (O : Matrix (Fin n) (Fin n) ℂ) := by
  simp only [← Matrix.coe_units_inv, ← Units.val_mul]
  congr 1
  group

theorem transp_frame {n : ℕ} (O F c : GL (Fin n) ℂ) :
    (((O : Matrix (Fin n) (Fin n) ℂ)⁻¹ * (F : Matrix (Fin n) (Fin n) ℂ))⁻¹)ᵀ *
      ((((F⁻¹ * c * F)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᵀ *
      ((O : Matrix (Fin n) (Fin n) ℂ)⁻¹ * (F : Matrix (Fin n) (Fin n) ℂ))ᵀ =
        (((O : Matrix (Fin n) (Fin n) ℂ)⁻¹ * (c : Matrix (Fin n) (Fin n) ℂ) * (O : Matrix (Fin n) (Fin n) ℂ))⁻¹)ᵀ := by
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul]
  congr 1
  simp only [← Matrix.coe_units_inv, ← Units.val_mul]
  congr 1
  group

theorem realChar_top (W : G.Weil) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (t : T) (j : ℕ)
    (e₁ e₂ : D.what₂.Tau → ℤ) (k : GA D (G.V (.top j))) (h : GA D (G.V (.top (j + 1)))) :
    realChar W (Pair.top t j) e₁ e₂ k (infOf _ h) =
      ∏ τ, ((realIn W.θ fr (.top j) k τ : GL (Fin (G.V (.top j)).rank) ℂ) :
          Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ).det ^ e₂ τ *
        ((realIn W.θ fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
          Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ).det ^ e₁ τ := by
  unfold realChar
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [det_realIn, det_realIn, ← realGL_infOf W.θ _ h]
  rfl

theorem coe_realIn (θ : InfFam D) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (g : GA D (G.V X))
    (τ : D.what₂.Tau) :
    realIn θ fr X g τ = (frGL fr X τ)⁻¹ * GlobalTheory.CoefModel.realGL θ (G.V X) g τ * frGL fr X τ := by
  simp [realIn]

theorem realSubst_top {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) {U : Set T} (N : Std G U) (t : T) (j : ℕ)
    (hj : j + 1 ≤ D.R.m) (k : GA D (G.V (.top j))) (h : GA D (G.V (.top (j + 1))))
    (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) :
    realSubst W W.onb (Pair.top t j) k (infOf _ h) Q =
      GlobalTheory.AvgCol.frCh W N j (GlobalTheory.CompactHowe.substF
        (fun τ => ((realIn W.θ N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
          Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ))
        (fun τ => (((realIn W.θ N.fr (.top j) k τ)⁻¹ : GL (Fin (G.V (.top j)).rank) ℂ) :
          Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)ᵀ)
        (GlobalTheory.AvgCol.frChInv W N j Q)) := by
  have hO : ∀ X, DefNode D.R.m X → ∀ τ, IsUnit (W.onb X τ).det := fun X hX τ => by
    have e := congrArg Matrix.det (onb_def hL W hX τ)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at e
    exact isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact e⟩
  have hn := DefPair.nodes (show DefPair D.R.m (Pair.top t j) from hj)
  have hid : ⇑(opp (Pair.top t j)) = (id : ℂ → ℂ) := rfl
  unfold GlobalTheory.AvgCol.frCh GlobalTheory.AvgCol.frChInv realSubst
  rw [substF_mul, substF_mul]
  refine congrArg₂ (fun A B => GlobalTheory.CompactHowe.substF A B Q) (funext fun τ => ?_) (funext fun τ => ?_)
  · rw [hid, Matrix.map_id, coe_realIn]
    have eC : compAt W.θ τ (Formalism.L2.Theta.mt (G.pT (Pair.top t j)) (G.toPair (Pair.top t j) k ↑(infOf _ h)).2) =
        ((GlobalTheory.CoefModel.realGL W.θ _ h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
          Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ) := by
      rw [← realGL_infOf]; rfl
    rw [eC]
    exact (conj_frame (Matrix.nonsingInvUnit _ (hO _ hn.2 τ)) (frGL N.fr _ τ) _).symm
  · rw [hid, Matrix.map_id, coe_realIn]
    exact (transp_frame (Matrix.nonsingInvUnit _ (hO _ hn.1 τ)) (frGL N.fr _ τ) (GlobalTheory.CoefModel.realGL W.θ (G.V (.top j)) k τ)).symm

open GlobalTheory.SignedHC in

theorem detShift_top (G : GridData L sc) (t : T) (j : ℕ) (hj : j < D.R.m) (τ : D.what₂.Tau) :
    (((wt G (.top (j + 1)) τ).detShift : ℤ) : ℚ) = -((D.hc τ).e ⟨j, hj⟩ : ℚ) + ((G.V (.top j)).rank : ℚ) / 2 ∧
    (((nuEnd G (.top t j) τ : ℤ) - (wt G (.top j) τ).detShift : ℤ) : ℚ) =
      -(-((D.hc τ).e ⟨j, hj⟩ : ℚ) + ((G.V (.top (j + 1))).rank : ℚ) / 2) := by
  have hj' : j + 1 ≤ D.R.m := hj
  have r0 := rank_top G (j := j) (by omega)
  have r1 := rank_top G (j := j + 1) hj'
  have h0 := isHC_top D sc.cGap τ (j := j) (by omega) r0
  have h1 := isHC_top D sc.cGap τ hj' r1
  have hE := h0.1.card_entries.trans h0.2.1
  have hF := h1.1.card_entries.trans h1.2.1
  have e0 : entries (Node.par D sc.cGap (.top j) τ) = (num D sc.cGap τ).weightX j := entries_plus _
  have e1 : entries (Node.par D sc.cGap (.top (j + 1)) τ) = (num D sc.cGap τ).weightX (j + 1) := entries_plus _
  have w0 : ∀ r, ((wt G (.top j) τ).w r : ℚ) = highestWeight _ hE r := fun r => wtOf_cast hE h0.2.2 r
  have w1 : ∀ r, ((wt G (.top (j + 1)) τ).w r : ℚ) = highestWeight _ hF r := fun r => wtOf_cast hF h1.2.2 r
  have hb : (G.V (.top (j + 1))).rank = (G.V (.top j)).rank + (D.R.t + 1) := by
    rw [r0, r1]; simp only [rankX]; ring
  obtain ⟨v1, v2⟩ := highestWeight_below hb (-((num D sc.cGap τ).e (j + 1) : ℚ)) hE
    (by rw [e0, e1, GridData.weightX_succ]; rfl)
    (fun x hx y hy => by rw [e0] at hx; exact weightX_above D sc.cGap τ hj' hx hy) hF
  have ha : 0 < (G.V (.top j)).rank := r0 ▸ rankX_pos D j
  have hce : (((num D sc.cGap τ).e (j + 1) : ℤ) : ℚ) = (D.hc τ).e ⟨j, hj⟩ := num_e D sc.cGap τ (l := j + 1) (by omega) hj'
  have hS1 : (wt G (.top (j + 1)) τ).detShift = (wt G (.top (j + 1)) τ).w ⟨(G.V (.top (j + 1))).rank - 1, by omega⟩ := by
    rw [DomWeight.detShift, dif_pos (by omega)]
  have hS0 : (wt G (.top j) τ).detShift = (wt G (.top j) τ).w ⟨(G.V (.top j)).rank - 1, by omega⟩ := by
    rw [DomWeight.detShift, dif_pos ha]
  have d1 : (((wt G (.top (j + 1)) τ).detShift : ℤ) : ℚ) = -((D.hc τ).e ⟨j, hj⟩ : ℚ) + ((G.V (.top j)).rank : ℚ) / 2 := by
    rw [hS1, w1, v2 _ (by simp only; omega), hce]
  refine ⟨d1, ?_⟩
  have hlt : (G.V (.top j)).rank - 1 < (G.V (.top (j + 1))).rank := by omega
  have hν : nuEnd G (.top t j) τ = (wt G (.top (j + 1)) τ).natW ⟨(G.V (.top j)).rank - 1, hlt⟩ := by
    simp only [nuEnd, dif_pos hlt]
  have hanti : (wt G (.top (j + 1)) τ).detShift ≤ (wt G (.top (j + 1)) τ).w ⟨(G.V (.top j)).rank - 1, hlt⟩ := by
    rw [hS1]; exact (wt G (.top (j + 1)) τ).anti (Fin.mk_le_mk.2 (by omega))
  have hnat : ((nuEnd G (.top t j) τ : ℕ) : ℤ) =
      (wt G (.top (j + 1)) τ).w ⟨(G.V (.top j)).rank - 1, hlt⟩ - (wt G (.top (j + 1)) τ).detShift := by
    rw [hν, DomWeight.natW, Int.toNat_of_nonneg (by omega)]
  have hc : (G.V (.top j)).rank - 1 < (G.V (.top j)).rank := by omega
  have ew : (((wt G (.top (j + 1)) τ).w ⟨(G.V (.top j)).rank - 1, hlt⟩ : ℤ) : ℚ) =
      highestWeight _ hE ⟨(G.V (.top j)).rank - 1, hc⟩ - ((D.R.t + 1 : ℕ) : ℚ) / 2 := by
    rw [w1, ← v1]
    rfl
  have hrk : ((G.V (.top (j + 1))).rank : ℚ) = (G.V (.top j)).rank + (D.R.t + 1) := by
    rw [hb]; push_cast; ring
  rw [Int.cast_sub, hnat, Int.cast_sub, ew, d1, hS0, w0, hrk]
  push_cast
  ring

theorem kerA_col_mul_real : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m → ∀ (t : T) (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    ∀ (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (x : FinPt G (.top j)) (k : GA D (G.V (.top j))),
    k ∈ GinfC (G.V (.top j)) → ∀ (h : GA D (G.V (.top (j + 1)))),
      W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * k) h =
        (∏ τ, ((realIn W.θ S.N.fr (.top j) k τ : GL (Fin (G.V (.top j)).rank) ℂ) :
              Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ).det ^
                ((nuEnd G (.top t j) τ : ℤ) - (wt G (.top j) τ).detShift) *
            ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
              Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ).det ^ (wt G (.top (j + 1)) τ).detShift) *
          W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (GlobalTheory.AvgCol.frCh W S.N j
            (GlobalTheory.CompactHowe.substF
              (fun τ => ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
                Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ))
              (fun τ => (((realIn W.θ S.N.fr (.top j) k τ)⁻¹ : GL (Fin (G.V (.top j)).rank) ℂ) :
                Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)ᵀ)
              (GlobalTheory.AvgCol.frChInv W S.N j Q))))
            (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1)))) := by
  intro D T L sc G W U S μ₀ hL j hj t d hd Q x k hk h
  have hp : DefPair D.R.m (Pair.top t j) := show j + 1 ≤ D.R.m by omega
  have hh : ((finOf _ h : GA D (G.V (.top (j + 1)))) * (infOf _ h : GA D (G.V (.top (j + 1))))) = h := by
    rw [← GlobalTheory.AdelicSplit.commute_GinfC_GfC _ (infOf _ h).2 (finOf _ h).2]
    exact infOf_mul_finOf _ h
  have hr0 : Even (G.V (.top j)).rank := by rw [rank_top G (j := j) (by omega)]; exact rankX_even D j
  have hr1 : Even (G.V (.top (j + 1))).rank := by rw [rank_top G (j := j + 1) (by omega)]; exact rankX_even D (j + 1)
  have hS : G.chrS (.top t j) = L.mu t (j + 1) := by
    simp only [GridData.chrS, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pS, Nat.not_odd_iff_even.2 hr0, if_false]
  have hT : G.chrT (.top t j) = L.mu t (j + 1) := by
    simp only [GridData.chrT, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pT, Nat.not_odd_iff_even.2 hr1, if_false]
  set a : D.what₂.Tau → ℚ := fun τ => -((D.hc τ).e ⟨j, hj⟩ : ℚ) with ha_def
  have ha : ∀ τ, HasInfExp D (G.chrS (.top t j)) τ (a τ) := fun τ => by rw [hS]; exact mu_exp hL t j hj τ
  have hb : ∀ τ, HasInfExp D (G.chrT (.top t j)) τ (a τ) := fun τ => by rw [hT]; exact mu_exp hL t j hj τ
  have he₁ : ∀ τ, (((wt G (.top (j + 1)) τ).detShift : ℤ) : ℚ) =
      a τ + sgnP (Pair.top t j) * (G.pS (.top t j)).rank / 2 := fun τ => by
    rw [(detShift_top G t j hj τ).1]; simp only [sgnP, one_mul, a]
  have he₂ : ∀ τ, ((((nuEnd G (.top t j) τ : ℤ) - (wt G (.top j) τ).detShift) : ℤ) : ℚ) =
      -(a τ + sgnP (Pair.top t j) * (G.pT (.top t j)).rank / 2) := fun τ => by
    rw [(detShift_top G t j hj τ).2]; simp only [sgnP, one_mul, a]
  show W.ker (.top t j) _ ((x : GA D (G.V (.top j))) * k) h = _
  conv_lhs => rw [← hh]
  have key := ker_fock_moved_real (p := Pair.top t j) hL W S t hp d hd a a ha hb _ _ he₁ he₂ k hk (infOf _ h) (infOf _ h).2 Q
    (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1))))
  rw [key, realChar_top W S.N.fr t j, realSubst_top hL W S.N t j hp k h Q]

end GlobalTheory.ColKer

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryAdelicSchwartzArchimedeanReplace
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

namespace GlobalTheory.TwistRest

open scoped Classical in
theorem restTr : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f f₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ) (r : (κ → AF F) → ℂ),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f r → f ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rest (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) f₁ r := by
  intro F _ _ κ _ f f₁ r hr hf
  obtain ⟨hinv, hsch⟩ := hr

  set g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ := fun y => r (fun i => ((0 : InfiniteAdeleRing F), y i)) with hgdef
  have hrg : ∀ x : κ → AF F, r x = g (fun i => (x i).2) := by
    intro x
    let z : κ → AF F := fun i => ((x i).1, (0 : FiniteAdeleRing (𝓞 F) F))
    have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) z := by
      intro u hu
      have hu1 : u.1 = 0 :=
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (by rw [map_zero]; exact hu)
      funext i
      change (u * z i : AF F) = 0
      refine Prod.ext ?_ ?_
      · change u.1 * (x i).1 = 0
        rw [hu1, zero_mul]
      · change u.2 * 0 = 0
        exact mul_zero _
    let x' : κ → AF F := fun i => ((0 : InfiniteAdeleRing F), (x i).2)
    have := hinv x' z hz
    have hx : x = x' + z := by
      funext i
      refine Prod.ext ?_ ?_
      · change (x i).1 = (0 : InfiniteAdeleRing F) + (x i).1
        rw [zero_add]
      · change (x i).2 = (x i).2 + (0 : FiniteAdeleRing (𝓞 F) F)
        rw [add_zero]
    exact (congrArg r hx).trans this
  have htens : ∀ f' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F κ,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F) (⇑f') r = GlobalTheory.WeilM.pureA F (⇑f') g := by
    intro f'
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.WeilM.pureA, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI]
    rw [hrg x]

  obtain ⟨x₀, hx₀⟩ : ∃ x₀, f x₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hf (SchwartzMap.ext h)
  let a : κ → InfiniteAdeleRing F := fun i => (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (x₀ i)
  let Λ : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → FiniteAdeleRing (𝓞 F) F) → ℂ) :=
    { toFun := fun Φ y => Φ (fun i => (a i, y i))
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hΛ : ∀ (f' : (κ → mixedEmbedding.mixedSpace F) → ℂ) (g' : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
      Λ (GlobalTheory.WeilM.pureA F f' g') = f' x₀ • g' := by
    intro f' g'
    funext y
    simp [Λ, GlobalTheory.WeilM.pureA, a]
  have hle : GlobalTheory.WeilM.schA F κ ≤ (GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)).comap Λ := by
    refine Submodule.span_le.2 ?_
    rintro Φ ⟨f', g', hg', rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, hΛ]
    exact Submodule.smul_mem _ _ hg'
  have hg : g ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F) := by
    have h1 := hle (htens f ▸ hsch)
    rw [Submodule.mem_comap, hΛ] at h1
    have := Submodule.smul_mem _ (f x₀)⁻¹ h1
    rwa [smul_smul, inv_mul_cancel₀ hx₀, one_smul] at this
  refine ⟨hinv, ?_⟩
  rw [htens f₁]
  exact Submodule.subset_span ⟨f₁, g, hg, rfl⟩

end GlobalTheory.TwistRest
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplexDerivativeAdjointOfSkewFormStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open scoped TensorProduct
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complexDerivative_adjoint_of_skew_form : ∀ {D : D7} (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D) (τ : D.what₂.Tau)
    (A : Submodule ℂ (GA D V → ℂ)) (b : (GA D V → ℂ) →ₗ⋆[ℂ] (GA D V → ℂ) →ₗ[ℂ] ℂ),
    (∀ X ∈ lieAt V τ, ∀ x ∈ A, ∀ y ∈ A, b x (Rder θ V τ X y) = -b (Rder θ V τ X x) y) →
    ∀ (Z : Matrix (Fin V.rank) (Fin V.rank) ℂ), ∀ x ∈ A, ∀ y ∈ A,
      b x (RderC θ V τ Z y) = b (RderC θ V τ ((gramAt D V τ)⁻¹ * Matrix.conjTranspose Z * gramAt D V τ) x) y := by
  first | exact @GlobalTheory.RderCAdjoint.rderC_adjoint | exact GlobalTheory.RderCAdjoint.rderC_adjoint | (intros; apply GlobalTheory.RderCAdjoint.rderC_adjoint <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormAvgSeriesClosureStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_form_avg_series_closure : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → GlobalTheory.FunPr.Hypotheses₂ → ∀ (N : GlobalTheory.Grid.Node D) (ψ : GA D N.V → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N ψ → ∀ (τ : D.what₂.Tau) (e : Formalism.REAL.KG (N.M.ε τ) → ℂ), GlobalTheory.TypeSum.KFinFun (N.M.ε τ) e → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.IsCuspOfType θ N (GlobalTheory.SeriesToClosure.avg θ N.V τ (N.M.ε τ) (N.M.fr τ) e ψ) := by
  first | exact @GlobalTheory.AvgCuspType.avg_isCuspOfType | exact GlobalTheory.AvgCuspType.avg_isCuspOfType | (intros; apply GlobalTheory.AvgCuspType.avg_isCuspOfType <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspFormsOfVertexTypeZeroMemAndSmulMemStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspFormsOfVertexType_zero_mem_and_smul_mem : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (N : GlobalTheory.Grid.Node D) (U : Subgroup (GA D N.V)), (0 : GA D N.V → ℂ) ∈ Cls θ N U ∧ ∀ (c : ℂ) (f : GA D N.V → ℂ), f ∈ Cls θ N U → c • f ∈ Cls θ N U := by
  first | exact @GlobalTheory.PlaceDecomp.cls_zero_smul | exact GlobalTheory.PlaceDecomp.cls_zero_smul | (intros; apply GlobalTheory.PlaceDecomp.cls_zero_smul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergCommutingOperatorBlindToArchimedeanFibStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenbergCommuting_operator_independent_of_archimedeanFibres : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (T : Module.End ℂ ((κ → AF F) → ℂ)),
    IsStd ψ → (∀ Φ ∈ schA F κ, T Φ ∈ schA F κ) →
    (∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ, T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ)) →
    ∀ Φ ∈ schA F κ, ∀ y : κ → AF F, (∀ z, At (evI F) z → Φ (y + z) = 0) → T Φ y = 0 := by
  first | exact @GlobalTheory.FinFibre.fibre_zero | exact GlobalTheory.FinFibre.fibre_zero | (intros; apply GlobalTheory.FinFibre.fibre_zero <;> assumption)
end

