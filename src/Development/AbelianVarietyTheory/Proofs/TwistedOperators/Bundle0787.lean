import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0512
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0529
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0563
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0556
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0559
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0783
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0671
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0784
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0298
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0562

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairedPointsFirstLevelLawStatement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowVertex

open GlobalTheory.LastVertexInv in

theorem paired_points_first_level_law : GlobalTheory.FunPr.Hypotheses₂ → SumOKK → Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) a, ∀ β ∈ ch.S.supp t (ch.Phi a), ∀ τ, ch.S.IsExpansion t (ch.Phi a) β τ →
    ∀ (x : ∀ j, FinPt ch.G (.top j)) (y : ∀ i, FinPt ch.G (.grid i D.R.m)) (k : FinPt ch.G (.grid 0 D.R.m))
      (_ : finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _)) (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J)
      (v : VV ℂ (wt ch.G (.top 0))) (w : VV ℂ (listedWt ch.G (.grid 0 D.R.m))),
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x (Function.update y 0 (y 0 * k)) v
        ((((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • w) =
      GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x y v w := by
  intro hP hS
  obtain ⟨a₁, h₁⟩ := GlobalTheory.T.first_column_vector_sum_formula hP hS
  obtain ⟨a₂, h₂⟩ := hS
  refine ⟨max a₁ a₂, fun ε CF hC => ?_⟩
  have hb₁ := h₁ ε CF (le_of_max_le_left hC)
  have hb₂ := h₂ ε CF (le_of_max_le_right hC)
  obtain ⟨x₁, hc₁⟩ := hb₁
  obtain ⟨x₂, hc₂⟩ := hb₂
  refine ⟨max x₁ x₂, fun D large₂ e hx Γ _ _ Pl0 T A Ks _ _ _ R F s ch hi hsc => ?_⟩
  intro t a β hβ τ hτ x y k hkl hk v w
  have key := hc₁ D large₂ e (le_of_max_le_left hx) Γ Pl0 T A Ks R F s ch hi hsc t a β hβ τ hτ k hkl hk
  have hOK := hc₂ D large₂ e (le_of_max_le_right hx) Γ Pl0 T A Ks R F s ch hi hsc t a
  generalize hχk : (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) = χk at key ⊢
  have hth : ∀ d ∈ τ.support, (∀ j, IsThetaFunO ch.W.ψ _ _ (ch.S.Z.vec (d.1 j))) ∧ ∀ i, IsThetaFunO ch.W.ψ _ _ (ch.S.Z.vec (d.2 i)) :=
    fun d hd => ⟨fun j => vec_theta ch.S.toGridChoice (defPair_top t j) (inRange_top t j) _ ((hOK.vec β τ hτ d hd).1 j),
      fun i => vec_theta ch.S.toGridChoice (defPair_chi i) (inRange_chi i) _ ((hOK.vec β τ hτ d hd).2 i)⟩
  obtain ⟨M, hM⟩ := GlobalTheory.T.exists_multilinear_columnRowKernelPairing ch.S.toGridChoice t x y v w
  have thr : ∀ d ∈ τ.support, ∀ i,
      IsThetaFunO ch.W.ψ _ _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i) := by
    intro d hd i
    by_cases hi0 : i = firstIx D
    · subst hi0
      simp only [movedRow, Function.update_self]
      exact rowShift0_theta ch.S.toGridChoice k ((hth d hd).2 _)
    · simp only [movedRow, Function.update_of_ne hi0]
      exact (hth d hd).2 i
  have thr' : ∀ d ∈ τ.support, ∀ i, IsThetaFunO ch.W.ψ _ _
      (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D)
        (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i) := by
    intro d hd i
    by_cases hi0 : i = firstIx D
    · subst hi0
      simp only [Function.update_self]
      exact GlobalTheory.OrientedHeis.theta_smul χk (thr d hd _)
    · simp only [Function.update_of_ne hi0]
      exact thr d hd i
  have lhs : GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x (Function.update y 0 (y 0 * k)) v w =
      τ.sum fun d c => c * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i)) := by
    simp only [GlobalTheory.ExpansionInvariance.pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    rw [hM, colMap_eq, rowMap_eq, rowMapV_update_zero ch.S.toGridChoice _ y k ((hth d hd).2 _)]
    have e1 : (fun j : Fin D.R.m => (toTh ch.W _ (ch.S.Z.vec (d.1 j)) : WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)) → ℂ)) =
        fun j : Fin D.R.m => ch.S.Z.vec (d.1 j) :=
      funext fun j => coe_toTh ch.W _ ((hth d hd).1 j)
    have e2 : (fun i : Fin D.R.m => (toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i) :
        WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) → ℂ)) =
        movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) :=
      funext fun i => coe_toTh ch.W _ (thr d hd i)
    rw [e1, e2]
  have rhs : GlobalTheory.ExpansionInvariance.pairPts ch.S.toGridChoice τ x y v w =
      τ.sum fun d c => c * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j))) (fun i => toTh ch.W _ (ch.S.Z.vec (d.2 i))) := by
    simp only [GlobalTheory.ExpansionInvariance.pairPts, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun d hd => ?_
    congr 1
    rw [hM, colMap_eq, rowMap_eq]
    have e1 : (fun j : Fin D.R.m => (toTh ch.W _ (ch.S.Z.vec (d.1 j)) : WO (ch.G.pS (.top t j)) (ch.G.pT (.top t j)) → ℂ)) =
        fun j : Fin D.R.m => ch.S.Z.vec (d.1 j) :=
      funext fun j => coe_toTh ch.W _ ((hth d hd).1 j)
    have e2 : (fun i : Fin D.R.m => (toTh ch.W _ (ch.S.Z.vec (d.2 i)) :
        WO (ch.G.pS (.chi i D.R.m : Pair T)) (ch.G.pT (.chi i D.R.m : Pair T)) → ℂ)) =
        fun i : Fin D.R.m => ch.S.Z.vec (d.2 i) :=
      funext fun i => coe_toTh ch.W _ ((hth d hd).2 i)
    rw [e1, e2]

  have hscale : ∀ d ∈ τ.support,
      M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D)
          (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i)) =
      χk * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i)) := by
    intro d hd
    have eg : (fun i : Fin D.R.m => toTh ch.W (.chi i D.R.m : Pair T)
        (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D)
          (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i)) =
        Function.update (fun i : Fin D.R.m => toTh ch.W (.chi i D.R.m : Pair T) (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i))
          (firstIx D) (χk • toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D))) := by
      funext i
      by_cases hi0 : i = firstIx D
      · subst hi0
        apply Subtype.ext
        have h1 := coe_toTh ch.W _ (thr' d hd (firstIx D))
        simp only [Function.update_self] at h1 ⊢
        rw [h1, Submodule.coe_smul, coe_toTh ch.W _ (thr d hd _)]
      · simp only [Function.update_of_ne hi0]
    rw [eg, MultilinearMap.map_update_smul, Function.update_eq_self, smul_eq_mul]
  rw [LinearMap.map_smul, smul_eq_mul, lhs, rhs, Finsupp.sum, Finset.mul_sum]
  have step1 : (∑ d ∈ τ.support, χk * (τ d * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) i)))) =
      τ.sum fun d c => c * M (fun j => toTh ch.W _ (ch.S.Z.vec (d.1 j)))
        (fun i => toTh ch.W _ (Function.update (movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i))) (firstIx D)
          (χk • movedRow ch.S.toGridChoice k (fun i => ch.S.Z.vec (d.2 i)) (firstIx D)) i)) := by
    refine Finset.sum_congr rfl fun d hd => ?_
    dsimp only
    rw [hscale d hd]
    ring
  rw [step1]
  refine GlobalTheory.T.multilinear_sum_eq_of_function_product_sums_eq M τ _ _ _ _ fun xs ys => ?_
  have hk' := key xs ys
  simp only [Finsupp.sum] at hk' ⊢
  refine (?_ : _ = χk * _).trans (hk'.trans (Finset.sum_congr rfl fun d hd => ?_))
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    simp only [coe_toTh ch.W _ ((hth d hd).1 _), coe_toTh ch.W _ (thr' d hd _)]
    rw [prod_update_smul, Function.update_eq_self]
    simp only [movedRow]
    ring
  · simp only [coe_toTh ch.W _ ((hth d hd).1 _), coe_toTh ch.W _ ((hth d hd).2 _)]

end GlobalTheory.FirstRowVertex

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingJointDataJointlySmoothThetaEvenIndex
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaJoint

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {M : Vol G} {t : T}

set_option maxHeartbeats 1000000 in

theorem isBiTheta_lastDat (hM : M.Is t) (j : ℕ) (hj : j + 2 * 0 + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j 0 hj))
    (g : GA D (G.V (.grid D.R.m j)))
    (Φ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Φ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m D.R.m)) → ℂ)
    (hΦ₁ : IsThetaFunO W.ψ _ _ Φ₁) (hΦ₂ : IsThetaFunO W.ψ _ _ Φ₂) :
    IsBiTheta W.ψ _ _ _ (lastDat W hM j hj vN g Φ₁ Φ₂) := by
  have hΨ : IsThetaFunO W.ψ _ _ ((lastAt G W t hM j hj vN).s.om (g, 1) Φ₁) := (lastAt G W t hM j hj vN).s.weil.om_pres _ _ hΦ₁
  have hΞ : IsThetaFunO W.ψ (besAt G hM j 0 hj vN).V₀ (G.V (.top (j + 1)))
      (GlobalTheory.Unf.flatBF (lastAt G W t hM j hj vN).s ((lastAt G W t hM j hj vN).s.om (g, 1) Φ₁)) :=
    (GlobalTheory.LastRed.val_zero (lastAt G W t hM j hj vN).s hΨ).1
  have hΦ₂' : IsThetaFunO W.ψ (G.V (.top (j + 1))) (G.V (.grid D.R.m D.R.m))
      (fun w => Φ₂ ((rowJac G (j + 1) (by omega) 0 (by omega)).ext0 _ w)) := GlobalTheory.RankZeroVac.isThetaFunction_comp_wittExtendByZero _ _ hΦ₂
  exact GlobalTheory.LastBiTheta.isBiTheta_lastBi D W.ψ W.ψ_std (besAt G hM j 0 hj vN).V₀ (G.V (.top j)) (GlobalTheory.SeeSaw.Model.nLine D)
    (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1))) (G.V (.grid D.R.m D.R.m)) (pLine D) (besAt G hM j 0 hj vN).o
    (topOrthAt G (show D.R.m = j + 1 + 1 by omega)) lastTau LastSeeSawStep.lastTau_gram _ _ hΞ hΦ₂'

set_option maxHeartbeats 1000000 in

theorem isBiTheta_contr (hM : M.Is t) (j σ : ℕ) (hj : j + 2 * (σ + 1) + 2 = D.R.m) (vN : GlobalTheory.Unf.VolN (besDecAt G j (σ + 1) hj))
    (vN' : GlobalTheory.Unf.VolN (besDecAt G (j + 1 + 1) σ (by omega))) (vL : GlobalTheory.Unf.VolM D _ _)
    (Ψ₁ : WO (G.V (.grid D.R.m j)) (G.V (.grid D.R.m (j + 1))) → ℂ)
    (Ψ₂ : WO (G.V (.grid D.R.m (j + 1))) (G.V (.grid D.R.m (j + 1 + 1))) → ℂ)
    (h₁ : IsThetaFunO W.ψ _ _ Ψ₁) (h₂ : IsThetaFunO W.ψ _ _ Ψ₂) :
    IsBiTheta W.ψ (G.V (.top j)) (G.V (.top (j + 1))) (G.V (.top (j + 1 + 1)))
      (GlobalTheory.Unf.contr (linkAt hM j σ hj vN (by omega) vN') (G.V (.top (j + 1))) vL
      (GlobalTheory.Unf.flatBF (B := besAt G hM j _ hj vN) (J := jacAt G hM (j + 1) (σ + 1) (by omega))
        (stepAt G W t hM j (by omega) (besDecAt G j _ hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))) Ψ₁)
      (GlobalTheory.Unf.flatFB (J := jacAt G hM (j + 1) (σ + 1) (by omega)) (B := besAt G hM (j + 1 + 1) σ (by omega) vN')
        (stepAt G W t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
          (besDecAt G (j + 1 + 1) σ (by omega))) Ψ₂)) := by
  let B := besAt G hM j (σ + 1) hj vN
  let J := jacAt G hM (j + 1) (σ + 1) (by omega)
  let B' := besAt G hM (j + 1 + 1) σ (by omega) vN'
  let s₁ : GlobalTheory.Unf.StepBF W.ψ B J :=
    stepAt G W t hM j (by omega) (besDecAt G j (σ + 1) hj) (rowJac G (j + 1) (by omega) (σ + 1) (by omega))
  let s₂ : GlobalTheory.Unf.StepFB W.ψ J B' :=
    stepAt G W t hM (j + 1) (by omega) (rowJac G (j + 1) (by omega) (σ + 1) (by omega)) (besDecAt G (j + 1 + 1) σ (by omega))
  have t₁ : IsThetaFunO W.ψ B.V₀ J.W₀ (GlobalTheory.Unf.flatBF s₁ Ψ₁) :=
    (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) W.ψ).1 _ B J s₁ _ h₁
  have t₂ : IsThetaFunO W.ψ J.W₀ B'.V₀ (GlobalTheory.Unf.flatFB s₂ Ψ₂) :=
    (GlobalTheory.Unf.FlatTheta.flat_isThetaFun D (GlobalTheory.T.flatThetaMaps_converge_thetaFunctions D) W.ψ).2 _ J B' s₂ _ h₂
  exact (GlobalTheory.ContrComb.contr_comb_main D W.ψ W.ψ_std _ _ B B' (linkAt hM j σ hj vN (by omega) vN') _ vL _ _ t₁ t₂).1

theorem castSch_theta' {k n : ℕ} (e : n = D.R.m) (f : WO (G.V (.grid D.R.m k)) (G.V (.grid D.R.m n)) → ℂ)
    (hf : IsThetaFunO W.ψ _ _ f) : IsThetaFunO W.ψ _ _ (castSch G e f) := by
  subst e
  exact hf

theorem dite_pred {α : Type} (P : α → Prop) {c : Prop} [Decidable c] {a : c → α} {b : ¬c → α} (ha : ∀ h, P (a h))
    (hb : ∀ h, P (b h)) : P (dite c a b) := by
  by_cases h : c
  · rw [dif_pos h]; exact ha h
  · rw [dif_neg h]; exact hb h

set_option maxHeartbeats 1000000 in

theorem isBiTheta_conAt (hM : M.Is t) (Φ : SchDown G t) (hΦ : ∀ j, IsThetaFunO W.ψ _ _ (Φ j)) (h : Pts G) (j : ℕ) :
    IsBiTheta W.ψ _ _ _ (conAt W hM Φ h j) := by
  unfold conAt
  refine dite_pred (IsBiTheta W.ψ _ _ _) (fun h0 => ?_) (fun _ => dite_pred (IsBiTheta W.ψ _ _ _) (fun hj => ?_) (fun _ => ?_))
  · exact isBiTheta_lastDat W hM j h0 _ _ _ _ (hΦ ⟨j, by omega⟩) (castSch_theta' W _ _ (hΦ ⟨j + 1, by omega⟩))
  · refine isBiTheta_contr W hM j _ hj _ _ _ _ _ ?_ ?_
    · exact (W.om_is (.mu t D.R.m j) ⟨le_rfl, by omega⟩).om_pres _ _ (hΦ ⟨j, by omega⟩)
    · exact (W.om_is (.mu t D.R.m (j + 1)) ⟨le_rfl, by omega⟩).om_pres _ _ (hΦ ⟨j + 1, by omega⟩)
  · exact GlobalTheory.TriStep.isBiTheta_zero'

theorem main : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t Φ τ, IsFlipFin t ch.S.B ch.rm Φ τ → ∀ (M : Vol ch.G) (hM : M.Is t), ∀ d ∈ τ.support, ∀ P h,
    ∀ j, Even j → j < D.R.m → IsBiTheta ch.W.ψ _ _ _ (conAt ch.W hM (fockD ch.W t d.2 P) h j) := by
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch _ _ t Φ τ hτ M hM d hd P h j _ _
  obtain ⟨e, he, φ, hφ, -⟩ := hτ
  exact isBiTheta_conAt ch.W hM _ (fun a => GlobalTheory.DownFock.isThetaFunO_fock_down ch.rm t D.R.m a le_rfl a.2 he ((hφ d hd).2 a) (P a)) h j

end GlobalTheory.ThetaJoint
end
end

