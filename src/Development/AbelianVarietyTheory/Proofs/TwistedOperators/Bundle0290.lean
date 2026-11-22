import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ZeroPartEigenvalueConvention
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0032
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0010
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.Bundle0032
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0279
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0223
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0323
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0328
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0321
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0071
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0277
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0078
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0005
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0267
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0299
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0215
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0266
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittTargetProjections

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerEquivariantRealPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.ConjEquivReal

set_option maxHeartbeats 1000000 in

theorem conjMap_update_real : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ τ : D.what₂.Tau, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (Yc D 0) τ), ∀ (v : (MP R).Vec) (w : (MP R).sm τ), (w : (MP R).H τ) = (MP R).rep τ g (v τ) → GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t (Function.update v τ w) = rTr (Yc D 0) (atTau R.θ (Yc D 0) τ g) (GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t v) := by
  intro hDS D G _ _ Pl0 T A Ks _ _ _ R F X h hlev hgrp hmod hhost hιE t c ht hconj hc Φ hΦ hrep τ g hg v w hw
  classical
  obtain ⟨hfin, hreal, -⟩ := GlobalTheory.IotaReal.iotaX_real_finite R F X h hlev hgrp hmod hιE
  obtain ⟨ha2, ha1, -⟩ := hreal τ g hg
  obtain ⟨-, Rm, -, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  have hint : ∀ (x : X.B.I.Ginf) (z : X.B.Hs), Φ (X.B.σs x z) = X.B.R (x, 1) (Φ z) := by
    obtain ⟨B, hB, rfl⟩ := hΦ
    intro x z
    have hb : B (X.B.σs x z) = X.B.R (x, 1) (B z) := DFunLike.congr_fun (hB x) z
    show X.B.Re (B (X.B.σs x z)) = X.B.R (x, 1) (X.B.Re (B z))
    rw [hb]
    obtain ⟨-, hT⟩ := X.B.Re_spec
    apply ext_inner_left ℂ
    intro u
    rw [← ContinuousLinearMap.adjoint_inner_left (X.B.R (x, 1)), hT, hT]
    congr 1
    funext k
    rw [ContinuousLinearMap.adjoint_inner_left, ← ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply,
      ← Rm, ← ContinuousLinearMap.comp_apply (X.B.R (x, 1)), ← Rm]
    simp
  have hσ1 : ∀ v', X.B.σ v' 1 = 1 := fun v' => (X.ds v').2.2.1.1.1
  have hvec : GlobalTheory.ConjRowMult.vecC X (MP R) c (Function.update v τ w) = fun v' =>
      X.B.σ v' (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 v')) (GlobalTheory.ConjRowMult.vecC X (MP R) c v v') := by
    rw [GlobalTheory.ConjRowMult.vecC_update]
    funext v'
    by_cases hv : v' = X.pl.symm τ
    · subst hv
      rw [Function.update_self, hw, hc τ g hg]
      unfold GlobalTheory.ConjRowMult.vecC
      rw [Equiv.piCongrLeft_apply_apply]
    · rw [Function.update_of_ne hv, ha1 v' hv,
        show uMat (1 : Formalism.REAL.UJ (X.B.I.ε v')) = 1 from rfl, hσ1]
      rfl
  have hsig : X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c (Function.update v τ w)) =
      X.B.σs ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1) (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c v)) := by
    rw [hvec, X.B.tens_spec.2.1]
  have ea : iotaX X h (atTau R.θ (D.sp.Y 0) τ g) = ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1, 1) :=
    Prod.ext rfl ha2
  have hcomm : iotaX X h t⁻¹ * iotaX X h (atTau R.θ (D.sp.Y 0) τ g) =
      iotaX X h (atTau R.θ (D.sp.Y 0) τ g) * iotaX X h t⁻¹ := by
    have h1 : (iotaX X h t).1 = 1 := (hfin t).1 ht
    erw [map_inv]
    refine Prod.ext ?_ ?_
    · simp [h1]
    · simp [ha2]
  obtain ⟨ψ, hψ⟩ := hrep v
  have hψ' := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ (iotaX X h (atTau R.θ (D.sp.Y 0) τ g))
  funext y
  show _ = GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t v (y * atTau R.θ (D.sp.Y 0) τ g)
  erw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.conjMap_apply]
  rw [hsig, hint, ← ea,
    GlobalTheory.ConjRowMult.contRepL_spec X hψ', GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  simp only [map_mul]
  rw [mul_assoc, hcomm, mul_assoc]

end GlobalTheory.ConjEquivReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugatedIntertwinerHasColumnLevel
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
noncomputable section

namespace GlobalTheory.ConjRowLevel

private theorem inner_R_eq_inner_R_inv {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (a : X.B.I.GA)
    (x z : X.B.I.L2 X.B.μf X.B.fund) : ⟪x, X.B.R a z⟫_ℂ = ⟪X.B.R a⁻¹ x, z⟫_ℂ := by
  obtain ⟨h1, hmul, hnorm, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  let L : X.B.I.L2 X.B.μf X.B.fund →ₗᵢ[ℂ] X.B.I.L2 X.B.μf X.B.fund :=
    { toLinearMap := (X.B.R a⁻¹ : X.B.I.L2 X.B.μf X.B.fund →ₗ[ℂ] X.B.I.L2 X.B.μf X.B.fund)
      norm_map' := hnorm a⁻¹ }
  have hback : X.B.R a⁻¹ (X.B.R a z) = z := by
    rw [← ContinuousLinearMap.comp_apply, ← hmul, inv_mul_cancel, h1]
    rfl
  calc ⟪x, X.B.R a z⟫_ℂ = ⟪L x, L (X.B.R a z)⟫_ℂ := (L.inner_map_map _ _).symm
    _ = ⟪X.B.R a⁻¹ x, z⟫_ℂ := by
      show ⟪X.B.R a⁻¹ x, X.B.R a⁻¹ (X.B.R a z)⟫_ℂ = _
      rw [hback]

private theorem e_inv_mul_eq_chi2_mul {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (k : X.B.I.Gf) (hk : k ∈ X.K2)
    (y : X.B.I.Gf) : X.B.e (k⁻¹ * y) = X.chi2 k * X.B.e y := by
  classical
  obtain ⟨_, hmulK, hinvK, hchi, hnorm⟩ := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have he : ∀ z, X.B.e z = if z ∈ X.K2 then star (X.chi2 z) / ((X.B.μf X.K2).toReal : ℂ) else 0 :=
    X.e_eq
  have hunit : X.chi2 k * star (X.chi2 k) = 1 := by
    rw [RCLike.star_def, RCLike.mul_conj, hnorm k hk]
    norm_num
  by_cases hy : y ∈ X.K2
  · have hky : k⁻¹ * y ∈ X.K2 := hmulK _ (hinvK _ hk) _ hy
    have hsplit : X.chi2 y = X.chi2 k * X.chi2 (k⁻¹ * y) := by
      rw [← hchi _ hk _ hky, mul_inv_cancel_left]
    rw [he, he, if_pos hky, if_pos hy, hsplit, star_mul']
    linear_combination (-(star (X.chi2 (k⁻¹ * y)) / ((X.B.μf X.K2).toReal : ℂ))) * hunit
  · have hky : k⁻¹ * y ∉ X.K2 := fun h => hy (by simpa using hmulK _ hk _ h)
    rw [he, he, if_neg hky, if_neg hy, mul_zero]

theorem reg_comp_Re {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (k : X.B.I.Gf) (hk : k ∈ X.K2) :
    (X.B.R (1, k)).comp X.B.Re = X.chi2 k • X.B.Re := by
  obtain ⟨-, hmul, -, -⟩ := GlobalTheory.RightRegProps.rightReg_unitary_mul_continuous X.B.I X.B.μf X.B.fund
    X.B.fund_spec X.B.R X.B.R_spec
  ext1 y
  apply ext_inner_left ℂ
  intro x
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, inner_smul_right,
    inner_R_eq_inner_R_inv X, X.B.Re_spec.2, X.B.Re_spec.2]
  have hstep : ∀ g : X.B.I.Gf,
      ⟪X.B.R (1, k)⁻¹ x, X.B.R (1, g) y⟫_ℂ = ⟪x, X.B.R (1, k * g) y⟫_ℂ := by
    intro g
    have hprod : (((1 : X.B.I.Ginf), k * g) : X.B.I.GA) = (1, k) * (1, g) := by simp
    rw [hprod, hmul, ContinuousLinearMap.comp_apply]
    exact (inner_R_eq_inner_R_inv X (1, k) x _).symm
  simp_rw [hstep]
  have hinv := integral_mul_left_eq_self (μ := X.B.μf)
    (fun g' => X.B.e (k⁻¹ * g') * ⟪x, X.B.R (1, g') y⟫_ℂ) k
  simp only [inv_mul_cancel_left] at hinv
  rw [hinv]
  simp_rw [e_inv_mul_eq_chi2_mul X k hk, mul_assoc]
  exact integral_const_mul _ _
private theorem contRep_mul_right_eq_chi2_mul {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Φ : X.B.Hs →L[ℂ] L2X X)
    (hΦ : Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re) (v : X.B.Hs) {ψ : X.B.I.GA → ℂ}
    (hψ : Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ v) ψ) (κ : X.B.I.Gf) (hκ : κ ∈ X.K2) :
    ∀ z, ψ (z * ((1 : X.B.I.Ginf), κ)) = X.chi2 κ * ψ z := by
  obtain ⟨A, -, hA⟩ := Submodule.mem_map.1 hΦ
  have hΦv : Φ v = X.B.Re (A v) := by
    rw [← hA]
    rfl
  have h1 := Formalism.L2.SG.EvalTOntoRep.contRep_reg X hψ ((1 : X.B.I.Ginf), κ)
  have hR : X.B.R ((1 : X.B.I.Ginf), κ) (Φ v) = X.chi2 κ • Φ v := by
    rw [hΦv, ← ContinuousLinearMap.comp_apply, reg_comp_Re X κ hκ, ContinuousLinearMap.smul_apply]
  rw [hR] at h1
  have h2 := Formalism.L2.SG.EvalTOntoRep.contRep_smul X (X.chi2 κ) hψ
  have heq := Formalism.L2.SG.EvalTOntoRep.contRep_unique X h1 h2
  intro z
  simpa using congrFun heq z

theorem conjMap_level : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∀ (t : GA D (Yc D 0)) (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), t ∈ GfC (Yc D 0) → ConjLevel (t)⁻¹ (levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) (levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true))) ((iotaX X h).toMulEquiv ⁻¹' {x : X.B.I.GA | x.1 = 1 ∧ x.2 ∈ X.K2}) (fun k => star (X.chi2 ((iotaX X h).toMulEquiv k).2)) → (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) → ∀ Φ : X.B.Hs →L[ℂ] L2X X, Φ ∈ X.B.I.eHom X.B.σs X.B.μf X.B.fund X.B.R X.B.Re → (∀ u : (MP R).Vec, ∃ ψ, Formalism.L2.SG.EvalTOntoRep.IsContRep X (Φ (X.B.tens (GlobalTheory.ConjRowMult.vecC X (MP R) c u))) ψ) → ∀ u : (MP R).Vec, ∀ k ∈ levS (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)), ∀ g : GA D (Yc D 0), GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u (@HMul.hMul (GA D (Yc D 0)) (GA D (Yc D 0)) (GA D (Yc D 0)) _ g k) = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k * GlobalTheory.ConjRowMult.conjMap X (MP R) c Φ h t u g := by
  intro _ D G _ _ Pl0 T A Ks _ _ _ R F X h _ _ _ _ _ t c _ hconj _ Φ hΦ hcont u k hk g
  obtain ⟨ψ, hψ⟩ := hcont u
  erw [GlobalTheory.ConjRowMult.conjMap_apply, GlobalTheory.ConjRowMult.conjMap_apply]
  rw [GlobalTheory.ConjRowMult.contRepL_spec X hψ]
  obtain ⟨hmem, hval⟩ := hconj k
  have hk' : ((iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹)).1 = 1 ∧
      ((iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹)).2 ∈ X.K2 := hmem.1 hk
  have hv := hval hk
  obtain ⟨hp1, hp2⟩ := hk'
  obtain ⟨κ, hκdef⟩ : ∃ κ, κ = ((iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹)).2 := ⟨_, rfl⟩
  have hq : (iotaX X h).toMulEquiv (t⁻¹⁻¹ * k * t⁻¹) = ((1 : X.B.I.Ginf), κ) := Prod.ext hp1 hκdef.symm
  have hκ : κ ∈ X.K2 := by
    rw [hκdef]
    exact hp2
  have hv' : star (X.chi2 κ) = levChi (Yc D 0) (R.βY 0) (R.dat0 (R.levR F true)) k := by
    rw [hκdef]
    exact hv
  have hsplit : (iotaX X h).toMulEquiv (g * k * t⁻¹) =
      (iotaX X h).toMulEquiv (g * t⁻¹) * ((1 : X.B.I.Ginf), κ) := by
    rw [← hq]
    calc (iotaX X h).toMulEquiv (g * k * t⁻¹)
        = (iotaX X h).toMulEquiv (g * t⁻¹ * (t⁻¹⁻¹ * k * t⁻¹)) := by
          rw [show g * t⁻¹ * (t⁻¹⁻¹ * k * t⁻¹) = g * k * t⁻¹ by group]
      _ = _ := map_mul _ _ _
  change star (ψ ((iotaX X h).toMulEquiv (g * k * t⁻¹))) = _ * star (ψ ((iotaX X h).toMulEquiv (g * t⁻¹)))
  rw [hsplit, contRep_mul_right_eq_chi2_mul X Φ hΦ _ hψ κ hκ, star_mul', hv']

end GlobalTheory.ConjRowLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousRealPlacesMatrixCoefficientProduct
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SepPer.CoefCont

theorem continuous_coefR : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (v a : ∀ τ, M.H τ), Continuous (coefR θ M v a) := by
  intro D θ hθ V S M v a
  haveI : IsTotallyReal D.host.F := D.sp.cm.totReal
  unfold coefR
  refine continuous_finset_prod _ fun τ _ => ?_
  have hc : Continuous fun g : GA D V => cmp θ τ g := GlobalTheory.Mem.VolExists.continuous_infMat V.gram (hθ τ)
  have hu : ∀ g : GA D V, (cmp θ τ g)ᴴ * gramAt D V τ * cmp θ τ g = gramAt D V τ := by
    intro g
    have h0 := GlobalTheory.MarkUnit.infMat_unitary D.sp.cm.sig V.gram (tauE D τ)
      (fun x => IsCMField.complexEmbedding_complexConj D.host.E (tauE D τ) x) (θ τ) (hθ τ) g
    have he : (cmp θ τ g)ᴴ = ((cmp θ τ g).map (starRingEnd ℂ)).transpose := by
      ext i j; simp [Matrix.conjTranspose_apply]
    rw [he]
    exact h0
  have hB : M.fr τ * (M.fr τ)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (M.fr_unit τ))
  have hmem : ∀ g : GA D V, Formalism.REAL.inUJ (M.ε τ) (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹) := by
    intro g
    unfold Formalism.REAL.inUJ
    calc (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * cmp θ τ g * (M.fr τ)⁻¹)
        = ((M.fr τ)⁻¹)ᴴ * ((cmp θ τ g)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * cmp θ τ g) * (M.fr τ)⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((M.fr τ)⁻¹)ᴴ * ((M.fr τ)ᴴ * Formalism.REAL.Jm (M.ε τ) * M.fr τ) * (M.fr τ)⁻¹ := by
          rw [M.fr_gram τ, hu g]
      _ = (M.fr τ * (M.fr τ)⁻¹)ᴴ * Formalism.REAL.Jm (M.ε τ) * (M.fr τ * (M.fr τ)⁻¹) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm (M.ε τ) := by
          rw [hB, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hconj : Continuous fun g : GA D V => M.fr τ * cmp θ τ g * (M.fr τ)⁻¹ :=
    (continuous_const.matrix_mul hc).matrix_mul continuous_const
  have hσ := (M.ds τ).2.2.1.2.2 (a τ)
  have hrep : Continuous fun g : GA D V => M.rep τ (cmp θ τ g) (a τ) :=
    hσ.comp_continuous hconj hmem
  exact continuous_const.inner hrep

end GlobalTheory.SepPer.CoefCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousThetaMatrixCoeffAlongSandwich
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ThetaCoefCont

private theorem measure_fundamentalDomain_ratL_lt_infty {D : D7} (V W : HSp D) (ν : Measure (WO V W)) (𝓕 : Set (WO V W))
    (hν : ν.IsAddHaarMeasure) (h𝓕 : IsAddFundamentalDomain (ratL W V) 𝓕 ν) : ν 𝓕 < ⊤ := by
  obtain ⟨hg, -, hsc, -, hdisc, K, hK, hcov⟩ := GlobalTheory.AdelicMatrixLattice.lattice D W V
  haveI := hg
  haveI := hsc
  haveI := hdisc
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  haveI : Countable (ratL W V) := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  exact GlobalTheory.measure_addFundamentalDomain_lt_top_of_cocompact (ratL W V) hK hcov ν h𝓕

theorem continuous_coef : ∀ (D : D7) (V W : HSp D) (a b : ℕ) (P : Matrix (Fin W.rank) (Fin a) D.host.E) (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (ν : Measure (WO V W)) (𝓕 : Set (WO V W)), ν.IsAddHaarMeasure → IsAddFundamentalDomain (ratL W V) 𝓕 ν → ∀ G G' : WO V W → ℂ, IsThetaFunO ψ V W G → IsThetaFunO ψ V W G' → Continuous (fun y : Mx D a b => ∫ u in 𝓕, heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u * star (G' u) ∂ν) := by
  intro D V W a b P Q ψ hψ ν 𝓕 hν h𝓕 G G' hG hG'
  haveI : BorelSpace (WO V W) := ⟨rfl⟩
  have hfin : ν 𝓕 < ⊤ := measure_fundamentalDomain_ratL_lt_infty V W ν 𝓕 hν h𝓕
  haveI : IsFiniteMeasure (ν.restrict 𝓕) := ⟨by rw [Measure.restrict_apply_univ]; exact hfin⟩
  obtain ⟨C', hC'⟩ := GlobalTheory.OrientedHeis.theta_bounded hψ hG'
  obtain ⟨g, hg⟩ : ∃ g : GlobalTheory.RealWeil.BB ψ V W, (g.1 : WO V W → ℂ) = G :=
    ⟨_, GlobalTheory.RealWeil.coe_toB hψ G hG⟩
  have hE : Continuous (GlobalTheory.IsoMean.emb V W P Q) := by
    unfold GlobalTheory.IsoMean.emb
    exact (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  have hρ : Continuous fun y : Mx D a b => GlobalTheory.RealWeil.rhoB hψ (GlobalTheory.IsoMean.emb V W P Q y) g :=
    (GlobalTheory.RealWeil.continuous_rhoB hψ g).comp hE

  have hΦ : Continuous fun h : GlobalTheory.RealWeil.BB ψ V W => ∫ u in 𝓕, h.1 u * star (G' u) ∂ν := by
    rw [continuous_iff_continuousAt]
    intro h₀
    have hnear : ∀ᶠ h in nhds h₀, ‖h‖ < ‖h₀‖ + 1 :=
      (continuous_norm.tendsto h₀).eventually (gt_mem_nhds (lt_add_one _))
    refine MeasureTheory.continuousAt_of_dominated (bound := fun _ => (‖h₀‖ + 1) * C') ?_ ?_ ?_ ?_
    · exact Filter.Eventually.of_forall fun h =>
        (h.1.continuous.mul (continuous_star.comp hG'.cont)).aestronglyMeasurable
    · refine hnear.mono fun h hh => Filter.Eventually.of_forall fun u => ?_
      rw [norm_mul, norm_star]
      exact mul_le_mul ((GlobalTheory.RealWeil.norm_ev_le u h).trans hh.le) (hC' u) (norm_nonneg _)
        ((norm_nonneg h).trans hh.le)
    · exact integrable_const _
    · refine Filter.Eventually.of_forall fun u => ?_
      have hev : Continuous fun h : GlobalTheory.RealWeil.BB ψ V W => h.1 u := by
        have hc : Continuous fun h : GlobalTheory.RealWeil.BB ψ V W => GlobalTheory.RealWeil.ev _ _ u h :=
          (GlobalTheory.RealWeil.ev _ _ u).continuous
        simpa only [GlobalTheory.RealWeil.ev_apply] using hc
      exact (hev.mul continuous_const).continuousAt
  have key : ∀ (y : Mx D a b) (u : WO V W), heisO ψ V W (GlobalTheory.IsoMean.emb V W P Q y) G u =
      (GlobalTheory.RealWeil.rhoB hψ (GlobalTheory.IsoMean.emb V W P Q y) g).1 u := by
    intro y u
    rw [GlobalTheory.RealWeil.coe_rhoB, hg]
  simp_rw [key]
  exact hΦ.comp hρ

end GlobalTheory.ThetaCoefCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContragredientModelEqConjTraceFormulaDiscreteSerStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearIsometryEquiv_intertwining_modelRep : GlobalTheory.Published.DiscreteSeriesClassification → ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D), R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsModels → HostHyp D → (∀ x : X.B.I.E, HEq (X.ιE x) x) → ∃ (c : ∀ τ, (MP R).H τ ≃ₗᵢ⋆[ℂ] X.B.H (X.pl.symm τ)), (∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D (D.sp.Y 0) τ), ∀ w, c τ ((MP R).rep τ g w) = X.B.σ (X.pl.symm τ) (uMat ((iotaX X h (atTau R.θ (D.sp.Y 0) τ g)).1 (X.pl.symm τ))) (c τ w)) ∧ ∀ τ, (c τ).symm (X.B.w (X.pl.symm τ)) ∈ (MP R).sm τ := by
  first | exact @GlobalTheory.SeeInt.conjModel_of_setting | exact GlobalTheory.SeeInt.conjModel_of_setting | (intros; apply GlobalTheory.SeeInt.conjModel_of_setting <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecayWeightOneParamTranslateLeConstMul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Classical

noncomputable section

namespace GlobalTheory.OnePDecay

section Frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedRing

theorem hsn_eq_norm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : hsn A = ‖A‖ := by
  rw [hsn, Matrix.frobenius_norm_def, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  exact (Real.rpow_natCast _ 2).symm

theorem hsn_mul_le {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) : hsn (A * B) ≤ hsn A * hsn B := by
  rw [hsn_eq_norm, hsn_eq_norm, hsn_eq_norm]
  exact Matrix.frobenius_norm_mul A B

end Frob

theorem hsn_nonneg' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hsn A := Real.sqrt_nonneg _

theorem continuous_hsn_exp {n : ℕ} (X : Matrix (Fin n) (Fin n) ℂ) :
    Continuous fun s : ℝ => hsn (NormedSpace.exp (s • X) : Matrix (Fin n) (Fin n) ℂ) := by
  unfold hsn
  refine Real.continuous_sqrt.comp (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_)
  exact (continuous_iff_continuousAt.2 fun t => (GlobalTheory.Mem.Lift.hasDerivAt_exp_entry X t i j).continuousAt).norm.pow 2

theorem decay_oneP : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (τ : D.what₂.Tau)
    (X : Matrix (Fin V.rank) (Fin V.rank) ℂ), X ∈ lieAt V τ → ∀ N : ℕ, ∃ L : ℝ, 0 ≤ L ∧
      ∀ (x : GA D V) (t : ℝ), |t| < 1 → ∏ τ', ((1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N)⁻¹ ≤
        L * ∏ τ', ((1 + hsn (cmp θ τ' x)) ^ N)⁻¹ := by
  intro D θ hθ V τ X hX N
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    (continuous_hsn_exp X).continuousOn
  set m : ℝ := max 1 (max M (hsn (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ))) with hmdef
  have hm1 : 1 ≤ m := le_max_left _ _
  have hbound : ∀ τ' (s : ℝ), |s| ≤ 1 → hsn (cmp θ τ' (oneP θ V τ X s)) ≤ m := by
    intro τ' s hs
    have h := GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX s
    by_cases e : τ' = τ
    · subst e
      show hsn (infMat _ _ (θ τ') _) ≤ m
      rw [h.2.1]
      have := hM s ⟨(abs_le.1 hs).1, (abs_le.1 hs).2⟩
      rw [Real.norm_eq_abs] at this
      exact (le_abs_self _).trans (this.trans (le_max_of_le_right (le_max_left _ _)))
    · show hsn (infMat _ _ (θ τ') _) ≤ m
      rw [h.2.2 τ' e]
      exact le_max_of_le_right (le_max_right _ _)
  have hkey : ∀ (x : GA D V) (t : ℝ) τ', |t| < 1 →
      1 + hsn (cmp θ τ' x) ≤ (1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) * m := by
    intro x t τ' ht
    have hx : x = x * oneP θ V τ X t * oneP θ V τ X (-t) := by
      rw [mul_assoc, ← GlobalTheory.Mem.Lift.oneP_add hθ hX, add_neg_cancel, GlobalTheory.Mem.Lift.oneP_zero hθ, mul_one]
    have h1 : hsn (cmp θ τ' x) ≤ hsn (cmp θ τ' (x * oneP θ V τ X t)) * m := by
      have e2 : cmp θ τ' x = cmp θ τ' (x * oneP θ V τ X t) * cmp θ τ' (oneP θ V τ X (-t)) := by
        show infMat _ _ (θ τ') x = infMat _ _ (θ τ') _ * infMat _ _ (θ τ') _
        rw [← GlobalTheory.PointAtPlaceHom.infMat_mul, ← hx]
      rw [e2]
      exact (hsn_mul_le _ _).trans (mul_le_mul_of_nonneg_left
        (hbound τ' (-t) (by rw [abs_neg]; exact ht.le)) (hsn_nonneg' _))
    nlinarith [hsn_nonneg' (cmp θ τ' (x * oneP θ V τ X t))]
  refine ⟨m ^ (N * Fintype.card D.what₂.Tau), by positivity, fun x t ht => ?_⟩
  rw [pow_mul, ← Finset.card_univ, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun τ' _ => inv_nonneg.2 (pow_nonneg (by linarith [hsn_nonneg' (cmp θ τ' (x * oneP θ V τ X t))]) N)) (fun τ' _ => ?_)
  have ha := hsn_nonneg' (cmp θ τ' (x * oneP θ V τ X t))
  have hb := hsn_nonneg' (cmp θ τ' x)
  have hk := hkey x t τ' ht
  have hpa : 0 < (1 + hsn (cmp θ τ' (x * oneP θ V τ X t))) ^ N := pow_pos (by linarith) N
  have hpb : 0 < (1 + hsn (cmp θ τ' x)) ^ N := pow_pos (by linarith) N
  rw [← div_eq_mul_inv, le_div_iff₀ hpb, inv_mul_eq_div, ← div_pow]
  refine pow_le_pow_left₀ (div_nonneg (by linarith) (by linarith)) ?_ N
  rw [div_le_iff₀ (by linarith)]
  linarith

end GlobalTheory.OnePDecay

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowDualPartFinitePairsTriviallyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeGridRow_dualPart_finite_pairs_trivially : OnStd fun {D} _ _ {sc} {G} W F => ∀ ρ (h : 2 * ρ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * ρ + 1), MxAt (fun _ => True) (u ⬝ (F.dB ρ h).jY) ∧ ∀ a, (F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a ∈ latRow G (2 * ρ + 1) → W.ψ (symplO (G.V (.grid (2 * ρ + 2) 0)) (G.V (.grid (2 * ρ + 1) 0)) ((F.dB ρ h).extX (G.V (.grid (2 * ρ + 1) 0)) a) ((F.dB ρ h).extY (G.V (.grid (2 * ρ + 1) 0)) (u ⬝ (F.dB ρ h).jY))) = 1 := by
  first | exact @GlobalTheory.AscFin.BesIso.splits_iso | exact GlobalTheory.AscFin.BesIso.splits_iso | (intros; apply GlobalTheory.AscFin.BesIso.splits_iso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowStableWittTargetProjectionsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.depthLatticeGridRow_stable_wittTargetProjections : OnStd fun {D} _ _ {sc} {G} _ F => ∀ σ (_ : 2 * (σ + 1) + 2 ≤ D.R.m) (h' : 2 * σ + 2 ≤ D.R.m), ∀ u ∈ latRow G (2 * σ + 2), ((F.dB σ h').jX * (F.dB σ h').pX) * u ∈ latRow G (2 * σ + 2) ∧ ((F.dB σ h').jY * (F.dB σ h').pY) * u ∈ latRow G (2 * σ + 2) := by
  first | exact @GlobalTheory.AscFin.latRow_proj_tgt | exact GlobalTheory.AscFin.latRow_proj_tgt | (intros; apply GlobalTheory.AscFin.latRow_proj_tgt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleMixedModelSupportedClassSubsetSplitLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubleMixedModelSupportedClass_subset_splitLatticeVacua : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ σ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ σ) (p : Pieces V₀ W W₀ ρ σ) (x : Mx D W.rank ρ) (y : Mx D V₀.rank σ) (Γ : AddSubgroup (WO V W)), p.Is dV dW x ψ → Splits dV dW p x y ψ Γ → ∀ Φ ∈ cls dV dW p x y ψ, VacG ψ V W Γ Φ := by
  first | exact @GlobalTheory.AscFin.SplitVac.cls_vac | exact GlobalTheory.AscFin.SplitVac.cls_vac | (intros; apply GlobalTheory.AscFin.SplitVac.cls_vac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EnormMixedModelTermLeISup
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTerm

theorem enorm_term_le_iSup : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ (G : WO V W → ℂ) (y : Matrix (Fin W.rank) (Fin r) D.host.E), ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ ≤ ⨆ w, ‖G w‖ₑ := by
  intro D V V' W r C C' B ψ hψ μ 𝓨 hμ G y
  have hψ1 : ∀ x, ‖(ψ x : ℂ)‖ₑ = 1 := fun x => by
    rw [← ofReal_norm_eq_enorm, hψ.1.2.1 x, ENNReal.ofReal_one]
  calc ‖term ψ V V' W C C' B μ 𝓨 G y‖ₑ
      ≤ ∫⁻ z in 𝓨, ‖heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) G
          (isoPart V W C z + midPart V V' W B 0)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ _ in 𝓨, (⨆ w, ‖G w‖ₑ) ∂μ := by
        refine lintegral_mono fun z => ?_
        simp only [heisO, enorm_mul, hψ1, one_mul]
        exact le_iSup (fun w => ‖G w‖ₑ) _
    _ = ⨆ w, ‖G w‖ₑ := by rw [setLIntegral_const, hμ.2.2, mul_one]

end GlobalTheory.MixedTerm
end

