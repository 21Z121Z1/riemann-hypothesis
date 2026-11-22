import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0026
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0027
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0474
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0318
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0464
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0346
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0380
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0328
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0379
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0289
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0251
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0249
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0447
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0473
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0200
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0232
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0025
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfPderivStable
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0475
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0006
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0397
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0476
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0356
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesUnitaryAbsolutelyConvergentModerat
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.DepthPays
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0261
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviFactorScalarsAutomorphicCharacters
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LeviChar

open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition

theorem detPow_pos' {D : D7} {r : ℕ} (a : GL (Fin r) (AE D)) (n : ℕ) : 0 < GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow
  apply Real.rpow_pos_of_pos
  exact NNReal.coe_pos.2 (pos_iff_ne_zero.2
    ((Group.isUnit (Matrix.GeneralLinearGroup.det a)).map (GlobalTheory.Doubling.absE D.host.F D.host.E)).ne_zero)

theorem detPow_mul' {D : D7} {r : ℕ} (a b : GL (Fin r) (AE D)) (n : ℕ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow (a * b) n = GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n * GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow b n := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow
  rw [map_mul, map_mul, NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)]

theorem detPow_one' {D : D7} {r : ℕ} (n : ℕ) : GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow (1 : GL (Fin r) (AE D)) n = 1 := by
  have h := detPow_mul' (1 : GL (Fin r) (AE D)) 1 n
  rw [mul_one] at h
  exact mul_left_cancel₀ (detPow_pos' 1 n).ne' (h.symm.trans (mul_one _).symm)

theorem continuous_detPow' {D : D7} {r : ℕ} (n : ℕ) :
    Continuous fun a : GL (Fin r) (AE D) => GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a n := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow
  have h1 : Continuous fun a : GL (Fin r) (AE D) => Matrix.GeneralLinearGroup.det a :=
    Matrix.GeneralLinearGroup.continuous_det
  have h2 := (GlobalTheory.Doubling.continuous_absE (F := D.host.F) (E := D.host.E))
  exact (NNReal.continuous_coe.comp (h2.comp h1)).rpow_const (fun _ => Or.inr (by positivity))

set_option maxHeartbeats 400000 in

open GlobalTheory.MixModel in

theorem levi_scalars_autChar : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.IsIsoSplit V V' C B → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (χS' χT' : (AE D)ˣ →* Circle) (ω' : GA D V' × GA D W →* Module.End ℂ (WO V' W → ℂ)), IsWeilDatumO ψ V' W χS' χT' ω' → ∃ (μa : GL (Fin r) (AE D) →* Circle) (ξ : GA D V' →* Circle), GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.IsAutCharGL r μa ∧ GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.IsAutCharU V' ξ ∧ ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨 → ∀ (a : GL (Fin r) (AE D)) (g' : GA D V') (m : GA D V), HMul.hMul (Formalism.L2.Theta.mt V m) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val → HMul.hMul (Formalism.L2.Theta.mt V m) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (Formalism.L2.Theta.mt V' g') → ∀ f, IsThetaFunO ψ V W f → GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 (ω (m, 1) f) = ((μa a : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank : ℂ) * (ξ g' : ℂ)) • ω' (g', 1) (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.res V V' W C B μ 𝓨 f) := by
  intro D V V' W r C B hs ψ χS χT ω hω χS' χT' ω' hω'
  obtain ⟨d, hdC, hdB, hker⟩ := GlobalTheory.T.exists_wittDecomposition_isotropicSplit_unipotent D V V' r C B hs
  obtain ⟨μ₀, 𝓨₀, h₀⟩ := GlobalTheory.MixModel.exists_isCovolOne D W.rank r
  have hind := fun f hf μ 𝓨 (hμ : IsCovolOne (GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.ratMx D W.rank r) μ 𝓨) =>
    GlobalTheory.T.thetaRestrictIsotropic_indep_covolume_measure D V V' W r C B hs d hdC hdB ψ f hf μ₀ μ 𝓨₀ 𝓨 h₀ hμ

  let s : GL (Fin r) (AE D) → GA D V' → GA D V := fun a g' => d.levi a * d.emb0 g'
  have hsC : ∀ a g', HMul.hMul (mt V (s a g')) (C.map (incA D)) = HMul.hMul (C.map (incA D)) a.val := by
    intro a g'
    subst hdC
    show mt V (d.levi a * d.emb0 g') ⬝ d.jX = d.jX ⬝ a.1
    rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclX, d.levi_jX]
  have hsB : ∀ a g', HMul.hMul (mt V (s a g')) (B.map (incA D)) = HMul.hMul (B.map (incA D)) (mt V' g') := by
    intro a g'
    subst hdB
    show mt V (d.levi a * d.emb0 g') ⬝ d.j0 = d.j0 ⬝ mt V' g'
    rw [mt_mul, Matrix.mul_assoc, d.wittDecomp_anisotropicEmbedding_inclAnisotropic, ← Matrix.mul_assoc, d.wittDecomp_levi_inclAnisotropic]
  have hsmul : ∀ a₁ g₁ a₂ g₂, s (a₁ * a₂) (g₁ * g₂) = s a₁ g₁ * s a₂ g₂ := by
    intro a₁ g₁ a₂ g₂
    show d.levi (a₁ * a₂) * d.emb0 (g₁ * g₂) = d.levi a₁ * d.emb0 g₁ * (d.levi a₂ * d.emb0 g₂)
    rw [map_mul, map_mul, show d.levi a₁ * d.emb0 g₁ * (d.levi a₂ * d.emb0 g₂) =
      d.levi a₁ * (d.emb0 g₁ * d.levi a₂) * d.emb0 g₂ by simp only [mul_assoc], d.wittHyperbolic_anisotropic_commute_levi]
    simp only [mul_assoc]
  have hs1 : s 1 1 = 1 := by simp [s]
  have hc := fun a g' => GlobalTheory.T.restriction_wittTower_intertwines_levi_weilRep D V V' W r C B hs ψ χS χT ω hω χS' χT' ω' hω' μ₀ 𝓨₀ h₀ a g' (s a g')
    (hsC a g') (hsB a g') 1
  choose c hc using hc
  set R := res V V' W C B μ₀ 𝓨₀ with hR
  have dpos := fun a : GL (Fin r) (AE D) => detPow_pos' a W.rank
  have dmul := fun a b : GL (Fin r) (AE D) => detPow_mul' a b W.rank
  have d1 : GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow (1 : GL (Fin r) (AE D)) W.rank = 1 := detPow_one' W.rank
  have dcont : Continuous fun a : GL (Fin r) (AE D) => GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank := continuous_detPow' W.rank

  by_cases hz : ∃ f₀, IsThetaFunO ψ V W f₀ ∧ R f₀ ≠ 0
  swap
  · push_neg at hz
    refine ⟨1, 1, ⟨continuous_const, fun _ => rfl⟩, ⟨continuous_const, fun _ _ => rfl⟩, ?_⟩
    intro μ 𝓨 hμ a g' m _ _ f hf
    rw [hind _ (hω.om_pres _ f hf) μ 𝓨 hμ, hind f hf μ 𝓨 hμ, hz _ (hω.om_pres _ f hf), hz f hf, map_zero,
      smul_zero]
  obtain ⟨f₀, hf₀, hne⟩ := hz
  have hRth : IsThetaFunO ψ V' W (R f₀) := ((GlobalTheory.TowerRestrict.res_theta D V V' W r C B hs ψ hω.std μ₀ 𝓨₀ h₀).1 f₀ hf₀).2.1

  have hinj : ∀ (g' : GA D V') (v : WO V' W → ℂ), ω' (g', 1) v = 0 → v = 0 := by
    intro g' v hv
    have : ω' (g'⁻¹, 1) (ω' (g', 1) v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, inv_mul_cancel, mul_one, ← Prod.one_eq_mk, map_one,
        Module.End.one_apply]
    rw [← this, hv, map_zero]
  have huniq : ∀ (g' : GA D V') (k₁ k₂ : ℂ), k₁ • ω' (g', 1) (R f₀) = k₂ • ω' (g', 1) (R f₀) → k₁ = k₂ := by
    intro g' k₁ k₂ h
    have hw : ω' (g', 1) (R f₀) ≠ 0 := fun h0 => hne (hinj g' _ h0)
    exact smul_left_injective ℂ hw h
  let K : GL (Fin r) (AE D) → GA D V' → ℂ := fun a g' => (c a g' : ℂ) * (GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank : ℂ)
  have hK : ∀ a g' f, IsThetaFunO ψ V W f → R (ω (s a g', 1) f) = K a g' • ω' (g', 1) (R f) := fun a g' f hf =>
    hc a g' f hf
  have Kmul : ∀ a₁ g₁ a₂ g₂, K (a₁ * a₂) (g₁ * g₂) = K a₁ g₁ * K a₂ g₂ := by
    intro a₁ g₁ a₂ g₂
    apply huniq (g₁ * g₂)
    rw [← hK _ _ f₀ hf₀, hsmul, show ((s a₁ g₁ * s a₂ g₂, (1 : GA D W)) : GA D V × GA D W) = (s a₁ g₁, 1) * (s a₂ g₂, 1) by
      rw [Prod.mk_mul_mk, mul_one], map_mul, Module.End.mul_apply, hK _ _ _ (hω.om_pres _ f₀ hf₀), hK _ _ f₀ hf₀,
      map_smul, smul_smul, ← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one]
  have cmul : ∀ a₁ g₁ a₂ g₂, c (a₁ * a₂) (g₁ * g₂) = c a₁ g₁ * c a₂ g₂ := by
    intro a₁ g₁ a₂ g₂
    have h := Kmul a₁ g₁ a₂ g₂
    simp only [K, dmul] at h
    have hd : ((GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a₁ W.rank * GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a₂ W.rank : ℝ) : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.2 (mul_pos (dpos a₁) (dpos a₂)).ne'
    apply Circle.coe_inj.1
    rw [Circle.coe_mul]
    apply mul_right_cancel₀ hd
    rw [h, Complex.ofReal_mul]; ring
  have c11 : c 1 1 = 1 := by
    have h := huniq 1 (K 1 1) 1 (by rw [← hK _ _ f₀ hf₀, hs1, ← Prod.one_eq_mk, ← Prod.one_eq_mk, map_one, map_one, Module.End.one_apply,
      Module.End.one_apply, one_smul])
    simp only [K, d1, Complex.ofReal_one, mul_one] at h
    exact Circle.coe_inj.1 (by rw [h, Circle.coe_one])
  let μa : GL (Fin r) (AE D) →* Circle :=
    { toFun := fun a => c a 1
      map_one' := c11
      map_mul' := fun a b => by rw [← cmul, mul_one] }
  let ξ : GA D V' →* Circle :=
    { toFun := fun g => c 1 g
      map_one' := c11
      map_mul' := fun g g' => by rw [← cmul, mul_one] }
  have csplit : ∀ a g', c a g' = μa a * ξ g' := by
    intro a g'
    have := cmul a 1 1 g'
    rwa [mul_one, one_mul] at this
  refine ⟨μa, ξ, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  ·
    obtain ⟨x₁, hx₁⟩ := Function.ne_iff.1 hne
    have hΦ := GlobalTheory.T.continuous_restrictedWeilFirstFactor_apply D V V' W r C B ψ χS χT ω hω μ₀ 𝓨₀ h₀ f₀ hf₀ x₁
    have heq : ∀ a, ((μa a : Circle) : ℂ) = R (ω (d.levi a, 1) f₀) x₁ /
        ((GlobalTheory.IndefiniteRowSideFullHecke.WittDecompositions.detPow a W.rank : ℂ) * R f₀ x₁) := by
      intro a
      have h := congrFun (hK a 1 f₀ hf₀) x₁
      rw [show s a 1 = d.levi a by simp [s], ← Prod.one_eq_mk, map_one, Module.End.one_apply, Pi.smul_apply,
        smul_eq_mul] at h
      rw [h, eq_div_iff (mul_ne_zero (Complex.ofReal_ne_zero.2 (dpos a).ne') hx₁)]
      simp only [K]; rw [← mul_assoc]; rfl
    refine continuous_induced_rng.2 ?_
    change Continuous fun a => ((μa a : Circle) : ℂ)
    simp only [heq]
    exact (hΦ.comp d.continuous_levi).div ((Complex.continuous_ofReal.comp dcont).mul continuous_const)
      fun a => mul_ne_zero (Complex.ofReal_ne_zero.2 (dpos a).ne') hx₁
  ·
    intro a₀
    have h := huniq 1 (K (Matrix.GeneralLinearGroup.map (incA D) a₀) 1) 1 (by
      rw [← hK _ _ f₀ hf₀, one_smul, ← Prod.one_eq_mk, map_one, Module.End.one_apply,
        show s (Matrix.GeneralLinearGroup.map (incA D) a₀) 1 = d.levi (Matrix.GeneralLinearGroup.map (incA D) a₀) by
          simp [s]]
      exact GlobalTheory.T.thetaRestriction_invariant_rationalLeviGL D V V' W r C B hs d hdC hdB ψ χS χT ω hω μ₀ 𝓨₀ h₀ a₀ f₀ hf₀)
    simp only [K] at h
    have hn := congrArg norm h
    rw [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_of_nonneg (dpos _).le, norm_one] at hn
    rw [hn, Complex.ofReal_one, mul_one] at h
    exact Circle.coe_inj.1 (by rw [Circle.coe_one]; exact h)
  ·
    refine continuous_induced_rng.2 ?_
    change Continuous fun g => ((ξ g : Circle) : ℂ)
    rw [continuous_iff_continuousAt]
    intro g₀
    have hw : ω' (g₀, 1) (R f₀) ≠ 0 := fun h0 => hne (hinj g₀ _ h0)
    obtain ⟨x₁, hx₁⟩ := Function.ne_iff.1 hw
    have hΦ := (GlobalTheory.T.continuous_restrictedWeilFirstFactor_apply D V V' W r C B ψ χS χT ω hω μ₀ 𝓨₀ h₀ f₀ hf₀ x₁).comp d.continuous_embed
    have hΨ : Continuous fun g : GA D V' => ω' (g, 1) (R f₀) x₁ :=
      (hω'.om_cont (R f₀) hRth x₁).comp (continuous_id.prodMk continuous_const)
    have heq : ∀ g, ω' (g, 1) (R f₀) x₁ ≠ 0 → ((ξ g : Circle) : ℂ) =
        R (ω (d.emb0 g, 1) f₀) x₁ / ω' (g, 1) (R f₀) x₁ := by
      intro g hg
      have h := congrFun (hK 1 g f₀ hf₀) x₁
      rw [show s 1 g = d.emb0 g by simp [s], Pi.smul_apply, smul_eq_mul] at h
      rw [h, eq_div_iff hg]
      simp only [K, d1, Complex.ofReal_one, mul_one]; rfl
    have hq : ContinuousAt (fun g => R (ω (d.emb0 g, 1) f₀) x₁ / ω' (g, 1) (R f₀) x₁) g₀ :=
      hΦ.continuousAt.div hΨ.continuousAt hx₁
    exact hq.congr ((hΨ.continuousAt.eventually_ne hx₁).mono fun g hg => (heq g hg).symm)
  ·
    intro γ hγ
    have h := huniq γ (K 1 γ) 1 (by
      rw [← hK _ _ f₀ hf₀, one_smul, show s 1 γ = d.emb0 γ by simp [s]]
      exact GlobalTheory.T.rational_unitary_acts_on_thetaRestriction_smaller D V V' W r C B hs d hdC hdB ψ χS χT ω hω χS' χT' ω' hω' μ₀ 𝓨₀ h₀ γ hγ f₀ hf₀)
    simp only [K, d1, Complex.ofReal_one, mul_one] at h
    exact Circle.coe_inj.1 (by rw [Circle.coe_one]; exact h)
  ·
    intro μ 𝓨 hμ a g' m h1 h2 f hf
    obtain ⟨n, hn⟩ : ∃ n, n = (s a g')⁻¹ * m := ⟨_, rfl⟩
    have hmn : s a g' * n = m := by rw [hn, mul_inv_cancel_left]
    have hnC : HMul.hMul (mt V n) (C.map (incA D)) = C.map (incA D) := by
      rw [hn, mt_mul, Matrix.mul_assoc, h1, ← hsC a g', ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    have hnB : HMul.hMul (mt V n) (B.map (incA D)) = B.map (incA D) := by
      rw [hn, mt_mul, Matrix.mul_assoc, h2, ← hsB a g', ← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
    have hnI : n ∈ NI V C := hker n hnC hnB
    have hnf := hω.om_pres (n, 1) f hf
    have key : ω (m, 1) f = ω (s a g', 1) (ω (n, 1) f) := by
      rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, hmn]
    have hk : R (ω (n, 1) f) = R f := GlobalTheory.T.wittTower_restriction_unipotentRadical_invariant D V V' W r C B hs ψ χS χT ω hω μ₀ 𝓨₀ h₀ ⟨n, hnI⟩ f hf
    rw [hind _ (hω.om_pres _ f hf) μ 𝓨 hμ, hind f hf μ 𝓨 hμ, key, hK a g' _ hnf, hk]
    simp only [K, csplit, Circle.coe_mul]
    congr 1
    ring

end GlobalTheory.LeviChar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LieAlgebrasAtPlaceActFockVectorsByFockOperators
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec
open GlobalTheory.ChainFr (Fr ptF IsVacF)

noncomputable section

namespace GlobalTheory.ArchRec.LieAtPlace

variable {D : D7}

open scoped ComplexOrder in

theorem cart_isCartanInv {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) (A.cart τ) := by
  have h1 : A.fr τ * (A.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ))
  have h2 : (A.fr τ)⁻¹ * A.fr τ = 1 := mul_eq_one_comm.1 h1
  have hJ := Formalism.REAL.Jm_mul_self (A.ε τ)
  have hJ' := Formalism.REAL.Jm_conjTranspose (A.ε τ)
  have hG : gramAt D V τ * A.cart τ = (A.fr τ)ᴴ * A.fr τ := by
    rw [← A.fr_gram τ]; unfold Fr.cart
    calc _ = (A.fr τ)ᴴ * (Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one]
  have hs : A.cart τ * A.cart τ = 1 := by
    unfold Fr.cart
    calc _ = (A.fr τ)⁻¹ * (Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one, h2]
  refine ⟨hs, ?_, ?_⟩
  · have hGh : (gramAt D V τ)ᴴ = gramAt D V τ := by
      rw [← A.fr_gram τ]; simp [Matrix.conjTranspose_mul, hJ', Matrix.mul_assoc]
    have h3 : (A.cart τ)ᴴ * gramAt D V τ = gramAt D V τ * A.cart τ := by
      have := congrArg Matrix.conjTranspose hG
      rw [Matrix.conjTranspose_mul, hGh, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at this
      rw [this, hG]
    rw [h3, Matrix.mul_assoc, hs, Matrix.mul_one]
  · rw [hG]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit (A.fr_unit τ))

theorem exists_fr {V : HSp D} {τ : D.what₂.Tau} {s fr : Mn V.rank} {ε : Fin V.rank → Bool}
    (h : IsFrameOf (gramAt D V τ) s ε fr) : ∃ A : Fr V, A.ε τ = ε ∧ A.fr τ = fr ∧ A.cart τ = s := by
  classical
  obtain ⟨A⟩ := (GlobalTheory.FrameExists.frame_exists_signCompat D V).1
  refine ⟨⟨Function.update A.ε τ ε, Function.update A.fr τ fr, fun ρ => ?_, fun ρ => ?_⟩, by simp, by simp, ?_⟩
  · by_cases e : ρ = τ
    · subst e; rw [Function.update_self]; exact h.1
    · rw [Function.update_of_ne e]; exact A.fr_unit ρ
  · by_cases e : ρ = τ
    · subst e; rw [Function.update_self, Function.update_self]; exact h.2.1
    · rw [Function.update_of_ne e, Function.update_of_ne e]; exact A.fr_gram ρ
  · simp [Fr.cart, h.2.2]

theorem pure_rename {ι κ X : Type} {A : ι → (X → ℂ) → (X → ℂ)} {A' : κ → (X → ℂ) → (X → ℂ)} {g : X → ℂ}
    (hX : ∀ v Q, pureTensorL A g (MvPolynomial.X v * Q) = A v (pureTensorL A g Q))
    (hX' : ∀ v Q, pureTensorL A' g (MvPolynomial.X v * Q) = A' v (pureTensorL A' g Q))
    (e : κ → ι) (h : ∀ k, A (e k) = A' k) (Q : MvPolynomial κ ℂ) :
    pureTensorL A g (MvPolynomial.rename e Q) = pureTensorL A' g Q := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.rename_C, ← mul_one (MvPolynomial.C a : MvPolynomial ι ℂ),
      ← mul_one (MvPolynomial.C a : MvPolynomial κ ℂ), MvPolynomial.C_mul', MvPolynomial.C_mul', map_smul, map_smul,
      GlobalTheory.FockIndep.pure_one, GlobalTheory.FockIndep.pure_one]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    rw [mul_comm, map_mul (MvPolynomial.rename e), MvPolynomial.rename_X, hX, hX', hp, h]

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}

theorem ptF_rename (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (A : Fr S) (B : Fr T) (τ : D.what₂.Tau)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (P : LPol T.rank S.rank) :
    ptF ψ θ A B f (MvPolynomial.rename (fun s => (τ, s)) P) =
      ptAt ψ θ S T τ (A.cart τ) (B.cart τ) (A.fr τ)⁻¹ (B.fr τ)⁻¹ f P := by
  have hS := cart_isCartanInv A
  have hT := cart_isCartanInv B
  refine pure_rename (fun v Q => ?_) (fun v Q => ?_) _ (fun k => rfl) P
  · refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ i.1 _ hS hT j.1 _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h
  · refine GlobalTheory.FockIndep.pure_X_mul (P := IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add)
      (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) (fun _ _ h => GlobalTheory.FockIndep.aPlus_theta hψ hθ _ _ _ h) ?_ ?_ ?_ hf Q v
    · exact fun i j _ h => GlobalTheory.FockIndep.aPlus_comm' hψ hθ τ _ hS hT τ _ h
    · exact fun _ _ _ h h' => GlobalTheory.FockIndep.aPlus_add hψ hθ _ _ _ h h'
    · exact fun _ a _ h => GlobalTheory.FockIndep.aPlus_smul hψ hθ _ _ _ a h

theorem ins_one {a b : ℕ} (τ : D.what₂.Tau) (p : LPol b a) :
    GlobalTheory.Chain.RealIt.GlueProof.ins τ (fun _ => 1) p = (MvPolynomial.rename (fun s => (τ, s)) p : PolF D b a) := by
  rw [GlobalTheory.Chain.RealIt.GlueProof.ins_apply]
  simp [GlobalTheory.Chain.RealIt.GlueProof.rest]

theorem derAll_of_one (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) {τ : D.what₂.Tau}
    {sS frS : Mn S.rank} {εS : Fin S.rank → Bool} {sT frT : Mn T.rank} {εT : Fin T.rank → Bool}
    (hS : IsFrameOf (gramAt D S τ) sS εS frS) (hT : IsFrameOf (gramAt D T τ) sT εT frT)
    {ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} {γ : ℝ → GA D S × GA D T} (hγ : QuadGen ψ θ τ ω γ)
    {f₀ : WO S T → ℂ} (h0 : IsThetaFunO ψ S T f₀) (v0 : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f₀) (n0 : f₀ ≠ 0)
    {P P' : LPol T.rank S.rank}
    (hd : ∀ z, HasDerivAt (fun t : ℝ => ω (γ t) (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f₀ P) z)
      (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f₀ P' z) 0)
    {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) (hv : IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f) :
    DerAll ψ ω γ (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f P) (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f P') := by
  obtain ⟨k, c, z, z', lam, hq⟩ := hγ
  choose L hL using GlobalTheory.T.exists_fockPolynomial_operator_heisenberg_derivative D ψ θ S T τ hψ hθ sS frS εS sT frT εT hS hT
  have hc := GlobalTheory.T.fockVectors_at_one_realPlace_over_vacuum D ψ θ S T τ hψ hθ sS frS εS sT frT εT hS hT
  have key : ∀ g, IsThetaFunO ψ S T g → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) g →
      DerAll ψ ω γ (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g P)
        (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g ((∑ i, c i • L (z i) (L (z' i) P)) + lam • P)) := fun g hg vg => by
    have h := hq _ ((hc g hg vg).1 P)
    simp only [hL _ g hg vg] at h
    have e : ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g ((∑ i, c i • L (z i) (L (z' i) P)) + lam • P) =
        (∑ i, c i • ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g (L (z i) (L (z' i) P))) +
          lam • ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ g P := by
      simp only [ptAt, map_add, map_sum, map_smul]
    rw [e]
    exact h
  have e : P' = (∑ i, c i • L (z i) (L (z' i) P)) + lam • P := by
    refine ((hc f₀ h0 v0).2 n0).1 (funext fun w => (hd w).unique ?_)
    simpa using (key f₀ h0 v0).1 1 w
  rw [e]
  exact key f hf hv

theorem lieAt_of_vacAt : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → IsWeilDatumO ψ S T χS χT ω → ∀ aS aT : ℚ, HasInfExp D χS τ aS → HasInfExp D χT τ aT → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ f, IsThetaFunO ψ S T f → IsFockVacAt (heisO ψ S T) θ τ (cplxO sS sT) f → LieAt ψ θ τ ω εS frS εT frT aS aT (ptAt ψ θ S T τ sS sT frS⁻¹ frT⁻¹ f) := by
  intro D ψ θ S T χS χT ω τ hθ hW aS aT haS haT sS frS εS sT frT εT hS hT f hf hv
  have hψ := hW.std
  obtain ⟨A, rfl, rfl, rfl⟩ := exists_fr hS
  obtain ⟨B, rfl, rfl, rfl⟩ := exists_fr hT
  obtain ⟨f₀, h0, n0⟩ := GlobalTheory.IndefiniteRowSideFullHecke.BoundedCommutantVacua.exists_isVac_ne_zero hψ hθ (cart_isCartanInv A) (cart_isCartanInv B)
  have hl := GlobalTheory.T.lieAction_fockOperators_scalars_trace D S T A B θ ψ χS χT ω f₀ τ aS aT hθ hW haS haT h0
  have hg := GlobalTheory.T.weilGenerator_quadratic_oneParameter_at_place D ψ θ S T χS χT ω τ hθ hW
  refine ⟨fun X hX P => ?_, fun Y hY P => ?_⟩
  · refine derAll_of_one hψ hθ hS hT (hg.1 X hX) h0.1 (h0.2 τ) n0 (fun z => ?_) hf hv
    have h := hl.1 X hX (MvPolynomial.rename (fun s => (τ, s)) P) z
    rw [← ins_one, GlobalTheory.Chain.RealIt.GlueProof.fockS_ins, ← map_smul, ← map_add, ins_one, ins_one,
      ptF_rename hψ hθ A B τ h0.1, ptF_rename hψ hθ A B τ h0.1, neg_smul, ← sub_eq_add_neg] at h
    exact h
  · refine derAll_of_one hψ hθ hS hT (hg.2 Y hY) h0.1 (h0.2 τ) n0 (fun z => ?_) hf hv
    have h := hl.2 Y hY (MvPolynomial.rename (fun s => (τ, s)) P) z
    rw [← ins_one, GlobalTheory.Chain.RealIt.GlueProof.fockT_ins, ← map_smul, ← map_add, ins_one, ins_one,
      ptF_rename hψ hθ A B τ h0.1, ptF_rename hψ hθ A B τ h0.1] at h
    exact h

end GlobalTheory.ArchRec.LieAtPlace

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedCoordinatePoincareSumHalfWittEqBumpStatement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedCoordinate_poincareSum_halfWitt_eq_bump : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (v : VolM D T.rank ρ) (β : Mx D T.rank ρ → ℂ), IsBump β → ∀ x, d.mixS T ψ v.μ v.𝓕 (poinX ψ d T β) x 0 = β x := by
  first | exact @GlobalTheory.BumpMixSum.mixS_poinX | exact GlobalTheory.BumpMixSum.mixS_poinX | (intros; apply GlobalTheory.BumpMixSum.mixS_poinX <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelTermsRationalUnipotentInvariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelTerms_rationalUnipotent_invariant : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → adj D C * V.gram * C' = 1 → adj D C' * V.gram * C' = 0 → adj D C' * V.gram * B = 0 → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ n ∈ NI V C, n ∈ GQ V → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) (ω (n, 1) f)) 0 = res V V' W C B μ 𝓨 (heisO ψ V W (isoPart V W C' (Matrix.map y (incA D))) f) 0 := by
  first | exact @GlobalTheory.UnipMixed.res_heisO_unip | exact GlobalTheory.UnipMixed.res_heisO_unip | (intros; apply GlobalTheory.UnipMixed.res_heisO_unip <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrientedPairFockMapsLieEquivariantStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orientedPair_fockMaps_lie_equivariant : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsInfFam θ →
  ∀ (ε : Bool) (M X : HSp D) (A : Fr M) (B : Fr X) (χS χT : (AE D)ˣ →* Circle) (ω : WRep M X) (eS eT : D.what₂.Tau → ℚ),
  IsWeil ψ ε M X χS χT ω → (∀ τ, HasInfExp D χS τ (eS τ) ∧ HasInfExp D χT τ (eT τ)) →
  ∀ (Pi : ModuleCat.{0} ℂ) (rf : GA D X → Module.End ℂ Pi) (rl : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pi)
    (p : (WO M X → ℂ) →ₗ[ℂ] Pi), IsCoinvMap θ ω (algF ψ θ ε A B) Pi rf rl p →
  (∀ f, IsFinF ψ θ ε A B f → ∀ τ, ∀ Y ∈ lieAt X τ, ∀ P,
      p (fockF ψ θ ε A B f (GlobalTheory.RealQuot.actT ε A B eS τ Y P)) = rl τ Y (p (fockF ψ θ ε A B f P))) ∧
  (∀ f, IsFinF ψ θ ε A B f → ∀ P ∈ GlobalTheory.RealQuot.coinv ε A B eT, p (fockF ψ θ ε A B f P) = 0) ∧
  ∀ h ∈ GfC X, ∀ f, IsFinF ψ θ ε A B f → ∃ f', IsFinF ψ θ ε A B f' ∧
    ∀ P, rf h (p (fockF ψ θ ε A B f P)) = p (fockF ψ θ ε A B f' P) := by
  first | exact @GlobalTheory.RealQuot.oriented_maps | exact GlobalTheory.RealQuot.oriented_maps | (intros; apply GlobalTheory.RealQuot.oriented_maps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSeriesUnitaryAbsolutelyConvergentModeratStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.Grow
open GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup (coefPlus Cols SizeRows)
open GlobalTheory.ChainFr GlobalTheory.SepRows GlobalTheory.SepPer Matrix
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareSeries_unitary_absolutelyConvergent_moderateGrowth : ∀ (D : D7) (θ : InfFam D), IsInfFam θ → ∀ (V : HSp D) (Λ : Lat V), IsSelfDualC V Λ → ∀ c : GA D V, ∃ (C : ℝ) (A : ℕ), ∀ (g : GA D V) (s : Finset (GQ V)), (∀ γ ∈ s, Lev.finE V (c * (γ : GA D V) * g) ∈ congLev D.sp.cm V.gram Λ ⊤) → ∑ γ ∈ s, ∏ τ, ((1 + hsn (GlobalTheory.SepPer.cmp θ τ (c * (γ : GA D V) * g))) ^ (2 * V.rank ^ 2 + 1))⁻¹ ≤ C * height V g ^ A := by
  first | exact @GlobalTheory.PoinCount.poincare_count | exact GlobalTheory.PoinCount.poincare_count | (intros; apply GlobalTheory.PoinCount.poincare_count <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.PoincareSumHalfWittHeisenbergLevelOfZeroCoreStatement
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
open GlobalTheory.BumpMix

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareSumHalfWitt_heisenberg_level_of_zero_core : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), S₀.rank = 0 → ∀ (β : Mx D T.rank ρ → ℂ), IsBump β → ∃ U : AddSubgroup (WO S T), IsOpen (U : Set (WO S T)) ∧ ∀ u ∈ U, u.map (infPart D) = 0 → heisO ψ S T u (poinX ψ d T β) = poinX ψ d T β := by
  first | exact @GlobalTheory.BumpMixLevel.poinX_heis_level | exact GlobalTheory.BumpMixLevel.poinX_heis_level | (intros; apply GlobalTheory.BumpMixLevel.poinX_heis_level <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankPolynomialFockSchrodingerModelLeAleph0Statement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_polynomialFock_schrodingerModel_le_aleph0 : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d r s r' s' : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}
    (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → M.IsGood B.ψ →
    Module.rank ℂ (M.Pol B.ψ B.emb) ≤ Cardinal.aleph0 := by
  first | exact @GlobalTheory.FockCount.rank_pol_le_aleph0 | exact GlobalTheory.FockCount.rank_pol_le_aleph0 | (intros; apply GlobalTheory.FockCount.rank_pol_le_aleph0 <;> assumption)
end

