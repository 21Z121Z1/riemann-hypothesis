import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1549
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0273
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1573
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0887
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1563
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsHolFormConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1540

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordsRealFamilyArchimedeanLinear
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField MeasureTheory
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix Formalism.IndefR.Datum
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.RealDirCoord

theorem continuous_ringEquiv_mixed (F : Type) [Field F] [NumberField F] :
    Continuous (InfiniteAdeleRing.ringEquiv_mixedSpace F) := by
  refine Continuous.prodMk (continuous_pi fun v => ?_) (continuous_pi fun v => ?_)
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal v.2).continuous.comp
      (continuous_apply _)
  · exact (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v.1).continuous.comp
      (continuous_apply _)

theorem eps_smul_gen {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
    (z : AF F ⊗[F] E) :
    (pairA F 0 1) • z = LinearMap.rTensor E (LinearMap.inr F (Ainf F) (Af F))
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp; rfl
  | tmul a x =>
    rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
    congr 1
    show ((0 : Ainf F) * a.1, (1 : Af F) * a.2) = ((0 : Ainf F), a.2)
    simp
  | add a b ha hb => rw [smul_add, ha, hb, map_add, map_add]; rfl

theorem eps_smul_eq (D : D7) (z : AE D) :
    (pairA D.host.F 0 1) • z =
      LinearMap.rTensor D.host.E (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) (finPart D z) :=
  eps_smul_gen z

theorem eps_mul_snd {F : Type} [Field F] [NumberField F] (x : AF F) :
    (pairA F 0 1 * x).2 = x.2 := one_mul x.2

theorem darboux_real_coords : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ] (e : Formalism.IndefR.Datum.WO S T ≃ₗ[AF D.host.F] (κ → AF D.host.F) × (κ → AF D.host.F)) (k : ℕ) (L : (Fin k → ℝ) →+ Formalism.IndefR.Datum.WO S T), Continuous L → (∀ t, (L t).map (finPart D) = 0) → ∃ P Q : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace D.host.F), ∀ t, e (L t) = (fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (P t i)) 0, fun i => pairA D.host.F ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (Q t i)) 0) := by
  intro D S T κ _ e k L hL hfin

  have hε : ∀ t, (pairA D.host.F 0 1) • L t = 0 := by
    intro t
    ext i j
    have h0 : finPart D (L t i j) = 0 := congrFun (congrFun (hfin t) i) j
    rw [Matrix.smul_apply, eps_smul_eq, h0, LinearMap.map_zero]
    rfl
  have hsnd : ∀ t i, ((e (L t)).1 i).2 = 0 ∧ ((e (L t)).2 i).2 = 0 := by
    intro t i
    have h := congrArg e (hε t)
    rw [LinearEquiv.map_smul, LinearEquiv.map_zero] at h
    have h1 := congrArg Prod.snd (congrFun (congrArg Prod.fst h) i)
    have h2 := congrArg Prod.snd (congrFun (congrArg Prod.snd h) i)
    exact ⟨(eps_mul_snd _).symm.trans h1, (eps_mul_snd _).symm.trans h2⟩

  have he : Continuous e := by
    haveI : IsModuleTopology (AF D.host.F) (AE D) := ⟨rfl⟩
    haveI : IsModuleTopology (AF D.host.F) (Formalism.IndefR.Datum.WO S T) :=
      inferInstanceAs (IsModuleTopology (AF D.host.F) (Fin _ → Fin _ → AE D))
    exact IsModuleTopology.continuous_of_linearMap e.toLinearMap
  have hc : ∀ (p : ((κ → AF D.host.F) × (κ → AF D.host.F)) → (κ → AF D.host.F)), Continuous p →
      (∀ x y, p (x + y) = p x + p y) →
      ∃ P : (Fin k → ℝ) →L[ℝ] (κ → mixedEmbedding.mixedSpace D.host.F),
        ∀ t i, P t i = InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (p (e (L t)) i).1 := by
    intro p hp hadd
    let f : (Fin k → ℝ) →+ (κ → mixedEmbedding.mixedSpace D.host.F) :=
      { toFun := fun t i => InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F (p (e (L t)) i).1
        map_zero' := by
          funext i
          have h0 : p 0 = 0 := by simpa using hadd 0 0
          rw [map_zero, LinearEquiv.map_zero, h0]
          exact map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F)
        map_add' := by
          intro a b
          funext i
          rw [map_add, LinearEquiv.map_add, hadd]
          exact map_add (InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F) _ _ }
    have hf : Continuous f := by
      refine continuous_pi fun i => ?_
      exact (continuous_ringEquiv_mixed D.host.F).comp
        (continuous_fst.comp ((continuous_apply i).comp (hp.comp (he.comp hL))))
    exact ⟨f.toRealLinearMap hf, fun t i => rfl⟩
  obtain ⟨P, hP⟩ := hc Prod.fst continuous_fst (fun _ _ => rfl)
  obtain ⟨Q, hQ⟩ := hc Prod.snd continuous_snd (fun _ _ => rfl)
  refine ⟨P, Q, fun t => ?_⟩
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · show (e (L t)).1 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (P t i), 0)
    rw [hP, RingEquiv.symm_apply_apply]
    exact Prod.ext rfl (hsnd t i).1
  · show (e (L t)).2 i = ((InfiniteAdeleRing.ringEquiv_mixedSpace D.host.F).symm (Q t i), 0)
    rw [hQ, RingEquiv.symm_apply_apply]
    exact Prod.ext rfl (hsnd t i).2

end GlobalTheory.RealDirCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarAngleFormReEq
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CurveDens

theorem angleForm_alg (n : ℕ) (q P D H β β' L L' : ℂ) (a a' : ℝ) (ha : 0 < a) (ha' : 0 < a')
    (Qi dQi dv R dR : ℂ)
    (hQi : Qi = (((a * a')⁻¹ : ℝ) : ℂ))
    (hdQi : dQi = (((-((a * a') ^ 2)⁻¹ : ℝ) : ℂ)) *
      ((a : ℂ) * ((a' : ℂ) * starRingEnd ℂ β') + (a : ℂ) * starRingEnd ℂ β * (a' : ℂ)))
    (hdv : dv = q * starRingEnd ℂ q * dQi + (q * starRingEnd ℂ P + D * starRingEnd ℂ q) * Qi)
    (hR : R = starRingEnd ℂ q * (P - q * β') - q * (starRingEnd ℂ D - starRingEnd ℂ q * β))
    (hdR : dR = (starRingEnd ℂ q * (H - (q * L' + D * β')) + starRingEnd ℂ P * (P - q * β')) -
          (q * (starRingEnd ℂ H - (starRingEnd ℂ q * L + starRingEnd ℂ P * β)) +
            D * (starRingEnd ℂ D - starRingEnd ℂ q * β))) :
    ((((‖q‖ ^ 2 / (a * a')) ^ n : ℝ) : ℂ) * (R * dQi + dR * Qi) +
      (((n : ℝ) * (‖q‖ ^ 2 / (a * a')) ^ (n - 1) : ℝ) : ℂ) * dv * (R * Qi)).re =
    (n + 1) * (‖q‖ ^ 2 / (a * a')) ^ n * ((‖P - q * β'‖ ^ 2 - ‖D - q * starRingEnd ℂ β‖ ^ 2) / (a * a')) +
      (‖q‖ ^ 2 / (a * a')) ^ (n + 1) * (L.re - L'.re) := by
  subst hQi hdQi hdv hR hdR
  have hQ : (0:ℝ) < a * a' := mul_pos ha ha'
  have ha0 : a ≠ 0 := ha.ne'
  have ha0' : a' ≠ 0 := ha'.ne'
  obtain ⟨K, m, hK, hn⟩ : ∃ K m, K = (‖q‖ ^ 2 / (a * a')) ^ m ∧
      ((‖q‖ ^ 2 / (a * a')) ^ n = K * (‖q‖ ^ 2 / (a * a')) ∧
        ((n : ℝ) * (‖q‖ ^ 2 / (a * a')) ^ (n - 1)) = n * K ∧ (n:ℝ) ≠ 0 ∨
       (‖q‖ ^ 2 / (a * a')) ^ n = 1 ∧ ((n : ℝ) * (‖q‖ ^ 2 / (a * a')) ^ (n - 1)) = 0 ∧ n = 0) := by
    rcases n with _ | m
    · exact ⟨1, 0, by simp, Or.inr ⟨by simp, by simp, rfl⟩⟩
    · refine ⟨_, m, rfl, Or.inl ⟨pow_succ _ _, by simp, by positivity⟩⟩
  have hpow : (‖q‖ ^ 2 / (a * a')) ^ (n + 1) = (‖q‖ ^ 2 / (a * a')) ^ n * (‖q‖ ^ 2 / (a * a')) := pow_succ _ _
  rw [hpow]
  rcases hn with ⟨h1, h2, -⟩ | ⟨h1, h2, rfl⟩
  · rw [h1, h2]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
    field_simp
    ring
  · rw [h1]
    simp only [Nat.cast_zero, zero_mul, Complex.ofReal_zero, add_zero, zero_add, one_mul,
      Complex.ofReal_one]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
    field_simp
    ring

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E]

theorem differentiableAt_del_apply_of_contDiffAt_two {f : E → ℂ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (w : E) : DifferentiableAt ℝ (fun x => del f x w) z := by
  have h := differentiableAt_fderiv_of_contDiffAt_two hf
  simp only [del_apply]
  exact ((h.clm_apply (differentiableAt_const _)).sub
    ((h.clm_apply (differentiableAt_const _)).const_smul Complex.I)).const_smul (1 / 2 : ℂ)

theorem re_dbar_angleForm (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] (n : ℕ) (a a' : E → ℝ) (q : E → ℂ) (ξ z : E)
    (ha : ContDiffAt ℝ 2 a z) (ha' : ContDiffAt ℝ 2 a' z) (hq : ContDiffAt ℝ 2 q z)
    (h0 : 0 < a z) (h0' : 0 < a' z) :
    (dbar (angleForm n a a' q ξ) z ξ).re = (n + 1) * (‖q z‖ ^ 2 / (a z * a' z)) ^ n *
      ((‖del q z ξ - q z * del (fun x => (Real.log (a' x) : ℂ)) z ξ‖ ^ 2 -
        ‖dbar q z ξ - q z * dbar (fun x => (Real.log (a x) : ℂ)) z ξ‖ ^ 2) / (a z * a' z)) +
      (‖q z‖ ^ 2 / (a z * a' z)) ^ (n + 1) *
        ((leviForm (fun x => Real.log (a x)) z ξ ξ).re -
          (leviForm (fun x => Real.log (a' x)) z ξ ξ).re) := by
  have hq1 : DifferentiableAt ℝ q z := hq.differentiableAt (by norm_num)
  have ha1 : DifferentiableAt ℝ a z := ha.differentiableAt (by norm_num)
  have ha1' : DifferentiableAt ℝ a' z := ha'.differentiableAt (by norm_num)
  have hαC : ContDiffAt ℝ 2 (fun x => (Real.log (a x) : ℂ)) z :=
    contDiffAt_ofReal_comp (ha.log h0.ne')
  have hαC' : ContDiffAt ℝ 2 (fun x => (Real.log (a' x) : ℂ)) z :=
    contDiffAt_ofReal_comp (ha'.log h0'.ne')
  have hqc : ContDiffAt ℝ 2 (fun x => starRingEnd ℂ (q x)) z :=
    (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.contDiffAt.comp z hq
  have dP := differentiableAt_del_apply_of_contDiffAt_two hq ξ
  have dPt := differentiableAt_del_apply_of_contDiffAt_two hqc ξ
  have dB := differentiableAt_del_apply_of_contDiffAt_two hαC ξ
  have dB' := differentiableAt_del_apply_of_contDiffAt_two hαC' ξ
  have dqc : DifferentiableAt ℝ (fun x => starRingEnd ℂ (q x)) z := hqc.differentiableAt (by norm_num)
  have daC : DifferentiableAt ℝ (fun x => (a x : ℂ)) z :=
    (contDiffAt_ofReal_comp ha).differentiableAt (by norm_num)
  have daC' : DifferentiableAt ℝ (fun x => (a' x : ℂ)) z :=
    (contDiffAt_ofReal_comp ha').differentiableAt (by norm_num)
  have hQ1 : DifferentiableAt ℝ (fun x => a x * a' x) z := ha1.mul ha1'
  have hQ0 : a z * a' z ≠ 0 := (mul_pos h0 h0').ne'
  have hv1 : DifferentiableAt ℝ (fun x => ‖q x‖ ^ 2 / (a x * a' x)) z :=
    ((hq1.norm_sq (𝕜 := ℂ)).mul (hQ1.inv hQ0)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun x => by simp only [div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply])
  have dQi : DifferentiableAt ℝ (fun x => (((a x * a' x)⁻¹ : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z (hQ1.inv hQ0)
  have dW : DifferentiableAt ℝ (fun x => (((‖q x‖ ^ 2 / (a x * a' x)) ^ n : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.differentiableAt.comp z (hv1.pow n)
  have dR : DifferentiableAt ℝ (fun x => starRingEnd ℂ (q x) *
      (del q x ξ - q x * del (fun y => (Real.log (a' y) : ℂ)) x ξ) -
      q x * (del (fun y => starRingEnd ℂ (q y)) x ξ -
        starRingEnd ℂ (q x) * del (fun y => (Real.log (a y) : ℂ)) x ξ)) z :=
    (dqc.mul (dP.sub (hq1.mul dB'))).sub (hq1.mul (dPt.sub (dqc.mul dB)))
  have hG : angleForm n a a' q ξ = fun x =>
      (((‖q x‖ ^ 2 / (a x * a' x)) ^ n : ℝ) : ℂ) *
        ((starRingEnd ℂ (q x) * (del q x ξ - q x * del (fun y => (Real.log (a' y) : ℂ)) x ξ) -
            q x * (del (fun y => starRingEnd ℂ (q y)) x ξ -
              starRingEnd ℂ (q x) * del (fun y => (Real.log (a y) : ℂ)) x ξ)) *
          (((a x * a' x)⁻¹ : ℝ) : ℂ)) := by
    funext x
    rw [angleForm, map_sub, map_mul, dbar_ofReal (fun y => Real.log (a y)), Complex.conj_conj,
      ← del_conj]
    push_cast
    ring
  rw [dbar_ofReal (fun x => Real.log (a x)) z ξ, hG, dbar_mul dW (dR.fun_mul dQi) ξ, dbar_mul dR dQi ξ]
  beta_reduce
  have hW := dbar_ofReal_comp (h := fun s : ℝ => s ^ n) (hasDerivAt_pow n _) hv1 ξ
  beta_reduce at hW
  rw [hW, del_conj q z ξ]
  refine angleForm_alg n (q z) (del q z ξ) (dbar q z ξ) (ddbar q z ξ ξ)
    (del (fun x => (Real.log (a x) : ℂ)) z ξ) (del (fun x => (Real.log (a' x) : ℂ)) z ξ)
    (leviForm (fun x => Real.log (a x)) z ξ ξ) (leviForm (fun x => Real.log (a' x)) z ξ ξ)
    (a z) (a' z) h0 h0' _ _ _ _ _ rfl ?_ ?_ rfl ?_
  · have h1 := dbar_ofReal_comp (t := fun x => a x * a' x) (h := fun s : ℝ => s⁻¹)
      (hasDerivAt_inv (x := a z * a' z) hQ0) hQ1 ξ
    beta_reduce at h1
    have h2 : (fun x => ((a x * a' x : ℝ) : ℂ)) = fun x => (a x : ℂ) * (a' x : ℂ) := by
      funext x; push_cast; rfl
    have hda := dbar_ofReal_comp (h := Real.log) (Real.hasDerivAt_log h0.ne') ha1 ξ
    have hda' := dbar_ofReal_comp (h := Real.log) (Real.hasDerivAt_log h0'.ne') ha1' ξ
    rw [dbar_ofReal] at hda hda'
    have hz : (a z : ℂ) ≠ 0 := by exact_mod_cast h0.ne'
    have hz' : (a' z : ℂ) ≠ 0 := by exact_mod_cast h0'.ne'
    have e1 : dbar (fun x => (a x : ℂ)) z ξ =
        (a z : ℂ) * starRingEnd ℂ (del (fun x => (Real.log (a x) : ℂ)) z ξ) := by
      rw [hda]; push_cast; field_simp
    have e2 : dbar (fun x => (a' x : ℂ)) z ξ =
        (a' z : ℂ) * starRingEnd ℂ (del (fun x => (Real.log (a' x) : ℂ)) z ξ) := by
      rw [hda']; push_cast; field_simp
    rw [h1, h2, dbar_mul daC daC' ξ, e1, e2]
  · have h3 : (fun x => ((‖q x‖ ^ 2 / (a x * a' x) : ℝ) : ℂ)) =
        fun x => q x * starRingEnd ℂ (q x) * (((a x * a' x)⁻¹ : ℝ) : ℂ) := by
      funext x; rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
    rw [h3, dbar_mul (hq1.fun_mul dqc) dQi ξ, dbar_mul hq1 dqc ξ, dbar_conj]
  · rw [dbar_sub (dqc.fun_mul (dP.fun_sub (hq1.fun_mul dB')))
        (hq1.fun_mul (dPt.fun_sub (dqc.fun_mul dB))),
      ContinuousLinearMap.sub_apply, dbar_mul dqc (dP.fun_sub (hq1.fun_mul dB')) ξ,
      dbar_mul hq1 (dPt.fun_sub (dqc.fun_mul dB)) ξ,
      dbar_sub dP (hq1.fun_mul dB'), dbar_sub dPt (dqc.fun_mul dB),
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.sub_apply,
      dbar_mul hq1 dB' ξ, dbar_mul dqc dB ξ, dbar_conj,
      ← ddbar_eq_dbar_del hq, ← ddbar_eq_dbar_del hqc, ← ddbar_eq_dbar_del hαC,
      ← ddbar_eq_dbar_del hαC', ddbar_conj hq, del_conj q z ξ]
    rfl

end GlobalTheory.CurveDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarCompHolomorphic
section
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.CxForm

theorem sum_dbar_comp_smul_dzb {n m : ℕ} {φ : V n → V m} {c : V m → ℂ} {v : V n}
    (hφ : DifferentiableAt ℂ φ v) (hc : DifferentiableAt ℝ c (φ v)) :
    ∑ a, GlobalTheory.dbar (fun x => c (φ x)) v (coordVec a) • dzb a =
      pull (fderiv ℂ φ v) (∑ b, GlobalTheory.dbar c (φ v) (coordVec b) • dzb b) := by
  have key (w : V m) : GlobalTheory.dbar c (φ v) w = ∑ b, GlobalTheory.dbar c (φ v) (coordVec b) * conj (w b) := by
    have hw : w = ∑ b, w b • coordVec b := by
      simpa using ((EuclideanSpace.basisFun (Fin m) ℂ).sum_repr w).symm
    conv_lhs => rw [hw]
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [map_smulₛₗ, smul_eq_mul, mul_comm]
  rw [map_sum]
  simp only [map_smul, (pull_dz _ _).2, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [GlobalTheory.dbar_comp_holo hc hφ, key, Finset.sum_smul]

end GlobalTheory.CxForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarDensityOfTransition
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CurveDens

theorem clm_single_eq_det_smul (L : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) :
    L (EuclideanSpace.single 0 1) = L.det • EuclideanSpace.single 0 1 := by
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 1) ℂ).toBasis,
    Matrix.det_unique]
  ext i
  simp [LinearMap.toMatrix_apply, Subsingleton.elim i 0]

theorem det_eq_apply_single (L : EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1)) :
    L.det = L (EuclideanSpace.single 0 1) 0 := by
  rw [clm_single_eq_det_smul]; simp

theorem isDens_re_dbar_coeff : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ)
    (m : AlgChart p σ 1 → CxPts p σ → ℂ),
    (∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ContDiffAt ℝ 1 (fun v => m c (c.e.symm v)) (c.e y)) →
    (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
      m c y = ChartGlue.transDet c.e c'.e y * m c' y) →
    IsDens (fun (c : AlgChart p σ 1) (y : CxPts p σ) =>
      (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re) := by
  intro k _ X p σ m hC hT
  refine ⟨fun c c' y hy hy' => ?_, fun c => ?_⟩
  · show (dbar (fun v => m c (c.e.symm v)) (c.e y) (EuclideanSpace.single 0 1)).re =
      ‖ChartGlue.transDet c.e c'.e y‖ ^ 2 *
        (dbar (fun v => m c' (c'.e.symm v)) (c'.e y) (EuclideanSpace.single 0 1)).re
    have ho := ChartGlue.isOpen_over c.e c'.e.open_source
    have hm := ho.mem_nhds (ChartGlue.mem_over c.e hy hy')
    have e₂ : (c'.e ∘ c.e.symm) (c.e y) = c'.e y := congrArg c'.e (c.e.left_inv hy)
    have hτ : DifferentiableAt ℂ (c'.e ∘ c.e.symm) (c.e y) := (c.holo_trans c').differentiableAt hm
    have hτC : ContDiffAt ℂ 2 (c'.e ∘ c.e.symm) (c.e y) :=
      contDiffAt_euclidean.2 fun i =>
        ((ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn 1 _ _ ho
          (differentiableOn_euclidean.1 (c.holo_trans c') i)).contDiffAt hm).of_le (by norm_cast)
    have hdd : DifferentiableAt ℂ (fun v => (fderiv ℂ (c'.e ∘ c.e.symm) v).det) (c.e y) := by
      have h1 : DifferentiableAt ℂ (fderiv ℂ (c'.e ∘ c.e.symm)) (c.e y) :=
        (hτC.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
      have : (fun v => (fderiv ℂ (c'.e ∘ c.e.symm) v).det) =
          fun v => fderiv ℂ (c'.e ∘ c.e.symm) v (EuclideanSpace.single 0 1) 0 :=
        funext fun v => det_eq_apply_single _
      rw [this]
      exact (EuclideanSpace.proj (0 : Fin 1) : EuclideanSpace ℂ (Fin 1) →L[ℂ] ℂ).differentiableAt.comp _
        (h1.clm_apply (differentiableAt_const _))
    have hg : DifferentiableAt ℝ (fun v => m c' (c'.e.symm v)) ((c'.e ∘ c.e.symm) (c.e y)) := by
      rw [e₂]; exact (hC c' y hy').differentiableAt one_ne_zero
    have hgτ : DifferentiableAt ℝ (fun v => m c' (c'.e.symm ((c'.e ∘ c.e.symm) v))) (c.e y) :=
      hg.comp (f := c'.e ∘ c.e.symm) _ (hτ.restrictScalars ℝ)
    have hfe : (fun v => m c (c.e.symm v)) =ᶠ[𝓝 (c.e y)]
        fun v => (fderiv ℂ (c'.e ∘ c.e.symm) v).det * m c' (c'.e.symm ((c'.e ∘ c.e.symm) v)) := by
      filter_upwards [hm] with v hv
      rw [hT c c' _ (c.e.map_target hv.1) hv.2, ChartGlue.transDet, c.e.right_inv hv.1,
        Function.comp_apply, c'.e.left_inv hv.2]
    rw [dbar_congr hfe, dbar_mul (hdd.restrictScalars ℝ) hgτ, dbar_eq_zero hdd,
      ContinuousLinearMap.zero_apply, zero_mul, add_zero,
      dbar_comp_holo (u := fun v => m c' (c'.e.symm v)) hg hτ, clm_single_eq_det_smul,
      ContinuousLinearMap.map_smulₛₗ, e₂, smul_eq_mul, ← mul_assoc, Complex.mul_conj',
      ← Complex.ofReal_pow, Complex.re_ofReal_mul]
    rfl
  · have hcont : ContinuousOn (fun v => (dbar (fun v => m c (c.e.symm v)) v
        (EuclideanSpace.single 0 1)).re) c.e.target := by
      intro v hv
      have h1 := hC c (c.e.symm v) (c.e.map_target hv)
      rw [c.e.right_inv hv] at h1
      have h2 : ContinuousAt (fun w => fderiv ℝ (fun v => m c (c.e.symm v)) w) v :=
        (h1.fderiv_right (m := 0) (by norm_num)).continuousAt
      refine ContinuousAt.continuousWithinAt ?_
      have h3 : (fun w => (dbar (fun v => m c (c.e.symm v)) w (EuclideanSpace.single 0 1)).re) =
          fun w => ((1 / 2 : ℂ) • (fderiv ℝ (fun v => m c (c.e.symm v)) w (EuclideanSpace.single 0 1) +
            Complex.I • fderiv ℝ (fun v => m c (c.e.symm v)) w
              (Complex.I • EuclideanSpace.single 0 1))).re :=
        funext fun w => by rw [dbar_apply]
      rw [h3]
      have h4 : ContinuousAt (fun w => fderiv ℝ (fun v => m c (c.e.symm v)) w
          (EuclideanSpace.single 0 1)) v := h2.clm_apply continuousAt_const
      have h5 : ContinuousAt (fun w => fderiv ℝ (fun v => m c (c.e.symm v)) w
          (Complex.I • EuclideanSpace.single 0 1)) v := h2.clm_apply continuousAt_const
      exact Complex.continuous_re.continuousAt.comp ((h4.add (h5.const_smul Complex.I)).const_smul
        (1 / 2 : ℂ))
    exact hcont.congr fun v hv => by simp only [c.e.right_inv hv]

end GlobalTheory.CurveDens
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarSumLeibniz
section
open Set Filter Topology
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open GlobalTheory.CxForm
open scoped ComplexConjugate ContDiff

namespace GlobalTheory.CxForm

theorem coefwise_dbar_sum_smul {n : ℕ} {ι : Type} [Fintype ι] {c : ι → V n → ℂ} {F : ι → V n → Alt n} {v : V n}
    (hc : ∀ i, DifferentiableAt ℝ (c i) v)
    (hF : ∀ i S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) (w : V n) :
    coefwise (fun f => GlobalTheory.dbar f v w) (fun x => ∑ i, c i x • F i x) =
      ∑ i, (GlobalTheory.dbar (c i) v w • F i v + c i v • coefwise (fun f => GlobalTheory.dbar f v w) (F i)) := by
  have h (S : Finset (Fin (n + n))) :
      GlobalTheory.dbar (fun x => (bas n).repr (∑ i, c i x • F i x) S) v w =
        ∑ i, (c i v * GlobalTheory.dbar (fun x => (bas n).repr (F i x) S) v w +
          GlobalTheory.dbar (c i) v w * (bas n).repr (F i v) S) := by
    have e : (fun x => (bas n).repr (∑ i, c i x • F i x) S) =
        fun x => ∑ i, c i x * (bas n).repr (F i x) S := by
      funext x
      simp [map_sum, Finsupp.finset_sum_apply]
    rw [e, GlobalTheory.dbar_sum (A := fun i x => c i x * (bas n).repr (F i x) S) (fun i _ => (hc i).mul (hF i S)),
      ContinuousLinearMap.sum_apply]
    exact Finset.sum_congr rfl fun i _ => GlobalTheory.dbar_mul (hc i) (hF i S) w
  simp only [coefwise, h, Finset.sum_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [← (bas n).sum_repr (F i v)]
  simp only [add_smul, mul_smul, Finset.sum_add_distrib, Finset.smul_sum]
  rw [add_comm]

theorem dbarAt_sum_smul {n : ℕ} {ι : Type} [Fintype ι] {c : ι → V n → ℂ} {F : ι → V n → Alt n} {v : V n}
    (hc : ∀ i, DifferentiableAt ℝ (c i) v)
    (hF : ∀ i S, DifferentiableAt ℝ (fun x => (bas n).repr (F i x) S) v) :
    dbarAt (fun x => ∑ i, c i x • F i x) v =
      ∑ i, ((∑ a, GlobalTheory.dbar (c i) v (coordVec a) • dzb a) * F i v + c i v • dbarAt (F i) v) := by
  simp only [dbarAt, coefwise_dbar_sum_smul hc hF, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [mul_add, mul_smul_comm, smul_mul_assoc, Finset.sum_mul, Finset.sum_add_distrib, Finset.smul_sum]

end GlobalTheory.CxForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivHeisenbergCMThetaQuasiInvariantRational
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped ContDiff

noncomputable section

namespace GlobalTheory.ThetaDerivQuasi

open Formalism.IndefR.DatumF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem symplOHF_add_left' (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (xi0 : E) (x x' y : WOF F E nS nT) :
    symplOHF σ JS JT xi0 (x + x') y = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x' y := by
  simp only [symplOHF, symplOF, hOF, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add]

theorem symplOHF_add_right' (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (xi0 : E) (x y y' : WOF F E nS nT) :
    symplOHF σ JS JT xi0 x (y + y') = symplOHF σ JS JT xi0 x y + symplOHF σ JS JT xi0 x y' := by
  simp only [symplOHF, symplOF, hOF, Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add]

end GlobalTheory.ThetaDerivQuasi

theorem GlobalTheory.ThetaDerivQuasi.deriv_heis_quasi : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
      ∀ f : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f → ∀ L : ℝ →+ Formalism.IndefR.DatumF.WOF F E nS nT, Continuous L → (∀ t, (L t).map (Formalism.IndefR.DatumF.finPartF F E) = 0) →
      ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : Formalism.IndefR.DatumF.WOF F E nS nT),
      deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (Formalism.IndefR.DatumF.ratWF γ + w)) 0 = B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) * deriv (fun t : ℝ => Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (w)) 0 := by
  intro F E _ _ _ _ _ σ B _ nS nT JS JT _ _ ξ₀ _ _ _ f hf L _ _ γ w
  have key : ∀ t : ℝ, Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f (Formalism.IndefR.DatumF.ratWF γ + w) =
      B.ψ (-(Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w)) *
        Formalism.IndefR.DatumF.heisOF σ JS JT ξ₀ B.ψ (L t) f w := by
    intro t
    simp only [Formalism.IndefR.DatumF.heisOF]
    rw [add_assoc, hf.quasi γ (w + L t), GlobalTheory.ThetaDerivQuasi.symplOHF_add_left',
      GlobalTheory.ThetaDerivQuasi.symplOHF_add_right', neg_add, AddChar.map_add_eq_mul, AddChar.map_add_eq_mul]
    have h1 : B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) (L t)) *
        B.ψ (-Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) (L t)) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    linear_combination (B.ψ (Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ w (L t)) *
      B.ψ (-Formalism.IndefR.DatumF.symplOHF σ JS JT ξ₀ (Formalism.IndefR.DatumF.ratWF γ) w) * f (w + L t)) * h1
  simp_rw [key]
  exact congrFun (deriv_const_mul_field' _) 0

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetOmegaEqConstMulDetStatement
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_omega_eq_const_mul_det : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} (X : Obj F 𝔠 (Sp ℂ)) (L : LB X.A.left)
    (u : HolUnif X.A L (Module.finrank ℚ F)) (δ : X.DetOmega), ∃ C : ℂ,
    ∀ (v : Fin (Module.finrank ℚ F) → X.Lie) (W : Matrix (Fin (Module.finrank ℚ F)) (Fin (Module.finrank ℚ F)) ℂ),
      (∀ j, u.IsDiff (W j) (v j).hom) → δ v = C * W.det := by
  first | exact @GlobalTheory.UnifDet.detOmega_eq_const_mul_det | exact GlobalTheory.UnifDet.detOmega_eq_const_mul_det | (intros; apply GlobalTheory.UnifDet.detOmega_eq_const_mul_det <;> assumption)
end

