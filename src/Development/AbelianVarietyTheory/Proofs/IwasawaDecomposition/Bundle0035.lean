import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLSeriesEulerProduct
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyRayDataOfNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0021
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.VecMulVecComm

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLSeriesEulerProductStatement
section
open NumberField IsDedekindDomain GlobalTheory.Mem Complex
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ray_L_series_euler_product : ∀ (K : Type) [Field K] [NumberField K] (M : ℕ), 2 ≤ M → ∀ (D : RayData K M) (χ : D.G →* ℂˣ) (s : ℂ), 1 < s.re → LSeriesSummable (D.coef χ) s ∧ Summable (fun v : D.Pr => ‖((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s)‖) ∧ LSeries (D.coef χ) s = Complex.exp (∑' v : D.Pr, -Complex.log (1 - (χ (D.cls v.1.asIdeal) : ℂ) * ((Ideal.absNorm v.1.asIdeal : ℕ) : ℂ) ^ (-s))) := by
  first | exact @GlobalTheory.Mem.RayData.lseries_eq_exp_tsum | exact GlobalTheory.Mem.RayData.lseries_eq_exp_tsum | (intros; apply GlobalTheory.Mem.RayData.lseries_eq_exp_tsum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomainStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.regular_local_ring_normal_domain : ∀ (T : Type) [CommRing T] [IsRegularLocalRing T], IsDomain T ∧ IsIntegrallyClosed T := by
  first | exact @GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing | exact GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing | (intros; apply GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReversedCharpolyCoeffInDomainMulStatement
section
open CategoryTheory Polynomial GlobalTheory.NormalDescent
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reversedCharpolyCoeffInDomain_mul : ∀ {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Finite) (u : A) (b : B) (k : ℕ), normCoeff φ hφ (φ u * b) k = u ^ k * normCoeff φ hφ b k := by
  first | exact @GlobalTheory.NormalDescent.normCoeff_mul | exact GlobalTheory.NormalDescent.normCoeff_mul | (intros; apply GlobalTheory.NormalDescent.normCoeff_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothOfFiniteDimensionalTranslationStable
section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory

theorem contDiff_prod_ofFn_coord {A : Type} [NormedRing A] [NormedAlgebra ℝ A] {ι : Type}
    (R : ι → ℝ → A) (hR : ∀ i, ContDiff ℝ ∞ (R i)) (k : ℕ) (I : Fin k → ι) :
    ContDiff ℝ ∞ fun t : Fin k → ℝ => (List.ofFn fun a => R (I a) (t a)).prod := by
  induction k with
  | zero => simpa using contDiff_const
  | succ k ih =>
    simp only [List.ofFn_succ, List.prod_cons]
    refine ContDiff.mul ((hR (I 0)).comp (contDiff_apply ℝ ℝ 0)) ?_
    have h : ContDiff ℝ ∞ fun (t : Fin (k + 1) → ℝ) (a : Fin k) => t a.succ :=
      contDiff_pi.2 fun a => contDiff_apply ℝ ℝ a.succ
    exact (ih fun a => I a.succ).comp h

theorem smooth_of_finiteDimensional_translation_stable :
    ∀ (G : Type) [Group G] (M : Submodule ℂ (G → ℂ)) [FiniteDimensional ℂ M] (ι : Type) (c : ι → ℝ → G), (∀ i s t, c i (s + t) = c i s * c i t) → (∀ i t, ∀ f ∈ M, (fun g => f (g * c i t)) ∈ M) → (∀ i, ∀ f ∈ M, ∀ g, Continuous fun t : ℝ => f (g * c i t)) → (∀ i, ∀ f ∈ M, (fun g => deriv (fun t : ℝ => f (g * c i t)) 0) ∈ M) ∧ ∀ (k : ℕ) (I : Fin k → ι), ∀ f ∈ M, ∀ g, ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun a => c (I a) (t a)).prod) := by
  intro G _ M _ ι c hc hM hcont
  let V := Fin (Module.finrank ℂ M) → ℂ
  let Φ : M ≃L[ℂ] V := (Module.finBasis ℂ M).equivFun.toContinuousLinearEquiv
  let ρ : ι → ℝ → (M →ₗ[ℂ] M) := fun i t =>
    { toFun := fun f => ⟨fun g => f.1 (g * c i t), hM i t f.1 f.2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let R : ι → ℝ → (V →L[ℂ] V) := fun i t =>
    LinearMap.toContinuousLinearMap (Φ.toLinearEquiv.toLinearMap ∘ₗ ρ i t ∘ₗ Φ.symm.toLinearEquiv.toLinearMap)
  have hRapp : ∀ i t v, R i t v = Φ (ρ i t (Φ.symm v)) := fun _ _ _ => rfl
  let ev : G → (V →L[ℂ] ℂ) := fun g =>
    LinearMap.toContinuousLinearMap ((LinearMap.proj g : (G → ℂ) →ₗ[ℂ] ℂ) ∘ₗ M.subtype ∘ₗ Φ.symm.toLinearEquiv.toLinearMap)
  have hev : ∀ g v, ev g v = (Φ.symm v).1 g := fun _ _ => rfl
  have hkey : ∀ g i t v, ev g (R i t v) = ev (g * c i t) v := by
    intro g i t v
    rw [hev, hRapp, Φ.symm_apply_apply]
    rfl
  have hsep : ∀ v w : V, (∀ g, ev g v = ev g w) → v = w := by
    intro v w h
    apply Φ.symm.injective
    exact Subtype.ext (funext h)
  have hc0 : ∀ i, c i 0 = 1 := by
    intro i
    have := hc i 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hR : ∀ i, ContDiff ℝ ∞ (R i) := by
    intro i
    refine GlobalTheory.T.contDiff_of_continuous_oneParameter_hom _ (R i) ?_ ?_ ?_
    · refine continuous_clm_apply.2 fun v => ?_
      simp only [hRapp]
      refine Φ.continuous.comp ?_
      exact Continuous.subtype_mk (continuous_pi fun g => hcont i _ (Φ.symm v).2 g) _
    · refine ContinuousLinearMap.ext fun v => hsep _ _ fun g => ?_
      rw [hkey, hc0, mul_one]; rfl
    · intro s t
      refine ContinuousLinearMap.ext fun v => hsep _ _ fun g => ?_
      rw [ContinuousLinearMap.mul_apply, hkey, hkey, hkey, hc, mul_assoc]
  have hf : ∀ f (hf : f ∈ M) g, f g = ev g (Φ ⟨f, hf⟩) := by
    intro f hf g
    rw [hev, Φ.symm_apply_apply]
  refine ⟨fun i f hfM => ?_, fun k I f hfM g => ?_⟩
  · have hd : HasDerivAt (R i) (deriv (R i) 0) 0 :=
      ((hR i).differentiable (by simp) 0).hasDerivAt
    have : (fun g => deriv (fun t : ℝ => f (g * c i t)) 0)
        = (Φ.symm (deriv (R i) 0 (Φ ⟨f, hfM⟩))).1 := by
      funext g
      rw [← hev]
      have h1 : (fun t : ℝ => f (g * c i t)) = fun t => ev g (R i t (Φ ⟨f, hfM⟩)) := by
        funext t
        rw [hkey, ← hf]
      rw [h1]
      let L : (V →L[ℂ] V) →L[ℂ] ℂ := (ev g).comp (ContinuousLinearMap.apply ℂ V (Φ ⟨f, hfM⟩))
      exact ((L.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd).deriv
    rw [this]
    exact Subtype.property _
  · have hprod : ∀ (k : ℕ) (I : Fin k → ι) (t : Fin k → ℝ) (g : G) (v : V),
        ev g ((List.ofFn fun a => R (I a) (t a)).prod v)
          = ev (g * (List.ofFn fun a => c (I a) (t a)).prod) v := by
      intro k
      induction k with
      | zero => intro I t g v; simp
      | succ k ih =>
        intro I t g v
        simp only [List.ofFn_succ, List.prod_cons]
        rw [ContinuousLinearMap.mul_apply, hkey, ih (fun a => I a.succ) (fun a => t a.succ),
          mul_assoc]
    have h1 : (fun t : Fin k → ℝ => f (g * (List.ofFn fun a => c (I a) (t a)).prod))
        = fun t => ev g ((List.ofFn fun a => R (I a) (t a)).prod (Φ ⟨f, hfM⟩)) := by
      funext t
      rw [hprod, ← hf]
    rw [h1]
    let L : (V →L[ℂ] V) →L[ℂ] ℂ := (ev g).comp (ContinuousLinearMap.apply ℂ V (Φ ⟨f, hfM⟩))
    exact (L.restrictScalars ℝ).contDiff.comp (contDiff_prod_ofFn_coord R hR k I)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TracePowGrassmannBlockCurvatureSupertraceZeroStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trace_pow_grassmannBlockCurvature_supertrace_zero : ∀ {n p q : ℕ} (e : Fin p × Fin q → Fin n) (k : ℕ), 1 ≤ k → ((GlobalTheory.GrassModel.blockPoly e).map (GlobalTheory.GrassModel.toEven n) ^ k).trace + ((-GlobalTheory.GrassModel.blockPolyBar e).map (GlobalTheory.GrassModel.toEven n) ^ k).trace = 0 := by
  first | exact @GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar | exact GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar | (intros; apply GlobalTheory.GrassModel.trace_pow_blockPoly_add_trace_pow_neg_blockPolyBar <;> assumption)
end

