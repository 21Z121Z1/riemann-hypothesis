import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0067
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0065
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0021
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0059
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0062
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0056
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0001
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0055

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairEventuallyIsUnitContinuousAtIn
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory

theorem units_near_one_inverse_continuousAt (F K : Type) [NontriviallyNormedField F] [CommRing K] [Algebra F K]
    [Module.Finite F K] [TopologicalSpace K] [IsModuleTopology F K] [IsTopologicalRing K] :
    (∀ᶠ a in 𝓝 (1 : K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : K) := by
  classical
  let b := Module.finBasis F K
  let ι : K →ₐ[F] Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F := Algebra.leftMulMatrix b
  have hι : Continuous ι := IsModuleTopology.continuous_of_linearMap ι.toLinearMap
  have hdet : Continuous fun a : K => (ι a).det := (continuous_id.matrix_det).comp hι
  have h1 : (ι 1).det ≠ 0 := by simp
  have hev : ∀ᶠ a in 𝓝 (1 : K), (ι a).det ≠ 0 :=
    hdet.continuousAt.eventually_ne h1
  have hunit : ∀ a : K, (ι a).det ≠ 0 → IsUnit a := by
    intro a ha
    have hn : Algebra.norm F a ≠ 0 := by rw [Algebra.norm_eq_matrix_det b]; exact ha
    rw [Algebra.norm_apply] at hn
    have hu : IsUnit (Algebra.lmul F K a) := by
      rw [LinearMap.isUnit_iff_isUnit_det]; exact hn.isUnit
    obtain ⟨c, hc⟩ := ((Module.End.isUnit_iff _).1 hu).2 1
    exact IsUnit.of_mul_eq_one c (by simpa using hc)
  have hev' : ∀ᶠ a in 𝓝 (1 : K), IsUnit a := hev.mono hunit
  refine ⟨hev', ?_⟩
  let g : K → K := fun a => b.equivFun.symm ((ι a)⁻¹ *ᵥ b.equivFun 1)
  have hinv : ∀ a : K, IsUnit a → (ι a)⁻¹ = ι (Ring.inverse a) := by
    intro a ha
    apply Matrix.inv_eq_left_inv
    rw [← map_mul, Ring.inverse_mul_cancel a ha, map_one]
  have heq : g =ᶠ[𝓝 (1 : K)] Ring.inverse := by
    filter_upwards [hev'] with a ha
    simp only [g, hinv a ha, Module.Basis.equivFun_apply, ι, Algebra.leftMulMatrix_mulVec_repr, mul_one]
    rw [← Module.Basis.equivFun_apply, LinearEquiv.symm_apply_apply]
  refine ContinuousAt.congr ?_ heq
  have hsymm : Continuous b.equivFun.symm := LinearMap.continuous_on_pi b.equivFun.symm.toLinearMap
  have hdet1 : ContinuousAt Ring.inverse (ι 1).det := by
    have : (ι 1).det = 1 := by simp
    rw [this]
    have : (Ring.inverse : F → F) = Inv.inv := funext Ring.inverse_eq_inv
    rw [this]
    exact continuousAt_inv₀ one_ne_zero
  have hmi : ContinuousAt (fun a : K => (ι a)⁻¹) 1 :=
    (continuousAt_matrix_inv (ι 1) hdet1).comp hι.continuousAt
  have hmv : Continuous fun M : Matrix (Fin (Module.finrank F K)) (Fin (Module.finrank F K)) F => M *ᵥ b.equivFun 1 :=
    continuous_id.matrix_mulVec continuous_const
  exact hsymm.continuousAt.comp (hmv.continuousAt.comp hmi)

theorem et_units_near_one_inverse_continuousAt :
    ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
      (A : Et F E), (∀ᶠ a in 𝓝 (1 : A.K), IsUnit a) ∧ ContinuousAt Ring.inverse (1 : A.K) :=
  fun F _ _ _ _ _ A => units_near_one_inverse_continuousAt F A.K

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EulerOperatorInjectiveEigenvector
section
open MeasureTheory Filter Topology
open scoped InnerProductSpace BigOperators

namespace GlobalTheory

theorem eulerOp_Zbound : ∀ (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (a : ∀ v, X v → ℂ) (s : ι → ℝ) (B : (∀ v, X v) → (H →L[ℂ] H)) (Z : ι → (H →L[ℂ] H)), (∀ v, a v (x0 v) = 1) → (∀ v (C : Finset (X v)), x0 v ∉ C → ∑ x ∈ C, ‖a v x‖ ≤ s v) → (∀ f, ‖B f‖ ≤ 1) → B x0 = 1 → (∀ v (f : ∀ v, X v), {w | f w ≠ x0 w}.Finite → f v = x0 v → HasSum (fun x => a v x • B (Function.update f v x)) (B f * Z v)) → ∀ v, ‖Z v - 1‖ ≤ s v := by
  intro ι _ X x0 H _ _ _ a s B Z ha0 hC hB hB0 hZ v
  classical
  have h := hZ v x0 (by simp) rfl
  rw [hB0, one_mul] at h
  have ht0 : a v (x0 v) • B (Function.update x0 v (x0 v)) = 1 := by simp [ha0, hB0]
  have h2 := h.update (x0 v) 0
  rw [ht0] at h2
  let g : X v → ℝ := fun x => if x = x0 v then 0 else ‖a v x‖
  have hg0 : 0 ≤ g := fun x => by simp only [g]; split_ifs <;> simp
  have hgsum : ∀ u : Finset (X v), ∑ x ∈ u, g x ≤ s v := by
    intro u
    have e : ∑ x ∈ u, g x = ∑ x ∈ u.filter (fun x => ¬ x = x0 v), ‖a v x‖ := by
      simp only [g]; rw [Finset.sum_ite]; simp
    rw [e]; exact hC v _ (by simp)
  have hgs : Summable g := summable_of_sum_le hg0 hgsum
  have h3 := h2.norm_le_of_bounded hgs.hasSum (fun x => ?_)
  · calc ‖Z v - 1‖ = ‖0 - 1 + Z v‖ := by congr 1; abel
      _ ≤ ∑' x, g x := h3
      _ ≤ s v := hgs.tsum_le_of_sum_le hgsum
  · by_cases hx : x = x0 v
    · rw [hx]; simp [g]
    · rw [Function.update_of_ne hx]
      simp only [g, if_neg hx, norm_smul]
      exact (mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)).trans (by simp)

theorem eulerOp_rec : ∀ (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (a : ∀ v, X v → ℂ) (s : ι → ℝ) (B : (∀ v, X v) → (H →L[ℂ] H)) (Z : ι → (H →L[ℂ] H)), (∀ v, a v (x0 v) = 1) → (∀ v (f : ∀ v, X v), {w | f w ≠ x0 w}.Finite → f v = x0 v → HasSum (fun x => a v x • B (Function.update f v x)) (B f * Z v)) → Summable (fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => (∏ᶠ u, a u (f.1 u)) • B f.1) → ∀ (S : Finset ι) (v : ι), v ∉ S → HasSum (fun f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ insert v S, f.1 w = x0 w} => (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) ((∑' f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ S, f.1 w = x0 w}, (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) * Z v) := by
  intro ι _ X x0 H _ _ _ a s B Z ha0 hZ hsum S v hv
  classical
  have hprod : ∀ (T : Finset ι) (f : ∀ v, X v), (∀ w ∉ T, f w = x0 w) →
      (∏ᶠ u, a u (f u)) = ∏ u ∈ T, a u (f u) := by
    intro T f hf
    apply finprod_eq_prod_of_mulSupport_subset
    intro w hw
    rw [Function.mem_mulSupport] at hw
    by_contra h
    exact hw (by rw [hf w h, ha0])
  have hfinU : ∀ (g : ∀ v, X v) (x : X v), {w | g w ≠ x0 w}.Finite →
      {w | Function.update g v x w ≠ x0 w}.Finite := by
    intro g x hg
    apply (hg.insert v).subset
    intro w hw
    by_cases h : w = v
    · exact Or.inl h
    · right; simpa [Function.update_of_ne h] using hw
  let e : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ S, f.1 w = x0 w} × X v →
      {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ insert v S, f.1 w = x0 w} :=
    fun p => ⟨⟨Function.update p.1.1.1 v p.2, hfinU _ _ p.1.1.2⟩, fun w hw => by
      have h1 : w ≠ v := fun h => hw (h ▸ Finset.mem_insert_self _ _)
      have h2 : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
      simp only [Function.update_of_ne h1]; exact p.1.2 w h2⟩
  have he : Function.Bijective e := by
    constructor
    · rintro ⟨g, x⟩ ⟨g', x'⟩ h
      have h' : Function.update g.1.1 v x = Function.update g'.1.1 v x' :=
        congrArg (fun f => f.1.1) h
      have hx : x = x' := by simpa using congrFun h' v
      subst hx
      have hg : g.1.1 = g'.1.1 := by
        funext w
        by_cases hw : w = v
        · rw [hw, g.2 v hv, g'.2 v hv]
        · simpa [Function.update_of_ne hw] using congrFun h' w
      exact Prod.ext (Subtype.ext (Subtype.ext hg)) rfl
    · intro f
      refine ⟨(⟨⟨Function.update f.1.1 v (x0 v), hfinU _ _ f.1.2⟩, fun w hw => ?_⟩, f.1.1 v), ?_⟩
      · show Function.update f.1.1 v (x0 v) w = x0 w
        by_cases h : w = v
        · rw [h]; simp
        · rw [Function.update_of_ne h]; exact f.2 w (by simp [h, hw])
      · apply Subtype.ext; apply Subtype.ext; simp [e]
  have hsumI : Summable (fun f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ insert v S, f.1 w = x0 w} =>
      (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) :=
    hsum.comp_injective (f := fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => (∏ᶠ u, a u (f.1 u)) • B f.1) Subtype.val_injective
  have hsumS : Summable (fun f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ S, f.1 w = x0 w} =>
      (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) :=
    hsum.comp_injective (f := fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => (∏ᶠ u, a u (f.1 u)) • B f.1) Subtype.val_injective
  have hall := (Equiv.ofBijective e he).hasSum_iff.mpr hsumI.hasSum
  have hfib : ∀ g : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ S, f.1 w = x0 w},
      HasSum (fun x => ((fun f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ insert v S, f.1 w = x0 w} =>
        (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) ∘ (Equiv.ofBijective e he)) (g, x))
        (((∏ᶠ u, a u (g.1.1 u)) • B g.1.1) * Z v) := by
    intro g
    have hgv : g.1.1 v = x0 v := g.2 v hv
    have key : ∀ x, ((fun f : {f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} // ∀ w ∉ insert v S, f.1 w = x0 w} =>
        (∏ᶠ u, a u (f.1.1 u)) • B f.1.1) ∘ (Equiv.ofBijective e he)) (g, x) =
        (∏ᶠ u, a u (g.1.1 u)) • (a v x • B (Function.update g.1.1 v x)) := by
      intro x
      simp only [Function.comp, Equiv.ofBijective_apply, e]
      rw [smul_smul, hprod (insert v S) _ ?_, hprod S _ g.2, Finset.prod_insert hv]
      · congr 1
        rw [Function.update_self, mul_comm]
        congr 1
        apply Finset.prod_congr rfl
        intro w hw
        rw [Function.update_of_ne (by rintro rfl; exact hv hw)]
      · intro w hw
        have h1 : w ≠ v := fun h => hw (h ▸ Finset.mem_insert_self _ _)
        have h2 : w ∉ S := fun h => hw (Finset.mem_insert_of_mem h)
        rw [Function.update_of_ne h1]; exact g.2 w h2
    simp_rw [key]
    rw [smul_mul_assoc]
    exact (hZ v g.1.1 g.1.2 hgv).const_smul _
  have h3 := hall.prod_fiberwise hfib
  have h4 := hsumS.hasSum.mul_right (Z v)
  rw [← h3.unique h4]
  exact hsumI.hasSum

theorem eulerOp_normSummable (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] (a : ∀ v, X v → ℂ) (s : ι → ℝ) (B : (∀ v, X v) → (H →L[ℂ] H)) (ha0 : ∀ v, a v (x0 v) = 1) (hs : Summable s) (hC : ∀ v (C : Finset (X v)), x0 v ∉ C → ∑ x ∈ C, ‖a v x‖ ≤ s v) (hB : ∀ f, ‖B f‖ ≤ 1) :
    Summable (fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => ‖(∏ᶠ v, a v (f.1 v)) • B f.1‖) := by
  have h1 := GlobalTheory.T.summable_finprod_of_finite_support_euler_sum ι X x0 (fun v x => ‖a v x‖) s (fun v x => norm_nonneg _) (by intro v; simp [ha0]) hs hC
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun f => ?_) h1
  rw [norm_smul]
  have hfin := f.2
  have e1 : (∏ᶠ v, a v (f.1 v)) = ∏ v ∈ hfin.toFinset, a v (f.1 v) := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro w hw
    rw [Function.mem_mulSupport] at hw
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h; exact hw (by simp [h, ha0])
  have e2 : (∏ᶠ v, ‖a v (f.1 v)‖) = ∏ v ∈ hfin.toFinset, ‖a v (f.1 v)‖ := by
    apply finprod_eq_prod_of_mulSupport_subset
    intro w hw
    rw [Function.mem_mulSupport] at hw
    simp only [Set.Finite.coe_toFinset, Set.mem_setOf_eq]
    intro h; exact hw (by simp [h, ha0])
  rw [e1, e2, norm_prod]
  calc (∏ v ∈ hfin.toFinset, ‖a v (f.1 v)‖) * ‖B f.1‖ ≤ (∏ v ∈ hfin.toFinset, ‖a v (f.1 v)‖) * 1 :=
        mul_le_mul_of_nonneg_left (hB _) (Finset.prod_nonneg fun _ _ => norm_nonneg _)
    _ = _ := mul_one _

theorem eulerOp_injective_eigen : ∀ (ι : Type) [DecidableEq ι] (X : ι → Type) (x0 : ∀ v, X v) (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] (a : ∀ v, X v → ℂ) (s : ι → ℝ) (B : (∀ v, X v) → (H →L[ℂ] H)) (Z : ι → (H →L[ℂ] H)), (∀ v, a v (x0 v) = 1) → Summable s → (∀ v, s v < 1) → (∀ v (C : Finset (X v)), x0 v ∉ C → ∑ x ∈ C, ‖a v x‖ ≤ s v) → (∀ f, ‖B f‖ ≤ 1) → B x0 = 1 → (∀ v (f : ∀ v, X v), {w | f w ≠ x0 w}.Finite → f v = x0 v → HasSum (fun x => a v x • B (Function.update f v x)) (B f * Z v)) → ∃ W : H →L[ℂ] H, HasSum (fun f : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} => (∏ᶠ v, a v (f.1 v)) • B f.1) W ∧ Function.Injective W ∧ ∀ (y : H) (z : ι → ℂ), (∀ v, Z v y = z v • y) → W y = (∏' v, z v) • y := by
  intro ι _ X x0 H _ _ _ a s B Z ha0 hs hs1 hC hB hB0 hZ
  let t : {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} → (H →L[ℂ] H) := fun f => (∏ᶠ v, a v (f.1 v)) • B f.1
  have hnorm : Summable (fun f => ‖t f‖) := eulerOp_normSummable ι X x0 H a s B ha0 hs hC hB
  have hsum : Summable t := hnorm.of_norm
  let A : Finset ι → Set {f : ∀ v, X v // {w | f w ≠ x0 w}.Finite} := fun S => {f | ∀ w ∉ S, f.1 w = x0 w}
  let WS : Finset ι → (H →L[ℂ] H) := fun S => ∑' f : A S, t f
  have hs0 : ∀ v, 0 ≤ s v := fun v => by simpa using hC v ∅ (by simp)
  have hZb := eulerOp_Zbound ι X x0 H a s B Z ha0 hC hB hB0 hZ
  have hrec : ∀ S v, v ∉ S → WS (insert v S) = WS S * Z v := fun S v hv =>
    (eulerOp_rec ι X x0 H a s B Z ha0 hZ hsum S v hv).tsum_eq
  have hbase : WS ∅ = 1 := by
    let f0 : A ∅ := ⟨⟨x0, by simp⟩, fun w _ => rfl⟩
    have hf0 : ∀ b : A ∅, b = f0 := fun b =>
      Subtype.ext (Subtype.ext (funext fun w => b.2 w (by simp)))
    show ∑' f : A ∅, t f = 1
    rw [tsum_eq_single f0 (fun b hb => absurd (hf0 b) hb)]
    simp [t, f0, ha0, hB0]
  have hlim : Tendsto WS atTop (𝓝 (∑' f, t f)) := by
    have e : WS = fun S => ∑' f, (A S).indicator t f := by
      funext S; exact tsum_subtype (A S) t
    rw [e]
    refine tendsto_tsum_of_dominated_convergence hnorm (fun f => ?_)
      (Eventually.of_forall fun S f => norm_indicator_le_norm_self _ _)
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop f.2.toFinset] with S hS
    have hm : f ∈ A S := by
      intro w hw
      by_contra h
      exact hw (hS (by simpa using h))
    exact (Set.indicator_of_mem hm t).symm
  obtain ⟨δ, hδ, hδS⟩ := GlobalTheory.T.prod_one_sub_bounded_below_of_summable ι s hs0 hs1 hs
  have hlow : ∀ S : Finset ι, ∀ y, (∏ v ∈ S, (1 - s v)) * ‖y‖ ≤ ‖WS S y‖ := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro y; simp [hbase]
    | insert v S hv ih =>
      intro y
      rw [hrec S v hv, Finset.prod_insert hv, ContinuousLinearMap.mul_apply]
      have h1 : ‖(Z v - 1) y‖ ≤ s v * ‖y‖ :=
        ((Z v - 1).le_opNorm y).trans (mul_le_mul_of_nonneg_right (hZb v) (norm_nonneg _))
      have h2 : ‖y‖ ≤ ‖Z v y‖ + ‖(Z v - 1) y‖ := by
        calc ‖y‖ = ‖Z v y - (Z v - 1) y‖ := by simp
          _ ≤ _ := norm_sub_le _ _
      have hZy : (1 - s v) * ‖y‖ ≤ ‖Z v y‖ := by nlinarith
      have hP : 0 ≤ ∏ v ∈ S, (1 - s v) := Finset.prod_nonneg fun w _ => by linarith [hs1 w]
      calc (1 - s v) * (∏ v ∈ S, (1 - s v)) * ‖y‖ = (∏ v ∈ S, (1 - s v)) * ((1 - s v) * ‖y‖) := by ring
        _ ≤ (∏ v ∈ S, (1 - s v)) * ‖Z v y‖ := mul_le_mul_of_nonneg_left hZy hP
        _ ≤ _ := ih _
  have heig : ∀ S : Finset ι, ∀ y (z : ι → ℂ), (∀ v, Z v y = z v • y) → WS S y = (∏ v ∈ S, z v) • y := by
    intro S
    induction S using Finset.induction_on with
    | empty => intro y z _; simp [hbase]
    | insert v S hv ih =>
      intro y z hyz
      rw [hrec S v hv, ContinuousLinearMap.mul_apply, hyz v, map_smul, ih y z hyz, Finset.prod_insert hv, smul_smul]
  have hWy : ∀ y, Tendsto (fun S => WS S y) atTop (𝓝 ((∑' f, t f) y)) := fun y =>
    ((ContinuousLinearMap.apply ℂ H y).continuous.tendsto _).comp hlim
  have hlowW : ∀ y, δ * ‖y‖ ≤ ‖(∑' f, t f) y‖ := fun y =>
    ge_of_tendsto (hWy y).norm (Eventually.of_forall fun S =>
      (mul_le_mul_of_nonneg_right (hδS S) (norm_nonneg y)).trans (hlow S y))
  refine ⟨∑' f, t f, hsum.hasSum, ?_, ?_⟩
  · intro y1 y2 h
    have h1 := hlowW (y1 - y2)
    rw [map_sub, h, sub_self, norm_zero] at h1
    have h2 : ‖y1 - y2‖ ≤ 0 := le_of_mul_le_mul_left (by rw [mul_zero]; exact h1) hδ
    exact sub_eq_zero.mp (norm_le_zero_iff.mp h2)
  · intro y z hyz
    by_cases hy : y = 0
    · subst hy; simp
    obtain ⟨φ, -, hφ⟩ := exists_dual_vector ℂ y (norm_ne_zero_iff.mpr hy)
    have h1 : Tendsto (fun S => (∏ v ∈ S, z v) • y) atTop (𝓝 ((∑' f, t f) y)) :=
      Tendsto.congr (fun S => heig S y z hyz) (hWy y)
    have h2 : Tendsto (fun S => φ ((∏ v ∈ S, z v) • y)) atTop (𝓝 (φ ((∑' f, t f) y))) :=
      (φ.continuous.tendsto _).comp h1
    simp only [map_smul, hφ, smul_eq_mul] at h2
    have hy' : ((‖y‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hy
    have h3 : Tendsto (fun S => ∏ v ∈ S, z v) atTop (𝓝 (φ ((∑' f, t f) y) / ‖y‖)) := by
      refine (h2.div_const ((‖y‖ : ℂ))).congr (fun S => ?_)
      exact mul_div_cancel_right₀ _ hy'
    have hP : HasProd z (φ ((∑' f, t f) y) / ‖y‖) := h3
    rw [hP.tprod_eq]
    exact tendsto_nhds_unique h1 (h3.smul_const y)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAevalEqOfCharpolySeparableInvolution
section
open GlobalTheory.UnitLemma Polynomial

namespace GlobalTheory.UnitLemma

theorem exists_aeval_eq_of_charpoly_separable {E A : Type} [Field E] [CommRing A] [Algebra E A]
    [Module.Finite E A] (g : A) (hP : (LinearMap.mulLeft E g).charpoly.Separable) (a : A) :
    ∃ f : E[X], a = aeval g f := by
  classical
  rcases subsingleton_or_nontrivial A with hA | hA
  · exact ⟨0, Subsingleton.elim _ _⟩
  have hint : IsIntegral E g := Algebra.IsIntegral.isIntegral g
  have hm0 : minpoly E g ≠ 0 := minpoly.ne_zero hint
  have hf : aeval (LinearMap.mulLeft E g) (minpoly E g) = 0 := by
    have := aeval_algHom_apply (Algebra.lmul E A) g (minpoly E g)
    rw [minpoly.aeval, map_zero] at this
    exact this
  have hn : 0 < Module.finrank E A := Module.finrank_pos
  have h1 := GlobalTheory.CharpolyDvd.charpoly_dvd_pow_finrank _ _ hf
  have h2 : (LinearMap.mulLeft E g).charpoly ∣ minpoly E g :=
    (hP.squarefree.dvd_pow_iff_dvd hn.ne').1 h1
  have h3 : Module.finrank E A ≤ (minpoly E g).natDegree := by
    have := natDegree_le_of_dvd h2 hm0
    rwa [LinearMap.charpoly_natDegree] at this
  have hli := linearIndependent_pow (K := E) g
  have h4 := hli.fintype_card_le_finrank
  rw [Fintype.card_fin] at h4
  haveI : Nonempty (Fin (minpoly E g).natDegree) := ⟨⟨0, by omega⟩⟩
  have htop := hli.span_eq_top_of_card_eq_finrank (by rw [Fintype.card_fin]; omega)
  have hle : Submodule.span E (Set.range fun i : Fin (minpoly E g).natDegree => g ^ (i : ℕ)) ≤
      Subalgebra.toSubmodule (Algebra.adjoin E {g}) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hg : g ∈ Algebra.adjoin E {g} := Algebra.subset_adjoin (Set.mem_singleton g)
    exact Subalgebra.pow_mem (Algebra.adjoin E {g}) hg (i : ℕ)
  have ha : a ∈ Algebra.adjoin E {g} := by
    have : a ∈ Submodule.span E (Set.range fun i : Fin (minpoly E g).natDegree => g ^ (i : ℕ)) := by
      rw [htop]; trivial
    exact hle this
  rw [Algebra.adjoin_singleton_eq_range_aeval] at ha
  obtain ⟨f, hf⟩ := ha
  exact ⟨f, hf.symm⟩

theorem InvAlg.exists_aeval_eq_of_separable :
    ∀ (K : UQ) (B : InvAlg K), B.P.Separable → ∀ a : B.A, ∃ f : K.E[X], a = aeval B.g f :=
  fun _ B hP a => exists_aeval_eq_of_charpoly_separable B.g hP a

end GlobalTheory.UnitLemma
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompactUnitariesIntegralOrbitOfHankelDetNe
section
open GlobalTheory.JR Matrix MeasureTheory Filter Topology

namespace GlobalTheory.JR.SuppBdd

theorem isClosed_unitary_set {n : ℕ} {E : Type} [Field E] [TopologicalSpace E] [IsTopologicalRing E] [T2Space E]
    [StarRing E] [ContinuousStar E] :
    IsClosed ((Matrix.unitaryGroup (Fin n) E : Set (Matrix (Fin n) (Fin n) E))) := by
  have : ((Matrix.unitaryGroup (Fin n) E : Set (Matrix (Fin n) (Fin n) E))) =
      {U | star U * U = 1} ∩ {U | U * star U = 1} := by
    ext U; simp [Matrix.unitaryGroup, Unitary.mem_iff]
  rw [this]
  exact (isClosed_eq (continuous_star.mul continuous_id) continuous_const).inter
    (isClosed_eq (continuous_id.mul continuous_star) continuous_const)

theorem pow_conj {n : ℕ} {E : Type} [CommRing E] [StarRing E] (g : Matrix.unitaryGroup (Fin n) E)
    (A : Matrix (Fin n) (Fin n) E) (j : ℕ) : (g.1 * A * star g.1) ^ j = g.1 * A ^ j * star g.1 := by
  have hg : star g.1 * g.1 = 1 := Unitary.star_mul_self_of_mem g.2
  have hg' : g.1 * star g.1 = 1 := Unitary.mul_star_self_of_mem g.2
  induction j with
  | zero => simp [hg']
  | succ j ih =>
    rw [pow_succ, ih, pow_succ]
    calc g.1 * A ^ j * star g.1 * (g.1 * A * star g.1) = g.1 * A ^ j * (star g.1 * g.1) * A * star g.1 := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [hg, Matrix.mul_one]; simp only [Matrix.mul_assoc]

theorem Bm_actU {n : ℕ} {F E : Type} [CommRing F] [CommRing E] [StarRing E] [Algebra F E]
    (g : Matrix.unitaryGroup (Fin n) E) (Y : Hn n F E) :
    Bm (actU g Y).toGl = g.1 * Bm Y.toGl := by
  have hg : star g.1 * g.1 = 1 := Unitary.star_mul_self_of_mem g.2
  ext i j
  have h1 : ((g.1 * Y.1.1 * star g.1) ^ (j : ℕ)) *ᵥ (g.1 *ᵥ Y.2.1) = g.1 *ᵥ ((Y.1.1 ^ (j : ℕ)) *ᵥ Y.2.1) := by
    rw [pow_conj, mulVec_mulVec, mulVec_mulVec]
    congr 1
    rw [Matrix.mul_assoc, hg, Matrix.mul_one]
  have h2 : Bm (actU g Y).toGl i j = (g.1 *ᵥ ((Y.1.1 ^ (j : ℕ)) *ᵥ Y.2.1)) i := by
    rw [← h1]; rfl
  rw [h2, Matrix.mul_apply]
  simp only [mulVec, dotProduct, Bm, Hn.toGl, of_apply]

theorem exists_compact_of_integral : ∀ {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] {n : ℕ} (Y : Hn n F E), Delta (inv Y.toGl) ≠ 0 →
    ∃ K : Set (Matrix.unitaryGroup (Fin n) E), IsCompact K ∧ ∀ g, unitU n F E (actU g Y) ≠ 0 → g ∈ K := by
  intro F E _ _ _ _ _ n Y hD
  haveI : LocallyCompactSpace E := Unram.lcE (F := F)
  haveI : ProperSpace E := ProperSpace.of_locallyCompactSpace E
  haveI : NormedStarGroup E := ⟨fun x => (Unram.norm_star (F := F) x).le⟩
  set B := Bm Y.toGl with hBdef
  have hB : IsUnit B.det := by
    have h := GlobalTheory.JR.NormalFormL.hankel_eq Y.toGl
    have : (Cm Y.toGl * B).det ≠ 0 := by rw [h]; exact hD
    rw [det_mul] at this
    exact isUnit_iff_ne_zero.mpr (right_ne_zero_of_mul this)
  let Φ : Matrix (Fin n) (Fin n) E × (Fin n → E) → Matrix (Fin n) (Fin n) E :=
    fun p => (Matrix.of fun i (j : Fin n) => ((p.1 ^ (j : ℕ)) *ᵥ p.2) i) * B⁻¹
  let S : Set (Matrix (Fin n) (Fin n) E × (Fin n → E)) :=
    {A | ∀ i j, ‖A i j‖ ≤ 1} ×ˢ {v | ∀ i, ‖v i‖ ≤ 1}
  have hS : IsCompact S := by
    apply IsCompact.prod
    · have : {A : Matrix (Fin n) (Fin n) E | ∀ i j, ‖A i j‖ ≤ 1} =
          Set.pi Set.univ (fun _ => Set.pi Set.univ fun _ => Metric.closedBall (0 : E) 1) := by
        ext A; simp only [Set.mem_setOf_eq]
        exact ⟨fun h i _ j _ => by simpa using h i j, fun h i j => by simpa using h i trivial j trivial⟩
      rw [this]
      exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
    · have : {v : Fin n → E | ∀ i, ‖v i‖ ≤ 1} = Set.pi Set.univ (fun _ => Metric.closedBall (0 : E) 1) := by
        ext v; simp
      rw [this]
      exact isCompact_univ_pi fun _ => isCompact_closedBall _ _
  have hΦ : Continuous Φ := by
    refine Continuous.matrix_mul ?_ continuous_const
    refine continuous_matrix fun i j => ?_
    exact (continuous_apply i).comp ((continuous_fst.pow (j : ℕ)).matrix_mulVec continuous_snd)
  refine ⟨Subtype.val ⁻¹' (Φ '' S), ?_, ?_⟩
  · exact (isClosed_unitary_set (n := n) (E := E)).isClosedEmbedding_subtypeVal.isCompact_preimage (hS.image hΦ)
  · intro g hg
    have hm := Set.mem_of_indicator_ne_zero hg
    refine ⟨((actU g Y).1.1, (actU g Y).2.1), ⟨hm.1, hm.2.1⟩, ?_⟩
    show Bm (actU g Y).toGl * B⁻¹ = g.1
    rw [Bm_actU, ← hBdef, Matrix.mul_nonsing_inv_cancel_right _ _ hB]

end GlobalTheory.JR.SuppBdd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCompleteDvrPrimitiveRoot
section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum IsLocalRing

namespace GlobalTheory.CyclotomicCompletion

theorem exists_place_above (K : Type) [Field K] [NumberField K] {l : ℕ} (hl : l.Prime) :
    ∃ v : HeightOneSpectrum (𝓞 K), (l : 𝓞 K) ∈ v.asIdeal := by
  have hp : Prime (l : ℤ) := Nat.prime_iff_prime_int.1 hl
  have : (Ideal.span {(l : ℤ)}).IsPrime := (Ideal.span_singleton_prime hp.ne_zero).2 hp
  obtain ⟨Q, hQ, hQ'⟩ := Ideal.exists_ideal_over_prime_of_isIntegral_of_isDomain
    (S := 𝓞 K) (Ideal.span {(l : ℤ)}) (by
      rw [(RingHom.injective_iff_ker_eq_bot _).1 (RingHom.injective_int (algebraMap ℤ (𝓞 K)))]; exact bot_le)
  have hmem : (l : 𝓞 K) ∈ Q := by
    have : (l : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 K)) := by
      rw [hQ']; exact Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this
  refine ⟨⟨Q, hQ, ?_⟩, hmem⟩
  rintro rfl
  exact hl.ne_zero (by simpa using hmem)

theorem exists_complete_dvr_primitiveRoot : ∀ l : ℕ, l.Prime → ∃ (O : Type) (_ : CommRing O)
    (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
    (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (_ : CharZero O),
    ¬ IsUnit (l : O) ∧ ∃ ζ : O, IsPrimitiveRoot ζ l := by
  intro l hl
  have : NeZero l := ⟨hl.ne_zero⟩
  let K : Type := CyclotomicField l ℚ
  obtain ⟨v, hv⟩ := exists_place_above K hl
  have hinj : Function.Injective (algebraMap (𝓞 K) (v.adicCompletionIntegers K)) :=
    FaithfulSMul.algebraMap_injective _ _
  have hc : IsAdicComplete (maximalIdeal (v.adicCompletionIntegers K))
      (v.adicCompletionIntegers K) := by
    refine NormIntegers.isAdicComplete_of_fg (C := v.adicCompletion K) ⟨?_, ?_, ?_⟩
      (IsNoetherian.noetherian _) (maximalIdeal.isMaximal _).ne_top
    · exact FaithfulSMul.algebraMap_injective _ _
    · intro x
      have : ‖(x : v.adicCompletion K)‖ ≤ 1 := Valued.toNormedField.norm_le_one_iff.2 x.2
      exact_mod_cast this
    · intro x hx
      have : ‖x‖ ≤ 1 := by exact_mod_cast hx
      exact ⟨⟨x, Valued.toNormedField.norm_le_one_iff.1 this⟩, rfl⟩
  refine ⟨v.adicCompletionIntegers K, inferInstance, inferInstance, inferInstance, hc,
    charZero_of_injective_algebraMap hinj, ?_, ?_⟩
  · rw [← map_natCast (algebraMap (𝓞 K) (v.adicCompletionIntegers K)),
      adicCompletionIntegers.isUnit_iff_valued_eq_one, algebraMap_adicCompletionIntegers_apply,
      valuedAdicCompletion_eq_valuation', valuation_eq_one_iff_notMem]
    exact fun h => h hv
  · have : IsCyclotomicExtension {l} ℚ K := CyclotomicField.isCyclotomicExtension l ℚ
    have hζ := IsCyclotomicExtension.zeta_spec l ℚ K
    exact ⟨_, hζ.toInteger_isPrimitiveRoot.map_of_injective hinj⟩

end GlobalTheory.CyclotomicCompletion
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUniqueIntegralAdditiveSystemFrobeniusPowerStatement
section
open GlobalTheory.PMonE
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_integral_additiveSystemFrobeniusPowerSum_eq : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] (p : ℕ) [Fact p.Prime] [CharP F p] (m : Type) [Fintype m] [DecidableEq m] (e D : ℕ), 0 < e → ∀ U : ℕ → Matrix m m F, (∀ i j, ‖(U 0 - 1) i j‖ < 1) → (∀ n, 1 ≤ n → ∀ i j, ‖U n i j‖ < 1) → ∀ b : m → F, Integral b → ∃! y : m → F, Integral y ∧ gsum (p ^ e) D U y = b := by
  first | exact @GlobalTheory.PMonE.existsUnique_integral_gsum_eq | exact GlobalTheory.PMonE.existsUnique_integral_gsum_eq | (intros; apply GlobalTheory.PMonE.existsUnique_integral_gsum_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitBasePointAdjoinTwistedSigmaStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_basePoint_adjoin_twisted_sigma : ∀ (K : UQ) (B : InvAlg K), B.g * B.σ B.g = 1 → B.P.Separable → IsIntegral K.O B.g → ∀ (ε : B.A), (ε = 1 ∨ ε = -1) → ∃ β₀ : B.Aˣ, B.σ (β₀ : B.A) = β₀ * (ε * B.g) ∧ (β₀ : B.A) ∈ Algebra.adjoin K.O {B.g} ∧ ((β₀⁻¹ : B.Aˣ) : B.A) ∈ Algebra.adjoin K.O {B.g} := by
  first | exact @GlobalTheory.UnitLemma.UnitBase.exists_unit_base | exact GlobalTheory.UnitLemma.UnitBase.exists_unit_base | (intros; apply GlobalTheory.UnitLemma.UnitBase.exists_unit_base <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUnitSigmaEqMulHilbert90InvAlgStatement
section
open GlobalTheory.UnitLemma Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_sigma_eq_mul_invAlg : ∀ (K : UQ) (B : InvAlg K) (u : B.A), u * B.σ u = 1 → ∃ β : B.Aˣ, B.σ (β : B.A) = β * u := by
  first | exact @GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma | exact GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma | (intros; apply GlobalTheory.UnitLemma.HilbertNinety.exists_unit_sigma <;> assumption)
end

