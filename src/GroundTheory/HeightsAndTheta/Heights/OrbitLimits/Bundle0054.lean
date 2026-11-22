import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Assembly
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartDim
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0021
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0018
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0039
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PPtsIntegralSegreChartProj
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G.Geo (ptsIntegralAt)
open ComplexSets

theorem PtsIntegralSegreChartProj.proof (hFin : SegreChartProjFinite.Statement)
    (hZero : SegreChartZeroSet.Statement) (hAbs : SegreChartAbsIntegrable.Statement)
    (hSum : PtsSegreChartFibreSum.Statement) : PtsIntegralSegreChartProj.Statement := by
  intro K _ _ ι _ P e m σ i L g Ψ G Φ hP hL hg hΨ hΨ0 hgerm
  set A := chartProjMatrix σ Ψ
  set G' := chartWeight σ i g with hG'
  set Φ' := chartPot σ i L
  have hcoordS : ∀ x ∈ segreChartSet P σ i, x (σ.symm i) = 1 := by
    rintro _ ⟨z, -, hzi, rfl⟩
    simpa using hzi
  have hchart : ∀ J ∈ segreChartComponents P σ i, zeroSet J ⊆ segreChartSet P σ i := by
    intro J hJ x hx
    rw [← hZero K ι P m σ i hP.2.1.2.1]
    exact fun q hq => hx q ((mem_segreChartComponents.1 hJ).1.2 hq)
  have hprime : ∀ J ∈ segreChartComponents P σ i, J.IsPrime := fun J hJ =>
    (mem_segreChartComponents.1 hJ).1.1
  have hdim : ∀ J ∈ segreChartComponents P σ i,
      ringKrullDim (MvPolynomial (Fin m) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) := fun J hJ =>
    SegreChartDim.proof K ι P (e + 1) m σ i hP J hJ
  have hfin : ∀ J ∈ segreChartComponents P σ i, IsFiniteProjection J A :=
    hFin K ι P (e + 1) m σ i Ψ hP hΨ hΨ0
  have hmeas : Measurable G' := measurable_chartWeight σ i hg
  have hsm : ∀ J ∈ segreChartComponents P σ i, ∀ k, SmoothNear (zeroSet J) (Φ' k) := fun J hJ =>
    smoothNear_chartPot σ i hL fun x hx => chart_coord_eq_one hJ hx
  have habs : ∀ J ∈ segreChartComponents P σ i, Integrable (chartAbsDens J A G' Φ') := fun J hJ =>
    hAbs K ι P (e + 1) m σ i L g hP hL hg J hJ A (hfin J hJ)
  have hint : ∀ J ∈ segreChartComponents P σ i, Integrable (chartDens J A G' Φ') := by
    intro J hJ
    refine (habs J hJ).mono' (SheetSumMeasurable.full m (e + 1) J A G' Φ' (hprime J hJ) (hdim J hJ)
      (hfin J hJ) hmeas (hsm J hJ)).1.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs]
    unfold chartDens chartAbsDens sheetSum
    refine (abs_finsum_mem_le_finsum_mem_abs _ _).trans (le_of_eq (finsum_mem_congr rfl fun x _ => ?_))
    split_ifs <;> simp

  have hcong : ∀ J ∈ segreChartComponents P σ i, ∀ A₁ : Matrix (Fin (e + 1)) (Fin m) ℂ,
      chartDens J A₁ G Φ = chartDens J A₁ G' Φ' := by
    intro J hJ A₁
    funext y
    unfold chartDens sheetSum
    refine finsum_mem_congr rfl fun x hx => ?_
    have hxS : x ∈ segreChartSet P σ i := hchart J hJ hx.1
    split_ifs with h
    · obtain ⟨U, hU, hyU, hdiff, hsx, -, -⟩ := h.choose_spec
      have hy : A₁ *ᵥ x = y := hx.2
      have hG : G x = G' x := by
        rw [hG', chartWeight_of_coord g (hcoordS x hxS)]
        exact (hgerm x hxS).1.eq_of_nhds
      have hcont : Tendsto h.choose (𝓝 y) (𝓝 x) := by
        have := (hdiff.continuousOn.continuousAt (hU.mem_nhds hyU)).tendsto
        rwa [hsx, hy] at this
      beta_reduce
      rw [hG]
      congr 1
      exact ReciprocityTheory.AnForm.M.maDens_congr_eventuallyEq fun k => ((hgerm x hxS).2 k).comp_tendsto hcont
    · rfl

  have hvar : ∀ J ∈ segreChartComponents P σ i, varInt J (e + 1) G Φ = ∫ y, chartDens J A G' Φ' y := by
    intro J hJ
    have hex : ∃ A₁ : Matrix (Fin (e + 1)) (Fin m) ℂ, IsFiniteProjection J A₁ := ⟨A, hfin J hJ⟩
    rw [varInt, dif_pos hex, chartInt, hcong J hJ]
    exact (IntegralIndep.full m (e + 1) J A hex.choose G' Φ' (hprime J hJ) (hdim J hJ) (hfin J hJ)
      hex.choose_spec hmeas (hsm J hJ) (habs J hJ)).2.symm
  rw [Finset.sum_congr rfl hvar, ← integral_finsetSum _ hint]
  unfold ptsIntegralAt
  refine integral_congr_ae ?_
  filter_upwards [hSum K ι P (e + 1) m σ i L g Ψ hP hL hg hΨ hΨ0] with y hy
  exact hy

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.OrbitLimits.PSegreChartProjFinite
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsArithVar IsGoodProj mcPts segre segre_rel)
open ComplexSets MvPolynomial Matrix

theorem homogeneousComponent_mem_leadIdeal {n : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {f : MvPolynomial (Fin n) ℂ} (hf : f ∈ J) {r : ℕ} (hr : f.totalDegree ≤ r) :
    homogeneousComponent r f ∈ leadIdeal J := by
  rcases hr.eq_or_lt with h | h
  · rw [← h]
    exact Ideal.subset_span ⟨f, hf, rfl⟩
  · rw [homogeneousComponent_eq_zero (n := r) (φ := f) h]
    exact zero_mem _

theorem eval_linPoly_eq_mulVec {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (r : Fin d) (x : Fin n → ℂ) :
    eval x (linPoly A r) = (A *ᵥ x) r := by
  simp [linPoly, Matrix.mulVec, dotProduct]

theorem SegreChartProjFinite.pow_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {e m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)}
    (hP : IsArithVar P (e + 1)) (hΨ : IsGoodProj P Ψ) (hΨ0 : ∀ w, Ψ w 0 = w i)
    {J : Ideal (MvPolynomial (Fin m) ℂ)} (hJ : J ∈ segreChartComponents P σ i) (a : Fin m) :
    ∃ r : ℕ, (X a ^ r : MvPolynomial (Fin m) ℂ) ∈ leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ) := by
  classical
  obtain ⟨r, hr, G, hG, hrel⟩ := segre_rel hP.2.1.2.1 Ψ hΨ (σ a)
  set A := chartProjMatrix σ Ψ with hA
  let Gx : Fin (e + 1) → MvPolynomial (Fin m) ℂ := fun j => rename σ.symm (G j)
  have hGx : ∀ j, (Gx j).totalDegree ≤ r - 1 := fun j => (totalDegree_rename_le _ _).trans (hG j)
  let f : MvPolynomial (Fin m) ℂ := X a ^ r - (Gx 0 + ∑ j : Fin e, Gx j.succ * linPoly A j)
  have hfJ : f ∈ J := by
    refine (mem_segreChartComponents.1 hJ).1.2 ?_
    rw [segreChartIdeal, MvPolynomial.mem_vanishingIdeal_iff]
    rintro _ ⟨z, hz, hzi, rfl⟩
    have hw : ((fun a => segre z (σ a)) ∘ σ.symm) = segre z := by
      funext i'
      simp
    have h := hrel z hz
    rw [Fin.sum_univ_succ, hΨ0, hzi, one_mul] at h
    change eval (fun a => segre z (σ a)) f = 0
    simp only [f, Gx, map_sub, map_add, map_pow, map_sum, map_mul, eval_X, eval_rename, hw,
      eval_linPoly_eq_mulVec, hA, chartProjMatrix_mulVec]
    rw [h]
    simp [Equiv.apply_symm_apply, mul_comm]
  have hdeg : f.totalDegree ≤ r := by
    refine (totalDegree_sub _ _).trans (max_le (by rw [totalDegree_X_pow]) ?_)
    refine (totalDegree_add _ _).trans (max_le ((hGx 0).trans (Nat.sub_le _ _)) ?_)
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    have h1 := hGx j.succ
    have h2 := (isHomogeneous_linPoly A j).totalDegree_le
    omega
  have h1 : 1 ≤ r := hr
  have hX : homogeneousComponent r (X a ^ r : MvPolynomial (Fin m) ℂ) = X a ^ r := by
    rw [homogeneousComponent_of_mem ((mem_homogeneousSubmodule r _).2 (isHomogeneous_X_pow a r)),
      if_pos rfl]
  have h0 : homogeneousComponent r (Gx 0) = 0 :=
    homogeneousComponent_eq_zero (n := r) (φ := Gx 0) (by have := hGx 0; omega)
  have hcomp : homogeneousComponent r f =
      X a ^ r - ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j := by
    simp only [f, map_sub, map_add, map_sum, hX, h0, zero_add,
      homogeneousComponent_mul_of_isHomogeneous_right _ _ (isHomogeneous_linPoly A _), h1, if_true]
  have hmem : homogeneousComponent r f + ∑ j : Fin e, homogeneousComponent (r - 1) (Gx j.succ) * linPoly A j ∈
      leadIdeal J ⊔ linIdeal A :=
    add_mem (Ideal.mem_sup_left (homogeneousComponent_mem_leadIdeal hfJ hdeg))
      (Ideal.mem_sup_right (Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨j, rfl⟩)))
  rw [hcomp, sub_add_cancel] at hmem
  exact ⟨r, hmem⟩

theorem SegreChartProjFinite.proof : SegreChartProjFinite.Statement := by
  intro K _ ι _ P e m σ i Ψ hP hΨ hΨ0 J hJ
  have hfin : (projHom J (chartProjMatrix σ Ψ)).toRingHom.Finite := by
    have hrad : originIdeal m ≤ (leadIdeal J ⊔ linIdeal (chartProjMatrix σ Ψ)).radical := by
      refine Ideal.span_le.2 (Set.range_subset_iff.2 fun a => ?_)
      obtain ⟨r, hr⟩ := SegreChartProjFinite.pow_mem hP hΨ hΨ0 hJ a
      exact ⟨r, hr⟩
    obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg_radical hrad (IsNoetherian.noetherian _)
    exact ConeAvoidsFinite.proof m e N J _ hN
  exact ⟨FiniteProjHomInjective.proof m e J _ (mem_segreChartComponents.1 hJ).1.1
    (SegreChartDim.proof K ι P e m σ i hP J hJ) hfin, hfin⟩

end GroundTheory.Heights₂.Heights
end
end

