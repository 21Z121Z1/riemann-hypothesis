import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CycDim
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0040
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.Intersections.FunFieldLeLocRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0042

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.CompsDim
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing IsMultiHomog IsMultiHomogIdeal IsRelevant IsMultiProjPrime
  blockWeight)

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

omit [∀ k, Fintype (ι k)] in

theorem relDim_of_isProjVar {P : Ideal (MRing ι ℂ)} {e : ℕ} (h : IsProjVar P e) :
    GroundTheory.Heights₂.Heights.FieldNumbers.relDim P = (e : ℕ) := by
  rw [GroundTheory.Heights₂.Heights.FieldNumbers.relDim_of_ringKrullDim_eq P _ h.2]
  show ((((e + Fintype.card K : ℕ) : ℤ) - Fintype.card K : ℤ) : WithBot (WithTop ℤ)) =
    (((e : ℕ) : ℤ) : WithBot (WithTop ℤ))
  congr 1
  push_cast
  ring

theorem isProjVar_of_mem_comps {P : Ideal (MRing ι ℂ)} {e : ℕ} {s : MRing ι ℂ} {c : K → ℕ}
    (hP : IsProjVar P (e + 1)) (hs : IsMultiHomog s c) (hsP : s ∉ P) {W : Ideal (MRing ι ℂ)}
    (hW : W ∈ comps P s) : IsProjVar W e := by
  obtain ⟨hmin, hrel⟩ := hW
  have hWh : IsMultiHomogIdeal W := (GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff W).mpr
    (ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes
      ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomogIdeal_iff P).mp hP.1.multiHomog)
      ((GroundTheory.Heights₂.Heights.Bridge.isMultiHomog_iff s c).mp hs) hmin)
  refine ⟨⟨hmin.1.1, hWh, hrel⟩, ?_⟩
  have := hP.1.isPrime
  have hPd := hP.2
  have key : ringKrullDim (MRing ι ℂ ⧸ W) + 1 = ringKrullDim (MRing ι ℂ ⧸ P) :=
    ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_dim_quot_minimal_add_one hsP hmin (fun h => by
      rw [hPd] at h
      exact ENat.natCast_ne_top _ (WithBot.coe_injective h))
  rw [hPd, show e + 1 + Fintype.card K = (e + Fintype.card K) + 1 by ring] at key
  exact ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_withBot_eq_of_add_one key

omit [∀ k, Fintype (ι k)] in

theorem exists_form {P : Ideal (MRing ι ℂ)} (hP : IsMultiProjPrime P) (c : K → ℕ) :
    ∃ s : MRing ι ℂ, IsMultiHomog s c ∧ s ∉ P := by
  choose i hi using hP.relevant
  have hpr := hP.isPrime
  refine ⟨∏ k, X ⟨k, i k⟩ ^ c k, ?_, ?_⟩
  · have h : IsWeightedHomogeneous (blockWeight ι) (∏ k, (X ⟨k, i k⟩ : MRing ι ℂ) ^ c k)
        (∑ k, c k • blockWeight ι ⟨k, i k⟩) :=
      IsWeightedHomogeneous.prod _ _ _ fun k _ => (isWeightedHomogeneous_X ℂ _ _).pow (c k)
    have hw : (∑ k, c k • blockWeight ι ⟨k, i k⟩) = c := by
      funext k'
      simp [blockWeight, Finset.sum_apply, Pi.single_apply]
    rw [hw] at h
    exact h
  · intro hm
    obtain ⟨k, -, hk⟩ := Ideal.IsPrime.prod_mem_iff.mp hm
    exact hi k (hpr.mem_of_pow_mem _ hk)

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.DetRestrictScalarsEqZero
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter

namespace pullbackBadImage_holds

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' J' : Ideal (MRing ι')} {n : ℕ}

omit [Fintype K'] in

theorem pullQ_eq_local (hv : IsBlockMap κ v) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) {x z : R.X} (hz : z ∈ R.U x) :
    pullQ R v Ψ z = fun i =>
      Ψ (segre fun p => R.lift x z (v p)) i.succ / Ψ (segre fun p => R.lift x z (v p)) 0 := by
  obtain ⟨c, hc, hzc⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  have hpt : pullPt R v z = fun p => (c ∘ κ) p.1 * R.lift x z (v p) := by
    funext p
    simp only [pullPt, hzc, Function.comp_apply, hv.2.2.1 p]
  have hpc : ∏ k, (c ∘ κ) k ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc (κ k)
  funext i
  simp only [pullQ, hpt, segre_smul, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hpc

theorem analyticAt_pullQ (hv : IsBlockMap κ v) (R : AnLogRes P' J' n)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (x : R.X) (j : Fin R.A.n)
    (hj : x ∈ (R.A.chart j).source) (h0 : Ψ (segre (pullPt R v x)) 0 ≠ 0) :
    AnalyticAt ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) := by
  classical
  set u := R.A.chart j x
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  have hu : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩
  have hl := analyticAt_lift_chart R x j hu
  have hs : AnalyticAt ℂ (fun w => segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) u := by
    refine analyticAt_pi_iff.mpr fun i => ?_
    simp only [segre]
    exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl _
  have hH : AnalyticAt ℂ (fun w => Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p))) u :=
    (LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs
  have hH0 : AnalyticAt ℂ (fun w => Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) 0) u :=
    analyticAt_pi_iff.mp hH 0
  have hne : Ψ (segre fun p => R.lift x ((R.A.chart j).symm u) (v p)) 0 ≠ 0 := by rw [hsu]; exact h0
  have hF : AnalyticAt ℂ (fun w => fun i : Fin n =>
      Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) i.succ /
        Ψ (segre fun p => R.lift x ((R.A.chart j).symm w) (v p)) 0) u :=
    analyticAt_pi_iff.mpr fun i => (analyticAt_pi_iff.mp hH i.succ).div hH0 hne
  refine hF.congr ?_
  filter_upwards [((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds hu]
    with w hw
  exact (pullQ_eq_local hv R Ψ hw.2).symm

theorem det_restrictScalars_eq_zero {m : ℕ} (f : (Fin m → ℂ) →L[ℂ] (Fin m → ℂ))
    (h : LinearMap.det (f : (Fin m → ℂ) →ₗ[ℂ] (Fin m → ℂ)) = 0) :
    (f.restrictScalars ℝ).det = 0 := by
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).mp (LinearMap.det_eq_zero_iff_ker_ne_bot.mp h)
  show LinearMap.det ((f.restrictScalars ℝ : (Fin m → ℂ) →L[ℝ] (Fin m → ℂ)) :
    (Fin m → ℂ) →ₗ[ℝ] (Fin m → ℂ)) = 0
  refine LinearMap.det_eq_zero_iff_ker_ne_bot.mpr ((Submodule.ne_bot_iff _).mpr ⟨w, ?_, hw0⟩)
  simpa using hw

end pullbackBadImage_holds

open pullbackBadImage_holds in

theorem pullbackBadImage_holds.proof : pullbackBadImage_holds.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' J' n R Ψ hv _ _ _
  classical
  let S₁ : Fin R.A.n → Set (Fin n → ℂ) := fun j => (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹'
    ({x | R.lift x x ∈ mcPts J'} ∩ {x | Ψ (segre (pullPt R v x)) 0 ≠ 0})
  let S₂ : Fin R.A.n → Set (Fin n → ℂ) := fun j => {u | u ∈ (R.A.chart j).target ∧
    Ψ (segre (pullPt R v ((R.A.chart j).symm u))) 0 ≠ 0 ∧
    LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0}
  have hsub : pullQ R v Ψ '' (pullBad R v Ψ ∩ {x | Ψ (segre (pullPt R v x)) 0 ≠ 0}) ⊆
      ⋃ j, ((pullQ R v Ψ ∘ (R.A.chart j).symm) '' S₁ j ∪
        (pullQ R v Ψ ∘ (R.A.chart j).symm) '' S₂ j) := by
    rintro _ ⟨x, ⟨hx, h0⟩, rfl⟩
    rcases hx with (hB | hz) | ⟨j, hj, hn⟩
    · obtain ⟨j, hj⟩ := R.A.cover x
      refine Set.mem_iUnion.mpr ⟨j, Or.inl ⟨R.A.chart j x, ⟨(R.A.chart j).map_source hj, ?_⟩, ?_⟩⟩
      · rw [Set.mem_preimage, (R.A.chart j).left_inv hj]; exact ⟨hB, h0⟩
      · simp [(R.A.chart j).left_inv hj]
    · exact absurd hz h0
    · have hd : LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (R.A.chart j x) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0 := by
        by_contra hd
        exact hn ⟨analyticAt_pullQ hv R Ψ x j hj h0, hd⟩
      refine Set.mem_iUnion.mpr ⟨j, Or.inr ⟨R.A.chart j x, ⟨(R.A.chart j).map_source hj, ?_, hd⟩, ?_⟩⟩
      · rw [(R.A.chart j).left_inv hj]; exact h0
      · simp [(R.A.chart j).left_inv hj]
  refine measure_mono_null hsub (measure_iUnion_null fun j => measure_union_null ?_ ?_)
  · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono Set.inter_subset_left))
        (R.null j))
    intro u hu
    have hx := (R.A.chart j).map_target hu.1
    have hcu : R.A.chart j ((R.A.chart j).symm u) = u := (R.A.chart j).right_inv hu.1
    have := analyticAt_pullQ hv R Ψ _ j hx hu.2.2
    rw [hcu] at this
    exact (this.differentiableAt.restrictScalars ℝ).differentiableWithinAt
  · refine addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (f' := fun u => (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u).restrictScalars ℝ) ?_ ?_
    · intro u hu
      have hx := (R.A.chart j).map_target hu.1
      have hcu : R.A.chart j ((R.A.chart j).symm u) = u := (R.A.chart j).right_inv hu.1
      have := analyticAt_pullQ hv R Ψ _ j hx hu.2.1
      rw [hcu] at this
      exact (this.differentiableAt.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
    · intro u hu
      exact det_restrictScalars_eq_zero _ hu.2.2

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsIntValuationLtOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityValuationCentre.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsMultiProjPrime P → ∀ (Γ : Type) [LinearOrderedCommGroupWithZero Γ] (v : Valuation (funField P) Γ) (n : ℤ),
    v (n : funField P) < 1 →
    ∃ W : Ideal (MRing ι), IsMultiProjPrime W ∧ P ≤ W ∧ C n ∈ W ∧
      ∀ z : funField P, (z : FractionRing (MRing ι ⧸ P)) ∈ locRing P W → v z ≤ 1

theorem RegularityValuationCentre.exists_int_valuation_lt_one {F : Type*} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) :
    ∃ n : ℤ, n ≠ 0 ∧ v.valuation F (n : F) < 1 := by
  obtain ⟨x, hxv, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.ne_bot
  have hc : v.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers F)) ≠ ⊥ :=
    Ideal.comap_ne_bot_of_integral_mem hx0 hxv (Algebra.IsIntegral.isIntegral x)
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc
  refine ⟨n, hn0, ?_⟩
  have e : (n : F) = algebraMap (NumberField.RingOfIntegers F) F (algebraMap ℤ _ n) := by simp
  rw [e, IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem]
  exact hn

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ExistsSheetPullW
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter

namespace pullbackDensity_holds

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' J' : Ideal (MRing ι')} {n : ℕ}
  (R : AnLogRes P' J' n) (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ))

omit [Fintype K'] in

theorem pullQ_eq_local (hv : IsBlockMap κ v) {x z : R.X} (hz : z ∈ R.U x) :
    pullQ R v Ψ z = fun i => Ψ (segre (fun p => R.lift x z (v p))) i.succ /
      Ψ (segre (fun p => R.lift x z (v p))) 0 := by
  obtain ⟨c, hc, hzc⟩ := R.compat z x z ⟨R.mem_U z, hz⟩
  have hpt : pullPt R v z = fun p => c (κ p.1) * R.lift x z (v p) := by
    funext p
    simp only [pullPt, hzc, hv.2.2.1 p]
  have hpc : ∏ k, c (κ k) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun k _ => hc (κ k)
  have hsm := segre_smul (fun k => c (κ k)) (fun p => R.lift x z (v p))
  funext i
  simp only [pullQ, hpt, hsm, map_smul, Pi.smul_apply, smul_eq_mul]
  exact mul_div_mul_left _ _ hpc

theorem exists_sheet_pullW (hv : IsBlockMap κ v) (hP : IsArithVar (imageZ v P') (n + 1))
    (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (A : HermLine ι) (A' : HermLine ι') (s : MRing ι)
    (hL : ∀ j, IsSmoothHerm (L j)) (hLL' : ∀ j, IsPullHerm κ v (L j) (L' j)) (hAA' : IsPullHerm κ v A A')
    (hs : IsSectionOn (imageZ v P') A s) (x : R.X) (hx : x ∉ pullBad R v Ψ) :
    ∃ γ : (Fin n → ℂ) → (Σ k, ι k) → ℂ, IsSheet (imageZ v P') Ψ (pullQ R v Ψ x) (pullW R v Ψ x) γ ∧
      logNorm A s (γ (pullQ R v Ψ x)) * maDensity (fun j y' => pot L j (γ y')) (pullQ R v Ψ x) =
        logNorm A' (rename v s) (R.lift x x) * pushDens R.A (fun j => potOf R (L' j)) (pullQ R v Ψ) x := by
  classical
  obtain ⟨k0⟩ := hP.1
  have hPh : IsMultiHomogIdeal (imageZ v P') := hP.2.1.2.1
  set j := chartIdx R.A x with hjdef
  have hj : x ∈ (R.A.chart j).source := Classical.choose_spec (R.A.cover x)
  set u := R.A.chart j x with hudef
  have hsu : (R.A.chart j).symm u = x := (R.A.chart j).left_inv hj
  have huU : u ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by rw [Set.mem_preimage, hsu]; exact R.mem_U x⟩
  have hgood : AnalyticAt ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u ∧
      LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) ≠ 0 := by
    by_contra h
    exact hx (Or.inr ⟨j, hj, h⟩)
  obtain ⟨hQa, hQd⟩ := hgood
  have h0x : Ψ (segre (pullPt R v x)) 0 ≠ 0 := fun h => hx (Or.inl (Or.inr h))
  have hmemx : pullPt R v x ∈ mcPts (imageZ v P') :=
    IntersectionWithSection.comp_mem_mcPts hv (R.mem x x (R.mem_U x))
  set Q := pullQ R v Ψ ∘ (R.A.chart j).symm with hQdef
  set Df := fderiv ℂ Q u with hDf
  have hdet : Df.det ≠ 0 := hQd
  set Ce := Df.toContinuousLinearEquivOfDetNeZero hdet with hCe
  have hCe' : (Ce : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) = Df :=
    ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero Df hdet
  have hstrict : HasStrictFDerivAt Q (Ce : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) u := by
    rw [hCe']; exact hQa.hasStrictFDerivAt
  set F := hstrict.toOpenPartialHomeomorph Q with hF
  have hFc : (F : (Fin n → ℂ) → (Fin n → ℂ)) = Q := hstrict.toOpenPartialHomeomorph_coe
  have hus : u ∈ F.source := hstrict.mem_toOpenPartialHomeomorph_source
  have hyt : Q u ∈ F.target := hstrict.image_mem_toOpenPartialHomeomorph_target
  have hσu : F.symm (Q u) = u := by
    have := F.left_inv hus
    rwa [hFc] at this
  have hy0 : Q u = pullQ R v Ψ x := by simp only [hQdef, Function.comp_apply, hsu]
  have hσa : AnalyticAt ℂ F.symm (Q u) := by
    refine F.analyticAt_symm (i := Ce) hyt ?_ ?_
    · rw [hσu, hFc]; exact hQa
    · rw [hσu, hFc, hCe']
  have hσd : HasFDerivAt F.symm (Ce.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) (Q u) := by
    refine F.hasFDerivAt_symm hyt ?_
    rw [hσu, hFc, hCe']
    exact hQa.differentiableAt.hasFDerivAt
  have hl₀ : AnalyticAt ℂ (fun w => fun p => R.lift x ((R.A.chart j).symm w) (v p)) u :=
    analyticAt_pi_iff.mpr fun p => analyticAt_pi_iff.mp (analyticAt_lift_chart R x j huU) (v p)
  set γ₀ : (Fin n → ℂ) → (Σ k, ι k) → ℂ :=
    fun y' p => R.lift x ((R.A.chart j).symm (F.symm y')) (v p) with hγ₀
  have hγ₀a : AnalyticAt ℂ γ₀ (Q u) := hl₀.comp_of_eq hσa hσu
  have hγ₀u : γ₀ (Q u) = pullPt R v x := by
    funext p
    simp only [hγ₀, hσu, hsu, pullPt]
  have hsegl : AnalyticAt ℂ (fun w => Ψ (segre (fun p => R.lift x ((R.A.chart j).symm w) (v p)))) u := by
    have hs' : AnalyticAt ℂ (fun w => segre (fun p => R.lift x ((R.A.chart j).symm w) (v p))) u := by
      refine analyticAt_pi_iff.mpr fun i => ?_
      simp only [segre]
      exact Finset.analyticAt_fun_prod _ fun k _ => analyticAt_pi_iff.mp hl₀ _
    exact (LinearMap.toContinuousLinearMap Ψ).analyticAt _ |>.comp hs'
  set ψ0 : (Fin n → ℂ) → ℂ := fun y' => Ψ (segre (γ₀ y')) 0 with hψ0
  have hψ0a : AnalyticAt ℂ ψ0 (Q u) :=
    analyticAt_pi_iff.mp (hsegl.comp_of_eq hσa hσu) 0
  have hψ0u : ψ0 (Q u) ≠ 0 := by
    simp only [hψ0, hγ₀u]; exact h0x
  set c : (Fin n → ℂ) → K → ℂ := fun y' => Function.update (fun _ => (1 : ℂ)) k0 (ψ0 y')⁻¹
    with hcdef
  have hc_ne : ∀ y', ψ0 y' ≠ 0 → ∀ k, c y' k ≠ 0 := by
    intro y' h k
    by_cases hk : k = k0
    · subst hk; simp [hcdef, h]
    · simp [hcdef, Function.update_of_ne hk]
  have hca : ∀ k, AnalyticAt ℂ (fun y' => c y' k) (Q u) := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp only [hcdef, Function.update_self]; exact hψ0a.inv hψ0u
    · simp only [hcdef, Function.update_of_ne hk]; exact analyticAt_const
  set γ : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun y' => bsmul (c y') (γ₀ y') with hγdef
  have hγa : AnalyticAt ℂ γ (Q u) :=
    analyticAt_pi_iff.mpr fun p => (hca p.1).mul (analyticAt_pi_iff.mp hγ₀a p)
  have hprod : ∀ y', ∏ k, c y' k = (ψ0 y')⁻¹ := fun y' => by
    simp [hcdef, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  have hseg : ∀ y', segre (γ y') = (ψ0 y')⁻¹ • segre (γ₀ y') := fun y' => by
    rw [← hprod y']; exact segre_smul (c y') (γ₀ y')
  refine ⟨γ, ⟨?_, ?_⟩, ?_⟩
  · rw [← hy0, hseg]
    simp only [hψ0, hγ₀u]
    rfl
  · rw [← hy0]
    have hU : ∀ᶠ y' in 𝓝 (Q u),
        F.symm y' ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
      hσa.continuousAt.preimage_mem_nhds (by
        rw [hσu]; exact ((R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x)).mem_nhds huU)
    filter_upwards [hγa.eventually_analyticAt, hU, F.open_target.mem_nhds hyt,
      hψ0a.continuousAt.eventually_ne hψ0u] with y' ha hUy ht h0
    refine ⟨ha.differentiableAt, mcPts_smul hPh (c y') (hc_ne y' h0)
      (IntersectionWithSection.comp_mem_mcPts hv (R.mem x _ hUy.2)), ?_⟩
    have hq : Q (F.symm y') = y' := by
      have := F.right_inv ht
      rwa [hFc] at this
    rw [hQdef, Function.comp_apply, pullQ_eq_local R Ψ hv hUy.2] at hq
    rw [hseg, map_smul]
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero]
      exact inv_mul_cancel₀ h0
    · simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
      rw [← congrFun hq i, div_eq_inv_mul]
  · rw [← hy0]
    obtain ⟨a, ha, hsa, -⟩ := hs
    have hlog : logNorm A s (γ (Q u)) = logNorm A' (rename v s) (R.lift x x) := by
      show logNorm A s (bsmul (c (Q u)) (γ₀ (Q u))) = _
      rw [logNorm_bsmul A ha hsa (hc_ne _ hψ0u), hγ₀u]
      unfold logNorm
      rw [hAA'.2 (R.lift x x), map_rename, eval_rename]
      rfl
    rw [hlog]
    congr 1
    have hblk : ∀ k, ∃ i, γ₀ (Q u) ⟨k, i⟩ ≠ 0 := by
      rw [hγ₀u]; exact hmemx.1
    have hH : ∀ i, cxHessian (fun y' => pot L i (γ y')) (Q u) =
        cxHessian (fun y' => pot L i (γ₀ y')) (Q u) := by
      intro i
      set G : (Fin n → ℂ) → ℂ :=
        fun y' => ((-((L i).a k0 : ℝ) : ℝ) : ℂ) * Complex.log (ψ0 y' / ψ0 (Q u)) with hG
      set C : ℝ := -(((L i).a k0 : ℝ) * Real.log ‖ψ0 (Q u)‖) with hC
      have hGa : AnalyticAt ℂ G (Q u) := by
        refine analyticAt_const.mul ((hψ0a.div analyticAt_const hψ0u).clog ?_)
        show ψ0 (Q u) / ψ0 (Q u) ∈ Complex.slitPlane
        rw [div_self hψ0u]
        exact Complex.one_mem_slitPlane
      have heq : (fun y' => pot L i (γ y')) =ᶠ[𝓝 (Q u)]
          fun y' => pot L i (γ₀ y') + (G y').re + C := by
        filter_upwards [hψ0a.continuousAt.eventually_ne hψ0u,
          hγ₀a.continuousAt.eventually (isOpen_blockNonzero.mem_nhds hblk)] with y' h0 hb
        have hpos : 0 < (L i).h (γ₀ y') := (L i).pos _ hb
        have hn0 : ‖(ψ0 y')⁻¹‖ ^ (L i).a k0 ≠ 0 :=
          zpow_ne_zero _ (norm_ne_zero_iff.mpr (inv_ne_zero h0))
        simp only [pot, hγdef]
        rw [show bsmul (c y') (γ₀ y') = fun p => c y' p.1 * γ₀ y' p from rfl,
          (L i).smul _ _ (hc_ne y' h0), prod_norm_update_zpow, Real.log_mul hn0 hpos.ne',
          hG, hC, Complex.re_ofReal_mul, Complex.log_re, norm_div,
          Real.log_div (norm_ne_zero_iff.mpr h0) (norm_ne_zero_iff.mpr hψ0u), Real.log_zpow,
          norm_inv, Real.log_inv]
        ring
      rw [cxHessian_congr heq, cxHessian_add_re (φ := fun y' => pot L i (γ₀ y')) C
        (ReciprocityTheory.ChartRestriction.G.Geo.pot_contDiffAt (hL i) hγ₀a hblk) hGa]
    have hmd : maDensity (fun i y' => pot L i (γ y')) (Q u) =
        maDensity (fun i y' => pot L i (γ₀ y')) (Q u) := by
      simp only [maDensity, hH]
    rw [hmd, maDensity_eq_maDens]
    have hcd : ∀ i, ContDiffAt ℝ 2
        (fun w => pot L i (fun p => R.lift x ((R.A.chart j).symm w) (v p))) (F.symm (Q u)) := by
      intro i
      rw [hσu]
      refine ReciprocityTheory.ChartRestriction.G.Geo.pot_contDiffAt (hL i) hl₀ ?_
      show ∀ k, ∃ i, R.lift x ((R.A.chart j).symm u) (v ⟨k, i⟩) ≠ 0
      rw [hsu]
      exact hmemx.1
    have hcomp : ReciprocityTheory.AnForm.maDens (fun i y' => pot L i (γ₀ y')) (Q u) =
        ReciprocityTheory.AnForm.maDens (fun i w => pot L i (fun p => R.lift x ((R.A.chart j).symm w) (v p)))
          (F.symm (Q u)) * Complex.normSq (ReciprocityTheory.AnForm.A.jacC F.symm (Q u)).det :=
      ReciprocityTheory.AnForm.A.maDens_comp
        (fun i w => pot L i (fun p => R.lift x ((R.A.chart j).symm w) (v p))) F.symm (Q u) hσa hcd
    have hdetinv : LinearMap.det ((Ce.symm : (Fin n → ℂ) →L[ℂ] (Fin n → ℂ)) :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) =
          (LinearMap.det (Df : (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)))⁻¹ := by
      have := ContinuousLinearEquiv.det_coe_symm Ce
      rw [hCe'] at this
      exact this
    have hloc : ReciprocityTheory.AnForm.maDens
        (fun i w => pot L i (fun p => R.lift x ((R.A.chart j).symm w) (v p))) u =
          locDens R.A (fun i => potOf R (L' i)) j u := by
      unfold locDens
      rw [hsu]
      congr 1
      funext i w
      show Real.log ((L i).h _) = Real.log ((L' i).h _)
      rw [(hLL' i).2]
    rw [hcomp, hσu, ReciprocityTheory.AnForm.A.det_jacC, hσd.fderiv, hdetinv, hloc, Complex.normSq_inv,
      Complex.normSq_eq_norm_sq]
    unfold pushDens
    rw [div_eq_mul_inv]

end pullbackDensity_holds

theorem pullbackDensity_holds.proof : pullbackDensity_holds.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' J' n R Ψ L L' A A' s hv _hP' hP hΨ hL hLL' hA hAA' hs
  filter_upwards [sheetIndep K ι (imageZ v P') n Ψ L A s hP hΨ hL hA hs] with y hind
  intro x hx
  obtain ⟨γ, hγ, hval⟩ := pullbackDensity_holds.exists_sheet_pullW R Ψ hv hP L L' A A' s hL hLL' hAA' hs x hx.2
  rw [show pullQ R v Ψ x = y from hx.1] at hγ hval
  unfold sheetDensity
  rw [dif_pos ⟨γ, hγ⟩]
  exact ((hind _ _ _ (Exists.choose_spec
    (⟨γ, hγ⟩ : ∃ γ, IsSheet (imageZ v P') Ψ y (pullW R v Ψ x) γ)) hγ).trans hval).symm

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsFurtherRest
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

def PullbackEliminationOfVariable.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' J' : Ideal (MRing ι')) (n : ℕ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    IsMultiHomogIdeal J' → ¬ J' ≤ P' →
    ∃ (h : MRing ι) (a : K → ℕ), IsMultiHomog h a ∧ h ∉ imageZ v P' ∧
      ∀ z' ∈ mcPts P', z' ∈ mcPts J' → eval (fun p => z' (v p)) (map (Int.castRingHom ℂ) h) = 0

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

