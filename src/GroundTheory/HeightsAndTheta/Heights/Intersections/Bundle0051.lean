import Mathlib
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.Intersections.RegularizedCurvature
import GroundTheory.HeightsAndTheta.Heights.Intersections.AnalyticResolutionHypothesesProjectiveLine
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0045
import GroundTheory.HeightsAndTheta.Heights.Intersections.FourierIntegralBound
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0044
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0038
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0043

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PRegCurvBound
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian RegularizedCurvature MvPolynomial

theorem RegCurvBound.proof (hB : TorusInvLevi.Statement) : RegCurvBound.Statement := by
  intro K _ ι _ E t ht hE
  classical
  have hUo := isOpen_noZeroBlock (ι := ι)
  have hlogH : ∀ M : HermLine ι, IsSmoothHerm M → ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      ContDiffAt ℝ 2 (fun y => Real.log (M.h y)) z := fun M hM z hz =>
    ((hM.contDiffAt (hUo.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)).log (M.pos z hz).ne'
  set u : ((Σ k, ι k) → ℂ) → ℝ := fun y => Real.log (E.h y) + ∑ k, (-(E.a k : ℝ)) * F k y with hu
  have hu2 : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ContDiffAt ℝ 2 u z := fun z hz =>
    (levi_add_sum _ F (fun k => -(E.a k : ℝ)) (hlogH E hE z hz) (contDiffAt_F hz) 0 Finset.univ).1

  have hinv : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      u (fun p => c p.1 * z p) = u z := by
    intro c z hc hz
    have hcn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    have hF : ∀ k, F k (fun p => c p.1 * z p) = Real.log ‖c k‖ + F k z := by
      intro k
      show Real.log ((fsMetric (ι k)).ρ (c k • fun i => z ⟨k, i⟩)) =
        Real.log ‖c k‖ + Real.log ((fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩))
      rw [(fsMetric (ι k)).smul, Real.log_mul (hcn k) (rho_pos hz k).ne']
    have hh : Real.log (E.h (fun p => c p.1 * z p)) =
        ∑ k, (E.a k : ℝ) * Real.log ‖c k‖ + Real.log (E.h z) := by
      rw [E.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hcn k))
        (E.pos z hz).ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hcn k))]
      simp only [Real.log_zpow]
    rw [hu]
    show Real.log (E.h (fun p => c p.1 * z p)) + ∑ k, (-(E.a k : ℝ)) * F k (fun p => c p.1 * z p) =
      Real.log (E.h z) + ∑ k, (-(E.a k : ℝ)) * F k z
    rw [hh]
    simp only [hF, mul_add, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
    ring
  obtain ⟨C, hC⟩ := hB K ι u (fun z hz => (hu2 z hz).contDiffWithinAt) hinv

  have hΦ : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ w,
      leviForm (fun y => ∑ k, Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))) z w =
        ∑ k, ReciprocityTheory.AnForm.levi (F k) z w := by
    intro z hz w
    have h := (levi_add_sum (fun _ => (0 : ℝ)) F (fun _ => 1) contDiffAt_const (contDiffAt_F hz) w
      Finset.univ).2
    simp only [zero_add, one_mul, levi_const] at h
    exact h

  set N : ℕ := ⌈|C| + ∑ k, |(E.a k : ℝ)|⌉₊ with hN
  have hNk : ∀ k, C ≤ (E.a k : ℝ) + N := by
    intro k
    have h1 : |C| + ∑ k, |(E.a k : ℝ)| ≤ N := Nat.le_ceil _
    have h2 : |(E.a k : ℝ)| ≤ ∑ k, |(E.a k : ℝ)| :=
      Finset.single_le_sum (f := fun k => |(E.a k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h3 := le_abs_self C
    have h4 := neg_abs_le (E.a k : ℝ)
    linarith
  refine ⟨N, fun ε hε => ?_⟩
  set R : HermLine ι := regLine E t ht ε with hR
  have hRs : IsSmoothHerm R := isSmoothHerm_regLine hE hε
  intro z hz v
  have hW0 : 0 ≤ ∑ k, ReciprocityTheory.AnForm.levi (F k) z v :=
    Finset.sum_nonneg fun k _ => levi_F_nonneg hz k v

  have hLW : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log (E.h y)) z v +
      N * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
    have hs := levi_add_sum u F (fun k => (E.a k : ℝ)) (hu2 z hz) (contDiffAt_F hz) v Finset.univ
    have hfun : (fun y => u y + ∑ k, (E.a k : ℝ) * F k y) = fun y => Real.log (E.h y) := by
      funext y
      simp only [hu, neg_mul, Finset.sum_neg_distrib]
      ring
    rw [hfun] at hs
    have hC' : |ReciprocityTheory.AnForm.levi u z v| ≤ C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [← hΦ z hz v]
      exact hC z hz v
    have hsum : 0 ≤ ∑ k, ((E.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by linarith [hNk k]) (levi_F_nonneg hz k v)
    have hexp : ∑ k, (E.a k : ℝ) * ReciprocityTheory.AnForm.levi (F k) z v + N * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v =
        ∑ k, ((E.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v +
          C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h5 := neg_abs_le (ReciprocityTheory.AnForm.levi u z v)
    rw [hs.2]
    linarith

  have hΦ1 : ContDiffAt ℝ 2 (fun y => Real.log (E.h y) + 1 * Real.log (R.h y)) z :=
    (hlogH E hE z hz).add (contDiffAt_const.mul (hlogH R hRs z hz))
  obtain ⟨μ, hμ0, hμ1, hμ⟩ := levi_logSum (h := E.h)
    (T := fun y => eval y (map (Int.castRingHom ℂ) t))
    (Φ := fun y => Real.log (E.h y) + 1 * Real.log (R.h y)) (hlogH E hE z hz)
    (by filter_upwards [hUo.mem_nhds hz] with y hy; exact E.pos y hy) (analyticAt_eval_map t z) hε hΦ1
    (fun y => by rw [hR, log_regLine_h, secNorm, one_mul]) v

  have hs := levi_add_sum (fun y => Real.log (E.h y) + 1 * Real.log (R.h y)) F (fun _ => (N : ℝ)) hΦ1
    (contDiffAt_F hz) v Finset.univ
  have hev : (fun y => Real.log (((E.tensor R).tensor
      (HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun _ => (N : ℤ)))).h y)) =ᶠ[𝓝 z]
      fun y => (Real.log (E.h y) + 1 * Real.log (R.h y)) + ∑ k, (N : ℝ) * F k y := by
    filter_upwards [hUo.mem_nhds hz] with y hy
    show Real.log ((E.h y * R.h y) * ∏ k, (fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩) ^ ((N : ℤ))) = _
    rw [Real.log_mul (mul_pos (E.pos y hy) (R.pos y hy)).ne'
        (Finset.prod_pos fun k _ => zpow_pos (rho_pos hy k) _).ne',
      Real.log_mul (E.pos y hy).ne' (R.pos y hy).ne',
      Real.log_prod (fun k _ => (zpow_pos (rho_pos hy k) _).ne')]
    simp only [Real.log_zpow, F, Int.cast_natCast, one_mul]
  rw [laplacian_line_eq_levi (hs.1.congr_of_eventuallyEq hev) v, ReciprocityTheory.AnForm.levi_congr hev v, hs.2,
    ← Finset.mul_sum]
  have hmu : 0 ≤ μ * ReciprocityTheory.AnForm.levi (fun y => Real.log (E.h y)) z v +
      N * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
    rcases le_or_gt 0 (ReciprocityTheory.AnForm.levi (fun y => Real.log (E.h y)) z v) with hL0 | hL0
    · exact add_nonneg (mul_nonneg hμ0 hL0) (mul_nonneg (Nat.cast_nonneg _) hW0)
    · nlinarith
  linarith

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PZIntAdd
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open ReciprocityTheory.AnForm.M Topology
open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

theorem locDens_congr_germ {n : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas n X)
    (Φ Ψ : Fin n → LocPot X) (j : Fin A.n) (y : Fin n → ℂ)
    (h : ∀ k, (fun y' => (Φ k).φ ((A.chart j).symm y) ((A.chart j).symm y')) =ᶠ[𝓝 y]
      (fun y' => (Ψ k).φ ((A.chart j).symm y) ((A.chart j).symm y'))) :
    locDens A Φ j y = locDens A Ψ j y := by
  unfold locDens ReciprocityTheory.AnForm.maDens
  congr 3
  funext k
  exact ReciprocityTheory.AnForm.M.PLAux.hessC_congr_eventuallyEq (h k)

theorem ZIntAdd.proof : ZIntAdd.Statement := by
  intro K _ _ ι _ P e L A B hP hR hL hA hB
  unfold zInt
  rw [dif_pos hR, dif_pos hR, dif_pos hR]
  set R := hR.some
  unfold Res.int
  have hpA := R.isPotential_pot (isSmoothPot_logH hA)
  have hpB := R.isPotential_pot (isSmoothPot_logH hB)
  have hpL : ∀ j, IsPotential R.atlas (R.pot (logH (L j))) :=
    fun j => R.isPotential_pot (isSmoothPot_logH (hL j))
  have hcons : ∀ Q : LocPot R.R.M, IsPotential R.atlas Q →
      ∀ i, IsPotential R.atlas ((Fin.cons Q fun j => R.pot (logH (L j)) :
        Fin (e + 1) → LocPot R.R.M) i) := by
    intro Q hQ i
    cases i using Fin.cases
    · exact hQ
    · exact hpL _
  have e1 : ∀ φ0 : MCone ι → ℝ,
      mInt R.atlas (fun j => R.pot ((Fin.cons φ0 fun j => logH (L j) : Fin (e + 1) → MCone ι → ℝ) j))
        (fun x => (fun _ => (1 : ℝ)) (R.pt x)) =
      mInt R.atlas (Fin.cons (R.pot φ0) fun j => R.pot (logH (L j))) (fun _ => 1) := by
    intro φ0
    refine ReciprocityTheory.AnForm.M.PLC.mInt_congr_phi _ _ _ (fun i a b => ?_) _
    cases i using Fin.cases <;> rfl
  rw [e1, e1, e1, ← mIntAdd R.atlas (R.pot (logH A)) (R.pot (logH B)) _ hpA hpB hpL _
    (mIntegrableCont _ _ (hcons _ hpA) _ continuous_const)
    (mIntegrableCont _ _ (hcons _ hpB) _ continuous_const)]
  refine ReciprocityTheory.AnForm.M.PLAux.mInt_congr fun j y hy => ?_
  congr 1
  refine locDens_congr_germ _ _ _ j y fun k => ?_
  cases k using Fin.cases
  · set x0 := (R.atlas.chart j).symm y
    have hopen : (R.atlas.chart j).target ∩ (R.atlas.chart j).symm ⁻¹' R.R.src (R.idx x0) ∈ 𝓝 y :=
      ((R.atlas.chart j).continuousOn_symm.isOpen_inter_preimage (R.atlas.chart j).open_target
        (R.R.isOpen_alt_bis _)).mem_nhds ⟨hy, R.mem_src_idx x0⟩
    filter_upwards [hopen] with y' hy'
    have hz : ∀ k, ∃ i, R.liftAt x0 ((R.atlas.chart j).symm y') ⟨k, i⟩ ≠ 0 := (R.liftAt_mem hy'.2).1
    show Real.log (A.h _ * B.h _) = Real.log (A.h _) + Real.log (B.h _)
    exact Real.log_mul (A.pos _ hz).ne' (B.pos _ hz).ne'
  · rfl

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ProjectionPullbackZeroSetNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M
  Topology Filter Set

namespace pullbackPushforward_holds

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
  {P' J' : Ideal (MRing ι')} {n : ℕ} (R : AnLogRes P' J' n) {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')}

theorem orbit_subsingleton (t : (Σ k', ι' k') → ℂ) :
    {x : R.X | R.lift x x ∉ mcPts J' ∧ SameOrbit (R.lift x x) t}.Subsingleton := by
  rintro x ⟨hx, hxt⟩ x' ⟨-, hx't⟩
  exact R.inj x x' hx (sameOrbit_tr hxt (sameOrbit_comm hx't))

theorem not_flat_pull (hGen : BlockGenFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Φ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΦ : IsGoodProj (imageZ v P') Φ)
    (j : Fin R.A.n) {O : Set (Fin n → ℂ)} (hO : IsOpen O) (hOt : O ⊆ (R.A.chart j).target)
    (hne : O.Nonempty) (h0 : ∀ u ∈ O, Φ (segre (pullPt R v ((R.A.chart j).symm u))) 0 ≠ 0)
    (han : AnalyticOnNhd ℂ (pullQ R v Φ ∘ (R.A.chart j).symm) O)
    (hdet : ∀ u ∈ O, LinearMap.det (fderiv ℂ (pullQ R v Φ ∘ (R.A.chart j).symm) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0) : False := by
  classical
  obtain ⟨f, a, hf, hfP, hfin⟩ := hGen K ι K' ι' κ v P' n hv hP' hP
  set O' := O ∩ ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∉ mcPts J'}) ∩
    ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) ≠ 0}) with hO'def
  have hO' : IsOpen O' := (hO.inter (isOpen_chart_notB R j)).inter (isOpen_chart_ne R hf j)
  have hne' : O'.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    have hsub : O ⊆ ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∈ mcPts J'}) ∪
        ((R.A.chart j).target ∩
          (R.A.chart j).symm ⁻¹' {x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) = 0}) := by
      intro u hu
      by_cases hB : R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u) ∈ mcPts J'
      · exact Or.inl ⟨hOt hu, hB⟩
      by_cases hF : eval (R.lift ((R.A.chart j).symm u) ((R.A.chart j).symm u))
          (map (Int.castRingHom ℂ) f) = 0
      · exact Or.inr ⟨hOt hu, hF⟩
      have : u ∈ O' := ⟨⟨hu, hOt hu, hB⟩, hOt hu, hF⟩
      rw [h] at this
      exact absurd this (Set.notMem_empty u)
    exact (hO.measure_pos volume hne).ne'
      (measure_mono_null hsub (measure_union_null (R.null j) (fzero_null R hP' hf hfP j)))
  obtain ⟨y, hy⟩ := exists_infinite_fibre hO' hne' (han.mono fun u hu => hu.1.1)
    (fun u hu => hdet u hu.1.1)
  have hSinf : ((R.A.chart j).symm '' (O' ∩ (pullQ R v Φ ∘ (R.A.chart j).symm) ⁻¹' {y})).Infinite :=
    Set.Infinite.image ((R.A.chart j).symm.injOn.mono fun u hu => hu.1.1.2.1) hy
  have hF := fibreFinite K ι (imageZ v P') n Φ hP hΦ y
  choose! uw huw using fun w (hw : w ∈ fibre (imageZ v P') Φ y) => hw
  choose T hT using fun w => hfin (uw w)
  refine hSinf ((hF.biUnion fun w _ => (T w).finite_toSet.biUnion fun t _ =>
    (orbit_subsingleton R t).finite).subset ?_)
  rintro _ ⟨u, ⟨huO', hqu⟩, rfl⟩
  set x := (R.A.chart j).symm u
  have hxB : R.lift x x ∉ mcPts J' := huO'.1.2.2
  have hxf : eval (R.lift x x) (map (Int.castRingHom ℂ) f) ≠ 0 := huO'.2.2
  have h0x : Φ (segre (pullPt R v x)) 0 ≠ 0 := h0 u huO'.1.1
  have hqx : pullQ R v Φ x = y := hqu
  have hw := IntersectionWithSection.pullW_mem_fibre hv hP R Φ h0x
  rw [hqx] at hw
  obtain ⟨hu1, hu2, -⟩ := huw _ hw
  have hso : SameOrbit (pullPt R v x) (uw (pullW R v Φ x)) :=
    sameOrbit_of_segre hu1.1 (Φ (segre (pullPt R v x)) 0) h0x
      (by rw [hu2]; simp [pullW, smul_smul, mul_inv_cancel₀ h0x])
  obtain ⟨t, ht, hxt⟩ := hT (pullW R v Φ x) (R.lift x x) (R.mem x x (R.mem_U x)) hxf hso
  exact Set.mem_biUnion hw (Set.mem_biUnion (Finset.mem_coe.mpr ht) ⟨hxB, hxt⟩)

theorem projection_pullback_zeroSet_null (hGen : BlockGenFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΨ : IsGoodProj (imageZ v P') Ψ)
    (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩
      (R.A.chart j).symm ⁻¹' {x | Ψ (segre (pullPt R v x)) 0 = 0}) = 0 := by
  classical
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 ⟨hu0, R.mem_U x0⟩
  set f : (Fin n → ℂ) → ℂ := fun u => Ψ (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0
    with hfdef
  have hfa : AnalyticOnNhd ℂ f V := fun u hu =>
    analyticAt_pi_iff.mp (analyticAt_segre_pull R (v := v) Ψ x0 j hu) 0
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, f, hfa.mono hball, ?_, ?_⟩
  · by_contra hall
    push Not at hall
    have hgood := hΨ _ (IntersectionWithSection.comp_mem_mcPts hv (R.mem x0 x0 (R.mem_U x0)))
    obtain ⟨i0, hi0⟩ : ∃ i0, Ψ (segre (pullPt R v x0)) i0 ≠ 0 := by
      by_contra h
      push Not at h
      exact hgood (funext h)
    have hi0ne : i0 ≠ 0 := by
      rintro rfl
      exact hi0 (hall u0 (Metric.mem_ball_self hr))
    set m : Fin n := i0.pred hi0ne
    have hm : m.succ = i0 := Fin.succ_pred i0 hi0ne
    set Ψ' : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
      (LinearMap.funLeft ℂ ℂ (Equiv.swap (0 : Fin (n + 1)) i0)).comp Ψ with hΨ'def
    have hΨ'app : ∀ w i, Ψ' w i = Ψ w (Equiv.swap 0 i0 i) := fun w i => rfl
    have hΨ' : IsGoodProj (imageZ v P') Ψ' := by
      intro z hz h
      refine hΨ z hz (funext fun i => ?_)
      have := congrFun h (Equiv.swap 0 i0 i)
      rw [hΨ'app, Equiv.swap_apply_self] at this
      exact this
    have hg'c : ContinuousOn (fun u => Ψ' (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0)
        (Metric.ball u0 r) := fun u hu =>
      (analyticAt_pi_iff.mp (analyticAt_segre_pull R (v := v) Ψ' x0 j (hball hu)) 0).continuousAt.continuousWithinAt
    set O := Metric.ball u0 r ∩
      (fun u => Ψ' (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0) ⁻¹' {0}ᶜ with hOdef
    have hO : IsOpen O := hg'c.isOpen_inter_preimage Metric.isOpen_ball isOpen_compl_singleton
    have hu0O : u0 ∈ O := by
      refine ⟨Metric.mem_ball_self hr, ?_⟩
      show Ψ' (segre (pullPt R v x0)) 0 ≠ 0
      rw [hΨ'app, Equiv.swap_apply_left]
      exact hi0
    have h0O : ∀ u ∈ O, Ψ' (segre (pullPt R v ((R.A.chart j).symm u))) 0 ≠ 0 := by
      intro u hu
      obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv (hball hu.1).2)
      rw [hμeq, map_smul, Pi.smul_apply, smul_eq_mul]
      exact mul_ne_zero hμ hu.2
    have hanO : AnalyticOnNhd ℂ (pullQ R v Ψ' ∘ (R.A.chart j).symm) O := by
      intro u hu
      have := analyticAt_pullQ R hv Ψ' _ j ((R.A.chart j).map_target (hball hu.1).1) (h0O u hu)
      rwa [(R.A.chart j).right_inv (hball hu.1).1] at this
    have hzero : ∀ u ∈ O, (pullQ R v Ψ' ∘ (R.A.chart j).symm) u m = 0 := by
      intro u hu
      simp only [Function.comp_apply, pullQ]
      rw [hm, hΨ'app, Equiv.swap_apply_right]
      obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv (hball hu.1).2)
      rw [hμeq, map_smul, Pi.smul_apply, smul_eq_mul]
      have : f u = 0 := hall u hu.1
      simp only [hfdef] at this
      rw [this, mul_zero, zero_div]
    have hdetO : ∀ u ∈ O, LinearMap.det (fderiv ℂ (pullQ R v Ψ' ∘ (R.A.chart j).symm) u :
        (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0 := by
      intro u hu
      have hcoord : (fun w => (pullQ R v Ψ' ∘ (R.A.chart j).symm) w m) =ᶠ[𝓝 u] fun _ => 0 := by
        filter_upwards [hO.mem_nhds hu] with w hw
        exact hzero w hw
      have hd : HasFDerivAt (fun w => (pullQ R v Ψ' ∘ (R.A.chart j).symm) w m)
          ((ContinuousLinearMap.proj m).comp (fderiv ℂ (pullQ R v Ψ' ∘ (R.A.chart j).symm) u)) u :=
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n => ℂ) m).hasFDerivAt.comp u
          (hanO u hu).differentiableAt.hasFDerivAt
      have hd0 : HasFDerivAt (fun w => (pullQ R v Ψ' ∘ (R.A.chart j).symm) w m)
          (0 : (Fin n → ℂ) →L[ℂ] ℂ) u :=
        (hasFDerivAt_const (0 : ℂ) u).congr_of_eventuallyEq hcoord
      have hrow := hd.unique hd0
      refine det_eq_zero_of_coord m fun w => ?_
      have := congrArg (fun T : (Fin n → ℂ) →L[ℂ] ℂ => T w) hrow
      simpa using this
    exact not_flat_pull R hGen hv hP' hP Ψ' hΨ' j hO (fun u hu => (hball hu.1).1) ⟨u0, hu0O⟩ h0O
      hanO hdetO
  · rintro w ⟨⟨-, hw0⟩, hwb⟩
    obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv (hball hwb).2)
    have h := congrArg (fun s => Ψ s 0) hμeq
    simp only [map_smul, Pi.smul_apply, smul_eq_mul] at h
    have hw0' : Ψ (segre (pullPt R v ((R.A.chart j).symm w))) 0 = 0 := hw0
    rw [hw0'] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hμ

theorem ram_pull_null (hGen : BlockGenFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΨ : IsGoodProj (imageZ v P') Ψ)
    (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | Ψ (segre (pullPt R v x)) 0 ≠ 0 ∧
      ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0}) = 0 := by
  apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
  rintro u0 ⟨hu0, h00, -⟩
  set x0 := (R.A.chart j).symm u0
  set V := (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x0 with hVdef
  have hV : IsOpen V := (R.A.chart j).isOpen_inter_preimage_symm (R.isOpen_U x0)
  have hgc : ContinuousOn (fun u => Ψ (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0) V :=
    fun u hu => (analyticAt_pi_iff.mp (analyticAt_segre_pull R (v := v) Ψ x0 j hu) 0).continuousAt.continuousWithinAt
  set O := V ∩ (fun u => Ψ (segre (fun p => R.lift x0 ((R.A.chart j).symm u) (v p))) 0) ⁻¹' {0}ᶜ
    with hOdef
  have hO : IsOpen O := hgc.isOpen_inter_preimage hV isOpen_compl_singleton
  have hu0O : u0 ∈ O := ⟨⟨hu0, R.mem_U x0⟩, h00⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO u0 hu0O
  have h0 : ∀ u ∈ Metric.ball u0 r, Ψ (segre (pullPt R v ((R.A.chart j).symm u))) 0 ≠ 0 := by
    intro u hu
    obtain ⟨μ, hμ, hμeq⟩ := segre_of_sameOrbit (pullPt_sameOrbit R hv (hball hu).1.2)
    rw [hμeq, map_smul, Pi.smul_apply, smul_eq_mul]
    exact mul_ne_zero hμ (hball hu).2
  have hQa : AnalyticOnNhd ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) (Metric.ball u0 r) := by
    intro u hu
    have := analyticAt_pullQ R hv Ψ _ j ((R.A.chart j).map_target (hball hu).1.1) (h0 u hu)
    rwa [(R.A.chart j).right_inv (hball hu).1.1] at this
  refine ⟨Metric.ball u0 r, Metric.isOpen_ball, Metric.mem_ball_self hr,
    (convex_ball u0 r).isPreconnected, fun u => LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) u :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)), fun u hu => analyticAt_det_fderiv (hQa u hu), ?_, ?_⟩
  · by_contra hall
    push Not at hall
    exact not_flat_pull R hGen hv hP' hP Ψ hΨ j Metric.isOpen_ball (fun u hu => (hball hu).1.1)
      ⟨u0, Metric.mem_ball_self hr⟩ h0 hQa hall
  · rintro w ⟨⟨hwt, hw0, k, hk, hdk⟩, -⟩
    have := det_pullQ_chart R hv Ψ (j := j) ((R.A.chart j).map_target hwt) hk hw0
    rw [(R.A.chart j).right_inv hwt] at this
    show LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart j).symm) w :
      (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0
    rw [this, hdk, zero_mul]

theorem pullBad_null (hGen : BlockGenFinite.Statement) (hv : IsBlockMap κ v)
    (hP' : IsArithVar P' (n + 1)) (hP : IsArithVar (imageZ v P') (n + 1))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)) (hΨ : IsGoodProj (imageZ v P') Ψ)
    (j : Fin R.A.n) :
    volume ((R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' pullBad R v Ψ) = 0 := by
  have h3 : pullBad R v Ψ ⊆ {x | R.lift x x ∈ mcPts J'} ∪ {x | Ψ (segre (pullPt R v x)) 0 = 0} ∪
      {x | Ψ (segre (pullPt R v x)) 0 ≠ 0 ∧ ∃ k, x ∈ (R.A.chart k).source ∧
        LinearMap.det (fderiv ℂ (pullQ R v Ψ ∘ (R.A.chart k).symm) (R.A.chart k x) :
          (Fin n → ℂ) →ₗ[ℂ] (Fin n → ℂ)) = 0} := by
    rintro x ((h | h) | ⟨k, hk, hn⟩)
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · by_cases h0 : Ψ (segre (pullPt R v x)) 0 = 0
      · exact Or.inl (Or.inr h0)
      · refine Or.inr ⟨h0, k, hk, ?_⟩
        by_contra hd
        exact hn ⟨analyticAt_pullQ R hv Ψ x k hk h0, hd⟩
  refine measure_mono_null (Set.inter_subset_inter_right _ (Set.preimage_mono h3)) ?_
  simp only [Set.preimage_union, Set.inter_union_distrib_left]
  exact measure_union_null (measure_union_null (R.null j) (projection_pullback_zeroSet_null R hGen hv hP' hP Ψ hΨ j))
    (ram_pull_null R hGen hv hP' hP Ψ hΨ j)

end pullbackPushforward_holds

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PtsOverChart
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

section Over

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

def ptsOverChart (P' : Ideal (MRing ι')) (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k'))
    (j : ∀ k : FibreBlock κ, ι' k.1) (z : (Σ k, ι k) → ℂ) : Set (Set ((Σ k', ι' k') → ℂ)) :=
  {O | ∃ z' ∈ mcPts P', O = {z'' | SameOrbit z'' z'} ∧ SameOrbit (fun p => z' (v p)) z ∧
    ∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ ≠ 0}

end Over

def GenericPointsInAffineChart.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (j : ∀ k : FibreBlock κ, ι' k.1),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
    (∀ k : FibreBlock κ, G.x' ⟨k.1, j k⟩ ≠ 0) →
    ∃ (D : MRing ι) (a : K → ℕ), IsMultiHomog D a ∧ D ∉ imageZ v P' ∧
      ∀ z ∈ mcPts (imageZ v P'), eval z (map (Int.castRingHom ℂ) D) ≠ 0 →
        (ptsOverChart P' κ v j z).Finite ∧
        (ptsOverChart P' κ v j z).ncard = Module.finrank G.Φ (IntermediateField.adjoin G.Φ
          (Set.range fun q : Σ k : FibreBlock κ, ι' k.1 => G.x' ⟨q.1.1, q.2⟩ / G.x' ⟨q.1.1, j q.1⟩)) ∧
        ∀ z' ∈ mcPts P', SameOrbit (fun p => z' (v p)) z → (∀ k : FibreBlock κ, z' ⟨k.1, j k⟩ ≠ 0) →
          ∀ q : Σ k : FibreBlock κ, ι' k.1, G.x' ⟨q.1.1, q.2⟩ ≠ 0 → z' ⟨q.1.1, q.2⟩ ≠ 0

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.StZIntPoint
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open GroundTheory.Heights₂.Heights.NumbersDVR (MRing)

def ZIntPoint.Statement : Prop :=
  ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (P : Ideal (MRing ι ℂ)) (φ : Fin 0 → MCone ι → ℝ),
    IsProjVar P 0 → Nonempty (Res ι P 0) → zInt P 0 φ (fun _ => 1) = 1

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

