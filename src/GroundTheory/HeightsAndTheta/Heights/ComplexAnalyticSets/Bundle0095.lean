import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0087
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0057
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelPlace
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0084
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0085
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StTransverseObjects

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PZeroDimIsolated
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

theorem ZeroDimIsolated.proof : ZeroDimIsolated.Statement := by
  intro n I q hdim
  classical
  have : Ring.KrullDimLE 0 (curveLocalRing I q) := Ring.krullDimLE_iff.2 (by simpa using hdim)
  have hnil : ∀ i : Fin n, ∃ s : MvPolynomial (Fin n) ℂ, eval q s ≠ 0 ∧
      ∃ k : ℕ, s * (X i - C (q i)) ^ k ∈ I := by
    intro i
    have hmem : algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) (X i - C (q i)) ∈
        Ring.jacobson (curveLocalRing I q) := by
      rw [Ring.jacobson_eq_sInf_isMaximal, Submodule.mem_sInf]
      intro P hP
      have hP' : Ideal.IsMaximal P := hP
      let π : Localization.AtPrime (RingHom.ker (eval q)) →+* curveLocalRing I q := Ideal.Quotient.mk _
      have hPm : (Ideal.comap π P).IsMaximal :=
        Ideal.comap_isMaximal_of_surjective π Ideal.Quotient.mk_surjective (H := hP')
      have hL : algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))
          (X i - C (q i)) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime (RingHom.ker (eval q))) := by
        rw [IsLocalization.AtPrime.to_map_mem_maximal_iff _ (RingHom.ker (eval q))]
        simp [RingHom.mem_ker]
      rw [← IsLocalRing.eq_maximalIdeal hPm] at hL
      exact hL
    rw [Ring.jacobson_eq_nilradical_of_krullDimLE_zero, mem_nilradical] at hmem
    obtain ⟨k, hk⟩ := hmem
    rw [← map_pow] at hk
    have hmap : algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))
        ((X i - C (q i)) ^ k) ∈
        I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q)))) :=
      Ideal.Quotient.eq_zero_iff_mem.1 hk
    obtain ⟨m, hm, hmI⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff
      (RingHom.ker (eval q)).primeCompl (Localization.AtPrime (RingHom.ker (eval q))) I _).1 hmap
    exact ⟨m, fun h ↦ hm (RingHom.mem_ker.2 h), k, hmI⟩
  choose s hs k hk using hnil
  refine ⟨{x | eval x (∏ i, s i) ≠ 0}, ?_, ?_⟩
  · apply (isOpen_ne_fun (MvPolynomial.continuous_eval _) continuous_const).mem_nhds
    simp [map_prod, Finset.prod_ne_zero_iff, hs]
  · rintro x ⟨hxZ, hxN⟩
    simp only [Set.mem_ofPred_eq, map_prod, Finset.prod_ne_zero_iff] at hxN
    rw [Set.mem_singleton_iff]
    funext i
    have h := hxZ _ (hk i)
    simp only [map_mul, map_pow, map_sub, eval_X, eval_C, mul_eq_zero, pow_eq_zero_iff', ne_eq] at h
    rcases h with h | ⟨h, -⟩
    · exact absurd h (hxN i (Finset.mem_univ i))
    · exact sub_eq_zero.1 h

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PZeroSetOpenMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology

noncomputable section

theorem exists_eval_ne_zero_of_isOpen {d : ℕ} {P : MvPolynomial (Fin d) ℂ} (hP : P ≠ 0)
    {S : Set (Fin d → ℂ)} (hS : IsOpen S) (hne : S.Nonempty) : ∃ y ∈ S, eval y P ≠ 0 := by
  obtain ⟨y₀, hy₀⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hS y₀ hy₀
  by_contra h
  push Not at h
  apply hP
  have hinf : ∀ i, (Metric.ball (y₀ i) r).Infinite := fun i =>
    infinite_of_mem_nhds (y₀ i) (Metric.ball_mem_nhds _ hr)
  refine (funext_set_iff (p := P) (q := 0) _ hinf).mpr fun y hy => ?_
  rw [map_zero]
  exact h y (hball (by rwa [ball_pi _ hr]))

theorem eval_linPoly {n d : ℕ} (A : Matrix (Fin d) (Fin n) ℂ) (z : Fin n → ℂ) :
    (fun i => eval z (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i)) = A.mulVec z := by
  ext i
  simp [GroundTheory.Heights₂.Heights.ComplexSets.linPoly, Matrix.mulVec, dotProduct]

theorem finrank_real_fin_complex (d : ℕ) : Module.finrank ℝ (Fin d → ℂ) = 2 * d := by
  rw [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    Complex.finrank_real_complex, smul_eq_mul, mul_comm]

theorem ZeroSetOpenMass.proof
    (hG : GroundTheory.Heights₂.Heights.ComplexSets.GenericProjectionFinite.Statement)
    (hD : GroundTheory.Heights₂.Heights.ComplexSets.DiscriminantCover.Statement)
    (hF : FiniteMapOpen.Statement) : ZeroSetOpenMass.Statement := by
  intro n d W hW hdim x O hO hxO hxZ
  obtain ⟨A, hA⟩ := (hG n d W hW hdim).2.1
  obtain ⟨P, hP0, hPcov⟩ := hD n d W A hW hdim hA
  have hopen := hF n d W (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A) hW hA.injective hA.finite x hxZ O
    (hO.mem_nhds hxO)
  have hfun : (fun z : Fin n → ℂ => fun i => eval z (GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i)) =
      fun z => A.mulVec z := funext (eval_linPoly A)
  rw [hfun, eval_linPoly A x] at hopen
  obtain ⟨y, hyS, hPy⟩ := exists_eval_ne_zero_of_isOpen hP0 isOpen_interior
    ⟨_, mem_interior_iff_mem_nhds.mpr hopen⟩
  obtain ⟨z, ⟨hzW, hzO⟩, hzy⟩ := interior_subset hyS
  subst hzy
  obtain ⟨-, -, hloc⟩ := hPcov _ hPy
  obtain ⟨U, V, g, hU, hzU, hV, hzV, hg, hgz, hAg, hZV⟩ := hloc z ⟨hzW, rfl⟩
  set U' := U ∩ g ⁻¹' (O ∩ V) with hU'def
  have hU' : IsOpen U' := hg.continuousOn.isOpen_inter_preimage hU (hO.inter hV)
  have hzU' : A.mulVec z ∈ U' := ⟨hzU, by simp only [Set.mem_preimage, hgz]; exact ⟨hzO, hzV⟩⟩
  have hsub : g '' U' ⊆ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ O := by
    rintro _ ⟨w, ⟨hwU, hwO, -⟩, rfl⟩
    have hw : g w ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ V := by
      rw [hZV]; exact Set.mem_image_of_mem g hwU
    exact ⟨hw.1, hwO⟩
  have himg : (fun z => A.mulVec z) '' (g '' U') = U' := by
    rw [Set.image_image]
    exact (Set.image_congr fun w hw => hAg w hw.1).trans (Set.image_id' _)
  obtain ⟨K, hK⟩ : ∃ K, LipschitzWith K (fun z : Fin n → ℂ => A.mulVec z) :=
    ⟨_, (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).lipschitz⟩
  have hpos : 0 < μH[((2 * d : ℕ) : ℝ)] U' := by
    rw [← finrank_real_fin_complex d]
    exact hU'.measure_pos _ ⟨_, hzU'⟩
  have hle := hK.hausdorffMeasure_image_le (by positivity : (0 : ℝ) ≤ ((2 * d : ℕ) : ℝ)) (g '' U')
  rw [himg] at hle
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  refine pos_iff_ne_zero.mpr fun h0 => ?_
  rw [h0, mul_zero] at hle
  exact hpos.ne' (nonpos_iff_eq_zero.mp hle)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PointLocalRingOrder
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology

noncomputable section

variable {σ : Type*}

theorem pointLocalRing_exists_mul_eq (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (x : pointLocalRing I w) :
    ∃ a s : MvPolynomial σ ℂ, eval w s ≠ 0 ∧
      x * algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) s = algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) a := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective
    (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)).primeCompl y
  refine ⟨a, s, fun h ↦ s.2 (RingHom.mem_ker.2 h), ?_⟩
  have h := congrArg (Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial σ ℂ)
    (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))))))
    (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ))) a s)
  rw [map_mul] at h
  exact h

theorem pointLocalRing_exists_mul_mem (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ) (g : MvPolynomial σ ℂ)
    (hg : algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) g = 0) :
    ∃ s : MvPolynomial σ ℂ, eval w s ≠ 0 ∧ s * g ∈ I := by
  set p := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)
  have hmem : algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) g ∈
      I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p)) :=
    Ideal.Quotient.eq_zero_iff_mem.1 hg
  obtain ⟨⟨j, s⟩, hjs⟩ := (IsLocalization.mem_map_algebraMap_iff p.primeCompl (Localization.AtPrime p)).1 hmem
  refine ⟨s, fun h ↦ s.2 (RingHom.mem_ker.2 h), ?_⟩
  have hinj := IsLocalization.injective (Localization.AtPrime p) p.primeCompl_le_nonZeroDivisors
  have : (s : MvPolynomial σ ℂ) * g = j := hinj (by rw [map_mul, mul_comm]; exact hjs)
  rw [this]
  exact j.2

theorem pointLocalRing_eval_ne_zero_of_isUnit (I : Ideal (MvPolynomial σ ℂ)) (w : σ → ℂ)
    (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn I) (u : MvPolynomial σ ℂ)
    (hu : IsUnit (algebraMap (MvPolynomial σ ℂ) (pointLocalRing I w) u)) : eval w u ≠ 0 := by
  intro h0
  set p := RingHom.ker (eval w : MvPolynomial σ ℂ →+* ℂ)
  have hle : I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p)) ≤
      IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
    rw [Ideal.map_le_iff_le_comap]
    intro g hg
    rw [Ideal.mem_comap]
    exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ g).2 (RingHom.mem_ker.2 (hw g hg))
  have hum : algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) u ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime p) :=
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ u).2 (RingHom.mem_ker.2 h0)
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective v
  have hv' : Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p)))
      (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime p) u * z) = Ideal.Quotient.mk _ 1 := by
    rw [map_mul, map_one]
    exact hv
  have hd := hle (Ideal.Quotient.eq.1 hv')
  have h1 : (1 : Localization.AtPrime p) ∈ IsLocalRing.maximalIdeal (Localization.AtPrime p) := by
    have := (IsLocalRing.maximalIdeal (Localization.AtPrime p)).sub_mem
      (Ideal.mul_mem_right z _ hum) hd
    simp at this
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1)

theorem ord_zero_eq_top_of_dvr (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] :
    Ring.ord R 0 = ⊤ := by
  rw [Ring.ord_zero]
  by_contra h
  have hfin := Module.length_ne_top_iff.1 h
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 hfin
  exact IsDiscreteValuationRing.not_isField R (IsArtinianRing.isField_of_isDomain R)

theorem ord_pow_irreducible_of_dvr {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {ϖ : R} (hϖ : Irreducible ϖ) (e : ℕ) : Ring.ord R (ϖ ^ e) = e := by
  rw [Ring.ord_pow (mem_nonZeroDivisors_of_ne_zero hϖ.ne_zero), Ring.ord_of_irreducible hϖ]
  simp

theorem differentiable_eval_pointLocal [Fintype σ] (q : MvPolynomial σ ℂ) :
    Differentiable ℂ fun z : σ → ℂ ↦ eval z q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [eval_add]; exact hp.add hq
  | mul_X p i hp => simp only [eval_mul, eval_X]; exact hp.mul (differentiable_apply i)

theorem analyticAt_eval_disc [Fintype σ] {r : ℝ} (hr : 0 < r) {φ : (Fin 1 → ℂ) → σ → ℂ}
    (hφ : DifferentiableOn ℂ φ (Metric.ball 0 r)) (g : MvPolynomial σ ℂ) :
    AnalyticAt ℂ (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) 0 := by
  have hc : DifferentiableOn ℂ (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) (Metric.ball 0 r) :=
    (differentiable_pi.2 fun _ ↦ differentiable_id).differentiableOn
  have hmaps : Set.MapsTo (fun τ : ℂ ↦ (fun _ : Fin 1 ↦ τ)) (Metric.ball 0 r) (Metric.ball 0 r) := by
    intro τ hτ
    rw [mem_ball_zero_iff] at hτ ⊢
    exact lt_of_le_of_lt (pi_norm_const_le τ) hτ
  have hd : DifferentiableOn ℂ (fun τ : ℂ ↦ eval (φ fun _ ↦ τ) g) (Metric.ball 0 r) :=
    (differentiable_eval_pointLocal g).comp_differentiableOn (hφ.comp hc hmaps)
  exact hd.analyticAt (Metric.ball_mem_nhds 0 hr)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.SliceCut
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix
open scoped ContDiff

noncomputable section

def sliceCut {n : ℕ} (h : HermNorm n) (k : ℕ) (x : Fin n → ℂ) : ℝ :=
  Real.smoothTransition (2 - Real.log (h.dualNorm x) / ((k : ℝ) + 1))

namespace SliceCut

variable {n : ℕ} (h : HermNorm n)

theorem continuous_dualNorm : Continuous h.dualNorm := by
  unfold HermNorm.dualNorm
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => ?_)
  exact ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id)).norm.pow 2

theorem norm_coord_le (x : Fin n → ℂ) (i : Fin n) : ‖((h.matᵀ)⁻¹ *ᵥ x) i‖ ≤ h.dualNorm x := by
  unfold HermNorm.dualNorm
  refine Real.le_sqrt_of_sq_le ?_
  exact Finset.single_le_sum (f := fun j => ‖((h.matᵀ)⁻¹ *ᵥ x) j‖ ^ 2) (fun _ _ => by positivity)
    (Finset.mem_univ i)

theorem mulVec_inv (x : Fin n → ℂ) : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by rw [Matrix.det_transpose]; exact h.isUnit_det),
    Matrix.one_mulVec]

theorem isCompact_sublevel (R : ℝ) : IsCompact {x : Fin n → ℂ | h.dualNorm x ≤ R} := by
  refine ((isCompact_closedBall (0 : Fin n → ℂ) R).image
    (Continuous.matrix_mulVec (A := fun _ => h.matᵀ) continuous_const continuous_id)).of_isClosed_subset
    (isClosed_le (continuous_dualNorm h) continuous_const) fun x hx => ?_
  refine ⟨(h.matᵀ)⁻¹ *ᵥ x, ?_, mulVec_inv h x⟩
  have hR : 0 ≤ R := (Real.sqrt_nonneg _).trans hx
  rw [Metric.mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg hR]
  exact fun i => (norm_coord_le h x i).trans hx

theorem mem_Icc (k : ℕ) (x : Fin n → ℂ) : sliceCut h k x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem eq_one_of_lt_one (k : ℕ) {x : Fin n → ℂ} (hx : h.dualNorm x < 1) : sliceCut h k x = 1 := by
  unfold sliceCut
  refine Real.smoothTransition.one_of_one_le ?_
  have hlog : Real.log (h.dualNorm x) ≤ 0 := Real.log_nonpos (Real.sqrt_nonneg _) hx.le
  have : Real.log (h.dualNorm x) / ((k : ℝ) + 1) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hlog (by positivity)
  linarith

theorem contDiff (k : ℕ) : ContDiff ℝ ∞ (sliceCut h k) := by
  refine contDiff_iff_contDiffAt.mpr fun x => ?_
  by_cases hx : x = 0
  · subst hx
    have hU : {y : Fin n → ℂ | h.dualNorm y < 1} ∈ 𝓝 (0 : Fin n → ℂ) := by
      refine (isOpen_lt (continuous_dualNorm h) continuous_const).mem_nhds ?_
      simp [HermNorm.dualNorm]
    exact contDiffAt_const.congr_of_eventuallyEq
      (Filter.mem_of_superset hU fun y hy => eq_one_of_lt_one h k hy)
  · have hlog := (contDiffOn_log_dualNorm h).contDiffAt (isOpen_compl_singleton.mem_nhds hx)
    exact Real.smoothTransition.contDiff.contDiffAt.comp x (contDiffAt_const.sub (hlog.div_const _))

theorem hasCompactSupport (k : ℕ) : HasCompactSupport (sliceCut h k) := by
  refine HasCompactSupport.intro (isCompact_sublevel h (Real.exp (2 * ((k : ℝ) + 1)))) fun x hx => ?_
  simp only [Set.mem_ofPred_eq, not_le] at hx
  unfold sliceCut
  refine Real.smoothTransition.zero_of_nonpos ?_
  have hpos : 0 < h.dualNorm x := (Real.exp_pos _).trans hx
  have hlog : 2 * ((k : ℝ) + 1) < Real.log (h.dualNorm x) := by
    rw [Real.lt_log_iff_exp_lt hpos]; exact hx
  have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  rw [sub_nonpos, le_div_iff₀ hk]
  linarith

theorem tendsto_one (x : Fin n → ℂ) : Tendsto (fun k => sliceCut h k x) atTop (𝓝 1) := by
  have hdiv : Tendsto (fun k : ℕ => Real.log (h.dualNorm x) / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
  have h2 := (tendsto_const_nhds (x := (2 : ℝ))).sub hdiv
  rw [sub_zero] at h2
  have := (Real.smoothTransition.continuous.tendsto 2).comp h2
  rwa [Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2)] at this

theorem measurable (k : ℕ) : Measurable (sliceCut h k) :=
  (contDiff h k).continuous.measurable

end SliceCut

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchInComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

def BranchInComponent.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (k : ℕ) (q : Fin n → ℂ) (c : VarBranch I k q),
    ∃ J ∈ I.minimalPrimes, Set.MapsTo c.toFun (Metric.ball 0 c.radius) (zeroSet J)

def axisBranch : VarBranch (Ideal.span {X 0 * X 1} : Ideal (MvPolynomial (Fin 2) ℂ)) 1 0 where
  radius := 1
  radius_pos := one_pos
  toFun t := fun i ↦ if i = 0 then t 0 else 0
  differentiableOn := by
    refine Differentiable.differentiableOn (differentiable_pi.2 fun i ↦ ?_)
    by_cases hi : i = 0
    · simp only [hi, if_true]
      exact differentiable_apply 0
    · simp only [hi, if_false]
      exact differentiable_const 0
  injOn := by
    intro s _ t _ hst
    have h0 := congrFun hst 0
    simp only [if_true] at h0
    funext i
    rw [Subsingleton.elim i 0]
    exact h0
  map_zero := by
    funext i
    by_cases hi : i = 0 <;> simp [hi]
  mapsTo := by
    intro t _ g hg
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hg
    simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchInCurveComponent
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def BranchInCurveComponent.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch I 1 q),
    ringKrullDim (curveLocalRing I q) = 1 →
      ∃ J ∈ I.minimalPrimes, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) ∧
        ∀ᶠ t in 𝓝 (0 : Fin 1 → ℂ), c.toFun t ∈ zeroSet J

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchPlace
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def BranchPlace.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (c : VarBranch I 1 q),
    IsRadicalAt I q → ringKrullDim (curveLocalRing I q) = 1 →
      ∃ P : MaximalSpectrum (curveNormalisation I q), ∀ f : MvPolynomial (Fin n) ℂ,
        Ring.ord (Localization.AtPrime P.asIdeal)
            (algebraMap (curveNormalisation I q) (Localization.AtPrime P.asIdeal)
              (algebraMap (curveLocalRing I q) (curveNormalisation I q)
                (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) f))) = branchOrder c f

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMHeightAddDim
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u

def CMHeightAddDim.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (J : Ideal B), J ≠ ⊤ →
    (J.height : WithBot ℕ∞) + ringKrullDim (B ⧸ J) = ringKrullDim B

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMHeightOneGeneral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

def CMHeightOneGeneral.Statement : Prop :=
  ∀ (n : ℕ) (J W : Ideal (MvPolynomial (Fin n) ℂ)) (g : MvPolynomial (Fin n) ℂ),
    J.IsPrime → g ∉ J → W ∈ (J ⊔ Ideal.span {g}).minimalPrimes →
      ∃ f : MvPolynomial (Fin n) ℂ, f ∉ W ∧ ∀ q ∈ zeroSet W, eval q f ≠ 0 → IsCohenMacaulayAt J q

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMLengthParameters
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open IsLocalRing

universe u

noncomputable section

def CMLengthParameters.Statement : Prop :=
  ∀ (B : Type u) [CommRing B] [IsCohenMacaulayLocalRing B] (P : Ideal B) [P.IsPrime] (d : ℕ) (x : Fin d → B),
    minimalPrimes B = {P} → ringKrullDim (B ⧸ P) = (d : ℕ) →
    Ideal.span (Set.range x) ⊔ P = maximalIdeal B →
      Module.length B (B ⧸ Ideal.span (Set.range x)) =
        Module.length (Localization.AtPrime P) (Localization.AtPrime P)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCMLocusOpen
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

def CMLocusOpen.Statement : Prop :=
  ∀ (n : ℕ) (I P : Ideal (MvPolynomial (Fin n) ℂ)) [P.IsPrime], I ≤ P →
    IsCohenMacaulayLocalRing (Localization.AtPrime P ⧸
      I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime P))) →
    ∃ g : MvPolynomial (Fin n) ℂ, g ∉ P ∧ ∀ (Q : Ideal (MvPolynomial (Fin n) ℂ)) [Q.IsPrime], I ≤ Q → g ∉ Q →
      IsCohenMacaulayLocalRing (Localization.AtPrime Q ⧸
        I.map (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime Q)))

end GroundTheory.Heights₂.Heights
end

