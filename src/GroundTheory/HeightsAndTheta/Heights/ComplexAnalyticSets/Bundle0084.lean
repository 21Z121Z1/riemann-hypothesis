import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0036
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Statements
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0022
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0048
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0061
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0076
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0007
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0072
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0069
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0012

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceSectionMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem contDiffOn_log_dualNorm {n : ℕ} (h : HermNorm n) :
    ContDiffOn ℝ ∞ (fun x : Fin n → ℂ => Real.log (h.dualNorm x)) {0}ᶜ := by
  intro x hx
  have hM : (h.matᵀ)⁻¹ *ᵥ x ≠ 0 := by
    intro h0
    have : h.matᵀ *ᵥ ((h.matᵀ)⁻¹ *ᵥ x) = x := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (by rw [Matrix.det_transpose]; exact h.isUnit_det),
        Matrix.one_mulVec]
    exact hx (by rw [← this, h0, Matrix.mulVec_zero]; rfl)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hM
  have hpos : 0 < ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ x) i‖ ^ 2 :=
    Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, pow_pos (norm_pos_iff.mpr hi) 2⟩
  have hQ : ContDiff ℝ ∞ fun y : Fin n → ℂ => ∑ i, ‖((h.matᵀ)⁻¹ *ᵥ y) i‖ ^ 2 := by
    refine ContDiff.sum fun i _ => (contDiff_norm_sq ℝ).comp ?_
    simp only [Matrix.mulVec, dotProduct]
    exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_apply ℝ ℂ j)
  exact ((hQ.contDiffAt.sqrt hpos.ne').log (Real.sqrt_pos.mpr hpos).ne').contDiffWithinAt

theorem smoothNear_log_dualNorm_slice {n : ℕ} (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ))
    (ℓ : Fin n → ℂ) :
    SmoothNear (zeroSet (J ⊔ Ideal.span {linForm ℓ - 1})) fun x => Real.log (h.dualNorm x) := by
  refine ⟨{0}ᶜ, isOpen_compl_singleton, fun x hx hx0 => ?_, contDiffOn_log_dualNorm h⟩
  have := hx _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
  rw [Set.mem_singleton_iff] at hx0
  subst hx0
  simp [linForm] at this

theorem SliceSectionMass.proof (hSt : StokesOnVariety.Statement) (hPL : PoincareLelong.Statement)
    (hI : SliceIdeal.Statement) (hC : SliceComponents.Statement) (hE : SliceExhaustion.Statement) :
    SliceSectionMass.Statement := by
  intro n e h J F u ℓ hJ hF hu hℓ hℓW
  obtain ⟨hprime, hdim, huJ⟩ := hI n (e + 1) J F ℓ hJ hF hℓ
  obtain ⟨hinj, himg, hmult⟩ := hC n J u ℓ hJ hℓW
  obtain ⟨f, hfs, hfc, -, -, hlimJ, hlimW, herr⟩ := hE n e h J F u ℓ hJ hF hu hℓ hℓW
  have hsm := smoothNear_log_dualNorm_slice h J ℓ
  have hk : ∀ k, ∑ W ∈ (divCycle J u).support, ((divCycle J u W : ℕ) : ℝ) *
        varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (f k) (fun _ x => Real.log (h.dualNorm x)) +
      (varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log (h.dualNorm x))
          (vecCons (f k) fun _ x => Real.log (h.dualNorm x)) -
        varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun x => Real.log ‖linEval u x‖)
          (vecCons (f k) fun _ x => Real.log (h.dualNorm x))) =
      varInt (J ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (f k)
        (fun _ x => Real.log (h.dualNorm x)) := by
    intro k
    have hS := hSt n e _ (f k) (fun x => Real.log (h.dualNorm x))
      (fun _ x => Real.log (h.dualNorm x)) hprime hdim (smoothNear_of_contDiff (hfs k)) hsm (fun _ => hsm)
      (Or.inl (hfc k))
    have hP := hPL n e _ u (f k) (fun _ x => Real.log (h.dualNorm x)) hprime hdim (huJ u hu) (hfs k)
      (hfc k) (fun _ => hsm)
    have hcons : (vecCons (fun x => Real.log (h.dualNorm x)) fun (_ : Fin e) x =>
        Real.log (h.dualNorm x)) = fun _ x => Real.log (h.dualNorm x) :=
      funext fun i => Fin.cases rfl (fun _ => rfl) i
    rw [hcons] at hS
    rw [hS, hP, ← himg, finsum_mem_image hinj, finsum_mem_coe_finset]
    have hsum : ∑ W ∈ (divCycle J u).support,
        (localMult (J ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u})
          (W ⊔ Ideal.span {linForm ℓ - 1}) : ℝ) *
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (f k) (fun _ x => Real.log (h.dualNorm x)) =
        ∑ W ∈ (divCycle J u).support, ((divCycle J u W : ℕ) : ℝ) *
          varInt (W ⊔ Ideal.span {linForm ℓ - 1}) e (f k) (fun _ x => Real.log (h.dualNorm x)) :=
      Finset.sum_congr rfl fun W hW => by rw [hmult W hW]
    rw [hsum]
    ring
  have hlim := (tendsto_finsetSum _ fun W hW => (hlimW W hW).const_mul
    ((divCycle J u W : ℕ) : ℝ)).add herr
  rw [add_zero] at hlim
  exact tendsto_nhds_unique hlimJ (hlim.congr hk)

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarietySlabMeasure
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory

open scoped ENNReal

noncomputable section

namespace VarietySlabMeasure

theorem isFiniteLinProj_of {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (h : ComplexSets.IsFiniteProjection J A) :
    IsFiniteLinProj J A :=
  ⟨h.injective, h.finite⟩

theorem fibreCount_le {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} (hJ : J.IsPrime)
    (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) {U : Matrix (Fin n) (Fin n) ℂ}
    {s : Fin d → Fin n} (hA : ComplexSets.IsFiniteProjection J (U.submatrix s id))
    (B : Set (EuclideanSpace ℂ (Fin n))) (x : EuclideanSpace ℂ (Fin d)) :
    {z | z ∈ zeroSetEuc J ∩ B ∧ rowsProj U s z = x}.encard ≤
      ComplexSets.projDegree J (U.submatrix s id) := by
  obtain ⟨-, hfin, hle⟩ := ComplexSets.FibreBound.proof n d J _ hJ hd hA (WithLp.ofLp x)
  calc _ ≤ (ComplexSets.fibre J (U.submatrix s id) (WithLp.ofLp x)).encard := by
        refine Set.encard_le_encard_of_injOn (f := fun z : EuclideanSpace ℂ (Fin n) => WithLp.ofLp z)
          ?_ (fun a _ b _ h => WithLp.ofLp_injective 2 h)
        rintro z ⟨⟨hz, -⟩, hx⟩
        exact ⟨hz, congrArg WithLp.ofLp hx⟩
    _ = ((ComplexSets.fibre J (U.submatrix s id) (WithLp.ofLp x)).ncard : ℕ∞) :=
        hfin.cast_ncard_eq.symm
    _ ≤ _ := by exact_mod_cast hle

end VarietySlabMeasure

theorem VarietySlabMeasure.proof (hG : ComplexSets.FiniteProjectionsGeneric.Statement)
    (hW : VarietyProjectionMass.Statement) (hP : IndefiniteRowSideFullHecke.ComplexSets.PolySublevel.Statement) :
    VarietySlabMeasure.Statement := by
  classical
  intro n d J u hJ hdim hu R
  rcases hdim.lt_or_eq with hlt | heq
  · refine ⟨1, 1, one_pos, one_pos, fun ε _ _ => ?_⟩
    calc _ ≤ μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J) := measure_mono fun z hz => hz.1
      _ = 0 := NullSmaller.proof n d J hlt
      _ ≤ _ := by simp
  obtain ⟨U, hU, hfin⟩ := (hG n d J hJ heq).2.2 1 (fun _ => 1)
  have hA : ∀ s : Fin d → Fin n, StrictMono s →
      ComplexSets.IsFiniteProjection J (U.submatrix s id) := fun s hs => by
    simpa using hfin 0 ⟨s, hs.injective⟩

  have hQ : ∀ s : Fin d → Fin n, ∃ Q : MvPolynomial (Fin d) ℂ, StrictMono s → Q ≠ 0 ∧
      ∀ z ∈ zeroSetEuc J, ‖z‖ ≤ R →
        ‖eval ((U.submatrix s id).mulVec fun j => z j) Q‖ ≤ ‖∑ j, u j * z j‖ := by
    intro s
    by_cases hs : StrictMono s
    · obtain ⟨Q, hQ0, hb⟩ := IndefiniteRowSideFullHecke.ComplexSets.SlabBound.affine n d J (U.submatrix s id) u hJ
        (VarietySlabMeasure.isFiniteLinProj_of (hA s hs)) hu
      obtain ⟨C, hC⟩ := hb R
      have hK : (0 : ℝ) < max C 1 := lt_max_of_lt_right one_pos
      refine ⟨MvPolynomial.C ((max C 1 : ℝ) : ℂ)⁻¹ * Q, fun _ => ⟨?_, fun z hz hzR => ?_⟩⟩
      · exact mul_ne_zero (by simpa using hK.ne') hQ0
      · rw [eval_mul, eval_C, norm_mul, norm_inv, Complex.norm_of_nonneg hK.le, inv_mul_le_iff₀ hK]
        exact (hC z hz hzR).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
    · exact ⟨0, fun h => absurd h hs⟩
  choose Q hQ using hQ

  have hR' : ∀ s : Fin d → Fin n, ∃ R' : ℝ, 0 < R' ∧
      ∀ z : EuclideanSpace ℂ (Fin n), ‖z‖ ≤ R → ‖rowsProj U s z‖ < R' := by
    intro s
    have hc : Continuous (rowsProj U s) := by
      unfold rowsProj
      fun_prop
    obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : EuclideanSpace ℂ (Fin n)) R).exists_bound_of_continuousOn
      hc.continuousOn
    refine ⟨max K 0 + 1, by positivity, fun z hz => ?_⟩
    have := hK z (mem_closedBall_zero_iff.mpr hz)
    linarith [le_max_left K 0]
  choose R' hR'0 hR' using hR'

  have hS : ∀ s : Fin d → Fin n, ∃ C α : ℝ, 0 < C ∧ 0 < α ∧ (StrictMono s → ∀ η : ℝ, 0 < η → η ≤ 1 →
      μH[((2 * d : ℕ) : ℝ)] {x : EuclideanSpace ℂ (Fin d) | x ∈ Metric.ball 0 (R' s) ∧
        ‖eval (fun i => x i) (Q s)‖ ≤ η} ≤ ENNReal.ofReal (C * η ^ α)) := by
    intro s
    by_cases hs : StrictMono s
    · obtain ⟨C, α, hC, hα, hb⟩ := hP d (Q s) (hQ s hs).1 (R' s) (hR'0 s)
      exact ⟨C, α, hC, hα, fun _ => hb⟩
    · exact ⟨1, 1, one_pos, one_pos, fun h => absurd h hs⟩
  choose C α hC hα hS using hS
  set T := Finset.univ.filter (fun s : Fin d → Fin n => StrictMono s) with hT

  obtain ⟨α₀, hα₀, hα₀le⟩ : ∃ α₀ : ℝ, 0 < α₀ ∧ ∀ s ∈ T, α₀ ≤ α s := by
    by_cases hne : T.Nonempty
    · exact ⟨T.inf' hne α, (Finset.lt_inf'_iff hne).2 fun s _ => hα s,
        fun s hs => Finset.inf'_le _ hs⟩
    · exact ⟨1, one_pos, fun s hs => absurd ⟨s, hs⟩ hne⟩
  set N : (Fin d → Fin n) → ℕ := fun s => ComplexSets.projDegree J (U.submatrix s id)
  have hNC : 0 ≤ ∑ s ∈ T, (N s : ℝ) * C s :=
    Finset.sum_nonneg fun s _ => mul_nonneg (Nat.cast_nonneg _) (hC s).le
  refine ⟨∑ s ∈ T, (N s : ℝ) * C s + 1, α₀, by linarith, hα₀, fun ε hε hε1 => ?_⟩
  set B : Set (EuclideanSpace ℂ (Fin n)) := {z | ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε}
  have hB : MeasurableSet B := by
    have hc : Continuous fun z : EuclideanSpace ℂ (Fin n) => ‖∑ j, u j * z j‖ := by fun_prop
    exact (measurableSet_le continuous_norm.measurable measurable_const).inter
      (measurableSet_le hc.measurable measurable_const)
  have hεα : 0 < ε ^ α₀ := Real.rpow_pos_of_pos hε _
  have hterm : ∀ s ∈ T,
      (⨆ x : EuclideanSpace ℂ (Fin d),
          (({z | z ∈ zeroSetEuc J ∩ B ∧ rowsProj U s z = x}.encard : ℕ∞) : ℝ≥0∞)) *
          μH[((2 * d : ℕ) : ℝ)] (rowsProj U s '' (zeroSetEuc J ∩ B)) ≤
        ENNReal.ofReal ((N s : ℝ) * C s * ε ^ α₀) := by
    intro s hs
    have hs' : StrictMono s := (Finset.mem_filter.mp hs).2
    rw [mul_assoc, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
    gcongr
    · refine iSup_le fun x => ?_
      have := VarietySlabMeasure.fibreCount_le hJ heq (hA s hs') B x
      exact_mod_cast ENat.toENNReal_le.mpr this
    · calc _ ≤ μH[((2 * d : ℕ) : ℝ)] {x : EuclideanSpace ℂ (Fin d) | x ∈ Metric.ball 0 (R' s) ∧
            ‖eval (fun i => x i) (Q s)‖ ≤ ε} := by
            refine measure_mono ?_
            rintro _ ⟨z, ⟨hz, hzR, hzε⟩, rfl⟩
            exact ⟨mem_ball_zero_iff.mpr (hR' s z hzR), ((hQ s hs').2 z hz hzR).trans hzε⟩
        _ ≤ ENNReal.ofReal (C s * ε ^ α s) := hS s hs' ε hε hε1
        _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_ge hε hε1 (hα₀le s hs)) (hC s).le)
  calc μH[((2 * d : ℕ) : ℝ)] {z | z ∈ zeroSetEuc J ∧ ‖z‖ ≤ R ∧ ‖∑ j, u j * z j‖ ≤ ε}
        = μH[((2 * d : ℕ) : ℝ)] (zeroSetEuc J ∩ B) := rfl
    _ ≤ _ := hW n d J hJ heq U hU B hB
    _ ≤ ∑ s ∈ T, ENNReal.ofReal ((N s : ℝ) * C s * ε ^ α₀) := Finset.sum_le_sum hterm
    _ = ENNReal.ofReal (∑ s ∈ T, (N s : ℝ) * C s * ε ^ α₀) :=
        (ENNReal.ofReal_sum_of_nonneg fun s _ => by have := hC s; positivity).symm
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← Finset.sum_mul, add_mul, one_mul]
        linarith

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PWeierstrassPolynomialDivision
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open Topology Filter Metric Complex Real

noncomputable section

namespace WeierstrassPolynomialDivision

theorem circleIntegral_finset_sum {ι : Type} (u : Finset ι) (f : ι → ℂ → ℂ) {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : ∀ i ∈ u, ContinuousOn (f i) (sphere c R)) :
    (∮ z in C(c, R), ∑ i ∈ u, f i z) = ∑ i ∈ u, ∮ z in C(c, R), f i z := by
  classical
  induction u using Finset.induction_on with
  | empty => simp [circleIntegral]
  | insert a u ha ih =>
    simp only [Finset.sum_insert ha]
    rw [circleIntegral.integral_add ((hf a (by simp)).circleIntegrable hR)
      ((continuousOn_finsetSum u fun i hi => hf i (by simp [hi])).circleIntegrable hR),
      ih fun i hi => hf i (by simp [hi])]

theorem pointWithLast_eta {σ : Type} (x : Option σ → ℂ) : pointWithLast (fun i => x (some i)) (x none) = x := by
  funext o
  cases o <;> rfl

theorem differentiable_pointWithLast {σ : Type} [Fintype σ] :
    Differentiable ℂ (fun p : (σ → ℂ) × ℂ => pointWithLast p.1 p.2) := by
  rw [differentiable_pi]
  intro o
  cases o with
  | none => exact differentiable_snd
  | some i =>
    show Differentiable ℂ fun p : (σ → ℂ) × ℂ => p.1 i
    fun_prop

theorem norm_pointWithLast_lt {σ : Type} [Fintype σ] {z : σ → ℂ} {s : ℂ} {ε : ℝ} (hε : 0 < ε) (hz : ‖z‖ < ε)
    (hs : ‖s‖ < ε) : ‖pointWithLast z s‖ < ε := by
  rw [pi_norm_lt_iff hε]
  intro o
  cases o with
  | none => exact hs
  | some i => exact (norm_le_pi_norm z i).trans_lt hz

end WeierstrassPolynomialDivision

open WeierstrassPolynomialDivision in

theorem WeierstrassPolynomialDivision.proof (hC : ParametricCircleIntegralAnalytic.Statement) :
    WeierstrassPolynomialDivision.Statement := by
  intro σ _ d c g hc hc0 hg
  obtain ⟨εg, hεg, hgan⟩ := hg.exists_ball_analyticOnNhd
  obtain ⟨εc, hεc, hcan⟩ := Metric.eventually_nhds_iff_ball.1
    (Filter.eventually_all.2 fun j => (hc j).eventually_analyticAt)
  set ε := min εg εc with hε_def
  have hε : 0 < ε := lt_min hεg hεc
  set r := ε / 2 with hr_def
  have hr : 0 < r := half_pos hε
  have hrε : r < ε := half_lt_self hε

  let G : (σ → ℂ) × ℂ → ℂ := fun p => g (pointWithLast p.1 p.2)
  let F : (σ → ℂ) × ℂ → ℂ := fun p => weierstrassPolynomial c (pointWithLast p.1 p.2)
  let A : Set ((σ → ℂ) × ℂ) := ball 0 ε ×ˢ ball 0 ε
  have hcd : ∀ z ∈ ball (0 : σ → ℂ) ε, ∀ j, DifferentiableAt ℂ (c j) z := fun z hz j =>
    (hcan z (mem_ball_zero_iff.2 ((mem_ball_zero_iff.1 hz).trans_le (min_le_right _ _))) j).differentiableAt
  have hGd : ∀ p ∈ A, DifferentiableAt ℂ G p := by
    intro p hp
    have hp' : pointWithLast p.1 p.2 ∈ ball (0 : Option σ → ℂ) εg := mem_ball_zero_iff.2
      (norm_pointWithLast_lt hεg ((mem_ball_zero_iff.1 hp.1).trans_le (min_le_left _ _))
        ((mem_ball_zero_iff.1 hp.2).trans_le (min_le_left _ _)))
    exact (hgan _ hp').differentiableAt.comp p (differentiable_pointWithLast p)
  have hFd : ∀ p ∈ A, DifferentiableAt ℂ F p := by
    intro p hp
    show DifferentiableAt ℂ (fun p : (σ → ℂ) × ℂ => p.2 ^ d + ∑ j : Fin d, c j p.1 * p.2 ^ (j : ℕ)) p
    exact (differentiableAt_snd.pow d).add (DifferentiableAt.fun_sum fun j _ =>
      ((hcd p.1 hp.1 j).comp p differentiableAt_fst).mul (differentiableAt_snd.pow _))

  have hFne : ∀ᶠ z in 𝓝 (0 : σ → ℂ), ∀ s ∈ sphere (0 : ℂ) r, F (z, s) ≠ 0 := by
    refine (isCompact_sphere (0 : ℂ) r).eventually_forall_of_forall_eventually fun s hs => ?_
    have hsn : ‖s‖ = r := mem_sphere_zero_iff_norm.1 hs
    have hA : ((0 : σ → ℂ), s) ∈ A := ⟨mem_ball_self hε, mem_ball_zero_iff.2 (hsn ▸ hrε)⟩
    have h0 : F (0, s) ≠ 0 := by
      show weierstrassPolynomial c (pointWithLast 0 s) ≠ 0
      rw [weierstrassPolynomial_pointWithLast_zero c hc0]
      exact pow_ne_zero _ (norm_ne_zero_iff.1 (hsn ▸ hr.ne'))
    exact (hFd _ hA).continuousAt.eventually_ne h0
  obtain ⟨δ, hδ, hδF⟩ := Metric.eventually_nhds_iff_ball.1 (hFne.and (ball_mem_nhds (0 : σ → ℂ) hε))

  let O₀ : Set ((σ → ℂ) × ℂ) := A ∩ F ⁻¹' {0}ᶜ
  have hO₀ : IsOpen O₀ := ContinuousOn.isOpen_inter_preimage
    (fun p hp => (hFd p hp).continuousAt.continuousWithinAt) (isOpen_ball.prod isOpen_ball) isOpen_compl_singleton
  have hmem₀ : ∀ z ∈ ball (0 : σ → ℂ) δ, ∀ s ∈ sphere (0 : ℂ) r, (z, s) ∈ O₀ := fun z hz s hs =>
    ⟨⟨(hδF z hz).2, mem_ball_zero_iff.2 ((mem_sphere_zero_iff_norm.1 hs).trans_lt hrε)⟩, (hδF z hz).1 s hs⟩

  let μ : (Option σ → ℂ) × ℂ → (σ → ℂ) × ℂ := fun p => ((fun i => p.1 (some i)), p.2)
  have hμ : Differentiable ℂ μ :=
    (differentiable_pi.2 fun i => by fun_prop).prodMk differentiable_snd
  let Φq : (Option σ → ℂ) × ℂ → ℂ := fun p => G (μ p) / (F (μ p) * (p.2 - p.1 none))
  let Oq : Set ((Option σ → ℂ) × ℂ) := μ ⁻¹' O₀ ∩ {p | p.2 - p.1 none ≠ 0}
  have hOq : IsOpen Oq := (hO₀.preimage hμ.continuous).inter (isOpen_ne_fun (by fun_prop) continuous_const)
  let Uq : Set (Option σ → ℂ) :=
    (fun x : Option σ → ℂ => fun i => x (some i)) ⁻¹' ball (0 : σ → ℂ) δ ∩ (fun x : Option σ → ℂ => x none) ⁻¹' ball (0 : ℂ) r
  have hUq : IsOpen Uq :=
    (isOpen_ball.preimage (by fun_prop)).inter (isOpen_ball.preimage (continuous_apply none))
  have hΦq : DifferentiableOn ℂ Φq Oq := by
    rintro p ⟨⟨hA, hF⟩, hne⟩
    have hden : DifferentiableAt ℂ (fun p : (Option σ → ℂ) × ℂ => F (μ p) * (p.2 - p.1 none)) p :=
      ((hFd _ hA).comp p (hμ p)).mul (differentiableAt_snd.sub
        (by fun_prop : DifferentiableAt ℂ (fun p : (Option σ → ℂ) × ℂ => p.1 none) p))
    rw [show Φq = fun p => G (μ p) * (F (μ p) * (p.2 - p.1 none))⁻¹ from funext fun _ => div_eq_mul_inv _ _]
    exact (((hGd _ hA).comp p (hμ p)).mul (hden.inv (mul_ne_zero hF hne))).differentiableWithinAt
  have hmemq : ∀ x ∈ Uq, ∀ s ∈ sphere (0 : ℂ) r, (x, s) ∈ Oq := by
    intro x hx s hs
    refine ⟨hmem₀ _ hx.1 s hs, ?_⟩
    show s - x none ≠ 0
    intro h
    have h1 := mem_sphere_zero_iff_norm.1 hs
    have h2 := mem_ball_zero_iff.1 hx.2
    rw [sub_eq_zero.1 h] at h1
    linarith
  have h0q : (0 : Option σ → ℂ) ∈ Uq := ⟨mem_ball_self hδ, mem_ball_self hr⟩
  have hqan := hC (Option σ) Φq Oq Uq 0 r hr.le hOq hUq hΦq hmemq

  let Φa : Fin d → (σ → ℂ) × ℂ → ℂ := fun j p => G p * monicDifferenceCoeff (fun k => c k p.1) p.2 j / F p
  have hΦa : ∀ j, DifferentiableOn ℂ (Φa j) O₀ := by
    intro j p hp
    have hP : DifferentiableAt ℂ (fun p : (σ → ℂ) × ℂ => monicDifferenceCoeff (fun k => c k p.1) p.2 j) p := by
      show DifferentiableAt ℂ (fun p : (σ → ℂ) × ℂ => p.2 ^ (d - 1 - (j : ℕ)) +
        ∑ k ∈ Finset.univ.filter (fun k : Fin d => (j : ℕ) < k), c k p.1 * p.2 ^ ((k : ℕ) - 1 - j)) p
      exact (differentiableAt_snd.pow _).add (DifferentiableAt.fun_sum fun k _ =>
        ((hcd p.1 hp.1.1 k).comp p differentiableAt_fst).mul (differentiableAt_snd.pow _))
    rw [show Φa j = fun p => G p * monicDifferenceCoeff (fun k => c k p.1) p.2 j * (F p)⁻¹ from
      funext fun _ => div_eq_mul_inv _ _]
    exact (((hGd p hp.1).mul hP).mul ((hFd p hp.1).inv hp.2)).differentiableWithinAt
  have haan := fun j => hC σ (Φa j) O₀ (ball 0 δ) 0 r hr.le hO₀ isOpen_ball (hΦa j) hmem₀
  refine ⟨fun x => (2 * π * I)⁻¹ * ∮ s in C(0, r), Φq (x, s),
    fun j z => (2 * π * I)⁻¹ * ∮ s in C(0, r), Φa j (z, s),
    analyticAt_const.mul (hqan 0 h0q), fun j => analyticAt_const.mul (haan j 0 (mem_ball_self hδ)), ?_⟩
  filter_upwards [hUq.mem_nhds h0q] with x hx
  set z : σ → ℂ := fun i => x (some i) with hz
  set t : ℂ := x none with ht
  have hgx : g x = G (z, t) := congrArg g (pointWithLast_eta x).symm

  have hcau : (2 * π * I)⁻¹ • (∮ s in C(0, r), (s - t)⁻¹ • G (z, s)) = G (z, t) := by
    refine DiffContOnCl.two_pi_i_inv_smul_circleIntegral_sub_inv_smul (f := fun s => G (z, s)) ?_ hx.2
    refine DifferentiableOn.diffContOnCl_ball (U := ball 0 ε) (fun s hs => ?_) (closedBall_subset_ball hrε)
    exact ((hGd (z, s) ⟨(hδF z hx.1).2, hs⟩).comp s
      ((differentiableAt_const z).prodMk differentiableAt_id)).differentiableWithinAt

  have hpt : Set.EqOn (fun s => (s - t)⁻¹ • G (z, s))
      (fun s => weierstrassPolynomial c x * Φq (x, s) + ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s))
      (sphere (0 : ℂ) r) := by
    intro s hs
    have hFs : F (z, s) ≠ 0 := (hδF z hx.1).1 s hs
    have hst : s - t ≠ 0 := (hmemq x hx s hs).2
    have key : F (z, s) - weierstrassPolynomial c x =
        (s - t) * ∑ j : Fin d, monicDifferenceCoeff (fun k => c k z) s j * t ^ (j : ℕ) :=
      monic_sub_eq_mul_sum (fun k => c k z) s t
    have hsum : ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s) =
        G (z, s) / F (z, s) * ∑ j : Fin d, monicDifferenceCoeff (fun k => c k z) s j * t ^ (j : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      show t ^ (j : ℕ) * (G (z, s) * monicDifferenceCoeff (fun k => c k z) s j / F (z, s)) = _
      ring
    have hP : ∑ j : Fin d, monicDifferenceCoeff (fun k => c k z) s j * t ^ (j : ℕ) =
        (F (z, s) - weierstrassPolynomial c x) / (s - t) := by
      rw [key]
      field_simp
    show (s - t)⁻¹ • G (z, s) =
      weierstrassPolynomial c x * (G (z, s) / (F (z, s) * (s - t))) + ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s)
    rw [hsum, hP, smul_eq_mul]
    field_simp
    ring
  have hcq : ContinuousOn (fun s => Φq (x, s)) (sphere (0 : ℂ) r) :=
    hΦq.continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun s hs => hmemq x hx s hs
  have hca : ∀ j ∈ (Finset.univ : Finset (Fin d)), ContinuousOn (fun s => t ^ (j : ℕ) * Φa j (z, s))
      (sphere (0 : ℂ) r) := fun j _ => continuousOn_const.mul
    ((hΦa j).continuousOn.comp (Continuous.continuousOn (by fun_prop)) fun s hs => hmem₀ z hx.1 s hs)
  have hint : (∮ s in C(0, r), (s - t)⁻¹ • G (z, s)) =
      weierstrassPolynomial c x * (∮ s in C(0, r), Φq (x, s)) +
        ∑ j : Fin d, t ^ (j : ℕ) * ∮ s in C(0, r), Φa j (z, s) := by
    have hi1 : CircleIntegrable (fun s => weierstrassPolynomial c x * Φq (x, s)) 0 r :=
      (continuousOn_const.mul hcq).circleIntegrable hr.le
    have hi2 : CircleIntegrable (fun s => ∑ j : Fin d, t ^ (j : ℕ) * Φa j (z, s)) 0 r :=
      (continuousOn_finsetSum _ hca).circleIntegrable hr.le
    rw [circleIntegral.integral_congr hr.le hpt, circleIntegral.integral_add hi1 hi2,
      circleIntegral.integral_const_mul, circleIntegral_finset_sum _ _ hr.le hca]
    congr 1
    exact Finset.sum_congr rfl fun j _ => circleIntegral.integral_const_mul _ _ _ _
  rw [hgx, ← hcau, smul_eq_mul, hint, mul_add, Finset.mul_sum]
  congr 1
  · ring
  · exact Finset.sum_congr rfl fun j _ => by ring

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchIntDecompose
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff

noncomputable section

def BranchIntDecompose.Statement : Prop :=
  ∀ (n d : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u q : Fin n → ℂ) (m : ℕ)
    (γ : Fin m → VarBranch J (d + 1) q) (ord : Fin m → ℕ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ) → linForm u ∉ J →
    (∃ N ∈ 𝓝 q, zeroSet J ∩ N ⊆ ⋃ b, (γ b).image) →
    (∀ b b', b ≠ b' → (γ b).image ∩ (γ b').image ⊆ {x | linEval u x = 0}) →
    (∀ b, VanishesToOrder (fun t => linEval u ((γ b).toFun t)) (γ b).radius (ord b)) →
      ∃ N ∈ 𝓝 q, ∀ (f : (Fin n → ℂ) → ℝ) (ψ : Fin (d + 1) → (Fin n → ℂ) → ℝ),
        ContDiff ℝ ∞ f → HasCompactSupport f → tsupport f ⊆ N →
        (∀ i, SmoothNear (zeroSet J) (ψ i)) →
          varInt J (d + 1) f ψ =
            ∑ b, ReciprocityTheory.AnForm.maInt (fun k => ψ k ∘ (γ b).toFun) (f ∘ (γ b).toFun)
              (Metric.ball 0 (γ b).radius)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StConeSheetGram
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

noncomputable section

def ConeSheetGram.Statement : Prop :=
  ∀ (n e : ℕ) (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (ℓ : Fin n → ℂ)
    (A : Matrix (Fin e) (Fin n) ℂ) (f : EuclideanSpace ℂ (Fin n) → ℝ),
    IsProjPrime J → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((e + 1 : ℕ) : WithBot ℕ∞) →
    linForm ℓ ∉ J → IsFiniteProjection (J ⊔ Ideal.span {linForm ℓ - 1}) A →
    IntegrableOn f {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}
      (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) →
      Real.pi ^ (e + 1) / ((e + 1).factorial : ℝ) *
          ∫ z in {z : EuclideanSpace ℂ (Fin n) | ∀ q ∈ J, eval (h.pointOf z) q = 0}, f z
            ∂(Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)) =
        (Measure.hausdorffMeasure ((2 * (e + 1) : ℕ) : ℝ)
            {z : EuclideanSpace ℂ (Fin n) | ‖z‖ < 1 ∧ ∀ j : Fin n, e + 1 ≤ (j : ℕ) → z j = 0}).toReal *
          ∫ y, sheetSum (J ⊔ Ideal.span {linForm ℓ - 1}) A
            (fun _ s => ∫ t : ℂ, f (t • WithLp.toLp 2 ((h.matᵀ)⁻¹ *ᵥ s y)) *
              (‖t‖ ^ (2 * e) * gramVol (fun y' => (h.matᵀ)⁻¹ *ᵥ s y') y)) y

end

end GroundTheory.Heights₂.Heights
end

