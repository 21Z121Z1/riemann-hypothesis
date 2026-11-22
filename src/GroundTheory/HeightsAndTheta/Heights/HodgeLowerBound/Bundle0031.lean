import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0019
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.Bundle0016
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0014
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0027
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0024
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0028
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.Bundle0008
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0102
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.ContDiffAtSqrtQuotNormSq
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
open scoped Matrix ComplexOrder

namespace MuWeightChartSmooth

section Calculus

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {n : WithTop ℕ∞} {x : F}

theorem contDiffAt_eval {σ : Type*} {Φ : F → σ → ℂ} (hΦ : ∀ i, ContDiffAt ℝ n (fun w => Φ w i) x)
    (P : MvPolynomial σ ℂ) : ContDiffAt ℝ n (fun w => eval (Φ w) P) x := by
  induction P using MvPolynomial.induction_on with
  | C a => simpa using contDiffAt_const
  | add p q hp hq => simpa using hp.add hq
  | mul_X p i hp => simpa using hp.mul (hΦ i)

theorem contDiffAt_det {m : Type*} [Fintype m] [DecidableEq m] {M : F → Matrix m m ℂ}
    (hM : ∀ i j, ContDiffAt ℝ n (fun w => M w i j) x) : ContDiffAt ℝ n (fun w => (M w).det) x := by
  simp only [Matrix.det_apply']
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hM _ _)

theorem contDiffAt_star {f : F → ℂ} (hf : ContDiffAt ℝ n f x) :
    ContDiffAt ℝ n (fun w => star (f w)) x :=
  (Complex.conjCLE.contDiff.contDiffAt).comp x hf

theorem contDiffAt_zpow_of_ne {f : F → ℝ} (hf : ContDiffAt ℝ n f x) (h0 : f x ≠ 0) (m : ℤ) :
    ContDiffAt ℝ n (fun w => f w ^ m) x := by
  rcases m with m | m
  · simpa using hf.pow m
  · simp only [zpow_negSucc]
    exact (hf.pow (m + 1)).fun_inv (pow_ne_zero _ h0)

theorem contDiffAt_sandwich {m : Type*} [Fintype m] {A B : F → Matrix m m ℂ}
    (hA : ∀ i j, ContDiffAt ℝ n (fun w => A w i j) x) (hB : ∀ i j, ContDiffAt ℝ n (fun w => B w i j) x)
    (i j : m) : ContDiffAt ℝ n (fun w => ((A w)ᴴ * B w * A w) i j) x := by
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact ContDiffAt.sum fun k _ =>
    (ContDiffAt.sum fun l _ => (contDiffAt_star (hA l i)).mul (hB l k)).mul (hA k j)

end Calculus

section Chart

variable {II : IntersectionSystem} {Ψ : Type} [Fintype Ψ] {K : Type} [Fintype K] {ι : K → Type}
  [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {E : Ψ → Type} [∀ τ, AddCommGroup (E τ)]
  [∀ τ, Module Ω (E τ)]

omit [Algebra ℚ Ω] in

theorem contDiffAt_valAt {y : (Σ k, ι k) → Ω} {m : ℕ} {γ : (Fin m → ℂ) → (Σ k, ι k) → ℂ}
    {t : Fin m → ℂ} (hγ : ∀ p, ContDiffAt ℝ 2 (fun t' => γ t' p) t)
    (hP : ∀ᶠ t' in 𝓝 t, γ t' ∈ mcPts (mCoordIdeal y)) {a : Ω} {v : ℂ}
    (hv : IndefiniteRowSideFullHecke.LowerBoundFree.IsValueAt y a (γ t) v) :
    ContDiffAt ℝ 2 (fun t' => valAt y a (γ t')) t ∧ valAt y a (γ t) = v ∧
      ∀ᶠ t' in 𝓝 t, IsValueAt y a (γ t') (valAt y a (γ t')) := by
  obtain ⟨d, g, h, hg, hh, hy, hyg, hz, hgv⟩ := hv
  have hG := contDiffAt_eval hγ (map (Int.castRingHom ℂ) g)
  have hH := contDiffAt_eval hγ (map (Int.castRingHom ℂ) h)
  have hval : ∀ᶠ t' in 𝓝 t, IsValueAt y a (γ t') (eval (γ t') (map (Int.castRingHom ℂ) g) /
      eval (γ t') (map (Int.castRingHom ℂ) h)) ∧ γ t' ∈ mcPts (mCoordIdeal y) := by
    filter_upwards [hP, hH.continuousAt.eventually_ne hz] with t' h1 h2
    exact ⟨⟨d, g, h, hg, hh, hy, hyg, h2, rfl⟩, h1⟩
  have hev : ∀ᶠ t' in 𝓝 t, valAt y a (γ t') =
      eval (γ t') (map (Int.castRingHom ℂ) g) * (eval (γ t') (map (Int.castRingHom ℂ) h))⁻¹ := by
    filter_upwards [hval] with t' h1
    rw [valAt_eq h1.2 h1.1, div_eq_mul_inv]
  refine ⟨(hG.mul (hH.fun_inv hz)).congr_of_eventuallyEq hev, ?_, ?_⟩
  · rw [hev.self_of_nhds, hgv, mul_inv_cancel_right₀ hz]
  · filter_upwards [hval] with t' h1
    rw [valAt_eq h1.2 h1.1]
    exact h1.1

def datumValue {D : ComponentData II Ψ K ι Ω E} (H : HodgeData D) (c : (k : K) → ι k)
    (b : ∀ τ, Fin D.N → E τ) (u : Ω) (z : (Σ k, ι k) → ℂ) : ℝ :=
  ‖valAt D.y u z‖ * (∏ k, ‖z ⟨k, c k⟩‖ ^ H.aMu k) *
    ∏ τ, Real.sqrt (quotNormSq D.j_le_N (gramAt (D.h τ) (b τ) z))

end Chart

end MuWeightChartSmooth

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.HFl
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

noncomputable section

theorem GrassmannianHeightZTwo.proof (hZ2 : SuccessiveMinimaUpperBound) (hPush : FlagGrassPush.Statement)
    (hDeg : HilbertSamuel.FSGeomDegPos.Statement) : GrassmannianHeightZTwo.Statement := by
  intro II Ψ _ _ N j cf e hII hN hj1 hjN hJ hZ
  rcases isEmpty_or_nonempty Ψ with hΨ | hΨ
  · have hmu : muPoly Ψ N j = 0 := by
      unfold muPoly
      exact Finset.sum_eq_zero fun p _ => (IsEmpty.false p.1).elim
    have hFA : FA Ψ N j cf = 0 := by
      unfold FA
      rw [hmu, zero_pow (Nat.succ_ne_zero _), zero_mul]
    rw [hFA, Fintype.card_eq_zero]
    simp [hFl]
  · set f := Fintype.card Ψ with hfdef
    have hf : 1 ≤ f := Fintype.card_pos
    have hP := hPush II Ψ N j cf hII hN hj1 hjN
    have hG := GrassHeightE.full hZ2 f j (N - j) e hf hZ II hII
    have hD : 0 < geomDeg (grassIdeal f j (N - j)) (GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j (N - j)))
        (f * j * (N - j)) :=
      hDeg (Fin f) (plBlocks f j (N - j)) (grassIdeal f j (N - j)) (f * j * (N - j))
        (GrassArithVar.full f j (N - j) hf)
    have hJ' : (0 : ℝ) < (Jint Ψ N j cf : ℝ) := Rat.cast_pos.mpr hJ
    change -hFl Ψ N II (FA Ψ N j cf) * geomDeg (grassIdeal f j (N - j))
        (GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j (N - j))) (f * j * (N - j)) =
      (Jint Ψ N j cf : ℝ) * II (Fin f) (plBlocks f j (N - j)) (grassIdeal f j (N - j))
        (f * j * (N - j) + 1) (fun _ => GroundTheory.Heights₂.Heights.fsMulti (plBlocks f j (N - j))) at hP
    change -hFl Ψ N II (FA Ψ N j cf) ≤ ((f * j * (N - j) + 1 : ℕ) : ℝ) * (Jint Ψ N j cf : ℝ) * (f : ℝ) * e
    have h1 := mul_le_mul_of_nonneg_left hG hJ'.le
    refine le_of_mul_le_mul_right ?_ hD
    rw [hP]
    calc _ ≤ _ := h1
      _ = _ := by ring

end

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBdPtsNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem BdPtsNull.proof (h : ParamImageNull.Statement) : BdPtsNull.Statement := by
  intro II Ψ _ K _ ι _ Ω _ _ E _ _ D
  classical
  refine h K ι (mCoordIdeal D.y) D.n D.nCharts (fun _ => Metric.ball 0 1)
    (fun a => {t | t ∈ Metric.ball (0 : Fin D.n → ℂ) 1 ∧ ∃ i : Fin D.n, (i : ℕ) < (D.chart a).a ∧ t i = 0})
    (fun a => (D.chart a).γ) D.Bd (fun _ => Metric.isOpen_ball) (fun _ _ ht => ht.1) ?_
    (fun a => (D.chart a).analytic) ?_
  · intro a
    refine measure_mono_null (t := ⋃ i : Fin D.n, {t : Fin D.n → ℂ | t i = 0}) ?_
      (measure_iUnion_null fun i => ?_)
    · rintro t ⟨-, i, -, hi⟩
      exact Set.mem_iUnion.2 ⟨i, hi⟩
    · rw [volume_pi]
      exact Measure.pi_hyperplane _ i 0
  · rintro z ⟨hz, -⟩
    obtain ⟨a, t, ht, c, hc, rfl⟩ := D.chart_cover z (D.bd_subset hz)
    have htb : t ∈ Metric.ball (0 : Fin (Fintype.card Ψ * D.j * (D.N - D.j)) → ℂ) 1 :=
      mem_ball_zero_iff.2 (lt_of_le_of_lt ht (by norm_num))
    have hγ : (D.chart a).γ t ∈ D.Bd := by
      have h' := D.bd_torus _ hz c⁻¹ (fun k => inv_ne_zero (hc k))
      convert h' using 1
      funext p
      simp [torusSmul, hc p.1]
    exact ⟨a, t, ⟨htb, ((D.chart a).boundary t htb).1 hγ⟩, c, hc, rfl⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PBoundaryPtsNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem segre_torusSmul {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (c : K → ℂ)
    (z : (Σ k, ι k) → ℂ) : segre (torusSmul c z) = (∏ k, c k) • segre z := by
  funext i
  simp [segre, torusSmul, Finset.prod_mul_distrib]

theorem volume_coord_hyperplane {m : ℕ} (i : Fin m) : volume {t : Fin m → ℂ | t i = 0} = 0 := by
  rw [volume_pi]
  exact Measure.pi_hyperplane _ i 0

theorem differentiable_segre {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)] :
    Differentiable ℂ (segre : ((Σ k, ι k) → ℂ) → ((k : K) → ι k) → ℂ) := by
  refine differentiable_pi.2 fun i => ?_
  unfold segre
  fun_prop

theorem BoundaryPtsNull.proof : BoundaryPtsNull.Statement := by
  intro II T _ _ K _ ι _ Ω _ _ E _ _ D Ψ _
  classical
  let F : Fin D.nCharts → (Fin D.n → ℂ) → Fin D.n → ℂ := fun a t j =>
    Ψ (segre ((D.chart a).γ t)) j.succ / Ψ (segre ((D.chart a).γ t)) 0
  let s : Fin D.nCharts → Fin D.n → Set (Fin D.n → ℂ) := fun a i =>
    {t | ‖t‖ < 1 ∧ t i = 0 ∧ Ψ (segre ((D.chart a).γ t)) 0 ≠ 0}
  refine measure_mono_null (t := ⋃ a, ⋃ i, F a '' s a i) ?_
    (measure_iUnion_null fun a => measure_iUnion_null fun i => ?_)
  · rintro y ⟨z, hz, hzB, hΨ⟩
    obtain ⟨a, t, ht, c, hc, rfl⟩ := D.chart_cover z hz
    have hγB : (D.chart a).γ t ∈ D.Bd := by
      have := D.bd_torus _ hzB (fun k => (c k)⁻¹) (fun k => inv_ne_zero (hc k))
      convert this using 1
      funext p
      simp only [torusSmul]
      rw [inv_mul_cancel_left₀ (hc _)]
    have ht1 : ‖t‖ < 1 := by linarith
    obtain ⟨i, -, hi⟩ := ((D.chart a).boundary t (mem_ball_zero_iff.2 ht1)).1 hγB
    rw [segre_torusSmul, map_smul] at hΨ
    have h0 := congrFun hΨ 0
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero] at h0
    have hv0 : Ψ (segre ((D.chart a).γ t)) 0 ≠ 0 := fun h => by simp [h] at h0
    refine Set.mem_iUnion.2 ⟨a, Set.mem_iUnion.2 ⟨i, t, ⟨ht1, hi, hv0⟩, ?_⟩⟩
    funext j
    have hj := congrFun hΨ j.succ
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ] at hj
    show Ψ (segre ((D.chart a).γ t)) j.succ / Ψ (segre ((D.chart a).γ t)) 0 = y j
    rw [div_eq_iff hv0, ← hj]
    linear_combination (-(Ψ (segre ((D.chart a).γ t)) j.succ)) * h0
  · refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
      (measure_mono_null (fun t ht => ht.2.1) (volume_coord_hyperplane i))
    intro t ht
    have hγ : DifferentiableAt ℂ (D.chart a).γ t :=
      ((D.chart a).analytic t (mem_ball_zero_iff.2 ht.1)).differentiableAt
    have hS : DifferentiableAt ℂ (fun t => segre ((D.chart a).γ t)) t := by
      have := differentiable_segre.differentiableAt.comp t hγ
      exact this
    have hG : DifferentiableAt ℂ (fun t => Ψ (segre ((D.chart a).γ t))) t := by
      have := (LinearMap.toContinuousLinearMap Ψ).differentiableAt.comp t hS
      exact this
    have hF : DifferentiableAt ℂ (F a) t := by
      refine differentiableAt_pi.2 fun j => ?_
      have hn : DifferentiableAt ℂ (fun t => Ψ (segre ((D.chart a).γ t)) j.succ) t :=
        differentiableAt_pi.1 hG j.succ
      have hd : DifferentiableAt ℂ (fun t => Ψ (segre ((D.chart a).γ t)) 0) t :=
        differentiableAt_pi.1 hG 0
      show DifferentiableAt ℂ
        (fun t => Ψ (segre ((D.chart a).γ t)) j.succ / Ψ (segre ((D.chart a).γ t)) 0) t
      simp only [div_eq_mul_inv]
      exact hn.mul (hd.inv ht.2.2)
    exact (hF.restrictScalars ℝ).differentiableWithinAt

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PDivisorPreimageNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Set
open ReciprocityTheory.AnForm.A (coordDiv)

theorem volume_coordDiv {D : ℕ} (S : Finset (Fin D)) : volume (coordDiv S) = 0 := by
  have h : coordDiv S = ⋃ i ∈ S, (fun z : Fin D → ℂ => z i) ⁻¹' {0} := by
    ext z
    simp [coordDiv]
  rw [h]
  exact measure_iUnion_null fun i => measure_iUnion_null fun _ =>
    Measure.pi_eval_preimage_null (fun _ : Fin D => (volume : Measure ℂ)) (measure_singleton 0)

theorem DivisorPreimageNull.proof (h : ParamImageNull.Statement) : DivisorPreimageNull.Statement := by
  intro K _ ι _ P d M R
  classical
  have hloc : ∀ x : M.Xc, ∃ W : Set M.Xc, IsOpen W ∧ x ∈ W ∧ ∃ j : Fin R.N, W ⊆ (R.chart j).source ∧
      ∃ s : M.Xc → (Σ k, ι k) → ℂ, (∀ y ∈ W, s y ∈ mcPts P ∧ M.proj (s y) = y) ∧
        ∀ p, M.atlas.HoloOn W fun y => s y p := by
    intro x
    obtain ⟨U, hU, hxU, s, hs, hhol⟩ := M.sections x
    obtain ⟨j, hj⟩ := R.cover x
    refine ⟨U ∩ (R.chart j).source, hU.inter (R.chart j).open_source,
      ⟨hxU, R.mid_subset_source j (R.inner_subset_mid j hj)⟩, j, inter_subset_right, s,
      fun y hy => hs y hy.1, fun p i => ?_⟩
    exact (hhol p i).mono (inter_subset_inter_right _ (preimage_mono inter_subset_left))
  choose W hWo hxW j hWj s hs hhol using hloc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hWo (fun x _ => mem_iUnion.2 ⟨x, hxW x⟩)
  let xs : Fin t.card → M.Xc := fun i => (t.equivFin.symm i : M.Xc)
  refine h K ι P d t.card (fun i => R.chart (j (xs i)) '' W (xs i))
    (fun i => R.chart (j (xs i)) '' W (xs i) ∩ coordDiv (R.S (j (xs i))))
    (fun i w => s (xs i) ((R.chart (j (xs i))).symm w)) {z | M.proj z ∉ R.Yo}
    (fun i => (R.chart (j (xs i))).isOpen_image_of_subset_source (hWo _) (hWj _))
    (fun i => inter_subset_left)
    (fun i => measure_mono_null inter_subset_right (volume_coordDiv _)) ?_ ?_
  · rintro i w ⟨y, hyW, rfl⟩
    refine analyticAt_pi_iff.2 fun p => ?_
    exact GroundTheory.Heights₂.Heights.Regular.analyticAt_comp_symm_of_holoOn (R.compat _) (hhol (xs i) p) hyW
      (hWj _ hyW)
  · rintro z ⟨hzY, hz⟩
    obtain ⟨x, hxt, hzW⟩ := mem_iUnion₂.1 (ht (mem_univ (M.proj z)))
    obtain ⟨i, rfl⟩ : ∃ i, xs i = x := ⟨t.equivFin ⟨x, hxt⟩, by simp [xs]⟩
    have hsrc := hWj (xs i) hzW
    have hdiv : R.chart (j (xs i)) (M.proj z) ∈ coordDiv (R.S (j (xs i))) := by
      by_contra hc
      exact hzY ((R.mem_Yo _ _ hsrc).2 hc)
    refine ⟨i, R.chart (j (xs i)) (M.proj z), ⟨⟨M.proj z, hzW, rfl⟩, hdiv⟩, ?_⟩
    have hγ : s (xs i) ((R.chart (j (xs i))).symm (R.chart (j (xs i)) (M.proj z))) = s (xs i) (M.proj z) := by
      rw [(R.chart (j (xs i))).left_inv hsrc]
    rw [hγ]
    obtain ⟨hsm, hsp⟩ := hs (xs i) (M.proj z) hzW
    exact (M.fibre _ hsm z hz).1 hsp

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PMuHomDensityNonneg
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem maDensity_const_nonneg {D : ℕ} {φ : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ} (hφ : ContDiffAt ℝ 2 φ y)
    (hL : ∀ v, 0 ≤ leviForm φ y v) : 0 ≤ maDensity (fun _ : Fin D => φ) y := by
  unfold maDensity
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.mixedDiscriminant_constant]
  have hS : IsSymmSndFDerivAt ℝ φ y := hφ.isSymmSndFDerivAt (by simp)
  have hP := ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.complexHessian_posSemidef hS (zero_le_one' ℝ) hL
  have hd := hP.det_nonneg
  rw [Complex.ofReal_one, one_smul, Matrix.det_transpose] at hd
  have hre : 0 ≤ (cxHessian φ y).det.re := (Complex.nonneg_iff.1 hd).1
  have h1 : (0 : ℝ) ≤ (D.factorial : ℝ) * (2 / Real.pi) ^ D := by positivity
  exact mul_nonneg h1 hre

theorem MuHomDensityNonneg.proof (h : MuSheetLeviNonneg.Statement) : MuHomDensityNonneg.Statement := by
  intro II Ψ _ _ K _ ι _ Ω _ _ E _ _ D O Lt _ _ _ X Q hQ
  filter_upwards [h II Ψ K ι Ω E D O Lt X Q hQ] with y hy w
  unfold sheetDensity
  split_ifs with hγ
  · obtain ⟨h2, hL⟩ := hy w _ hγ.choose_spec
    rw [one_mul]
    exact maDensity_const_nonneg h2 hL
  · exact le_rfl

end GroundTheory.Heights₂.Heights.LowerBoundFree
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PParamImageNull
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo

theorem ParamImageNull.segre_torusSmul {K : Type} [Fintype K] {ι : K → Type} (c : K → ℂ) (v : (Σ k, ι k) → ℂ) :
    segre (torusSmul c v) = (∏ k, c k) • segre v := by
  funext x
  simp [segre, torusSmul, Finset.prod_mul_distrib]

theorem ParamImageNull.differentiableAt_segre_comp {K : Type} [Fintype K] {ι : K → Type} {d : ℕ}
    {f : (Fin d → ℂ) → (Σ k, ι k) → ℂ} {w : Fin d → ℂ} (hf : DifferentiableAt ℂ f w) :
    DifferentiableAt ℂ (fun u => segre (f u)) w := by
  refine differentiableAt_pi.2 fun x => ?_
  simp only [segre]
  have hk : ∀ k, DifferentiableAt ℂ (fun u => f u ⟨k, x k⟩) w := fun k => differentiableAt_pi.1 hf ⟨k, x k⟩
  fun_prop

theorem ParamImageNull.proof : ParamImageNull.Statement := by
  intro K _ ι _ P d m V A γ N _hV hAV hA hγ hN Ψ _
  classical
  set G : Fin m → (Fin d → ℂ) → Fin (d + 1) → ℂ := fun i w => Ψ (segre (γ i w)) with hG
  set F : Fin m → (Fin d → ℂ) → Fin d → ℂ := fun i w l => G i w l.succ / G i w 0 with hF
  have hsub : {y : Fin d → ℂ | ∃ z ∈ mcPts P, z ∈ N ∧ Ψ (segre z) = Fin.cons 1 y} ⊆
      ⋃ i, F i '' (A i ∩ {w | G i w 0 ≠ 0}) := by
    rintro y ⟨z, hzP, hzN, hzy⟩
    obtain ⟨i, w, hw, c, hc, rfl⟩ := hN z ⟨hzN, hzP⟩
    rw [ParamImageNull.segre_torusSmul, map_smul] at hzy
    have h0 := congrFun hzy 0
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_zero] at h0
    have hG0 : G i w 0 ≠ 0 := by
      intro h
      rw [hG] at h
      simp only at h
      rw [h, mul_zero] at h0
      exact zero_ne_one h0
    refine Set.mem_iUnion.2 ⟨i, w, ⟨hw, hG0⟩, ?_⟩
    funext l
    have hl := congrFun hzy l.succ
    simp only [Pi.smul_apply, smul_eq_mul, Fin.cons_succ] at hl
    simp only [hF]
    rw [div_eq_iff hG0, ← hl]
    have h0' : (∏ k, c k) * G i w 0 = 1 := h0
    calc G i w l.succ = G i w l.succ * ((∏ k, c k) * G i w 0) := by rw [h0', mul_one]
      _ = (∏ k, c k) * Ψ (segre (γ i w)) l.succ * G i w 0 := by simp only [hG]; ring
  refine measure_mono_null hsub (measure_iUnion_null fun i => ?_)
  refine addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume ?_
    (measure_mono_null Set.inter_subset_left (hA i))
  intro w ⟨hwA, hw0⟩
  have hγw : DifferentiableAt ℂ (γ i) w := (hγ i w (hAV i hwA)).differentiableAt
  have hGw : DifferentiableAt ℂ (G i) w :=
    (LinearMap.toContinuousLinearMap Ψ).differentiableAt.comp w (ParamImageNull.differentiableAt_segre_comp hγw)
  have hFw : DifferentiableAt ℂ (F i) w := by
    refine differentiableAt_pi.2 fun l => ?_
    show DifferentiableAt ℂ (fun u => G i u l.succ / G i u 0) w
    simp only [div_eq_mul_inv]
    exact (differentiableAt_pi.1 hGw l.succ).mul ((differentiableAt_pi.1 hGw 0).inv hw0)
  exact (hFw.restrictScalars ℝ).differentiableWithinAt

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.PPtsMonoSemipos
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo Filter Topology

theorem maDensity_logDiv_nonneg_of_sheet {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {L : HermLine ι} (hsp : IsSemipositiveH P L) {r : ℝ} (hr : 0 < r) {e : ℕ}
    {Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)} {y : Fin e → ℂ}
    {w : ((k : K) → ι k) → ℂ} {γ : (Fin e → ℂ) → (Σ k, ι k) → ℂ} (h : IsSheet P Ψ y w γ) :
    0 ≤ maDensity (fun (_ : Fin e) y' => Real.log (L.h (γ y')) / r) y := by
  have hA : AnalyticAt ℂ γ y := sheet_analyticAt osgood h
  have hpts : ∀ᶠ y' in 𝓝 y, γ y' ∈ mcPts P := h.2.mono fun _ hy' => hy'.2.1
  have hy : γ y ∈ mcPts P := hpts.self_of_nhds
  have hh : ContDiffAt ℝ 2 L.h (γ y) :=
    (hsp.1.contDiffAt
      (HilbertSamuel.IntegralAgainstPositive.isOpen_blocksNonzero.mem_nhds hy.1)).of_le
      (WithTop.coe_le_coe.2 le_top)
  have hlog : ContDiffAt ℝ 2 (fun z => Real.log (L.h z)) (γ y) := hh.log (L.pos _ hy.1).ne'
  have h2 : ContDiffAt ℝ 2 (fun y' => Real.log (L.h (γ y'))) y :=
    hlog.comp y (hA.contDiffAt.restrict_scalars ℝ)
  have h2r : ContDiffAt ℝ 2 (fun y' => Real.log (L.h (γ y')) / r) y := h2.div_const r
  rw [ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.adens_maDensity_eq_maDens]
  refine ReciprocityTheory.AnForm.A.maDens_nonneg_of_posSemidef _ _ fun _ => ?_
  refine ReciprocityTheory.AnForm.A.hessC_posSemidef_of_levi _ _ h2r fun ξ => ?_
  have hfun : (fun y' => Real.log (L.h (γ y')) / r) =
      fun y' => (fun _ : Fin e → ℂ => (0 : ℝ)) y' + r⁻¹ * Real.log (L.h (γ y')) := by
    funext y'
    simp [div_eq_inv_mul]
  rw [hfun, ReciprocityTheory.AnForm.levi_add_smul r⁻¹ contDiffAt_const h2 ξ]
  have h0 : ReciprocityTheory.AnForm.levi (fun _ : Fin e → ℂ => (0 : ℝ)) y ξ = 0 := by
    simp [ReciprocityTheory.AnForm.levi]
  have hc : 0 ≤ ReciprocityTheory.AnForm.levi ((fun z => Real.log (L.h z)) ∘ γ) y ξ := by
    rw [ReciprocityTheory.AnForm.levi_comp (φ := fun z => Real.log (L.h z)) ξ hA hlog]
    exact hsp.2 _ hy _ (HilbertSamuel.IntegralAgainstPositive.isConeTangent_of_sheet le_rfl hA hpts ξ)
  rw [h0, zero_add]
  exact mul_nonneg (inv_nonneg.2 hr.le) hc

theorem PtsMonoSemipos.proof : PtsMonoSemipos.Statement := by
  intro K _ ι _ P e L r g₁ g₂ N hP hL hr hN hle h1 h2
  classical
  unfold ptsIntegral
  by_cases hΨ : ∃ Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ), IsGoodProj P Ψ
  swap
  · rw [dif_neg hΨ, dif_neg hΨ]
  rw [dif_pos hΨ, dif_pos hΨ]
  have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
  unfold ptsIntegralAt
  refine integral_mono_ae (h1 _ hΨg) (h2 _ hΨg) ?_
  rw [Filter.EventuallyLE, ae_iff]
  refine measure_mono_null (fun y hy => ?_) (hN _ hΨg)
  by_contra hyB
  apply hy
  have hfin := fibreFinite K ι P e hΨ.choose hP hΨg y
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine Finset.sum_le_sum fun w _ => ?_
  unfold sheetDensity
  by_cases hγ : ∃ γ, IsSheet P hΨ.choose y w γ
  · rw [dif_pos hγ, dif_pos hγ]
    obtain ⟨-, hev⟩ := hγ.choose_spec
    obtain ⟨-, hmem, hproj⟩ := hev.self_of_nhds
    have hnot : hγ.choose y ∉ N := fun hN' => hyB ⟨hγ.choose y, hmem, hN', hproj⟩
    exact mul_le_mul_of_nonneg_right (hle _ hmem hnot)
      (maDensity_logDiv_nonneg_of_sheet hL hr hγ.choose_spec)
  · rw [dif_neg hγ, dif_neg hγ]

end GroundTheory.Heights₂.Heights.LowerBoundFree
end
end

