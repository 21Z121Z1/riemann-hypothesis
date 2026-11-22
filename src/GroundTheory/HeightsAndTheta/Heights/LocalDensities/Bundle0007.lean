import Mathlib
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.Statements
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.FlagPsDeriv
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.FourB

open Polynomial Matrix

noncomputable section

variable {N : ℕ} (p i : ℕ) (hi : i ≤ N)

theorem lowerMatrix_strict (u : LowerPair N → ℂ) :
    ∀ a b : Fin N, ¬ b < a → lowerMatrix u a b = 0 := by
  intro a b h
  simp [lowerMatrix, h]

theorem coeff_trace_kerPoly (L : Matrix (Fin N) (Fin N) ℂ) :
    (kerPoly p i hi L).trace.coeff 0 = (sigTop p i hi * tailForm p i hi L).trace := by
  have hV : (topPoly i hi L).map (evalRingHom 0) = 1 := by
    refine Matrix.ext fun a b => ?_
    simp [topPoly, colPoly, Matrix.one_apply, Fin.castLE_inj] <;> split_ifs <;> simp
  have hV' : (topPoly' i hi L).map (evalRingHom 0) = 1 := by
    refine Matrix.ext fun a b => ?_
    simp [topPoly', rowPoly, Matrix.one_apply, Fin.castLE_inj, eq_comm] <;> split_ifs <;> simp
  have hadj : ∀ M : Matrix (Fin i) (Fin i) ℂ[X],
      M.adjugate.map (evalRingHom 0) = (M.map (evalRingHom 0)).adjugate := fun M =>
    (evalRingHom (0 : ℂ)).map_adjugate M
  have hC : ∀ M : Matrix (Fin i) (Fin i) ℂ, (M.map C).map (evalRingHom 0) = M := fun M => by
    refine Matrix.ext fun a b => ?_
    simp
  have hmap : (kerPoly p i hi L).map (evalRingHom 0) = sigTop p i hi * tailForm p i hi L := by
    simp only [kerPoly, Matrix.map_mul, hadj, hV, hV', adjugate_one, Matrix.mul_one, hC]
  rw [coeff_zero_eq_eval_zero, ← hmap]
  simp [Matrix.trace, eval_finsetSum]

theorem re_trace_sigTop_tail (L : Matrix (Fin N) (Fin N) ℂ) :
    (sigTop p i hi * tailForm p i hi L).trace.re = tailSum p i L := by
  rw [tailSum, sum_fin_split_castLE hi (fun b => ∑ c : Fin N,
    if b.val < i ∧ i ≤ c.val then sigSign p b * sigSign p c * ‖L c b‖ ^ 2 else 0)]
  have h2 : (∑ b : Fin N, if i ≤ b.val then (∑ c : Fin N,
      if b.val < i ∧ i ≤ c.val then sigSign p b * sigSign p c * ‖L c b‖ ^ 2 else 0) else 0) =
      0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    split_ifs with hb
    · exact Finset.sum_eq_zero fun c _ => if_neg (by omega)
    · rfl
  rw [h2, add_zero, Matrix.trace, Complex.re_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp only [Matrix.diag_apply, sigTop, tailForm, Matrix.diagonal_mul, Matrix.of_apply,
    Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have ha : (Fin.castLE hi a).val < i := by simp
  by_cases hc : i ≤ c.val
  · rw [if_pos hc, if_pos ⟨ha, hc⟩]
    have : star (L c (Fin.castLE hi a)) * ((sigSign p c : ℝ) : ℂ) * L c (Fin.castLE hi a) =
        ((sigSign p c * ‖L c (Fin.castLE hi a)‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm (star _), mul_assoc, Complex.star_def, Complex.conj_mul']
      push_cast
      ring
    rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  · rw [if_neg hc, if_neg (fun h => hc h.2)]
    simp

theorem colPoly_eval (u : LowerPair N → ℂ) (t : ℝ) :
    (colPoly i hi (lowerMatrix u)).map (evalRingHom (t : ℂ)) =
      ((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (t • u)).submatrix id (Fin.castLE hi) := by
  refine Matrix.ext fun c b => ?_
  by_cases h : Fin.castLE hi b < c
  · simp [colPoly, lowerMatrix, Matrix.one_apply, h, Complex.real_smul] <;> split_ifs <;>
      simp [mul_comm]
  · simp [colPoly, lowerMatrix, Matrix.one_apply, h] <;> split_ifs <;> simp

theorem rowPoly_eval (u : LowerPair N → ℂ) (t : ℝ) :
    (rowPoly i hi (lowerMatrix u)).map (evalRingHom (t : ℂ)) =
      (((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (t • u)).submatrix id
        (Fin.castLE hi)).conjTranspose := by
  refine Matrix.ext fun a c => ?_
  by_cases h : Fin.castLE hi a < c
  · have h2 : c ≠ Fin.castLE hi a := fun h' => by rw [h'] at h; exact lt_irrefl _ h
    simp only [Matrix.map_apply, rowPoly, Matrix.of_apply, coe_evalRingHom, eval_add, eval_mul,
      eval_X, eval_C, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id_eq,
      Matrix.add_apply, Matrix.one_apply, lowerMatrix, dif_pos h, if_neg h2, eval_zero, zero_add]
    simp [Complex.real_smul, mul_comm]
  · by_cases h2 : c = Fin.castLE hi a
    · subst h2; simp [rowPoly, lowerMatrix]
    · simp [rowPoly, lowerMatrix, h, h2]

theorem det_flag_eval (u : LowerPair N → ℂ) (t : ℝ) :
    ((((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (t • u)).submatrix id
        (Fin.castLE hi)).conjTranspose * signatureForm N p *
        ((1 + lowerMatrix (t • u)).submatrix id (Fin.castLE hi))).det =
      (sigTop p i hi).det *
        ((1 + (X ^ 2 : ℂ[X]) • kerPoly p i hi (lowerMatrix u)).det).eval (t : ℂ) := by
  have hS : signatureForm N p = ((signatureForm N p).map C).map (evalRingHom (t : ℂ)) := by
    refine Matrix.ext fun a b => ?_
    simp
  rw [← rowPoly_eval, ← colPoly_eval, hS, ← Matrix.map_mul, ← Matrix.map_mul]
  rw [show ∀ M : Matrix (Fin i) (Fin i) ℂ[X], (M.map (evalRingHom (t : ℂ))).det =
      evalRingHom (t : ℂ) M.det from fun M => ((evalRingHom (t : ℂ)).map_det M).symm]
  rw [det_gram p i hi (lowerMatrix_strict u)]
  simp

theorem norm_det_sigTop : ‖(sigTop p i hi).det‖ = 1 := by
  rw [sigTop, det_diagonal, norm_prod]
  refine Finset.prod_eq_one fun a _ => ?_
  unfold sigSign
  split_ifs <;> simp

theorem flagPs_smul (u : LowerPair N → ℂ) (t : ℝ) :
    flagPs N p i hi (t • u) =
      Real.log ‖((1 + (X ^ 2 : ℂ[X]) • kerPoly p i hi (lowerMatrix u)).det).eval (t : ℂ)‖ := by
  rw [flagPs, det_flag_eval, norm_mul, norm_det_sigTop, one_mul]

theorem deriv_deriv_flagPs (u : LowerPair N → ℂ) :
    deriv (deriv fun t : ℝ => flagPs N p i hi (t • u)) 0 = 2 * tailSum p i (lowerMatrix u) := by
  simp only [flagPs_smul]
  obtain ⟨h0, h1, h2⟩ := coeff_det_one_add_X_sq_smul (kerPoly p i hi (lowerMatrix u))
  rw [deriv_deriv_log_norm_eval _ h0 h1, h2, coeff_trace_kerPoly, re_trace_sigTop_tail]

theorem contDiffAt_flagPs {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → (LowerPair N → ℂ)} (hg : ContDiff ℝ 2 g) (hg0 : g 0 = 0) :
    ContDiffAt ℝ 2 (fun z => flagPs N p i hi (g z)) 0 := by
  have hent : ∀ a b, ContDiff ℝ 2 fun z =>
      ((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (g z)) a b := by
    intro a b
    by_cases h : b < a
    · simp only [Matrix.add_apply, lowerMatrix, Matrix.of_apply, h, dif_pos]
      exact contDiff_const.add
        ((by fun_prop : ContDiff ℝ 2 fun f : LowerPair N → ℂ => f ⟨(a, b), h⟩).comp hg)
    · simp only [Matrix.add_apply, lowerMatrix, Matrix.of_apply, h, dif_neg, not_false_eq_true,
        add_zero]
      exact contDiff_const
  have hdet : ContDiff ℝ 2 fun z => ((((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (g z)).submatrix
      id (Fin.castLE hi)).conjTranspose * signatureForm N p *
      ((1 + lowerMatrix (g z)).submatrix id (Fin.castLE hi))).det := by
    refine contDiff_det_of_entries fun a b => ?_
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply, id]
    refine ContDiff.sum fun c _ => ContDiff.mul (ContDiff.sum fun d _ => ContDiff.mul ?_
      contDiff_const) (hent _ _)
    simpa [Function.comp_def] using Complex.conjCLE.contDiff.comp (hent d (Fin.castLE hi a))
  have h0 : ((((1 : Matrix (Fin N) (Fin N) ℂ) + lowerMatrix (g 0)).submatrix id
      (Fin.castLE hi)).conjTranspose * signatureForm N p *
      ((1 + lowerMatrix (g 0)).submatrix id (Fin.castLE hi))).det ≠ 0 := by
    have h := det_flag_eval p i hi (0 : LowerPair N → ℂ) 0
    rw [zero_smul] at h
    rw [hg0, h, Complex.ofReal_zero, ← coeff_zero_eq_eval_zero,
      (coeff_det_one_add_X_sq_smul _).1, mul_one]
    intro h'
    have := norm_det_sigTop p i hi
    rw [h', norm_zero] at this
    exact zero_ne_one this
  unfold flagPs
  exact (ContDiffAt.norm ℝ hdet.contDiffAt h0).log (norm_ne_zero_iff.mpr h0)

end

end GroundTheory.Heights₂.Heights.FourB
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.LocalDensities.OfFubiniStudyCoverMass
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.FourB

open MeasureTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M Filter Topology
open scoped ContDiff

namespace OpenSetChart

variable {D : ℕ} {M : Set (Fin D → ℂ)}

open scoped Classical in

def retract (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) (y : Fin D → ℂ) : M :=
  ⟨if y ∈ M then y else x₀, by split_ifs with h; exacts [h, hx₀]⟩

theorem retract_of_mem {x₀ : Fin D → ℂ} (hx₀ : x₀ ∈ M) {y : Fin D → ℂ} (hy : y ∈ M) :
    (retract x₀ hx₀ y : Fin D → ℂ) = y := by
  simp [retract, hy]

theorem measurable_retract (hM : IsOpen M) {x₀ : Fin D → ℂ} (hx₀ : x₀ ∈ M) :
    Measurable (retract x₀ hx₀) := by
  classical
  unfold retract
  exact (Measurable.ite hM.measurableSet measurable_id measurable_const).subtype_mk

def chart (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) : OpenPartialHomeomorph M (Fin D → ℂ) where
  toFun := Subtype.val
  invFun := retract x₀ hx₀
  source := Set.univ
  target := M
  map_source' x _ := x.2
  map_target' _ _ := Set.mem_univ _
  left_inv' x _ := Subtype.ext (retract_of_mem hx₀ x.2)
  right_inv' _ hy := retract_of_mem hx₀ hy
  open_source := isOpen_univ
  open_target := hM
  continuousOn_toFun := continuous_subtype_val.continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert (continuous_id : Continuous (id : M → M)) using 1
    funext y
    exact Subtype.ext (retract_of_mem hx₀ y.2)

theorem eventuallyEq_retract (hM : IsOpen M) {x₀ : Fin D → ℂ} (hx₀ : x₀ ∈ M) {y : Fin D → ℂ}
    (hy : y ∈ M) : (fun y' => (retract x₀ hx₀ y' : Fin D → ℂ)) =ᶠ[𝓝 y] id :=
  Filter.eventually_of_mem (hM.mem_nhds hy) fun _ hy' => retract_of_mem hx₀ hy'

def atlas (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) : FinHolAtlas D M where
  n := 1
  chart _ := chart hM x₀ hx₀
  cover _ := ⟨0, Set.mem_univ _⟩
  holo _ _ := fun _ hy => analyticAt_id.congr (eventuallyEq_retract hM hx₀ hy.1).symm

def partition (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) :
    ChartPartition (atlas hM x₀ hx₀) where
  χ _ _ := 1
  smooth _ := fun _ => contDiffOn_const
  nonneg _ _ := zero_le_one
  tsupport_subset _ := fun _ _ => Set.mem_univ _
  sum_eq_one _ := by
    show ∑ _j : Fin 1, (1 : ℝ) = 1
    simp

theorem maMeasure_univ (hM : IsOpen M) (x₀ : Fin D → ℂ) (hx₀ : x₀ ∈ M) (u : M → ℝ) :
    maMeasure (atlas hM x₀ hx₀) (fun _ => LocPot.ofFun u) Set.univ =
      ∫⁻ y in M, ENNReal.ofReal (maDens (fun _ y' => u (retract x₀ hx₀ y')) y) := by
  have hne : Nonempty (ChartPartition (atlas hM x₀ hx₀)) := ⟨partition hM x₀ hx₀⟩
  have : Subsingleton (Fin (atlas hM x₀ hx₀).n) := (inferInstance : Subsingleton (Fin 1))
  have hχ : ∀ j x, hne.some.χ j x = 1 := by
    intro j x
    have h := hne.some.sum_eq_one x
    rwa [Fintype.sum_subsingleton _ j] at h
  let j0 : Fin (atlas hM x₀ hx₀).n := ⟨0, Nat.zero_lt_one⟩
  have ht : ((atlas hM x₀ hx₀).chart j0).target = M := rfl
  have hm : Measurable ((atlas hM x₀ hx₀).chart j0).symm := measurable_retract hM hx₀
  rw [maMeasure, dif_pos hne, Fintype.sum_subsingleton _ j0,
    Measure.map_apply hm MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, ht]
  refine lintegral_congr fun y => ?_
  rw [hχ, one_mul]
  rfl

end OpenSetChart

open OpenSetChart

theorem maDens_congr_germ' {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ i, φ i =ᶠ[𝓝 y] ψ i) : maDens φ y = maDens ψ y := by
  have hH : ∀ i, hessC (φ i) y = hessC (ψ i) y := by
    intro i
    have h1 : fderiv ℝ (φ i) =ᶠ[𝓝 y] fderiv ℝ (ψ i) := (h i).fderiv
    unfold hessC
    rw [h1.fderiv_eq]
  unfold maDens
  simp only [hH]

theorem CoverMass2.of_fubiniStudyCoverMass (hA : FubiniStudyCoverMass.Statement) :
    IndefiniteRowSideFullHecke.FourB.CoverMass2.Statement := by
  intro D M Z z δ hB
  obtain ⟨hM, hZ, hz, hmaps, hcov, hfib⟩ := hB
  rcases M.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · have hZc : Zᶜ.Nonempty := by
      by_contra h
      rw [Set.not_nonempty_iff_eq_empty, Set.compl_empty_iff] at h
      rw [h, Measure.measure_univ_eq_zero] at hZ
      exact NeZero.ne (volume : Measure (Fin D → ℂ)) hZ
    obtain ⟨w, hw⟩ := hZc
    have h1 := hfib w hw
    have h0 : {x | x ∈ (∅ : Set (Fin D → ℂ)) ∧ z x = w} = ∅ := by simp
    rw [h0, Set.encard_empty] at h1
    have hδ : δ = 0 := by exact_mod_cast h1.symm
    subst hδ
    simp
  ·
    have hδ : δ ≠ 0 := by
      intro h0
      have h1 := hfib (z x₀) (hmaps hx₀)
      have hmem : x₀ ∈ {x | x ∈ M ∧ z x = z x₀} := ⟨hx₀, rfl⟩
      rw [h0, Nat.cast_zero, Set.encard_eq_zero] at h1
      rw [h1] at hmem
      exact hmem

    have hZcl : IsClosed Z := by
      rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
      intro w hw
      obtain ⟨-, U, hwU, hU, -, H, hH⟩ := hcov w hw
      obtain ⟨x, hxM, hxw⟩ : {x | x ∈ M ∧ z x = w}.Nonempty := by
        rw [← Set.encard_pos, hfib w hw]
        exact_mod_cast Nat.pos_of_ne_zero hδ
      let i : (fun x : M => z x) ⁻¹' {w} := ⟨⟨x, hxM⟩, hxw⟩
      refine ⟨U, fun v hv => ?_, hU, hwU⟩
      have h1 : v = z (H.symm (⟨v, hv⟩, i)).1 := by
        simpa using hH (H.symm (⟨v, hv⟩, i))
      rw [h1]
      exact hmaps (H.symm (⟨v, hv⟩, i)).1.2

    have han : ∀ i, AnalyticOnNhd ℂ (fun y => z y i) M := fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood D M _ hM (differentiableOn_pi.1 hz i)
    let A := atlas hM x₀ hx₀
    let q : M → Fin D → ℂ := fun x => z x
    let u : M → ℝ := fun x => (1 / 2) * Real.log (1 + ∑ i, ‖q x i‖ ^ 2)
    have hsm : ContDiffOn ℝ ∞ (fun y => (1 / 2) * Real.log (1 + ∑ i, ‖z y i‖ ^ 2)) M := by
      refine contDiffOn_const.mul (ContDiffOn.log (contDiffOn_const.add (ContDiffOn.sum
        fun i _ => (contDiff_norm_sq ℝ).comp_contDiffOn
          (((han i).contDiffOn hM.uniqueDiffOn).restrict_scalars ℝ))) fun y _ => ?_)
      positivity
    have hu : A.Smooth u := by
      intro j
      refine (hsm.mono Set.inter_subset_left).congr fun y hy => ?_
      show u (retract x₀ hx₀ y) = _
      simp only [u, q, retract_of_mem hx₀ hy.1]
    have hHyp : FubiniStudyCoverMass.Hyp A (LocPot.ofFun u) q Set.univ Z δ := by
      refine ⟨isPotential_ofFun A u hu, isOpen_univ, ?_, ?_, ?_, hZcl, hZ,
        ⟨fun x _ => hmaps x.2, ?_⟩, ?_, ?_⟩
      · intro x
        refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 1, fun _ _ => 1,
          fun _ _ => analyticOnNhd_const, ?_⟩
        ext y
        simp
      · simp
      · intro i j y hy
        exact ((han i) y hy.1).congr
          (((eventuallyEq_retract hM hx₀ hy.1).fun_comp fun y' => z y' i).symm)
      · have hpre : (Set.univ : Set M) = (fun x : M => z x) ⁻¹' Zᶜ := by
          ext x
          simpa using hmaps x.2
        exact hcov.isCoveringMap_restrictPreimage.comp_homeomorph (Homeomorph.setCongr hpre)
      · intro w hw
        rw [← hfib w hw, ← Subtype.val_injective.encard_image]
        congr 1
        ext y
        simp [q, and_comm]
      · intro x y _
        refine ⟨Set.univ, isOpen_univ, Set.mem_univ _, 0, fun _ _ _ => analyticAt_const, ?_⟩
        intro v _
        simp [LocPot.ofFun, u]
    have key := (hA A (LocPot.ofFun u) q Set.univ Z δ hHyp).2
    rw [maMeasure_univ] at key
    rw [← key]
    refine setLIntegral_congr_fun hM.measurableSet fun y hy => ?_
    show ENNReal.ofReal (maDens _ y) = ENNReal.ofReal (maDens _ y)
    congr 1
    refine maDens_congr_germ' fun _ => ?_
    filter_upwards [hM.mem_nhds hy] with y' hy'
    simp only [u, q, retract_of_mem hx₀ hy']
    ring

end GroundTheory.Heights₂.Heights.FourB
end
end

