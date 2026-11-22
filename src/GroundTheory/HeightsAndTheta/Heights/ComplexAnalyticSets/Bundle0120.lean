import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0058
import GroundTheory.HeightsAndTheta.Heights.LocalDensities.PFubiniStudyChartDensity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.AMassStA
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0074
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetFormCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0109
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0059
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0116
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0113
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0085
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0111

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPlaneSliceMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology ComplexSets
open scoped ContDiff Matrix

noncomputable section

abbrev affChartIdeal (e : ℕ) : Ideal (MvPolynomial (Fin (e + 1)) ℂ) := Ideal.span {X 0 - 1}

def tailProj (e : ℕ) : Matrix (Fin e) (Fin (e + 1)) ℂ := fun i j => if j = i.succ then 1 else 0

theorem tailProj_mulVec (e : ℕ) (x : Fin (e + 1) → ℂ) : tailProj e *ᵥ x = Fin.tail x := by
  ext i
  simp [tailProj, Matrix.mulVec, dotProduct, Fin.tail]

theorem linPoly_tailProj (e : ℕ) (i : Fin e) : linPoly (tailProj e) i = X i.succ := by
  simp [linPoly, tailProj]

def affChartEquiv (e : ℕ) : MvPolynomial (Fin (e + 1)) ℂ ⧸ affChartIdeal e ≃+* MvPolynomial (Fin e) ℂ :=
  (Ideal.quotientEquiv _ _ (finSuccEquiv ℂ e).toRingEquiv (by
      rw [Ideal.map_span, Set.image_singleton]
      congr 2
      simp [finSuccEquiv_X_zero])).trans
    (Polynomial.quotientSpanXSubCAlgEquiv (1 : MvPolynomial (Fin e) ℂ)).toRingEquiv

theorem affChartEquiv_projHom (e : ℕ) (a : MvPolynomial (Fin e) ℂ) :
    affChartEquiv e (projHom (affChartIdeal e) (tailProj e) a) = a := by
  have h : (affChartEquiv e : _ →+* MvPolynomial (Fin e) ℂ).comp
      (projHom (affChartIdeal e) (tailProj e)).toRingHom = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro c
      have hc : (finSuccEquiv ℂ e) (C c) = algebraMap ℂ _ c := (finSuccEquiv ℂ e).commutes c
      simp [affChartEquiv, projHom, pullback, Polynomial.quotientSpanXSubCAlgEquiv_mk, hc,
        Polynomial.algebraMap_apply, MvPolynomial.algebraMap_eq]
    · intro i
      simp [affChartEquiv, projHom, pullback, linPoly_tailProj,
        Polynomial.quotientSpanXSubCAlgEquiv_mk, finSuccEquiv_X_succ]
  exact RingHom.congr_fun h a

theorem isFiniteProjection_tailProj (e : ℕ) : IsFiniteProjection (affChartIdeal e) (tailProj e) := by
  refine ⟨fun a b h => ?_, RingHom.Finite.of_surjective _ fun z => ⟨affChartEquiv e z, ?_⟩⟩
  · have := congrArg (affChartEquiv e) h
    rwa [affChartEquiv_projHom, affChartEquiv_projHom] at this
  · exact (affChartEquiv e).injective (affChartEquiv_projHom e _)

theorem affChartIdeal_isPrime (e : ℕ) : (affChartIdeal e).IsPrime := by
  have : IsDomain (MvPolynomial (Fin (e + 1)) ℂ ⧸ affChartIdeal e) := (affChartEquiv e).toMulEquiv.isDomain _
  exact (Ideal.Quotient.isDomain_iff_prime _).mp inferInstance

theorem affChartIdeal_dim (e : ℕ) :
    ringKrullDim (MvPolynomial (Fin (e + 1)) ℂ ⧸ affChartIdeal e) = (e : ℕ) := by
  rw [ringKrullDim_eq_of_ringEquiv (affChartEquiv e), MvPolynomial.ringKrullDim_of_isNoetherianRing,
    ringKrullDim_eq_zero_of_field]
  simp

theorem mem_zeroSet_affChartIdeal {e : ℕ} (x : Fin (e + 1) → ℂ) : x ∈ zeroSet (affChartIdeal e) ↔ x 0 = 1 := by
  constructor
  · intro h
    have := h _ (Ideal.subset_span rfl)
    simpa [sub_eq_zero] using this
  · intro h q hq
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hq
    simp [h]

theorem fibre_affChartIdeal {e : ℕ} (y : Fin e → ℂ) :
    fibre (affChartIdeal e) (tailProj e) y = {(Fin.cons 1 y : Fin (e + 1) → ℂ)} := by
  ext x
  simp only [fibre, Set.mem_ofPred_eq, mem_zeroSet_affChartIdeal, Set.mem_singleton_iff]
  rw [tailProj_mulVec]
  constructor
  · rintro ⟨h0, ht⟩
    rw [← Fin.cons_self_tail x, h0, ht]
  · rintro rfl
    simp

theorem differentiable_consOne (e : ℕ) :
    Differentiable ℂ (fun y : Fin e → ℂ => (Fin.cons 1 y : Fin (e + 1) → ℂ)) := by
  intro y
  rw [differentiableAt_pi]
  intro j
  refine Fin.cases ?_ (fun i => ?_) j
  · simp
  · simpa using differentiableAt_apply (𝕜 := ℂ) i y

theorem isSheetAt_consOne {e : ℕ} (y : Fin e → ℂ) :
    IsSheetAt (affChartIdeal e) (tailProj e) (Fin.cons 1 y) fun y' => (Fin.cons 1 y' : Fin (e + 1) → ℂ) := by
  refine ⟨Set.univ, isOpen_univ, trivial, (differentiable_consOne e).differentiableOn, ?_,
    fun y' _ => ⟨?_, ?_⟩, Set.univ, univ_mem, fun x' hx' _ => ?_⟩
  · rw [tailProj_mulVec, Fin.tail_cons]
  · rw [tailProj_mulVec, Fin.tail_cons]
  · rw [mem_zeroSet_affChartIdeal]
    rfl
  · rw [tailProj_mulVec]
    conv_lhs => rw [← Fin.cons_self_tail x']
    rw [(mem_zeroSet_affChartIdeal x').1 hx'.1]

theorem affChart_sheet_eventuallyEq {e : ℕ} {y : Fin e → ℂ} {s : (Fin e → ℂ) → Fin (e + 1) → ℂ}
    (h : IsSheetAt (affChartIdeal e) (tailProj e) (Fin.cons 1 y) s) :
    s =ᶠ[𝓝 y] fun y' => (Fin.cons 1 y' : Fin (e + 1) → ℂ) := by
  obtain ⟨U, hU, hyU, -, -, hsec, -⟩ := h
  rw [tailProj_mulVec, Fin.tail_cons] at hyU
  filter_upwards [hU.mem_nhds hyU] with y' hy'
  obtain ⟨h1, h2⟩ := hsec y' hy'
  rw [tailProj_mulVec] at h1
  rw [mem_zeroSet_affChartIdeal] at h2
  rw [← Fin.cons_self_tail (s y'), h2, h1]

theorem sheetSum_affChartIdeal {e : ℕ} (F : (Fin (e + 1) → ℂ) → ((Fin e → ℂ) → Fin (e + 1) → ℂ) → ℝ)
    (y : Fin e → ℂ) (hF : ∀ s, s =ᶠ[𝓝 y] (fun y' => (Fin.cons 1 y' : Fin (e + 1) → ℂ)) →
      F (Fin.cons 1 y) s = F (Fin.cons 1 y) fun y' => Fin.cons 1 y') :
    sheetSum (affChartIdeal e) (tailProj e) F y = F (Fin.cons 1 y) fun y' => Fin.cons 1 y' := by
  unfold sheetSum
  rw [fibre_affChartIdeal, finsum_mem_singleton]
  have hex : ∃ s, IsSheetAt (affChartIdeal e) (tailProj e) (Fin.cons 1 y) s := ⟨_, isSheetAt_consOne y⟩
  rw [dif_pos hex]
  exact hF _ (affChart_sheet_eventuallyEq hex.choose_spec)

theorem maDens_congr {D : ℕ} {F G : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ k, F k =ᶠ[𝓝 z] G k) : ReciprocityTheory.AnForm.maDens F z = ReciprocityTheory.AnForm.maDens G z := by
  have h2 : ∀ k, fderiv ℝ (fderiv ℝ (F k)) z = fderiv ℝ (fderiv ℝ (G k)) z :=
    fun k => ((h k).fderiv (𝕜 := ℝ)).fderiv_eq
  have h3 : (fun k => ReciprocityTheory.AnForm.hessC (F k) z) = fun k => ReciprocityTheory.AnForm.hessC (G k) z := by
    funext k
    ext i j
    dsimp only [ReciprocityTheory.AnForm.hessC]
    rw [h2 k]
  unfold ReciprocityTheory.AnForm.maDens
  rw [h3]

theorem dualNorm_std {n : ℕ} (x : Fin n → ℂ) : (HermNorm.std n).dualNorm x = √(∑ i, ‖x i‖ ^ 2) := by
  simp [HermNorm.dualNorm, HermNorm.std]

theorem log_dualNorm_consOne {e : ℕ} (y : Fin e → ℂ) :
    Real.log ((HermNorm.std (e + 1)).dualNorm (Fin.cons 1 y)) =
      (1 / 2) * Real.log (1 + ∑ i, ‖y i‖ ^ 2) := by
  rw [dualNorm_std, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, norm_one, one_pow]
  rw [Real.log_sqrt (by positivity)]
  ring

def fsChartDens (e : ℕ) (y : Fin e → ℂ) : ℝ :=
  (e.factorial : ℝ) / (Real.pi ^ e * (1 + ∑ i, ‖y i‖ ^ 2) ^ (e + 1))

theorem fsChartDens_nonneg {e : ℕ} (y : Fin e → ℂ) : 0 ≤ fsChartDens e y := by
  unfold fsChartDens
  have : 0 < 1 + ∑ i, ‖y i‖ ^ 2 := by positivity
  have := Real.pi_pos
  positivity

theorem maDens_consOne {e : ℕ} (y : Fin e → ℂ) (s : (Fin e → ℂ) → Fin (e + 1) → ℂ)
    (hs : s =ᶠ[𝓝 y] fun y' => (Fin.cons 1 y' : Fin (e + 1) → ℂ)) :
    ReciprocityTheory.AnForm.maDens
        (fun k => (fun (_ : Fin e) x => Real.log ((HermNorm.std (e + 1)).dualNorm x)) k ∘ s) y =
      fsChartDens e y := by
  rw [maDens_congr (G := fun _ y' => (1 / 2) * Real.log (1 + ∑ i, ‖y' i‖ ^ 2)) fun k => ?_]
  · exact (FourB.FubiniStudyChartDensity.proof e y y).2
  · filter_upwards [hs] with y' hy'
    simp only [Function.comp_apply, hy', log_dualNorm_consOne]

theorem chartDens_affChartIdeal {e : ℕ} (y : Fin e → ℂ) :
    chartDens (affChartIdeal e) (tailProj e) (fun _ => 1)
      (fun _ x => Real.log ((HermNorm.std (e + 1)).dualNorm x)) y = fsChartDens e y := by
  unfold chartDens
  rw [sheetSum_affChartIdeal _ y fun s hs => by rw [maDens_consOne y s hs,
    maDens_consOne y _ (EventuallyEq.refl _ _)]]
  rw [one_mul, maDens_consOne y _ (EventuallyEq.refl _ _)]

theorem chartAbsDens_affChartIdeal {e : ℕ} (y : Fin e → ℂ) :
    chartAbsDens (affChartIdeal e) (tailProj e) (fun _ => 1)
      (fun _ x => Real.log ((HermNorm.std (e + 1)).dualNorm x)) y = fsChartDens e y := by
  unfold chartAbsDens
  rw [sheetSum_affChartIdeal _ y fun s hs => by rw [maDens_consOne y s hs,
    maDens_consOne y _ (EventuallyEq.refl _ _)]]
  rw [one_mul, maDens_consOne y _ (EventuallyEq.refl _ _), abs_of_nonneg (fsChartDens_nonneg y)]

theorem integral_fsChartDens (e : ℕ) : ∫ y, fsChartDens e y = 1 := by
  have h : fsChartDens e = fun y => ((e.factorial : ℝ) / Real.pi ^ e) *
      ((1 + ∑ i, ‖y i‖ ^ 2) ^ (e + 1))⁻¹ := by
    funext y
    rw [fsChartDens, div_eq_mul_inv, div_eq_mul_inv, mul_inv]
    ring
  rw [h, integral_const_mul, ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.gaM_integral_fsDens]
  have : (e.factorial : ℝ) ≠ 0 := by positivity
  have : Real.pi ^ e ≠ 0 := pow_ne_zero _ Real.pi_ne_zero
  field_simp

theorem integrable_fsChartDens (e : ℕ) : Integrable (fsChartDens e) :=
  Integrable.of_integral_ne_zero (by rw [integral_fsChartDens]; exact one_ne_zero)

theorem smoothNear_log_dualNorm (e : ℕ) :
    SmoothNear (zeroSet (affChartIdeal e)) fun x => Real.log ((HermNorm.std (e + 1)).dualNorm x) := by
  refine ⟨{x | x 0 ≠ 0}, isOpen_ne_fun (continuous_apply 0) continuous_const, fun x hx => ?_, ?_⟩
  · rw [Set.mem_ofPred_eq, (mem_zeroSet_affChartIdeal x).1 hx]
    exact one_ne_zero
  · intro x hx
    have h0 : 0 < ‖x 0‖ ^ 2 := pow_pos (norm_pos_iff.2 hx) 2
    have hpos : 0 < euclPot x :=
      lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun i => ‖x i‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ 0))
    have hf : (fun x => Real.log ((HermNorm.std (e + 1)).dualNorm x)) =
        fun x => Real.log (√(euclPot x)) := funext fun x => by rw [dualNorm_std]; rfl
    rw [hf]
    refine ContDiffAt.contDiffWithinAt ?_
    exact (Real.contDiffAt_log.2 (Real.sqrt_pos.2 hpos).ne').comp x
      ((Real.contDiffAt_sqrt hpos.ne').comp x (contDiff_euclPot _).contDiffAt)

theorem PlaneSliceMass.proof (h₁ : IntegralIndep.Statement) : PlaneSliceMass.Statement := by
  intro e
  have hex : ∃ A : Matrix (Fin e) (Fin (e + 1)) ℂ, IsFiniteProjection (affChartIdeal e) A :=
    ⟨_, isFiniteProjection_tailProj e⟩
  show varInt (affChartIdeal e) e _ _ = 1
  unfold varInt
  rw [dif_pos hex]
  have habs : Integrable (chartAbsDens (affChartIdeal e) (tailProj e) (fun _ => 1)
      fun _ x => Real.log ((HermNorm.std (e + 1)).dualNorm x)) := by
    rw [funext chartAbsDens_affChartIdeal]
    exact integrable_fsChartDens e
  obtain ⟨-, heq⟩ := h₁ (e + 1) e _ (tailProj e) hex.choose _ _ (affChartIdeal_isPrime e)
    (affChartIdeal_dim e) (isFiniteProjection_tailProj e) hex.choose_spec measurable_const
    (fun _ => smoothNear_log_dualNorm e) habs
  rw [← heq, chartInt, funext chartDens_affChartIdeal, integral_fsChartDens]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PRegFormCompare
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix Filter Topology ReciprocityTheory.AnForm ComplexSets
open scoped ContDiff ComplexOrder

noncomputable section

namespace RegularizedFormComparison

open TubeFormComparison

theorem posSemidef_hessC_logReg_comp {n D : ℕ} (u : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε)
    (s : (Fin D → ℂ) → Fin n → ℂ) (y : Fin D → ℂ) (hs : AnalyticAt ℂ s y) :
    (hessC (logReg u ε ∘ s) y).PosSemidef := by
  set τ : (Fin D → ℂ) → Fin 1 → ℂ := fun z _ => ((√ε : ℝ) : ℂ)⁻¹ * linEval u (s z) with hτ
  have hτa : AnalyticAt ℂ τ y := by
    refine analyticAt_pi_iff.2 fun _ => analyticAt_const.mul ?_
    unfold linEval
    exact Finset.analyticAt_fun_sum (f := fun j z => u j * s z j) _ fun j _ =>
      analyticAt_const.mul (analyticAt_pi_iff.1 hs j)
  have hsq : ((√ε : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (Real.sqrt_pos.2 hε).ne'
  have he : logReg u ε ∘ s =
      fun z => (1 / 2 : ℝ) * HilbertSamuel.ProjFS.logPot (τ z) + Real.log ε / 2 := by
    funext z
    have h1 : HilbertSamuel.ProjFS.logPot (τ z) = Real.log (1 + ‖linEval u (s z)‖ ^ 2 / ε) := by
      show Real.log (1 + euclPot (τ z)) = _
      congr 2
      simp only [euclPot, hτ, Finset.univ_unique, Finset.sum_singleton, norm_mul, norm_inv, mul_pow,
        inv_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg ε),
        Real.sq_sqrt hε.le]
      ring
    have h2 : ‖linEval u (s z)‖ ^ 2 + ε = ε * (1 + ‖linEval u (s z)‖ ^ 2 / ε) := by
      field_simp
      ring
    simp only [Function.comp_apply, logReg]
    rw [h1, h2, Real.log_mul hε.ne' (by positivity)]
    ring
  have hconst : ∀ (F : (Fin D → ℂ) → ℝ) (c : ℝ), hessC (fun z => F z + c) y = hessC F y := by
    intro F c
    have h : fderiv ℝ (fun z => F z + c) = fderiv ℝ F := funext fun z => fderiv_add_const c
    unfold hessC
    rw [h]
  have hL2 : ContDiffAt ℝ 2 (HilbertSamuel.ProjFS.logPot (N := 1)) (τ y) :=
    ((SheetFormComparison.contDiff_logPot 1).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  rw [he, hconst (fun z => (1 / 2 : ℝ) * HilbertSamuel.ProjFS.logPot (τ z)),
    ReciprocityTheory.AnForm.M.hessC_const_mul']
  have hcomp : hessC (fun z => HilbertSamuel.ProjFS.logPot (τ z)) y =
      hessC (HilbertSamuel.ProjFS.logPot ∘ τ) y := rfl
  rw [hcomp, ReciprocityTheory.AnForm.A.hessC_comp _ τ y hτa hL2]
  have hP : (hessC (HilbertSamuel.ProjFS.logPot (N := 1)) (τ y)).PosSemidef :=
    ReciprocityTheory.AnForm.M.hessC_posSemidef _ _ hL2 fun w => HilbertSamuel.ProjFS.levi_logPot_nonneg _ w
  set B := (ReciprocityTheory.AnForm.A.jacC τ y).map (starRingEnd ℂ) with hB
  have hBJ : Bᴴ = (ReciprocityTheory.AnForm.A.jacC τ y)ᵀ := by
    ext a b
    simp [hB]
  rw [← hBJ]
  exact (hP.conjTranspose_mul_mul_same B).smul (Complex.zero_le_real.2 (by norm_num))

theorem maDens_euclPot_nonneg {n d : ℕ} (g : (Fin n → ℂ) → ℝ) (s : (Fin (d + 1) → ℂ) → Fin n → ℂ)
    (y : Fin (d + 1) → ℂ) (hs : AnalyticAt ℂ s y) (hM : (hessC (g ∘ s) y).PosSemidef) :
    0 ≤ maDens (fun k => vecCons g (fun _ : Fin d => euclPot) k ∘ s) y := by
  have hE2 : ∀ _ : Fin d, ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) := fun _ =>
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  have hb : ∀ _ : Fin d, (hessC (euclPot : (Fin n → ℂ) → ℝ) (s y) + ((1 : ℝ) : ℂ) • 1).PosSemidef ∧
      (-hessC (euclPot : (Fin n → ℂ) → ℝ) (s y) + ((1 : ℝ) : ℂ) • 1).PosSemidef := fun _ => by
    rw [hessC_euclPot]
    refine ⟨?_, ?_⟩
    · simpa using Matrix.PosSemidef.one.add Matrix.PosSemidef.one
    · simpa using (Matrix.PosSemidef.zero : (0 : Matrix (Fin n) (Fin n) ℂ).PosSemidef)
  have key := abs_maDens_cons_le g (fun _ : Fin d => euclPot) s y hs hE2 hb hM
  have h0 := (abs_nonneg _).trans key
  rw [one_pow, mul_one] at h0
  exact nonneg_of_mul_nonneg_right h0 (by positivity)

end RegularizedFormComparison

open TubeFormComparison RegularizedFormComparison in

theorem RegFormCompare.proof : RegFormCompare.Statement := by
  intro n d J A φ f _hJ _hdim hA hφ hfc hfs
  set K := zeroSet J ∩ tsupport f with hKdef
  have hK : IsCompact K := hfs.isCompact.inter_left (isClosed_zeroSet J)
  choose U hU hZU hφU using hφ
  obtain ⟨c, hc, hb⟩ := exists_hessC_bound φ K hK U hU
    (fun i => Set.inter_subset_left.trans (hZU i)) (fun i => (hφU i).of_le (WithTop.coe_le_coe.2 le_top))
  obtain ⟨M, hM⟩ := hfc.bounded_above_of_compact_support hfs
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hC : 0 ≤ max M 0 * (3 ^ (d + 1) * c ^ d) := by positivity
  refine ⟨max M 0 * (3 ^ (d + 1) * c ^ d), hC, fun u ε hε v w hw hvw y => ?_⟩
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y),
    finsum_mem_eq_finite_toFinset_sum _ (IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y), Finset.mul_sum]
  refine Finset.sum_le_sum fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  obtain ⟨hxZ, hxy⟩ := hx
  subst hxy
  split_ifs with hsx
  swap
  · simp
  dsimp only
  obtain ⟨V, hV, hyV, hsd, hsx', -, -⟩ := hsx.choose_spec
  set s := hsx.choose with hsdef
  have hsa : AnalyticAt ℂ s (A *ᵥ x) :=
    analyticAt_pi_iff.2 fun i =>
      ReciprocityTheory.AnForm.Osgood.osgood _ V (fun z => s z i) hV (differentiableOn_pi.1 hsd i) _ hyV
  have hMs := posSemidef_hessC_logReg_comp u hε s (A *ᵥ x) hsa
  have hE := maDens_euclPot_nonneg (logReg u ε) s (A *ᵥ x) hsa hMs
  by_cases hxf : x ∈ tsupport f
  · have hφx : ∀ i, ContDiffAt ℝ 2 (φ i) (s (A *ᵥ x)) := fun i => by
      rw [hsx']
      exact ((hφU i).contDiffAt ((hU i).mem_nhds (hZU i hxZ))).of_le (WithTop.coe_le_coe.2 le_top)
    have hbx : ∀ i, (hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef ∧
        (-hessC (φ i) (s (A *ᵥ x)) + (c : ℂ) • 1).PosSemidef := fun i => by
      rw [hsx']
      exact hb i x ⟨hxZ, hxf⟩
    have key := abs_maDens_cons_le _ φ s (A *ᵥ x) hsa hφx hbx hMs
    have hfx : |f x| ≤ max M 0 := (Real.norm_eq_abs (f x) ▸ hM x).trans (le_max_left _ _)
    have hvx : |v x| ≤ w x := hvw x hxf
    rw [abs_mul, abs_mul]
    calc |v x| * |f x| * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)|
        ≤ w x * max M 0 * (3 ^ (d + 1) * c ^ d *
            maDens (fun k => vecCons (logReg u ε) (fun _ => euclPot) k ∘ s) (A *ᵥ x)) := by
          have hwx := hw x
          have hK0 : 0 ≤ (3 : ℝ) ^ (d + 1) * c ^ d := by positivity
          have h1 : |v x| * |f x| ≤ w x * max M 0 := mul_le_mul hvx hfx (abs_nonneg _) (hw x)
          calc |v x| * |f x| * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)|
              ≤ w x * max M 0 * |maDens (fun k => vecCons (logReg u ε) φ k ∘ s) (A *ᵥ x)| :=
                mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
            _ ≤ _ := mul_le_mul_of_nonneg_left key (mul_nonneg hwx hM0)
      _ = _ := by ring
  · rw [image_eq_zero_of_notMem_tsupport hxf, mul_zero, zero_mul, abs_zero]
    exact mul_nonneg hC (mul_nonneg (hw x) hE)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceFormLelongCompact
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Filter Topology Matrix ComplexSets
open scoped ContDiff

theorem SliceFormLelongCompact.proof (hSt : StokesOnVariety.Statement) (hLI : LogIntegrable.Statement)
    (hPL : PoincareLelong.Statement) (hCM : ChartMassCompact.Statement) (hI : SliceIdeal.Statement)
    (hC : SliceComponents.Statement) : SliceFormLelongCompact.Statement := by
  intro n e h W F u' ℓ f hW hF hu hℓ hℓP hf hfc
  obtain ⟨hprime, hdim, huS⟩ := hI n (e + 1) W F ℓ hW hF hℓ
  obtain ⟨hinj, himg, hmult⟩ := hC n W u' ℓ hW hℓP
  have h0 : ∀ x ∈ zeroSet (W ⊔ Ideal.span {linForm ℓ - 1}), x ≠ 0 := fun x hx =>
    SliceFormLelongCompact.ne_zero_of_mem_zeroSet (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) hx
  have hsm := smoothNear_log_dualNorm_slice h W ℓ
  obtain ⟨g, hg, hgc, hgf⟩ :=
    SliceFormLelongCompact.exists_contDiff_eqOn (SheetSumMeasurable.isClosed_zeroSet _) hf hfc
  have hSP : ∀ P ∈ (divCycle W u').support,
      W ⊔ Ideal.span {linForm ℓ - 1} ≤ P ⊔ Ideal.span {linForm ℓ - 1} := by
    intro P hP
    have hm : P ⊔ Ideal.span {linForm ℓ - 1} ∈
        (W ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u'}).minimalPrimes := by
      rw [← himg]
      exact ⟨P, Finset.mem_coe.2 hP, rfl⟩
    exact le_sup_left.trans hm.1.2
  have hw : ∀ (I : Ideal (MvPolynomial (Fin n) ℂ)) (d : ℕ) (ψ : Fin d → (Fin n → ℂ) → ℝ),
      W ⊔ Ideal.span {linForm ℓ - 1} ≤ I → varInt I d f ψ = varInt I d g ψ := fun I d ψ hle =>
    SliceFormLelongCompact.varInt_congr_weight
      (fun x hx => (hgf x (SliceFormLelongCompact.zeroSet_anti hle hx)).symm) ψ
  have hsumf : ∑ P ∈ (divCycle W u').support, ((divCycle W u' P : ℕ) : ℝ) *
        varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e f (fun _ x => Real.log (h.dualNorm x)) =
      ∑ P ∈ (divCycle W u').support, ((divCycle W u' P : ℕ) : ℝ) *
        varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e g (fun _ x => Real.log (h.dualNorm x)) :=
    Finset.sum_congr rfl fun P hP => by rw [hw _ _ _ (hSP P hP)]
  rw [hsumf, hw (W ⊔ Ideal.span {linForm ℓ - 1}) (e + 1) (fun _ x => Real.log (h.dualNorm x)) le_rfl]
  refine Tendsto.congr (fun ε => (hw _ _ _ le_rfl).symm) ?_
  have hgS : SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) g := smoothNear_of_contDiff hg
  have hlim := SliceFormLelongCompact.tendsto_varInt_fsLogReg hLI hCM h _ u' g
    (fun (_ : Fin e) x => Real.log (h.dualNorm x)) hprime hdim (huS u' hu) h0 hgS hgc (fun _ => hsm)
  have hP := hPL n e _ u' g (fun _ x => Real.log (h.dualNorm x)) hprime hdim (huS u' hu) hg hgc
    (fun _ => hsm)
  have hS2 := hSt n e _ g (fun x => Real.log (h.dualNorm x)) (fun _ x => Real.log (h.dualNorm x)) hprime
    hdim hgS hsm (fun _ => hsm) (Or.inl hgc)
  have hcons : (vecCons (fun x => Real.log (h.dualNorm x)) fun (_ : Fin e) x =>
      Real.log (h.dualNorm x)) = fun _ x => Real.log (h.dualNorm x) :=
    funext fun i => Fin.cases rfl (fun _ => rfl) i
  rw [hcons] at hS2
  have hsum : ∑ P ∈ (divCycle W u').support,
      (localMult (W ⊔ Ideal.span {linForm ℓ - 1} ⊔ Ideal.span {linForm u'})
        (P ⊔ Ideal.span {linForm ℓ - 1}) : ℝ) *
        varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e g (fun _ x => Real.log (h.dualNorm x)) =
      ∑ P ∈ (divCycle W u').support, ((divCycle W u' P : ℕ) : ℝ) *
        varInt (P ⊔ Ideal.span {linForm ℓ - 1}) e g (fun _ x => Real.log (h.dualNorm x)) :=
    Finset.sum_congr rfl fun P hP => by rw [hmult P hP]
  rw [hP, ← himg, finsum_mem_image hinj, finsum_mem_coe_finset, hsum, ← hS2] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (hSt n e _ g (fsLogReg h u' ε) _ hprime hdim hgS
    ⟨{0}ᶜ, isOpen_compl_singleton, fun x hx => h0 x hx, contDiffOn_fsLogReg h u' hε⟩ (fun _ => hsm)
    (Or.inl hgc)).symm

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StNormalModelDisc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormalModelDisc.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (M : IndefiniteRowSideFullHecke.ComplexSets.NormalModel J)
    (w : Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) → w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal →
      ∃ r : ℝ, 0 < r ∧ ∃ φ : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ,
        DifferentiableOn ℂ φ (Metric.ball 0 r) ∧ Set.InjOn φ (Metric.ball 0 r) ∧
          Set.MapsTo φ (Metric.ball 0 r) (IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal) ∧ φ 0 = w

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSameOrdersLiftCentre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

noncomputable section

def SameOrdersLiftCentre.Statement : Prop :=
  ∀ (n : ℕ) (J : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (M : NormalModel J)
    (γ γ' : VarBranch J 1 q) (Γ Γ' : (Fin 1 → ℂ) → Fin n ⊕ Fin M.m → ℂ),
    J.IsPrime → ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (1 : ℕ) →
    DifferentiableOn ℂ Γ (Metric.ball 0 γ.radius) →
    (∀ τ ∈ Metric.ball 0 γ.radius, Γ τ ∈ zeroSetIn M.ideal ∧ firstCoords (Γ τ) = γ.toFun τ) →
    DifferentiableOn ℂ Γ' (Metric.ball 0 γ'.radius) →
    (∀ τ ∈ Metric.ball 0 γ'.radius, Γ' τ ∈ zeroSetIn M.ideal ∧ firstCoords (Γ' τ) = γ'.toFun τ) →
    (∀ f : MvPolynomial (Fin n) ℂ, branchOrder γ f = branchOrder γ' f) →
      Γ 0 = Γ' 0

def lineDiagonalLift (τ : Fin 1 → ℂ) : Fin 1 ⊕ Fin 1 → ℂ := fun _ ↦ τ 0

end

end GroundTheory.Heights₂.Heights
end

