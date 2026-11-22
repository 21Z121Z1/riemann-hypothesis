import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0086
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0004
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0087
import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0004
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0080
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0075
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0035
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0023
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0085

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceImmersiveGeneral
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial Filter Topology MeasureTheory

noncomputable section

theorem dim_component_linForm {n d : ℕ} {J W : Ideal (MvPolynomial (Fin n) ℂ)} {u : Fin n → ℂ}
    (hJ : J.IsPrime) (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ))
    (hu : linForm u ∉ J) (hW : W ∈ (J ⊔ Ideal.span {linForm u}).minimalPrimes) :
    ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = (d : ℕ) := by
  have := hJ
  have hIW : J ≤ W := le_sup_left.trans hW.1.2
  have huW : linForm u ∈ W := (le_sup_right.trans hW.1.2) (Ideal.mem_span_singleton_self _)
  have hWprime : W.IsPrime := hW.1.1
  set B := MvPolynomial (Fin n) ℂ ⧸ J
  have _ : Algebra.FiniteType ℂ B :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ J) (Ideal.Quotient.mkₐ_surjective ℂ J)
  set W' : Ideal B := W.map (Ideal.Quotient.mk J)
  have hW'prime : W'.IsPrime :=
    Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hW'ne : W' ≠ ⊥ := by
    intro h
    apply hu
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    have : Ideal.Quotient.mk J (linForm u) ∈ W' := Ideal.mem_map_of_mem _ huW
    rw [h, Ideal.mem_bot] at this
    exact this
  have hht : W'.height ≤ 1 := Ideal.map_height_le_one_of_mem_minimalPrimes hW
  have hquot : ringKrullDim (B ⧸ W') = ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) :=
    ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hIW)
  have hform := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient ℂ W'
  have hdrop := GroundTheory.Arith.Abelian.Jacobian.ringKrullDim_quotient_add_one_le W' hW'ne
  rw [hquot] at hform hdrop
  change ringKrullDim B = _ at hdim
  rw [hdim] at hform hdrop
  obtain ⟨y, hy⟩ : ∃ y : ℕ∞, ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) = y := by
    cases h : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ W) with
    | bot =>
      have := ringKrullDim_nonneg_of_nontrivial (R := MvPolynomial (Fin n) ℂ ⧸ W)
      rw [h] at this
      exact absurd this (by simp)
    | coe y => exact ⟨y, rfl⟩
  rw [hy] at hform hdrop ⊢
  have h1 : y + 1 ≤ ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast hdrop
  have h2 : W'.height + y = ((d + 1 : ℕ) : ℕ∞) := by exact_mod_cast hform
  have hyle : y ≤ d := by
    have : y + 1 ≤ (d : ℕ∞) + 1 := by exact_mod_cast h1
    exact (ENat.add_le_add_iff_right ENat.one_ne_top).mp this
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, (k : ℕ∞) = y :=
    ENat.ne_top_iff_exists.mp (ne_top_of_le_ne_top (ENat.natCast_ne_top d) hyle)
  have h3 : ((d + 1 : ℕ) : ℕ∞) ≤ 1 + k := by rw [← h2]; gcongr
  have h4 : d + 1 ≤ 1 + k := by exact_mod_cast h3
  have h5 : k ≤ d := by exact_mod_cast hyle
  have : k = d := by omega
  subst this
  rfl

def hyperplaneEmb (d : ℕ) : (Fin d → ℂ) →L[ℂ] (Fin (d + 1) → ℂ) :=
  ContinuousLinearMap.pi
    (Fin.cons 0 fun j => ContinuousLinearMap.proj j : Fin (d + 1) → (Fin d → ℂ) →L[ℂ] ℂ)

theorem hyperplaneEmb_apply (d : ℕ) (t : Fin d → ℂ) : hyperplaneEmb d t = Fin.cons 0 t := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [hyperplaneEmb]

theorem hyperplaneEmb_tail {d : ℕ} {s : Fin (d + 1) → ℂ} (hs : s 0 = 0) :
    hyperplaneEmb d (Fin.tail s) = s := by
  rw [hyperplaneEmb_apply, ← hs]
  exact Fin.cons_self_tail s

def sliceMap {n d : ℕ} {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin n → ℂ}
    (γ : GroundTheory.Heights₂.Heights.VarBranch J (d + 1) p) : (Fin d → ℂ) → Fin n → ℂ :=
  fun t => γ.toFun (hyperplaneEmb d t)

theorem SliceImmersiveGeneral.proof (hcrit : CriticalImageNull.Statement)
    (hmass : ZeroSetOpenMass.Statement) : SliceImmersiveGeneral.Statement := by
  intro n d J W u p m γ hJ hdim hu hW hp hN
  obtain ⟨N, hN, hsl⟩ := hN
  have hWd := dim_component_linForm hJ hdim hu hW

  have hball : ∀ b, ∀ s ∈ Metric.ball (0 : Fin (d + 1) → ℂ) (γ b).radius,
      Fin.tail s ∈ Metric.ball (0 : Fin d → ℂ) (γ b).radius := by
    intro b s hs
    rw [ball_pi _ (γ b).radius_pos] at hs ⊢
    exact fun j _ => hs j.succ (Set.mem_univ _)
  have hmaps : ∀ b, Set.MapsTo (hyperplaneEmb d) (Metric.ball 0 (γ b).radius)
      (Metric.ball 0 (γ b).radius) := by
    intro b t ht
    rw [ball_pi _ (γ b).radius_pos] at ht ⊢
    intro i _
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hyperplaneEmb_apply, (γ b).radius_pos]
    · simpa [hyperplaneEmb_apply] using ht j (Set.mem_univ _)

  have hnull : ∀ b, μH[((2 * d : ℕ) : ℝ)] (sliceMap (γ b) '' {t | t ∈ Metric.ball 0 (γ b).radius ∧
      ¬ Function.Injective (fderiv ℂ (sliceMap (γ b)) t)}) = 0 := fun b =>
    hcrit d n _ _ Metric.isOpen_ball
      ((γ b).differentiableOn.comp (hyperplaneEmb d).differentiableOn (hmaps b))
  refine ⟨interior N, interior_mem_nhds.2 hN, ?_⟩
  rintro x ⟨hxW, hxN⟩
  rw [mem_closure_iff]
  intro o ho hxo
  by_contra hne
  rw [Set.not_nonempty_iff_eq_empty] at hne

  have hsub : GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∩ (o ∩ interior N) ⊆
      ⋃ b, sliceMap (γ b) '' {t | t ∈ Metric.ball 0 (γ b).radius ∧
        ¬ Function.Injective (fderiv ℂ (sliceMap (γ b)) t)} := by
    rintro y ⟨hyW, hyo, hyN⟩
    by_contra hy
    simp only [Set.mem_iUnion, not_exists] at hy
    have hyG : y ∈ o ∩ {x | x ∈ GroundTheory.Heights₂.Heights.ComplexSets.zeroSet W ∧
        ∀ b, ∃ s ∈ Metric.ball 0 (γ b).radius, s 0 = 0 ∧ (γ b).toFun s = x ∧
          ∀ v : Fin (d + 1) → ℂ, v 0 = 0 → fderiv ℂ (γ b).toFun s v = 0 → v = 0} := by
      refine ⟨hyo, hyW, fun b => ?_⟩
      obtain ⟨s, ⟨hs, hs0⟩, hsy⟩ := hsl b ⟨hyW, interior_subset hyN⟩
      have hs0' : s 0 = 0 := hs0
      refine ⟨s, hs, hs0', hsy, fun v hv0 hv => ?_⟩
      have hst := hyperplaneEmb_tail hs0'
      have hinj : Function.Injective (fderiv ℂ (sliceMap (γ b)) (Fin.tail s)) := by
        by_contra hni
        exact hy b ⟨Fin.tail s, ⟨hball b s hs, hni⟩, by simp only [sliceMap, hst, hsy]⟩
      have hγd : DifferentiableAt ℂ (γ b).toFun (hyperplaneEmb d (Fin.tail s)) := by
        rw [hst]
        exact (γ b).differentiableOn.differentiableAt (Metric.isOpen_ball.mem_nhds hs)
      have hchain : fderiv ℂ (sliceMap (γ b)) (Fin.tail s) =
          (fderiv ℂ (γ b).toFun (hyperplaneEmb d (Fin.tail s))).comp (hyperplaneEmb d) := by
        have h := fderiv_comp (Fin.tail s) hγd (hyperplaneEmb d).differentiableAt
        rw [ContinuousLinearMap.fderiv] at h
        exact h
      have hvt := hyperplaneEmb_tail hv0
      have : Fin.tail v = 0 := hinj (by
        rw [hchain, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hvt, hst, hv,
          map_zero, map_zero])
      rw [← hvt, this, map_zero]
    rw [hne] at hyG
    exact hyG
  have hpos := hmass n d W hW.1.1 hWd x (o ∩ interior N) (ho.inter isOpen_interior) ⟨hxo, hxN⟩ hxW
  exact hpos.ne' (measure_mono_null hsub (measure_iUnion_null hnull))

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PTubeDeepRankOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology

noncomputable section

namespace TubeDeepRankOne

theorem mdisc_vecMulVec {D : ℕ} (u : Fin D → Fin D → ℂ) :
    mdisc (fun k => vecMulVec (u k) (star (u k))) =
      (1 / (D.factorial : ℂ)) * (Complex.normSq (Matrix.of u).det : ℂ) := by
  rw [mdisc_eq_sum_perm]
  congr 1
  have hterm : ∀ σ : Equiv.Perm (Fin D),
      (Matrix.of fun i j => vecMulVec (u (σ j)) (star (u (σ j))) i j).det =
        (Matrix.of u).det * ((Equiv.Perm.sign σ : ℤ) * ∏ j, star (u (σ j) j)) := by
    intro σ
    have h1 : (Matrix.of fun i j => vecMulVec (u (σ j)) (star (u (σ j))) i j) =
        Matrix.of fun i j => (fun j => star (u (σ j) j)) j * ((Matrix.of u)ᵀ.submatrix id σ) i j := by
      ext i j
      simp [vecMulVec_apply, mul_comm]
    rw [h1, det_mul_row, det_permute', det_transpose]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  have hconj : ∑ σ : Equiv.Perm (Fin D), ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ j, star (u (σ j) j) =
      starRingEnd ℂ (Matrix.of u).det := by
    rw [RingHom.map_det, det_apply']
    rfl
  rw [hconj, Complex.mul_conj]

theorem mdisc_cons_sum {d n : ℕ} (A₀ : Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ)
    (B : Fin n → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) :
    mdisc (Fin.cons A₀ (fun _ => ∑ m, B m) : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
      ∑ I : Fin d → Fin n,
        mdisc (Fin.cons A₀ (fun i => B (I i)) : Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
  obtain ⟨L, hL⟩ := exists_multilinearMap_eq_mdisc (D := d + 1)
  rw [← hL]
  have h := (L.curryLeft A₀).map_sum (fun (_ : Fin d) m => B m)
  simpa [MultilinearMap.curryLeft_apply] using h

theorem hessC_euclPot_eq_one {N : ℕ} (z : Fin N → ℂ) : hessC (euclPot : (Fin N → ℂ) → ℝ) z = 1 := by
  have h : (euclPot : (Fin N → ℂ) → ℝ) = fun w => ∑ i, Complex.normSq (w i) := by
    funext w
    simp [euclPot, Complex.normSq_eq_norm_sq]
  rw [h]
  exact hessC_sum_normSq z

theorem hessC_euclPot_comp {n D : ℕ} (s : (Fin D → ℂ) → Fin n → ℂ) (y : Fin D → ℂ)
    (hs : AnalyticAt ℂ s y) :
    hessC (euclPot ∘ s) y = ∑ m, vecMulVec (fun j => jacC s y m j) (star fun j => jacC s y m j) := by
  have hE2 : ContDiffAt ℝ 2 (euclPot : (Fin n → ℂ) → ℝ) (s y) :=
    ((contDiff_euclPot n).of_le (WithTop.coe_le_coe.2 le_top)).contDiffAt
  rw [hessC_comp _ s y hs hE2, hessC_euclPot_eq_one, Matrix.mul_one]
  ext i j
  simp [Matrix.mul_apply, vecMulVec_apply, Matrix.sum_apply]

theorem analyticAt_eval_poly {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) :
    AnalyticAt ℂ (fun z => eval z P) y := by
  have h := AnalyticAt.aeval_mvPolynomial (𝕜 := ℂ) (f := fun z : Fin m → ℂ => z) (z := y)
    (fun i => (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) i).analyticAt y) P
  simpa [MvPolynomial.coe_aeval_eq_eval] using h

theorem dz_logAbsSq {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) (hP : eval y P ≠ 0)
    (j : Fin m) :
    dz j (cplx (logAbsSq P)) y = fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P := by
  have hg := analyticAt_eval_poly P y
  have hgd : HasFDerivAt (fun z => eval z P) (fderiv ℂ (fun z => eval z P) y) y :=
    hg.differentiableAt.hasFDerivAt
  have h1 := (hgd.restrictScalars ℝ).norm_sq
  have hne : ‖eval y P‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hP)
  have h2 := h1.log hne
  have hf : fderiv ℝ (logAbsSq P) y = _ := h2.fderiv
  set c := fderiv ℂ (fun z => eval z P) y (Pi.single j 1) with hc
  set p := eval y P with hp
  set w := c * (starRingEnd ℂ) p with hw
  have hI : fderiv ℂ (fun z => eval z P) y (Complex.I • Pi.single j 1) = Complex.I * c := by
    rw [map_smul, smul_eq_mul]
  have hN : Complex.normSq p ≠ 0 := (Complex.normSq_pos.2 hP).ne'
  have e1 : fderiv ℝ (logAbsSq P) y (Pi.single j 1) = 2 * w.re / Complex.normSq p := by
    rw [hf]
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.coe_restrictScalars', Complex.inner, smul_eq_mul, nsmul_eq_mul,
      Complex.normSq_eq_norm_sq]
    rw [← hc, hw]
    ring
  have e2 : fderiv ℝ (logAbsSq P) y (Complex.I • Pi.single j 1) = -(2 * w.im / Complex.normSq p) := by
    rw [hf]
    simp only [_root_.smul_apply, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
      ContinuousLinearMap.coe_restrictScalars', Complex.inner, smul_eq_mul, nsmul_eq_mul,
      Complex.normSq_eq_norm_sq]
    rw [hI, hw]
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    ring
  have hcp : c / p = w / (Complex.normSq p : ℂ) := by
    rw [← Complex.mul_conj, hw, mul_div_mul_right _ _ ((map_ne_zero _).2 hP)]
  rw [dz_cplx, e1, e2, hcp]
  conv_rhs => rw [← Complex.re_add_im w]
  have hN' : (Complex.normSq p : ℂ) ≠ 0 := by exact_mod_cast hN
  push_cast
  field_simp
  ring

theorem hessC_logAbsSq_sq_half {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (y : Fin m → ℂ) (hP : eval y P ≠ 0) :
    hessC (fun z => logAbsSq P z ^ 2 / 2) y =
      vecMulVec (fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P)
        (star fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P) := by
  have hg := analyticAt_eval_poly P y
  have hv : ContDiffAt ℝ 2 (logAbsSq P) y := by
    have h1 : ContDiffAt ℝ 2 (fun z => ‖eval z P‖ ^ 2) y :=
      ((hg.contDiffAt (n := 2)).restrict_scalars ℝ).norm_sq ℝ
    exact h1.log (by positivity)
  have hv0 : hessC (logAbsSq P) y = 0 := by
    have h : logAbsSq P = fun z => (2 : ℝ) * Real.log ‖eval z P‖ := by
      funext z
      rw [logAbsSq, Real.log_pow]
      norm_num
    rw [h, ReciprocityTheory.AnForm.M.hessC_const_mul', hessC_log_norm _ y hg hP, smul_zero]
  rw [MaDensLeibniz.hessC_sq_half _ y hv, hv0, smul_zero, zero_add, gradMat_eq_vecMulVec]
  have ha : (fun j => dz j (cplx (logAbsSq P)) y) =
      fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P :=
    funext fun j => dz_logAbsSq P y hP j
  rw [ha]

theorem fderiv_apply_coord {D m : ℕ} (F : (Fin D → ℂ) → Fin m → ℂ) (y h : Fin D → ℂ)
    (hF : DifferentiableAt ℂ F y) (a : Fin m) :
    fderiv ℂ F y h a = fderiv ℂ (fun x => F x a) y h := by
  have e := ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) a).hasFDerivAt.comp y
    hF.hasFDerivAt).fderiv
  have e' : (fun x => F x a) = (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin m => ℂ) a) ∘ F := rfl
  rw [e', e]
  rfl

theorem det_rows_eq_deepJacDet {n d : ℕ} (P : MvPolynomial (Fin (d + 1)) ℂ)
    (s : (Fin (d + 1) → ℂ) → Fin n → ℂ) (y : Fin (d + 1) → ℂ) (hs : DifferentiableAt ℂ s y)
    (I : Fin d → Fin n) :
    (Matrix.of (Fin.cons (fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P)
        (fun i j => jacC s y (I i) j) : Fin (d + 1) → Fin (d + 1) → ℂ)).det =
      (eval y P)⁻¹ * deepJacDet P s I y := by
  have hg := (analyticAt_eval_poly P y).differentiableAt
  have hF : DifferentiableAt ℂ (deepMap P s I) y := by
    refine differentiableAt_pi.2 fun k => ?_
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa [deepMap] using hg
    · simpa [deepMap] using differentiableAt_pi.1 hs (I i)
  set J := jacC (deepMap P s I) y with hJdef
  have hJ : (Matrix.of (Fin.cons (fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P)
        (fun i j => jacC s y (I i) j) : Fin (d + 1) → Fin (d + 1) → ℂ)) =
      J.updateRow 0 ((eval y P)⁻¹ • J 0) := by
    ext k j
    refine Fin.cases ?_ (fun i => ?_) k
    · have h0 : (fun x => deepMap P s I x 0) = fun z => eval z P := by
        funext x
        simp [deepMap]
      simp only [Matrix.of_apply, Fin.cons_zero, updateRow_self, Pi.smul_apply, smul_eq_mul, hJdef,
        jacC, fderiv_apply_coord _ _ _ hF, h0]
      rw [div_eq_inv_mul]
    · have hi : (fun x => deepMap P s I x i.succ) = fun x => s x (I i) := by
        funext x
        simp [deepMap]
      simp only [Matrix.of_apply, Fin.cons_succ, updateRow_ne (Fin.succ_ne_zero i), hJdef, jacC,
        fderiv_apply_coord _ _ _ hF, hi, fderiv_apply_coord _ _ _ hs]
  rw [hJ, det_updateRow_smul, updateRow_eq_self, hJdef, det_jacC]
  rfl

theorem proof : TubeDeepRankOne.Statement := by
  intro n d A P U s y hU hy hsd hAs hP
  have hsa : AnalyticAt ℂ s y := analyticAt_pi_iff.2 fun j =>
    ReciprocityTheory.AnForm.Osgood.osgood (d + 1) U (fun y => s y j) hU (differentiableOn_pi.1 hsd j) y hy
  set a : Fin (d + 1) → ℂ := fun j => fderiv ℂ (fun z => eval z P) y (Pi.single j 1) / eval y P with ha
  set b : Fin n → Fin (d + 1) → ℂ := fun m j => jacC s y m j with hb
  have h0 : hessC ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) y = vecMulVec a (star a) := by
    have hev : ((fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) ∘ s) =ᶠ[𝓝 y] fun z => logAbsSq P z ^ 2 / 2 := by
      filter_upwards [hU.mem_nhds hy] with z hz
      simp only [Function.comp_apply, hAs z hz]
    rw [hessC_congr' hev, hessC_logAbsSq_sq_half P y hP]
  have h1 : hessC (euclPot ∘ s) y = ∑ m, vecMulVec (b m) (star (b m)) := hessC_euclPot_comp s y hsa
  have hH : (fun k => hessC (vecCons (fun x => logAbsSq P (A *ᵥ x) ^ 2 / 2) (fun _ => euclPot) k ∘ s) y) =
      (Fin.cons (vecMulVec a (star a)) (fun _ => ∑ m, vecMulVec (b m) (star (b m))) :
        Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) := by
    funext k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using h0
    · simpa using h1
  have hI : ∀ I : Fin d → Fin n,
      (Fin.cons (vecMulVec a (star a)) (fun i => vecMulVec (b (I i)) (star (b (I i)))) :
        Fin (d + 1) → Matrix (Fin (d + 1)) (Fin (d + 1)) ℂ) =
      fun k => vecMulVec ((Fin.cons a (fun i => b (I i)) : Fin (d + 1) → Fin (d + 1) → ℂ) k)
        (star ((Fin.cons a (fun i => b (I i)) : Fin (d + 1) → Fin (d + 1) → ℂ) k)) := by
    intro I
    funext k
    refine Fin.cases ?_ (fun i => ?_) k <;> simp
  have hdet : ∀ I : Fin d → Fin n,
      (Matrix.of (Fin.cons a (fun i => b (I i)) : Fin (d + 1) → Fin (d + 1) → ℂ)).det =
        (eval y P)⁻¹ * deepJacDet P s I y := fun I =>
    det_rows_eq_deepJacDet P s y (hsd.differentiableAt (hU.mem_nhds hy)) I
  unfold ReciprocityTheory.AnForm.maDens
  rw [hH, mdisc_cons_sum]
  simp_rw [hI, mdisc_vecMulVec, hdet]
  rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun I _ => ?_
  have hf : ((d + 1).factorial : ℝ) ≠ 0 := by exact_mod_cast (d + 1).factorial_ne_zero
  have hre : ((1 / ((d + 1).factorial : ℂ)) *
      (Complex.normSq ((eval y P)⁻¹ * deepJacDet P s I y) : ℂ)).re =
      Complex.normSq ((eval y P)⁻¹ * deepJacDet P s I y) / ((d + 1).factorial : ℝ) := by
    rw [show (1 / ((d + 1).factorial : ℂ)) = (((1 / ((d + 1).factorial : ℝ)) : ℝ) : ℂ) by push_cast; rfl,
      ← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [hre, map_mul, map_inv₀, Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
  have hp : ‖eval y P‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hP)
  field_simp

end TubeDeepRankOne

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PVarietyLelongMono
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets
open scoped ENNReal

noncomputable section

theorem zeroSetEuc_subsingleton_of_dim_zero {n : ℕ} (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = ((0 : ℕ) : WithBot ℕ∞))
    {z : EuclideanSpace ℂ (Fin n)} (hz : z ∈ zeroSetEuc J) :
    ∀ y ∈ zeroSetEuc J, y = z := by
  have : Ring.KrullDimLE 0 (MvPolynomial (Fin n) ℂ ⧸ J) := Ring.krullDimLE_iff.2 (le_of_eq hdim)
  have hmax : J.IsMaximal := Ideal.Quotient.maximal_of_isField _ Ring.KrullDimLE.isField_of_isDomain
  obtain ⟨p, hp⟩ := (MvPolynomial.isMaximal_iff_eq_vanishingIdeal_singleton (K := ℂ)).1 hmax
  have hcoord : ∀ w ∈ zeroSetEuc J, ∀ i, w i = p i := by
    intro w hw i
    have hmem : (X i - C (p i) : MvPolynomial (Fin n) ℂ) ∈ J := by
      rw [hp, MvPolynomial.mem_vanishingIdeal_singleton_iff]
      simp
    have := hw _ hmem
    simp only [map_sub, eval_X, eval_C] at this
    exact sub_eq_zero.1 this
  intro y hy
  ext i
  rw [hcoord y hy i, hcoord z hz i]

theorem VarietyLelongMono.proof (hN : ComplexSets.LinearNoetherNormalization.Statement)
    (hW : VarWirtinger.Statement) (hM : VarLelongMono.Statement) : VarietyLelongMono.Statement := by
  intro n d J hJ hdim z hz r s hr hrs
  rcases d with _ | d
  · have hsub := zeroSetEuc_subsingleton_of_dim_zero J hJ hdim hz
    have hpt : ∀ ρ : ℝ, 0 < ρ → zeroSetEuc J ∩ Metric.ball z ρ = {z} := by
      intro ρ hρ
      ext y
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
      constructor
      · exact fun h => hsub y h.1
      · rintro rfl
        exact ⟨hz, Metric.mem_ball_self hρ⟩
    rw [hpt r hr, hpt s (hr.trans_le hrs)]
    simp [Measure.hausdorffMeasure_zero_singleton]
  · obtain ⟨A, hA⟩ := hN n (d + 1) J hdim
    obtain ⟨c, hc, hWc⟩ := hW d
    have hball : ∀ ρ : ℝ, (fun x : Fin n → ℂ => WithLp.toLp 2 x) ⁻¹' Metric.ball z ρ =
        euclBall (WithLp.ofLp z) ρ := by
      intro ρ
      ext y
      rw [Set.mem_preimage, mem_euclBall_iff, Metric.mem_ball]
    have hμ : ∀ ρ : ℝ, μH[((2 * (d + 1) : ℕ) : ℝ)] (zeroSetEuc J ∩ Metric.ball z ρ) =
        ENNReal.ofReal (c * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) ρ).indicator fun _ => 1)
          (fun _ => euclPot) y) := by
      intro ρ
      rw [← hball ρ]
      exact (hWc n J A hJ hdim hA _ measurableSet_ball Metric.isBounded_ball).2
    have key := hM n d J A (WithLp.ofLp z) r s hJ hdim hA hr hrs
    rw [hμ r, hμ s, ← ENNReal.ofReal_mul (pow_nonneg (hr.le.trans hrs) _),
      ← ENNReal.ofReal_mul (pow_nonneg hr.le _)]
    apply ENNReal.ofReal_le_ofReal
    calc s ^ (2 * (d + 1)) * (c * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) r).indicator fun _ => 1)
          (fun _ => euclPot) y)
        = c * (s ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) r).indicator fun _ => 1)
          (fun _ => euclPot) y) := by ring
      _ ≤ c * (r ^ (2 * (d + 1)) * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) s).indicator fun _ => 1)
          (fun _ => euclPot) y) := mul_le_mul_of_nonneg_left key hc.le
      _ = r ^ (2 * (d + 1)) * (c * ∫ y, chartDens J A ((euclBall (WithLp.ofLp z) s).indicator fun _ => 1)
          (fun _ => euclPot) y) := by ring

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchGermDimOne
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def BranchGermDimOne.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) (m : ℕ) (c : Fin m → VarBranch I 1 q),
    0 < m → (∃ N ∈ 𝓝 q, zeroSet I ∩ N ⊆ ⋃ b, (c b).image) →
      ringKrullDim (curveLocalRing I q) = 1

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StBranchImageNhdOffCentre
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets Filter Topology

noncomputable section

def BranchImageNhdOffCentre.Statement : Prop :=
  ∀ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ),
    ringKrullDim (curveLocalRing I q) = 1 →
      ∃ N ∈ 𝓝 q, ∀ c : VarBranch I 1 q, ∀ x ∈ c.image ∩ N, x ≠ q →
        ∃ U ∈ 𝓝 x, zeroSet I ∩ U ⊆ c.image

end

end GroundTheory.Heights₂.Heights
end

