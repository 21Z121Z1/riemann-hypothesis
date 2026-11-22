import Mathlib
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Statements
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.StatementsCusp
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0003
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0002
import GroundTheory.HeightsAndTheta.Heights.MatrixCharts.Bundle0001

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PIntGramQf
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem IntGramQf.proof : IntGramQf.Statement := by
  intro d k S N z
  simp only [MCSchur.qf, intGram, ← mulVec_mulVec]
  rw [dotProduct_mulVec, vecMul_transpose]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PIntGramSubLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem IntGramSubLast.proof : IntGramSubLast.Statement := by
  intro d k S M hM
  ext i j
  simp only [intGram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Matrix.submatrix_apply, Fin.sum_univ_castSucc, hM, Int.cast_zero, zero_mul, mul_zero,
    add_zero]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PIntGramUnimodular
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem IntGramUnimodular.proof : IntGramUnimodular.Statement := by
  intro d k S N U hU
  have hmap : (N * U).map (Int.cast : ℤ → ℝ) =
      N.map (Int.cast : ℤ → ℝ) * U.map (Int.cast : ℤ → ℝ) :=
    Matrix.map_mul (f := Int.castRingHom ℝ)
  have hdet : (U.map (Int.cast : ℤ → ℝ)).det = ((U.det : ℤ) : ℝ) :=
    ((Int.castRingHom ℝ).map_det U).symm
  have hsq : ((U.det : ℤ) : ℝ) * (U.det : ℝ) = 1 := by
    rcases Int.isUnit_iff.mp hU with h | h <;> rw [h] <;> norm_num
  unfold intGram
  rw [hmap, transpose_mul]
  have e : (U.map (Int.cast : ℤ → ℝ))ᵀ * (N.map (Int.cast : ℤ → ℝ))ᵀ * S *
      (N.map (Int.cast : ℤ → ℝ) * U.map (Int.cast : ℤ → ℝ)) =
      (U.map (Int.cast : ℤ → ℝ))ᵀ * ((N.map (Int.cast : ℤ → ℝ))ᵀ * S * N.map (Int.cast : ℤ → ℝ)) *
        U.map (Int.cast : ℤ → ℝ) := by
    simp only [Matrix.mul_assoc]
  rw [e, det_mul, det_mul, det_transpose, hdet]
  calc (U.det : ℝ) * ((N.map (Int.cast : ℤ → ℝ))ᵀ * S * N.map (Int.cast : ℤ → ℝ)).det * (U.det : ℝ)
      = ((U.det : ℤ) : ℝ) * (U.det : ℝ) *
          ((N.map (Int.cast : ℤ → ℝ))ᵀ * S * N.map (Int.cast : ℤ → ℝ)).det := by ring
    _ = _ := by rw [hsq, one_mul]

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLeadMinorBasic
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem LeadMinorBasic.proof : LeadMinorBasic.Statement := by
  intro d S
  refine ⟨?_, ?_, ?_⟩
  · simp [leadMinor]
  · unfold leadMinor
    congr 1
    ext a b
    simp only [Matrix.of_apply]
    rw [dif_pos ⟨a.2, b.2⟩]
  · intro hS i hi
    have e : (Matrix.of fun a b : Fin i =>
        if h : (a : ℕ) < d ∧ (b : ℕ) < d then S ⟨a, h.1⟩ ⟨b, h.2⟩ else 0) =
        S.submatrix (Fin.castLE hi) (Fin.castLE hi) := by
      ext a b
      simp only [Matrix.of_apply, Matrix.submatrix_apply]
      rw [dif_pos ⟨a.2.trans_le hi, b.2.trans_le hi⟩]
      rfl
    unfold leadMinor
    rw [e]
    exact (hS.submatrix (Fin.castLE_injective hi)).det_pos

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLeadMinorLeading
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

theorem LeadMinorLeading.proof : LeadMinorLeading.Statement := by
  intro d S m h j hj
  unfold leadMinor
  congr 1
  ext a b
  simp only [Matrix.of_apply, Matrix.submatrix_apply]
  have ha : (a : ℕ) < m := lt_of_lt_of_le a.2 hj
  have hb : (b : ℕ) < m := lt_of_lt_of_le b.2 hj
  rw [dif_pos ⟨ha, hb⟩, dif_pos ⟨ha.trans_le h, hb.trans_le h⟩]
  rfl

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLeadingCovolume
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix

noncomputable section

namespace LeadingCovolume

theorem periodBasis_of_lt {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (i : ℕ) (hi : i < g)
    (hi' : i < g + g) : periodBasis τ ⟨i, hi'⟩ = Pi.single (⟨i, hi⟩ : Fin g) 1 := by
  have e : (⟨i, hi'⟩ : Fin (g + g)) = Fin.castAdd g ⟨i, hi⟩ := rfl
  rw [e, periodBasis, Fin.append_left]

end LeadingCovolume

theorem LeadingCovolume.proof : LeadingCovolume.Statement := by
  intro g τ r h
  unfold covolume leadMinor
  congr 2
  ext a b
  have ha : (a : ℕ) < g + g := by omega
  have hb : (b : ℕ) < g + g := by omega
  rw [Matrix.of_apply, Matrix.of_apply, dif_pos ⟨ha, hb⟩, periodGram, Matrix.of_apply,
    LeadingCovolume.periodBasis_of_lt τ a (by omega) ha,
    LeadingCovolume.periodBasis_of_lt τ b (by omega) hb]
  rfl

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLogDetGramContinuous
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Metric MCPsh
open scoped MatrixOrder ComplexOrder

noncomputable section

namespace MCPsh

theorem continuousOn_inv_of_posDef {X : Type} [TopologicalSpace X] {s : Set X} {g : ℕ}
    {Y : X → Matrix (Fin g) (Fin g) ℝ} (hY : ContinuousOn Y s) (hpd : ∀ x ∈ s, (Y x).PosDef) :
    ContinuousOn (fun x => (Y x)⁻¹) s := by
  intro x hx
  have hdet : (Y x).det ≠ 0 := (hpd x hx).det_pos.ne'
  have hinvR : ContinuousAt (Ring.inverse : ℝ → ℝ) (Y x).det := by
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ hdet
  have hinvAt : ContinuousAt (Inv.inv : Matrix (Fin g) (Fin g) ℝ → Matrix (Fin g) (Fin g) ℝ)
      (Y x) := continuousAt_matrix_inv _ hinvR
  exact hinvAt.comp_continuousWithinAt (hY x hx)

theorem gram_posDef {g rk : ℕ} {Y : Matrix (Fin g) (Fin g) ℝ} {F : Matrix (Fin g) (Fin rk) ℂ}
    (hY : Y.PosDef) (hF : F.rank = rk) :
    (Fᴴ * (Y⁻¹).map (fun x : ℝ => (x : ℂ)) * F).PosDef := by
  have hinj : Function.Injective F.mulVec := mulVec_injective_of_rank (by rw [hF, Fintype.card_fin])
  have := (cx_posDef hY).inv.conjTranspose_mul_mul_same hinj
  rwa [cx_inv ((Matrix.isUnit_iff_isUnit_det _).mp hY.isUnit)] at this

theorem continuous_gram (g rk : ℕ) :
    Continuous (fun p : Matrix (Fin g) (Fin rk) ℂ × Matrix (Fin g) (Fin g) ℝ =>
      p.1ᴴ * p.2.map (fun x : ℝ => (x : ℂ)) * p.1) := by
  have h1 : Continuous (fun p : Matrix (Fin g) (Fin rk) ℂ × Matrix (Fin g) (Fin g) ℝ => p.1) :=
    continuous_fst
  have h2 : Continuous (fun p : Matrix (Fin g) (Fin rk) ℂ × Matrix (Fin g) (Fin g) ℝ =>
      p.2.map (fun x : ℝ => (x : ℂ))) := continuous_snd.matrix_map Complex.continuous_ofReal
  exact (h1.matrix_conjTranspose.matrix_mul h2).matrix_mul h1

end MCPsh

theorem LogDetGramContinuous.proof : LogDetGramContinuous.Statement := by
  intro X _ s g rk Y F hY hF hpd hr
  have hYinv := continuousOn_inv_of_posDef hY hpd
  have hΦ : Continuous (fun p : Matrix (Fin g) (Fin rk) ℂ × Matrix (Fin g) (Fin g) ℝ =>
      (p.1ᴴ * p.2.map (fun x : ℝ => (x : ℂ)) * p.1).det.re) :=
    Complex.continuous_re.comp (continuous_gram g rk).matrix_det
  have hG := hΦ.comp_continuousOn (hF.prodMk hYinv)
  simp only [Function.comp_def] at hG
  show ContinuousOn (fun x => Real.log ((F x)ᴴ * ((Y x)⁻¹).map (fun x : ℝ => (x : ℂ)) * F x).det.re) s
  refine hG.log fun x hx => ?_
  have h := MCDet.re_det_pos (gram_posDef (hpd x hx) (hr x hx))
  rw [RCLike.re_to_complex] at h
  exact h.ne'

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLogDetGramPsh
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Metric Real MCPsh

noncomputable section

theorem LogDetGramPsh.proof (hcont : LogDetGramContinuous.Statement)
    (hsub : LogDetGramSubmean.Statement) : LogDetGramPsh.Statement := by
  intro N g rk S
  have hYc : ContinuousOn (fun x => (S.τ x).map Complex.im) S.W :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k =>
      Complex.continuous_im.comp_continuousOn (S.τ_analytic j k).continuousOn
  have hFc : ContinuousOn S.f S.W :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k => (S.f_analytic j k).continuousOn
  have hc := hcont (Fin N → ℂ) S.W g rk (fun x => (S.τ x).map Complex.im) S.f hYc hFc
    S.im_posDef S.f_rank
  refine ⟨hc.upperSemicontinuousOn, ?_⟩
  intro z w hdisc
  have hline : ∀ ζ ∈ closedBall (0:ℂ) 1, z + ζ • w ∈ S.W := fun ζ hζ =>
    hdisc ζ (by simpa using hζ)
  have haff : ∀ ζ : ℂ, AnalyticAt ℂ (fun ζ : ℂ => z + ζ • w) ζ := fun ζ =>
    analyticAt_const.add (analyticAt_id.smul analyticAt_const)
  have hτ : ∀ j k, AnalyticOnNhd ℂ (fun ζ : ℂ => S.τ (z + ζ • w) j k) (closedBall 0 1) :=
    fun j k ζ hζ => AnalyticAt.comp (g := fun x => S.τ x j k) (f := fun ζ : ℂ => z + ζ • w)
      (S.τ_analytic j k _ (hline ζ hζ)) (haff ζ)
  have hf : ∀ j k, AnalyticOnNhd ℂ (fun ζ : ℂ => S.f (z + ζ • w) j k) (closedBall 0 1) :=
    fun j k ζ hζ => AnalyticAt.comp (g := fun x => S.f x j k) (f := fun ζ : ℂ => z + ζ • w)
      (S.f_analytic j k _ (hline ζ hζ)) (haff ζ)
  have hYd : ContinuousOn (fun ζ : ℂ => (S.τ (z + ζ • w)).map Complex.im) (closedBall 0 1) :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k =>
      Complex.continuous_im.comp_continuousOn (hτ j k).continuousOn
  have hmean : ∀ j k, circleAverage (fun ζ : ℂ => (S.τ (z + ζ • w)).map Complex.im j k) 0 1 =
      (S.τ (z + (0:ℂ) • w)).map Complex.im j k := fun j k => by
    simpa only [map_apply] using circleAverage_im_of_analytic (hτ j k)
  obtain ⟨hint, hle⟩ := hsub g rk (fun ζ => (S.τ (z + ζ • w)).map Complex.im)
    (fun ζ => S.f (z + ζ • w)) (fun ζ hζ => S.im_posDef _ (hline ζ hζ)) hYd hmean hf
    (fun ζ hζ => S.f_rank _ (hline ζ hζ))
  refine ⟨hint, ?_⟩
  have e : z + (0:ℂ) • w = z := by simp
  simpa only [e] using hle

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.MatrixCharts.PLogDetGramSubmean
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open Matrix Metric Real MCPsh
open scoped MatrixOrder ComplexOrder

noncomputable section

set_option maxHeartbeats 400000 in
theorem LogDetGramSubmean.proof (hcont : LogDetGramContinuous.Statement) :
    LogDetGramSubmean.Statement := by
  classical
  intro g rk Y F hYpd hYc hYmean hF hFrank
  have h0mem : (0:ℂ) ∈ closedBall (0:ℂ) 1 := mem_closedBall_self zero_le_one
  have hsph : sphere (0:ℂ) 1 ⊆ closedBall 0 1 := sphere_subset_closedBall
  have hYu : ∀ ζ ∈ closedBall (0:ℂ) 1, IsUnit (Y ζ).det := fun ζ hζ =>
    (Matrix.isUnit_iff_isUnit_det _).mp (hYpd ζ hζ).isUnit
  have hFr : ∀ ζ ∈ closedBall (0:ℂ) 1, Function.Injective (F ζ).mulVec := fun ζ hζ =>
    mulVec_injective_of_rank (by rw [hFrank ζ hζ, Fintype.card_fin])
  have hFc : ContinuousOn F (closedBall 0 1) :=
    continuousOn_pi.mpr fun j => continuousOn_pi.mpr fun k => (hF j k).continuousOn
  have hφc : ContinuousOn (fun ζ => logDetGram (Y ζ) (F ζ)) (closedBall 0 1) :=
    hcont ℂ (closedBall 0 1) g rk Y F hYc hFc hYpd hFrank
  have hφint : CircleIntegrable (fun ζ => logDetGram (Y ζ) (F ζ)) 0 1 :=
    (hφc.mono hsph).circleIntegrable zero_le_one
  refine ⟨hφint, ?_⟩

  have hGpd : ∀ ζ ∈ closedBall (0:ℂ) 1,
      ((F ζ)ᴴ * ((Y ζ)⁻¹).map (fun x : ℝ => (x : ℂ)) * F ζ).PosDef := by
    intro ζ hζ
    have h := (cx_posDef (hYpd ζ hζ)).inv.conjTranspose_mul_mul_same (hFr ζ hζ)
    rw [cx_inv (hYu ζ hζ)] at h
    exact h
  have hGdet : ∀ ζ ∈ closedBall (0:ℂ) 1,
      0 < ((F ζ)ᴴ * ((Y ζ)⁻¹).map (fun x : ℝ => (x : ℂ)) * F ζ).det.re := by
    intro ζ hζ
    have h := MCDet.re_det_pos (hGpd ζ hζ)
    rw [RCLike.re_to_complex] at h
    exact h

  obtain ⟨B, hBu, hB⟩ := exists_factor (hGpd 0 h0mem)
  set Ci : Matrix (Fin g) (Fin g) ℂ := ((Y 0)⁻¹).map (fun x : ℝ => (x : ℂ)) with hCidef
  set W0 : Matrix (Fin g) (Fin rk) ℂ := Ci * F 0 * B⁻¹ with hW0def
  have hCiH : Ciᴴ = Ci := by
    have h := (cx_posDef (hYpd 0 h0mem)).inv.isHermitian
    rw [cx_inv (hYu 0 h0mem)] at h
    exact h
  have hCiY : Ci * cx (Y 0) = 1 := by
    rw [hCidef, ← cx_mul, nonsing_inv_mul _ (hYu 0 h0mem), cx_one]
  have hBH : (B⁻¹)ᴴ * Bᴴ = 1 := by
    rw [conjTranspose_nonsing_inv]
    exact nonsing_inv_mul _ (by rwa [det_conjTranspose, isUnit_star])
  have hBB : B * B⁻¹ = 1 := mul_nonsing_inv _ hBu
  have hG0 : (F 0)ᴴ * Ci * F 0 = Bᴴ * B := hB
  have hW0H : W0ᴴ = (B⁻¹)ᴴ * ((F 0)ᴴ * Ci) := by
    rw [hW0def, conjTranspose_mul, conjTranspose_mul, hCiH]
  have hW0F0 : W0ᴴ * F 0 = B := by
    calc W0ᴴ * F 0 = (B⁻¹)ᴴ * ((F 0)ᴴ * Ci * F 0) := by rw [hW0H]; simp only [Matrix.mul_assoc]
      _ = B := by rw [hG0, ← Matrix.mul_assoc, hBH, Matrix.one_mul]
  have hM0 : W0ᴴ * cx (Y 0) * W0 = 1 := by
    calc W0ᴴ * cx (Y 0) * W0 = (B⁻¹)ᴴ * ((F 0)ᴴ * (Ci * cx (Y 0)) * Ci * F 0) * B⁻¹ := by
          rw [hW0H, hW0def]; simp only [Matrix.mul_assoc]
      _ = (B⁻¹)ᴴ * (Bᴴ * B) * B⁻¹ := by rw [hCiY, Matrix.mul_one, hG0]
      _ = 1 := by rw [← Matrix.mul_assoc, hBH, Matrix.one_mul, hBB]
  have hW0inj : Function.Injective W0.mulVec := by
    intro v w hvw
    have h : (W0ᴴ * cx (Y 0) * W0) *ᵥ v = (W0ᴴ * cx (Y 0) * W0) *ᵥ w := by
      rw [← mulVec_mulVec, hvw, mulVec_mulVec]
    rwa [hM0, one_mulVec, one_mulVec] at h

  have hh : AnalyticOnNhd ℂ (fun ζ => (W0ᴴ * F ζ).det) (closedBall 0 1) := by
    refine analyticOnNhd_det fun i j => ?_
    intro z hz
    simp only [mul_apply]
    exact Finset.univ.analyticAt_fun_sum fun k _ => analyticAt_const.mul (hF k j z hz)
  have hh0ne : (W0ᴴ * F 0).det ≠ 0 := by rw [hW0F0]; exact hBu.ne_zero

  have hMpd : ∀ ζ ∈ closedBall (0:ℂ) 1, (W0ᴴ * cx (Y ζ) * W0).PosDef := fun ζ hζ =>
    (cx_posDef (hYpd ζ hζ)).conjTranspose_mul_mul_same hW0inj
  have hMdet : ∀ ζ ∈ closedBall (0:ℂ) 1, 0 < (W0ᴴ * cx (Y ζ) * W0).det.re := by
    intro ζ hζ
    have h := MCDet.re_det_pos (hMpd ζ hζ)
    rw [RCLike.re_to_complex] at h
    exact h
  have hMc : ContinuousOn (fun ζ => (W0ᴴ * cx (Y ζ) * W0).det.re) (closedBall 0 1) := by
    have hΦ : Continuous (fun Z : Matrix (Fin g) (Fin g) ℝ =>
        (W0ᴴ * Z.map (fun x : ℝ => (x : ℂ)) * W0).det.re) :=
      Complex.continuous_re.comp
        ((continuous_const.matrix_mul (continuous_id.matrix_map Complex.continuous_ofReal)).matrix_mul
          continuous_const).matrix_det
    have h := hΦ.comp_continuousOn hYc
    simp only [Function.comp_def] at h
    exact h
  have hℓc : ContinuousOn (fun ζ => Real.log (W0ᴴ * cx (Y ζ) * W0).det.re) (closedBall 0 1) :=
    hMc.log fun ζ hζ => (hMdet ζ hζ).ne'
  have hℓint : CircleIntegrable (fun ζ => Real.log (W0ᴴ * cx (Y ζ) * W0).det.re) 0 1 :=
    (hℓc.mono hsph).circleIntegrable zero_le_one

  have hYent : ∀ j k, CircleIntegrable (fun ζ => Y ζ j k) 0 1 := by
    intro j k
    have h := (continuous_id.matrix_elem j k).comp_continuousOn hYc
    simp only [Function.comp_def, id] at h
    exact (h.mono hsph).circleIntegrable zero_le_one
  have hYentc : ∀ j k, CircleIntegrable
      (fun ζ => (∑ a, (star (W0 j a) * W0 k a).re) * Y ζ j k) 0 1 := by
    intro j k
    simpa only [smul_eq_mul] using
      (hYent j k).const_fun_smul (a := ∑ a, (star (W0 j a) * W0 k a).re)
  have htr : ∀ ζ, RCLike.re (W0ᴴ * cx (Y ζ) * W0).trace =
      ∑ j, ∑ k, (∑ a, (star (W0 j a) * W0 k a).re) * Y ζ j k := fun ζ => re_trace_eq W0 (Y ζ)
  have hsum_int : CircleIntegrable
      (fun ζ => ∑ j, ∑ k, (∑ a, (star (W0 j a) * W0 k a).re) * Y ζ j k) 0 1 :=
    CircleIntegrable.fun_sum _ fun j _ => CircleIntegrable.fun_sum _ fun k _ => hYentc j k
  have htravg : circleAverage
      (fun ζ => ∑ j, ∑ k, (∑ a, (star (W0 j a) * W0 k a).re) * Y ζ j k) 0 1 = rk := by
    rw [circleAverage_fun_sum fun j _ => CircleIntegrable.fun_sum _ fun k _ => hYentc j k]
    have hj : ∀ j, circleAverage (fun ζ => ∑ k, (∑ a, (star (W0 j a) * W0 k a).re) * Y ζ j k) 0 1 =
        ∑ k, (∑ a, (star (W0 j a) * W0 k a).re) * Y 0 j k := by
      intro j
      rw [circleAverage_fun_sum fun k _ => hYentc j k]
      refine Finset.sum_congr rfl fun k _ => ?_
      have h := circleAverage_fun_smul (c := (0:ℂ)) (R := 1)
        (a := ∑ a, (star (W0 j a) * W0 k a).re) (f := fun ζ => Y ζ j k)
      simp only [smul_eq_mul] at h
      rw [h, hYmean]
    simp only [hj]
    rw [← htr 0, hM0]
    simp

  have hℓavg : circleAverage (fun ζ => Real.log (W0ᴴ * cx (Y ζ) * W0).det.re) 0 1 ≤ 0 := by
    have hle : ∀ ζ ∈ sphere (0:ℂ) |(1:ℝ)|, Real.log (W0ᴴ * cx (Y ζ) * W0).det.re ≤
        (∑ j, ∑ k, (∑ a, (star (W0 j a) * W0 k a).re) * Y ζ j k) - rk := by
      intro ζ hζ
      have hζ' : ζ ∈ closedBall (0:ℂ) 1 := hsph (by simpa using hζ)
      have h := MCDet.log_re_det_le (hMpd ζ hζ')
      rw [htr ζ, RCLike.re_to_complex, Fintype.card_fin] at h
      exact h
    have hint2 := hsum_int.fun_sub (circleIntegrable_const (rk : ℝ) 0 1)
    calc circleAverage (fun ζ => Real.log (W0ᴴ * cx (Y ζ) * W0).det.re) 0 1
        ≤ circleAverage
          (fun ζ => (∑ j, ∑ k, (∑ a, (star (W0 j a) * W0 k a).re) * Y ζ j k) - rk) 0 1 :=
          circleAverage_mono hℓint hint2 hle
      _ = 0 := by
          rw [circleAverage_fun_sub hsum_int (circleIntegrable_const _ _ _), htravg,
            circleAverage_const]
          ring

  have hpt : ∀ ζ ∈ sphere (0:ℂ) 1, (W0ᴴ * F ζ).det ≠ 0 →
      2 * Real.log ‖(W0ᴴ * F ζ).det‖ - Real.log (W0ᴴ * cx (Y ζ) * W0).det.re ≤
        logDetGram (Y ζ) (F ζ) := by
    intro ζ hζ hhζ
    have hζ' : ζ ∈ closedBall (0:ℂ) 1 := hsph hζ
    have hcs := MCDet.norm_det_mul_sq_le_of_posDef (cx_posDef (hYpd ζ hζ')) (F ζ) W0
    rw [cx_inv (hYu ζ hζ'), RCLike.re_to_complex, RCLike.re_to_complex] at hcs
    have hpos : 0 < ‖(W0ᴴ * F ζ).det‖ ^ 2 := by positivity
    have hlog := Real.log_le_log hpos hcs
    rw [Real.log_mul (hMdet ζ hζ').ne' (hGdet ζ hζ').ne', Real.log_pow] at hlog
    show _ ≤ Real.log ((F ζ)ᴴ * ((Y ζ)⁻¹).map (fun x : ℝ => (x : ℂ)) * F ζ).det.re
    push_cast at hlog
    linarith

  have hφ0 : logDetGram (Y 0) (F 0) ≤ 2 * Real.log ‖(W0ᴴ * F 0).det‖ - 0 := by
    show Real.log ((F 0)ᴴ * Ci * F 0).det.re ≤ _
    rw [sub_zero, hW0F0, hG0]
    have h : (Bᴴ * B).det.re = ‖B.det‖ ^ 2 := by
      rw [det_mul, det_conjTranspose, Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
        Complex.ofReal_re]
    rw [h, Real.log_pow]
    push_cast
    linarith
  exact le_circleAverage_of_minorant hh hh0ne hφint hℓint hpt hℓavg hφ0

end

end GroundTheory.Heights₂.Heights
end

