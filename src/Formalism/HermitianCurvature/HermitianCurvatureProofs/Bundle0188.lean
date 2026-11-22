import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixTranspose
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SymmetricScalarBlockMatrixMul
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Block3MulBlocks
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CoordinateSizesOfHypotheses
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0183
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CompactGroupHaarExists
import Formalism.HermitianCurvature.HermitianCurvatureProofs.UnipotentCoordinatesMeasurePreserving
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MulVecBvecApply
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0120
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0176
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0182
import Formalism.HermitianCurvature.HermitianCurvatureProofs.Bundle0174
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelsOfBuiltSetting
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmPActualCptOfStepForm

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceContOn
section
open Matrix MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBM

section dom

variable {k r : ℕ}

theorem detM_zero (Z : G.Mat 0) : G.detM Z = 1 := by
  unfold G.detM; exact Matrix.det_isEmpty

theorem hMat_det_ne (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ i, d i ≠ 0) : (U.hMat σ d).det ≠ 0 := by
  rw [U.hMat, Matrix.det_mul, Matrix.det_diagonal]
  exact mul_ne_zero (Dx2.SL.isUnit_wP σ).ne_zero (Finset.prod_ne_zero_iff.2 fun i _ => hd i)

theorem zjH_det (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (η : U.XiH r 0 σ) :
    (U.ZjH σ d η (fun a => a.elim0)).det = (U.hMat σ d).det := by
  rw [Formalism.FourierDecayAlt.P.level_determinant_z r 0 σ d η (fun a => a.elim0), detM_zero, mul_one]

theorem rn_mem_GV (x : U.RC k r 0) : U.Rn k r 0 x ∈ B.GV k (r + 0) := by
  have h := (Formalism.FourierDecayAlt.P.radical_parametrisation k r 0).2.1
  have : U.Rn k r 0 x ∈ U.Rset k r 0 := by rw [← h]; exact ⟨x, rfl⟩
  exact this.1

theorem gaXi_mem_GV (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ i, d i ≠ 0) (ξ : U.Xi k r 0 0 σ)
    (γ : B.Mat k 0) (hγ : γ ∈ B.GV k 0) : U.gaXi k 0 σ d ξ (fun a => a.elim0) γ ∈ B.GV k r := by
  have hG := Formalism.FourierDecayAlt.P.unitary_group_closed k (r + 0)
  have hm := (Formalism.FourierDecayAlt.P.slice_membership k r 0).1 (U.ZjH σ d ξ.2 (fun a => a.elim0)) γ
    (by rw [zjH_det]; exact hMat_det_ne σ d hd) hγ
  unfold U.gaXi
  exact hG.mul_mem _ (hG.mul_mem _ (hG.inv_mem _ (rn_mem_GV _)) _ hm) _ (rn_mem_GV _)

theorem slice_dom (k r : ℕ) (hr : 1 ≤ r) (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ i, d i ≠ 0)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (F : B.Mat k r → E)
    (hFc : ContinuousOn F (B.GV k r)) (R : ℝ) (hFs : ∀ g ∈ B.GV k r, F g ≠ 0 → B.gN g ≤ R) :
    ∃ (M : ℝ) (Bs : Set (U.Xi k r 0 0 σ)), MeasurableSet Bs ∧ U.muXi k r 0 0 σ Bs < ⊤ ∧
      ∀ (ξ : U.Xi k r 0 0 σ) (γ : B.Mat k 0), γ ∈ B.GV k 0 →
        ‖F (U.gaXi k 0 σ d ξ (fun a => a.elim0) γ)‖ ≤ Bs.indicator (fun _ => M) ξ := by

  have hK : IsCompact {g : B.Mat k r | g ∈ B.GV k r ∧ B.gN g ≤ R} := by
    have h1 := Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k r R
    have h2 := (Formalism.FourierDecayAlt.P.unitary_group_closed k r).closed
    have : {g : B.Mat k r | g ∈ B.GV k r ∧ B.gN g ≤ R} = B.GV k r ∩ {g | B.gN g ≤ R} := rfl
    rw [this]; exact h1.inter_left h2
  obtain ⟨M0, hM0⟩ := hK.exists_bound_of_continuousOn (hFc.mono fun g hg => hg.1)

  obtain ⟨C1, hC1⟩ := Formalism.FourierDecayAlt.P.block3_apply_embedding k r 0 hr
  obtain ⟨C2, hC2⟩ := Formalism.FourierDecayAlt.P.aux_statement_17 r 0 σ d hd
  set δ := ‖(U.hMat σ d).det‖ with hδ
  have hδ0 : 0 < δ := norm_pos_iff.2 (hMat_det_ne σ d hd)
  set R0 := max R 0
  set C1' := max C1 0
  set C2' := max C2 0
  set K1 := C1' * R0 ^ r / min 1 δ
  set K2 := C2' * (C1' * R0) ^ r
  set K := max (max K1 K2) 0
  set B1 : Set (U.RC k (r + 0) 0) := Metric.closedBall (0 : Fin (2 * 0 + k + 1) → Fin (r + 0) → ℂ) K ×ˢ
    (Metric.closedBall (0 : G.UT (r + 0) → ℂ) K ×ˢ Metric.closedBall (0 : Fin (r + 0) → ℝ) K) with hB1
  set Bs : Set (U.Xi k r 0 0 σ) :=
    (B1 ×ˢ B1) ×ˢ
      ((Metric.closedBall (0 : Fin 0 → Fin r → ℂ) K ×ˢ Metric.closedBall (0 : Fin r → Fin 0 → ℂ) K) ×ˢ
        (Metric.closedBall (0 : U.LW σ → ℂ) K ×ˢ Metric.closedBall (0 : G.UT r → ℂ) K)) with hBs
  have hB1m : MeasurableSet B1 := Metric.isClosed_closedBall.measurableSet.prod
    (Metric.isClosed_closedBall.measurableSet.prod Metric.isClosed_closedBall.measurableSet)
  have hprod : ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (μ : Measure α) (ν : Measure β) [SFinite ν]
      {s : Set α} {t : Set β}, μ s < ⊤ → ν t < ⊤ → (μ.prod ν) (s ×ˢ t) < ⊤ := by
    intro α β _ _ μ ν _ s t hs ht; rw [Measure.prod_prod]; exact ENNReal.mul_lt_top hs ht
  have hRC : U.muRC k (r + 0) 0 B1 < ⊤ := by
    unfold U.muRC
    exact hprod volume volume measure_closedBall_lt_top (hprod volume volume measure_closedBall_lt_top
      measure_closedBall_lt_top)
  refine ⟨max M0 0, Bs, ?_, ?_, ?_⟩
  · exact (hB1m.prod hB1m).prod
      ((Metric.isClosed_closedBall.measurableSet.prod Metric.isClosed_closedBall.measurableSet).prod
        (Metric.isClosed_closedBall.measurableSet.prod Metric.isClosed_closedBall.measurableSet))
  · unfold U.muXi U.muXiH
    have h1 : SFinite (volume : Measure ((G.UT (r + 0) → ℂ) × (Fin (r + 0) → ℝ))) :=
      (inferInstance : SFinite ((volume : Measure (G.UT (r + 0) → ℂ)).prod (volume : Measure (Fin (r + 0) → ℝ))))
    have : SFinite (U.muRC k (r + 0) 0) :=
      (inferInstance : SFinite ((volume : Measure (Fin (2 * 0 + k + 1) → Fin (r + 0) → ℂ)).prod
        (volume : Measure ((G.UT (r + 0) → ℂ) × (Fin (r + 0) → ℝ)))))
    exact hprod _ volume (hprod _ _ hRC hRC)
      (hprod volume volume (hprod volume volume measure_closedBall_lt_top measure_closedBall_lt_top)
        (hprod volume volume measure_closedBall_lt_top measure_closedBall_lt_top))
  · intro ξ γ hγ
    set g := U.gaXi k 0 σ d ξ (fun a => a.elim0) γ with hg
    by_cases hF : F g = 0
    · rw [hF, norm_zero]
      exact Set.indicator_nonneg (fun _ _ => le_max_right _ _) ξ
    · have hgG : g ∈ B.GV k r := gaXi_mem_GV σ d hd ξ γ hγ
      have hgR := hFs g hgG hF
      have hgn : 0 ≤ B.gN g := Real.sqrt_nonneg _
      have hgR0 : B.gN g ≤ R0 := hgR.trans (le_max_left _ _)
      have hdet : (U.ZjH σ d ξ.2 (fun a => a.elim0)).det ≠ 0 := by rw [zjH_det]; exact hMat_det_ne σ d hd
      obtain ⟨h1, h2, h3, -, -⟩ := hC1 ξ.1.1 ξ.1.2 (U.ZjH σ d ξ.2 (fun a => a.elim0)) γ hdet hγ
      have hdetn : ‖(U.ZjH σ d ξ.2 (fun a => a.elim0)).det‖ = δ := by rw [zjH_det]
      rw [hdetn] at h1 h2
      have hmin : 0 < min 1 δ := lt_min one_pos hδ0
      have hC1n : 0 ≤ C1' := le_max_right _ _
      have hpow : B.gN g ^ r ≤ R0 ^ r := pow_le_pow_left₀ hgn hgR0 r
      have hpow0 : 0 ≤ B.gN g ^ r := pow_nonneg hgn r
      have hb1 : ‖ξ.1.1‖ ≤ K1 := by
        refine (Formalism.FourierDecayAlt.P.Ux6.norm_le_gN_Rn ξ.1.1).trans (h1.trans ?_)
        refine div_le_div_of_nonneg_right ?_ hmin.le
        exact (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow0).trans (mul_le_mul_of_nonneg_left hpow hC1n)
      have hb2 : ‖ξ.1.2‖ ≤ K1 := by
        refine (Formalism.FourierDecayAlt.P.Ux6.norm_le_gN_Rn ξ.1.2).trans (h2.trans ?_)
        refine div_le_div_of_nonneg_right ?_ hmin.le
        exact (mul_le_mul_of_nonneg_right (le_max_left _ _) hpow0).trans (mul_le_mul_of_nonneg_left hpow hC1n)
      have hmx : U.mx (U.ZjH σ d ξ.2 (fun a => a.elim0)) ≤ C1' * R0 :=
        h3.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hgn).trans (mul_le_mul_of_nonneg_left hgR0 hC1n))
      have hmx0 : 0 ≤ U.mx (U.ZjH σ d ξ.2 (fun a => a.elim0)) := norm_nonneg _
      obtain ⟨e1, e2, e3, e4, -, -⟩ := hC2 ξ.2 (fun a => a.elim0)
      have hC2n : 0 ≤ C2' := le_max_right _ _
      have hpm : U.mx (U.ZjH σ d ξ.2 (fun a => a.elim0)) ^ r ≤ (C1' * R0) ^ r := pow_le_pow_left₀ hmx0 hmx r
      have hpm0 : 0 ≤ U.mx (U.ZjH σ d ξ.2 (fun a => a.elim0)) ^ r := pow_nonneg hmx0 r
      have hK2 : ∀ t : ℝ, t ≤ C2 * U.mx (U.ZjH σ d ξ.2 (fun a => a.elim0)) ^ r → t ≤ K2 := fun t ht =>
        ht.trans ((mul_le_mul_of_nonneg_right (le_max_left _ _) hpm0).trans (mul_le_mul_of_nonneg_left hpm hC2n))
      have hξ : ‖ξ‖ ≤ K := by
        have k1 : K1 ≤ K := le_max_left _ _ |>.trans (le_max_left _ _)
        have k2 : K2 ≤ K := le_max_right _ _ |>.trans (le_max_left _ _)
        exact norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨hb1.trans k1, hb2.trans k1⟩,
          norm_prod_le_iff.2 ⟨norm_prod_le_iff.2 ⟨(hK2 _ e1).trans k2, (hK2 _ e2).trans k2⟩,
            norm_prod_le_iff.2 ⟨(hK2 _ e3).trans k2, (hK2 _ e4).trans k2⟩⟩⟩
      have hmem : ξ ∈ Bs := by
        have hb := fun {α : Type} [SeminormedAddCommGroup α] (x : α) (h : ‖x‖ ≤ K) =>
          (show x ∈ Metric.closedBall (0 : α) K by rw [Metric.mem_closedBall, dist_zero_right]; exact h)
        obtain ⟨⟨h11, h12⟩, ⟨h21, h22⟩, h23, h24⟩ :
            (‖ξ.1.1‖ ≤ K ∧ ‖ξ.1.2‖ ≤ K) ∧ (‖ξ.2.1.1‖ ≤ K ∧ ‖ξ.2.1.2‖ ≤ K) ∧ ‖ξ.2.2.1‖ ≤ K ∧ ‖ξ.2.2.2‖ ≤ K := by
          obtain ⟨ha, hb'⟩ := norm_prod_le_iff.1 hξ
          obtain ⟨ha1, ha2⟩ := norm_prod_le_iff.1 ha
          obtain ⟨hb1', hb2'⟩ := norm_prod_le_iff.1 hb'
          exact ⟨⟨ha1, ha2⟩, norm_prod_le_iff.1 hb1', norm_prod_le_iff.1 hb2'⟩
        have hrc : ∀ x : U.RC k (r + 0) 0, ‖x‖ ≤ K → x ∈ B1 := by
          intro x hx
          obtain ⟨hx1, hx2⟩ := norm_prod_le_iff.1 hx
          obtain ⟨hx21, hx22⟩ := norm_prod_le_iff.1 hx2
          exact ⟨hb _ hx1, hb _ hx21, hb _ hx22⟩
        exact ⟨⟨hrc _ h11, hrc _ h12⟩, ⟨hb _ h21, hb _ h22⟩, hb _ h23, hb _ h24⟩
      rw [Set.indicator_of_mem hmem]
      exact (hM0 g ⟨hgG, hgR⟩).trans (le_max_left _ _)

theorem zjH_eq (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (η : U.XiH r 0 σ) :
    U.ZjH σ d η (fun a => a.elim0) = U.headH σ d η.2.1 η.2.2 := by
  unfold U.ZjH; exact Dx2.SL.zj_zero _ _ _ _

theorem headH_det (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (η : U.XiH r 0 σ) :
    (U.headH σ d η.2.1 η.2.2).det = (U.hMat σ d).det := by
  rw [← zjH_eq, zjH_det]

theorem headH_cont (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) :
    Continuous (fun η : U.XiH r 0 σ => U.headH σ d η.2.1 η.2.2) := by
  unfold U.headH
  exact ((continuous_const.matrix_mul ((Dx2.SL.cont_lowW σ).comp (continuous_fst.comp continuous_snd))).matrix_mul
    continuous_const).matrix_mul (Dx2.SL.cont_upper.comp (continuous_snd.comp continuous_snd))

theorem gaXi_cont (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) (hd : ∀ i, d i ≠ 0) :
    Continuous (fun p : U.Xi k r 0 0 σ × B.Mat k 0 => U.gaXi k 0 σ d p.1 (fun a => a.elim0) p.2) := by
  set c := (U.hMat σ d).det with hc
  have hc0 : star c ≠ 0 := star_ne_zero.2 (hMat_det_ne σ d hd)
  have hinv : ∀ η : U.XiH r 0 σ, (U.headH σ d η.2.1 η.2.2)ᴴ⁻¹ = (star c)⁻¹ • (U.headH σ d η.2.1 η.2.2)ᴴ.adjugate := by
    intro η
    rw [Formalism.FourierDecayAlt.P.B2x2.inv_eq, Matrix.det_conjTranspose, headH_det]
  have hH : Continuous (fun p : U.Xi k r 0 0 σ × B.Mat k 0 => U.headH σ d p.1.2.2.1 p.1.2.2.2) :=
    (headH_cont σ d).comp (continuous_snd.comp continuous_fst)
  have hm : Continuous (fun p : U.Xi k r 0 0 σ × B.Mat k 0 =>
      U.mMap k r 0 (U.headH σ d p.1.2.2.1 p.1.2.2.2) p.2) := by
    unfold U.mMap
    simp only [hinv]
    refine Dx2.SplitF.continuous_block3_matrix continuous_const continuous_const ?_ continuous_const continuous_snd continuous_const
      (continuous_const.matrix_mul hH) continuous_const continuous_const
    exact (hH.matrix_conjTranspose.matrix_adjugate.const_smul ((star c)⁻¹ : ℂ)).matrix_mul continuous_const
  have e : (fun p : U.Xi k r 0 0 σ × B.Mat k 0 => U.gaXi k 0 σ d p.1 (fun a => a.elim0) p.2) =
      fun p => U.Rn k r 0 (-p.1.1.1) * U.mMap k r 0 (U.headH σ d p.1.2.2.1 p.1.2.2.2) p.2 * U.Rn k r 0 p.1.1.2 := by
    funext p
    unfold U.gaXi
    rw [rn_inv, zjH_eq]
    rfl
  rw [e]
  exact (((Dx2.SplitF.rn_cont r 0).comp (continuous_fst.comp (continuous_fst.comp continuous_fst)).neg).matrix_mul hm).matrix_mul
    ((Dx2.SplitF.rn_cont r 0).comp (continuous_snd.comp (continuous_fst.comp continuous_fst)))

def slF (σ : Equiv.Perm (Fin r)) (d : Fin r → ℂ) {E : Type*} (F : B.Mat k r → E) (γ0 : B.Mat k 0)
    (p : (Mt k (r + 0) × Mt k (r + 0)) × U.Xi k r 0 0 σ) : E :=
  F (U.gaXi k 0 σ d p.2 (fun a => a.elim0) ((midB r 0 (Matrix.of p.1.1))⁻¹ * γ0 * midB r 0 (Matrix.of p.1.2)))

def slS (σ : Equiv.Perm (Fin r)) (z0 z0' : Fin (2 * 0 + k + 1) → ℂ) :
    Set ((Mt k (r + 0) × Mt k (r + 0)) × U.Xi k r 0 0 σ) :=
  ({h | Matrix.of h ∈ UWset k (r + 0) (liftVec k r 0 z0)} ×ˢ
    {h | Matrix.of h ∈ UWset k (r + 0) (liftVec k r 0 z0')}) ×ˢ Set.univ

end dom

end Formalism.FourierDecayAlt.P.PBM
end
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceGermPoints
section
namespace Formalism.FourierDecayAlt.P.FormNormSumIdentities

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.G MeasureTheory

noncomputable section

section tr

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem phiFun_tr {k p s ρ ρ' r : ℕ} (hρ : ρ = ρ') (σ : Equiv.Perm (Fin p)) (d : Fin p → ℂ)
    (z z' : Fin (2 * r + k + 1) → ℂ) (F : B.Mat k r → E) (e : r = p + s + ρ) (e' : r = p + s + ρ')
    (Z : G.Mat s) (γ : B.Mat k ρ) :
    U.PhiFun k ρ' σ d (D.castV e' z) (D.castV e' z') (D.castF e'.symm F) Z (D.castM hρ γ) =
      U.PhiFun k ρ σ d (D.castV e z) (D.castV e z') (D.castF e.symm F) Z γ := by
  subst hρ
  rw [Formalism.FourierDecayAlt.P.JCTx5.castM_rfl]

end tr

theorem finrank_UT_lt (m : ℕ) (a : ℝ) (ha : ((m : ℝ) + 1) * ((m : ℝ) + 4) < a) :
    (Module.finrank ℝ (UT (m + 1 + 1) → ℂ) : ℝ) < a := by
  have h1 : Module.finrank ℝ (UT (m + 1 + 1) → ℂ) = Fintype.card (UT (m + 1 + 1)) * 2 := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex]
  have h2 := Formalism.FourierDecayAlt.P.Dx2.SL.card_UT (m + 1 + 1)
  have h3 : ((Fintype.card (UT (m + 1 + 1)) * 2 : ℕ) : ℝ) = ((m : ℝ) + 2) * ((m : ℝ) + 1) := by
    have : Fintype.card (UT (m + 1 + 1)) * 2 = (m + 2) * (m + 1) := by
      rw [mul_comm, h2, show m + 1 + 1 - 1 = m + 1 by omega]
    rw [this]; push_cast; ring
  rw [h1, h3]
  nlinarith

end

end Formalism.FourierDecayAlt.P.FormNormSumIdentities

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.G MeasureTheory Formalism.FourierDecayAlt.P.FormNormSumIdentities

theorem slice_germ_points : Formalism.FourierDecayAlt.P.FormNormSumIdentities.YGSlice := by
  intro k r E _ _ _ z z' F h' m ρ e1 V _ _ _ Φ L γ Kc K a hh' hKc ha hΦ hL q hq hint
  have hW : (G.wMat (m + 1)).det ≠ 0 := (Formalism.FourierDecayAlt.P.Ux3.wMat_det (m + 1)).ne_zero
  rcases q with ⟨t, c⟩ | w0
  · obtain ⟨ht, hcK⟩ := hq
    have hc0 : c ≠ 0 := by
      rintro rfl; apply hKc; simpa using hcK
    have hne : ∀ p, G.detM (G.orbM (m + 1) t c p) ≠ 0 := by
      intro p; rw [Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_orbM]
      exact mul_ne_zero hW (fun h0 => hKc (h0 ▸ hcK))
    have himg : ∀ p, G.detM (G.orbM (m + 1) t c p) ∈ (fun D => (G.wMat (m + 1)).det * D) '' Kc :=
      fun p => ⟨c * t ^ (m + 1), hcK, (Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_orbM _ _ _ _).symm⟩
    have hI := integrable_blockIntegrand U.betaU m Φ t c ht K a ha (fun p => (hΦ _ (hne p)).1)
      (fun p => (hΦ _ (hne p)).2)
    show L (((kapB m : ℝ) : ℂ) • G.OmBlock U.betaU (m + 1) Φ t c) = _
    rw [L.map_smul, clm_omBlock L U.betaU (m + 1) Φ t c hI]
    have hloc : D.IsLocPt (ptG h' m (Sum.inl (t, c))) (D.ptSize (ptG h' m (Sum.inl (t, c)))) := by
      refine ⟨fun b hb => ?_, rfl⟩
      simp only [ptG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with hb | hb | hb
      · exact hh'.1 b hb
      · subst hb; exact ⟨by omega, ht⟩
      · subst hb; exact ⟨le_rfl, hc0⟩
    have hle : D.ptSize (ptG h' m (Sum.inl (t, c))) ≤ r := by rw [ptSize_ptG]; omega
    have hSB := Formalism.FourierDecayAlt.P.slice_orbital_block k r E z z' F h' (ptG h' m (Sum.inl (t, c))) m t c rfl hle
      (D.castM (by rw [ptSize_ptG]; omega) γ) hloc hint
    rw [hSB]
    congr 1
    unfold G.OmBlock
    congr 1
    funext p
    simp only [G.blockIntegrand]
    congr 1
    have hp := hL _ (hne p) (himg p)
    simp only [G.orbM] at hp
    rw [hp]
    exact (phiFun_tr (by rw [ptSize_ptG]; omega) _ _ z z' F _ _ _ γ).symm
  · obtain ⟨D0, hDK, hz⟩ := hq
    have hz0 : w0 ≠ 0 := by
      rintro rfl
      apply hKc
      have : (0 : ℂ) = (-1) ^ (m + 3) * D0 := by simpa using hz
      have h1 : D0 = 0 := by
        rcases mul_eq_zero.1 this.symm with h | h
        · exact absurd h (pow_ne_zero _ (by norm_num))
        · exact h
      exact h1 ▸ hDK
    have hne : ∀ v, G.detM (Formalism.FourierDecayAlt.P.JCTx6.Pos.Zv (m + 1) w0 v) ≠ 0 := by
      intro v
      have := Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_longM m w0 D0 hz v
      show G.detM (Formalism.FourierDecayAlt.P.OrbitTailEstimates.longM (m + 1 + 1) w0 v) ≠ 0
      rw [this]
      exact mul_ne_zero hW (fun h0 => hKc (h0 ▸ hDK))
    have himg : ∀ v, G.detM (Formalism.FourierDecayAlt.P.JCTx6.Pos.Zv (m + 1) w0 v) ∈ (fun D => (G.wMat (m + 1)).det * D) '' Kc :=
      fun v => ⟨D0, hDK, (Formalism.FourierDecayAlt.P.OrbitTailEstimates.detM_longM m w0 D0 hz v).symm⟩
    have hI := integrable_longIntegrand (m + 1) Φ w0 hz0 K a (finrank_UT_lt m a ha)
      (fun v => (hΦ _ (hne v)).1) (fun v => (hΦ _ (hne v)).2)
    show L (((Real.pi ^ ((m + 2) * (m + 1) / 2) : ℝ) : ℂ) • G.OmLong U.betaU (m + 1) Φ w0) = _
    rw [L.map_smul, clm_omLong L U.betaU (m + 1) Φ w0 hI]
    have hloc : D.IsLocPt (ptG h' m (Sum.inr w0)) (D.ptSize (ptG h' m (Sum.inr w0))) := by
      refine ⟨fun b hb => ?_, rfl⟩
      simp only [ptG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hb
      rcases hb with hb | hb
      · exact hh'.1 b hb
      · subst hb; exact ⟨by omega, hz0⟩
    have hle : D.ptSize (ptG h' m (Sum.inr w0)) ≤ r := by rw [ptSize_ptG]; omega
    have hSO := Formalism.FourierDecayAlt.P.slice_measure_identity k r E z z' F h' (ptG h' m (Sum.inr w0)) (m + 1) w0 rfl hle
      (D.castM (by rw [ptSize_ptG]; omega) γ) hloc hint
    rw [hSO]
    congr 1
    unfold G.OmLong
    congr 1
    funext v
    congr 1
    have hp := hL _ (hne v) (himg v)
    exact hp.trans (phiFun_tr (by rw [ptSize_ptG]; omega) _ _ z z' F _ _ _ γ).symm

end Formalism.FourierDecayAlt.P
end

-- bundled from Formalism.HermitianCurvature.HermitianCurvatureProofs.ThmPActualCptOfOuter
section
open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB

section Ent

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]
variable {P : M.Par} {z z' : Fin (2 * P.r + P.k + 1) → ℂ} {π : Mx P.k P.r → (Wp →L[ℂ] Wp)}
  {π' : Mx P.k P.r → (Wq →L[ℂ] Wq)}

theorem site_lc (X : ActualOps P.k P.r z z' π π') {L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r}
    (hAL : IsActualLevel X L) (l : Fin P.r) :
    L.p l ∈ presAlg (lcSub P.k P.r z z' π π') ∧ L.c l ∈ presAlg (lcSub P.k P.r z z' π π') ∧
      L.ci l ∈ presAlg (lcSub P.k P.r z z' π π') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [hAL.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 0) (neg_lc (op_lc X l 3))
  · rw [hAL.2.2.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 1) (op_lc X l 4)
  · rw [hAL.2.2.2.1 l]; exact mkPair_mem_preservingAlgebra (op_lc X l 2) (op_lc X l 5)

theorem QQ_lc (X : ActualOps P.k P.r z z' π π') (Y : ℂ) (a b : Fin 2) :
    X.QQ Y a b ∈ presAlg (lcSub P.k P.r z z' π π') :=
  mkPair_mem_preservingAlgebra (t_lc X Y a b) (t_lc X (star Y) b a)

theorem RRi_lc (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (hD : IsData P z z' π π' X μ L st l0) (i : Fin (P.r + 1)) (w : List (Letter ℂ S))
    (hw : ∀ l ∈ w, star l.pt = l.pt) : RRi L st i w ∈ entSub (presAlg (lcSub P.k P.r z z' π π')) := by
  obtain ⟨-, -, hAL, hQQ, -⟩ := hD
  refine rrw_mem (QQi L st i) (QQi_mem L st _ i (fun Y _ a b => ?_) (fun l _ => site_lc X hAL l)) w hw
  rw [hQQ Y, Matrix.smul_apply]
  exact (presAlg (lcSub P.k P.r z z' π π')).smul_mem (QQ_lc X Y a b) _

end Ent

section G

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem int_lc (μ : Measure (Mt k r)) (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) {Φ Ψ : RadSp k r z z' π π'}
    (hΦ : Φ ∈ lcSub k r z z' π π') (hΨ : Ψ ∈ lcSub k r z z' π π') (c : Fin r → ℂ) :
    Integrable (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
      ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) μ := by
  by_cases hc : c ∈ OmX r
  · exact intOn_cpt μ hμ c hc Φ (lcSub_le_cptSub hΦ) Ψ (lcSub_le_cptSub hΨ)
  · have e : (fun g : Mt k r => B.hsInner ((Φ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))
        ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c (Matrix.of g))) = fun _ => 0 := by
      funext g
      rw [radSp_zero_off Φ (x := (c, Matrix.of g)) (fun h => hc h.1)]
      exact hsInner_zero_left _
    rw [e]; exact integrable_zero _ _ _

end G

section Form

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] {S : Type} [Fintype S] [DecidableEq S]

theorem formIntG_herKc (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq) (hD : IsData P z z' π π' X μ L st l0) (hz : D.z = z) (hz' : D.z' = z')
    (hπ : D.π = π) (hπ' : D.π' = π') (w : List (Letter ℂ S)) (hw : WordOK P z z' π π' st l0 w)
    (i : Fin (P.r + 1)) (c : Fin P.r → ℂ) (x y : Ix S → RadSp P.k P.r z z' π π')
    (hx : InK (herKc S P z z' π π' L st l0 D i) x) (hy : InK (herKc S P z z' π π' L st l0 D i) y)
    (c' : Cf P.r i) (a : Ix S) :
    Integrable (fun g : Mt P.k P.r =>
      B.hsInner ((act (RRi L st i w) x a : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))
        ((y a : Fn P.k P.r (Wq →L[ℂ] Wp)) (glue i c c') (Matrix.of g))) μ := by
  have hle := herKc_le_lc (S := S) (st := st) (l0 := l0) X hD.2.2.1
    (fun F Φ hF hΦ => jfCptLocAll Wp Wq P z z' π π' D F Φ hD.1 hz hz' hπ hπ' hF hΦ) i
  have hRR := RRi_lc X μ L st l0 hD i w hw.1.2.1
  have hu : act (RRi L st i w) x a ∈ lcSub P.k P.r z z' π π' :=
    (lcSub P.k P.r z z' π π').sum_mem fun b _ => (hRR a b).1 _ (hle (hx b))
  exact int_lc μ hD.2.1 hu (hle (hy a)) _

def FormIntOuterCpt : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (i : Fin (P.r + 1)) (c : Fin P.r → ℂ), c ∈ OmX P.r →
    ∀ x y : Ix S → RadSp P.k P.r z z' π π', InK (herKc S P z z' π π' L st l0 D i) x →
      InK (herKc S P z z' π π' L st l0 D i) y →
      Integrable (fun c' : Cf P.r i => ((∏ l, ‖c' l‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (act (RRi L st i w) x a) (y a) (glue i c c'))

def StepDensCptAll : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    StepDens (S := S) P z z' π π' μ L st (herKc S P z z' π π' L st l0 D) l0

theorem stepFormCptAll_of (hSD : StepDensCptAll) (hFO : FormIntOuterCpt) : StepFormCptAll := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ'
  refine ⟨hSD Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ', fun w hw i c hc x y hx hy => ⟨?_, ?_⟩⟩
  · exact fun c' a => formIntG_herKc P z z' π π' X μ L st l0 D hD hz hz' hπ hπ' w hw i c x y hx hy c' a
  · exact hFO Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' w hw i c hc x y hx hy

theorem thmPActualCpt_of_outer (hSD : StepDensCptAll) (hFO : FormIntOuterCpt) : ThmPActualCpt :=
  thmPActualCpt_of_stepForm (stepFormCptAll_of hSD hFO)

end Form

end Formalism.FourierDecayAlt.P5.HerC
end
end

