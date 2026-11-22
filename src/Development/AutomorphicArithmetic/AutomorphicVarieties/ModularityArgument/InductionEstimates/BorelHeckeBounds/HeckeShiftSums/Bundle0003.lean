import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.Full
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.SgBasics
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.HpSpec
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0001
import GroundTheory.AutomorphicForms.ReductionHeight
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.Bundle0001
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.UnipotentBlockMatrices.ClosedKernelMinors.Bundle0005
import Development.AutomorphicArithmetic.Foundations.Convolution.ConvolutionKernels.Bundle0004

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.SecDec
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

section SlopeTestRemainingChoices

variable {K : Type} [Field K] [NumberField K]

private theorem sd_ent {n : ℕ} (h : AdelicGLn.AdelicGL K n) (i j : Fin n) (y : GroundTheory.Global.IdeleGroup K)
    (hy : (y : 𝔸[K]) = (h : Matrix (Fin n) (Fin n) 𝔸[K]) i j) :
    (GroundTheory.Global.IdeleGroup.ideleModule K y : ℝ) ≤ AutomorphicForm.height h := by
  rw [GroundTheory.Global.IdeleGroup.ideleModule_eq, AutomorphicForm.height]
  refine mul_le_mul (Finset.prod_le_prod (fun w _ => by positivity) fun w _ => ?_)
    (finprod_le_finprod_of_nonneg (GroundTheory.Global.IdeleGroup.finite_mulSupport_norm y) (finite_mulSupport_locHeight_finAt h)
      (fun v => norm_nonneg _) fun v => ?_) (finprod_nonneg fun v => norm_nonneg _)
    (Finset.prod_nonneg fun w _ => pow_nonneg (locHeight_pos _).le _)
  · refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    rw [hy]
    exact norm_apply_le_locHeight (infAt w h) i j
  · rw [hy]
    exact norm_apply_le_locHeight (finAt v h) i j

private theorem mul_upper_triangular_first_col {R : Type} [CommRing R] (S T : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (hT : T.IsUpperTriangular)
    (i : Fin (2 + 2)) : (S * T) i 0 = S i 0 * T 0 0 := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single 0 (fun l _ hl => ?_) (fun h => absurd (Finset.mem_univ _) h)
  rw [hT (show (id 0 : Fin (2 + 2)) < id l from Fin.pos_iff_ne_zero.2 hl), mul_zero]

private theorem upper_triangular_mul_last_row {R : Type} [CommRing R] (S T : Matrix (Fin (2 + 2)) (Fin (2 + 2)) R) (hT : T.IsUpperTriangular)
    (j : Fin (2 + 2)) : (T * S) 3 j = T 3 3 * S 3 j := by
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_single 3 (fun l _ hl => ?_) (fun h => absurd (Finset.mem_univ _) h)
  rw [hT (show (id l : Fin (2 + 2)) < id 3 from Fin.lt_last_iff_ne_last.2 hl), zero_mul]

private theorem sd_col (δ : GL (Fin (2 + 2)) K) (T : AdelicGLn.AdelicGL K (2 + 2)) (hT : T ∈ adelicBorel)
    (u : GroundTheory.Global.IdeleGroup K) (hu : (u : 𝔸[K]) = (T : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) 0 0) :
    (GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ) ≤ AutomorphicForm.height (AdelicGLn.diagonal K (2 + 2) δ * T) := by
  obtain ⟨i, hi⟩ : ∃ i, (δ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) i 0 ≠ 0 := by
    by_contra h
    push Not at h
    have := congrArg (fun M => M 0 0) (Units.inv_mul δ)
    simp only [Matrix.mul_apply, h, mul_zero, Finset.sum_const_zero, Matrix.one_apply_eq] at this
    exact zero_ne_one this
  have h := sd_ent (AdelicGLn.diagonal K (2 + 2) δ * T) i 0 (GroundTheory.Global.IdeleGroup.diagonal K (Units.mk0 _ hi) * u) (by
    rw [Units.val_mul, Units.val_mul, mul_upper_triangular_first_col _ _ hT, hu, GroundTheory.Global.IdeleGroup.coe_diagonal, AdelicGLn.diagonal_apply,
      Units.val_mk0])
  rwa [map_mul, GroundTheory.Global.IdeleGroup.ideleModule_diagonal, one_mul] at h

private theorem sd_row (δ : GL (Fin (2 + 2)) K) (T : AdelicGLn.AdelicGL K (2 + 2)) (hT : T ∈ adelicBorel)
    (u : GroundTheory.Global.IdeleGroup K) (hu : (u : 𝔸[K]) = (T : Matrix (Fin (2 + 2)) (Fin (2 + 2)) 𝔸[K]) 3 3) :
    (GroundTheory.Global.IdeleGroup.ideleModule K u : ℝ) ≤ AutomorphicForm.height (T * AdelicGLn.diagonal K (2 + 2) δ) := by
  obtain ⟨j, hj⟩ : ∃ j, (δ : Matrix (Fin (2 + 2)) (Fin (2 + 2)) K) 3 j ≠ 0 := by
    by_contra h
    push Not at h
    have := congrArg (fun M => M 3 3) (Units.mul_inv δ)
    simp only [Matrix.mul_apply, h, zero_mul, Finset.sum_const_zero, Matrix.one_apply_eq] at this
    exact zero_ne_one this
  have h := sd_ent (T * AdelicGLn.diagonal K (2 + 2) δ) 3 j (u * GroundTheory.Global.IdeleGroup.diagonal K (Units.mk0 _ hj)) (by
    rw [Units.val_mul, Units.val_mul, upper_triangular_mul_last_row _ _ hT, hu, GroundTheory.Global.IdeleGroup.coe_diagonal, AdelicGLn.diagonal_apply,
      Units.val_mk0])
  rwa [map_mul, GroundTheory.Global.IdeleGroup.ideleModule_diagonal, mul_one] at h

private theorem sd_zt (s : ℝ) : ∃ a : GroundTheory.Global.IdeleGroup K, zt K s = diagUnits 2 (fun _ => a) ∧
    (GroundTheory.Global.IdeleGroup.ideleModule K a : ℝ) = Real.exp (s / 2) := by
  obtain ⟨a, ha⟩ : ∃ a : GroundTheory.Global.IdeleGroup K, zt K s = diagUnits 2 (fun _ => a) := ⟨_, rfl⟩
  refine ⟨a, ha, ?_⟩
  have h : (detModule K 2 (zt K s) : ℝ) = Real.exp s := by rw [zt, detModule_centralSection two_pos]
  change (GroundTheory.Global.IdeleGroup.ideleModule K (AdelicGLn.det K 2 (zt K s)) : ℝ) = _ at h
  rw [ha, det_diagUnits, Fin.prod_univ_two, map_mul, Positive.val_mul] at h
  refine (pow_left_inj₀ (GroundTheory.Global.IdeleGroup.ideleModule K a).2.le (Real.exp_pos _).le two_ne_zero).1 ?_
  rw [sq, h, sq, ← Real.exp_add, add_halves]

private theorem sd_lv (s : ℝ) : ∃ a : Fin (2 + 2) → GroundTheory.Global.IdeleGroup K,
    ((lv 1 1 s : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) = diagUnits (2 + 2) a ∧
    (GroundTheory.Global.IdeleGroup.ideleModule K (a 0) : ℝ) = Real.exp (s / 2) ∧
    (GroundTheory.Global.IdeleGroup.ideleModule K (a 3) : ℝ) = Real.exp (-s / 2) := by
  obtain ⟨a, ha, ha'⟩ := sd_zt (K := K) s
  obtain ⟨c, hc, hc'⟩ := sd_zt (K := K) (-s)
  refine ⟨fun i => Sum.elim (fun _ => a) (fun _ => c) (finSumFinEquiv.symm i), ?_, ha', hc'⟩
  rw [blkLaws.1, Subgroup.coe_one, one_mul, one_mul, ha, hc]
  refine Units.ext ?_
  change Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (Matrix.diagonal _) 0 0 (Matrix.diagonal _)) = _
  rw [Matrix.fromBlocks_diagonal, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv, coe_diagUnits]
  congr 1
  funext i
  simp only [Function.comp_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rfl

private theorem sd_key (δ : GL (Fin (2 + 2)) K) (b : AdelicGLn.AdelicGL K (2 + 2)) (hb : b ∈ adelicBorel)
    (a r : Fin (2 + 2) → GroundTheory.Global.IdeleGroup K) :
    (GroundTheory.Global.IdeleGroup.ideleModule K (a 0) : ℝ) * GroundTheory.Global.IdeleGroup.ideleModule K (r 0) ≤ AutomorphicForm.height b *
      AutomorphicForm.height (AdelicGLn.diagonal K (2 + 2) δ * (diagUnits (2 + 2) a * b * diagUnits (2 + 2) r)) ∧
    ((GroundTheory.Global.IdeleGroup.ideleModule K (a 3) : ℝ) * GroundTheory.Global.IdeleGroup.ideleModule K (r 3))⁻¹ ≤ AutomorphicForm.height b *
      AutomorphicForm.height (AdelicGLn.diagonal K (2 + 2) δ * (diagUnits (2 + 2) a * b * diagUnits (2 + 2) r)) := by
  have hT : diagUnits (2 + 2) a * b * diagUnits (2 + 2) r ∈ adelicBorel :=
    mul_mem (mul_mem (diagUnits_mem_adelicBorel _ a) hb) (diagUnits_mem_adelicBorel _ r)
  constructor
  · obtain ⟨β, hβ⟩ := isUnit_apply_self_of_mem_adelicBorel hb 0
    have h1 := sd_col δ _ hT (a 0 * β * r 0) (by
      simp only [Units.val_mul, coe_diagUnits, Matrix.mul_diagonal, Matrix.diagonal_mul, hβ])
    have h2 := sd_ent b⁻¹ 0 0 β⁻¹ (by
      have := mul_upper_triangular_first_col (b⁻¹ : AdelicGLn.AdelicGL K (2 + 2)).val b.val hb 0
      rw [Units.inv_mul, Matrix.one_apply_eq, ← hβ] at this
      exact Units.inv_eq_of_mul_eq_one_left this.symm)
    rw [height_inv, map_inv, Positive.coe_inv] at h2
    rw [map_mul, map_mul, Positive.val_mul, Positive.val_mul] at h1
    have hp := (GroundTheory.Global.IdeleGroup.ideleModule K β).2
    refine le_trans (le_of_eq ?_) (mul_le_mul h2 h1 (le_of_lt (mul_pos (mul_pos (Subtype.prop _) hp) (Subtype.prop _))) (height_pos _).le)
    field_simp
  · obtain ⟨β, hβ⟩ := isUnit_apply_self_of_mem_adelicBorel (inv_mem hb) 3
    have h1 := sd_row δ⁻¹ _ (inv_mem hT) ((r 3)⁻¹ * (β * (a 3)⁻¹)) (by
      rw [mul_inv_rev, mul_inv_rev, ← map_inv, ← map_inv]
      simp only [Units.val_mul, coe_diagUnits, Matrix.mul_diagonal, Matrix.diagonal_mul, hβ, Pi.inv_apply])
    have h2 := sd_ent b 3 3 β⁻¹ (by
      have := upper_triangular_mul_last_row b.val (b⁻¹ : AdelicGLn.AdelicGL K (2 + 2)).val (inv_mem hb : b⁻¹ ∈ adelicBorel) 3
      rw [Units.inv_mul, Matrix.one_apply_eq, ← hβ] at this
      exact Units.inv_eq_of_mul_eq_one_right this.symm)
    rw [map_inv, Positive.coe_inv] at h2
    rw [map_inv (AdelicGLn.diagonal K (2 + 2)), ← mul_inv_rev, height_inv, map_mul, map_mul, map_inv, map_inv, Positive.val_mul,
      Positive.val_mul, Positive.coe_inv, Positive.coe_inv] at h1
    have hp := (GroundTheory.Global.IdeleGroup.ideleModule K β).2
    have hp1 := (GroundTheory.Global.IdeleGroup.ideleModule K (a 3)).2
    have hp2 := (GroundTheory.Global.IdeleGroup.ideleModule K (r 3)).2
    refine le_trans (le_of_eq ?_) (mul_le_mul h2 h1 (by positivity) (height_pos _).le)
    field_simp

private theorem sd_real {d : ℕ} (hd : 0 < d) {ρ : Fin (2 + 2) → ℝ} (hρ : ∀ i, 0 < ρ i) {h C X : ℝ} (hX : 1 ≤ X) (hC : 0 ≤ C)
    (h1 : |h - (d : ℝ) * Real.log (ρ 0 * ρ 1)| ≤ C) (h2 : |Real.log (ρ 0 * ρ 1 * (ρ 2 * ρ 3))| ≤ C)
    (h3 : Real.exp (-h / 2) * ρ 0 ^ d ≤ X) (h4 : (Real.exp (- -h / 2) * ρ 3 ^ d)⁻¹ ≤ X) :
    inR ρ ≤ Real.exp (3 * C) * X ^ 4 := by
  have p0 := hρ 0
  have p1 := hρ 1
  have p2 := hρ 2
  have p3 := hρ 3
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hL := Real.log_nonneg hX
  have h3' := Real.log_le_log (by positivity) h3
  have h4' := Real.log_le_log (by positivity) h4
  rw [Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow] at h3'
  rw [Real.log_inv, Real.log_mul (by positivity) (by positivity), Real.log_exp, Real.log_pow] at h4'
  rw [Real.log_mul (by positivity) (by positivity)] at h1
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity)] at h2
  rw [← Real.log_le_log_iff (by unfold inR; positivity) (by positivity), inR, Real.log_mul (by positivity) (by positivity),
    Real.log_div p0.ne' p1.ne', Real.log_div p2.ne' p3.ne', Real.log_mul (by positivity) (by positivity), Real.log_exp,
    Real.log_pow]
  have h5 := (abs_le.1 h1).2
  have h6 := (abs_le.1 h2).2
  have h7 : (d : ℝ) * -(Real.log (ρ 1) + Real.log (ρ 3)) ≤ C + 2 * Real.log X := by linarith
  have h8 : -(Real.log (ρ 1) + Real.log (ρ 3)) ≤ C + 2 * Real.log X := by
    rcases le_total (-(Real.log (ρ 1) + Real.log (ρ 3))) 0 with h | h
    · linarith
    · exact (le_mul_of_one_le_left h hd1).trans h7
  push_cast
  linarith

end SlopeTestRemainingChoices

theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.secDec :
    ∀ {K : Type} [Field K] [NumberField K] (ω : Set (AdelicGLn.AdelicGL K (2 + 2))) (t : ℝ), Bor ω → 0 < t → ∀ f : G1 K (2 + 2) → ℂ, SFun f → ∀ N : ℕ, ∃ C : ℝ, ∀ (ρ : Fin (2 + 2) → ℝ) (z : G1 K (2 + 2)), Sg ω ρ z → Rel t ρ →
      ‖f z‖ * inR ρ ^ N ≤ C := by
  intro K _ _ ω t hω _ f hf N
  obtain ⟨C, c, hC, hS⟩ := sgBasics ω hω
  obtain ⟨M, hM⟩ := exists_height_le_of_isCompact hω.1
  obtain ⟨C', hC'⟩ := hf.dec (4 * N) 0
  have hc1 := one_le_heightConst (K := K) (n := 2 + 2)
  refine ⟨(Real.exp (3 * C) * (M * heightConst K (2 + 2)) ^ 4) ^ N * C', fun ρ z hz _ => ?_⟩
  obtain ⟨h1, h2, -⟩ := hS ρ z hz
  obtain ⟨hρ, b, hb, k, hk, e⟩ := hz
  have hy : HH (lv 1 1 (-HH z) * z) = 0 := by
    have := (hpSpec (K := K)).1 0 1 1 (-HH z) z
    rw [show nn (K := K) 0 = 1 from unipOne_zero _, one_mul] at this
    rw [this, neg_add_cancel]
  obtain ⟨γ, hγ, hd⟩ := hC' _ (by rw [hy, abs_zero])
  rw [hf.ray] at hd
  obtain ⟨δ, hδ⟩ : ∃ δ : GL (Fin (2 + 2)) K, AdelicGLn.diagonal K (2 + 2) δ = (γ : AdelicGLn.AdelicGL K (2 + 2)) := by
    obtain ⟨γ', -, rfl⟩ := hγ
    exact γ'.2
  obtain ⟨a, ha, ha0, ha3⟩ := sd_lv (K := K) (-HH z)
  set H := AutomorphicForm.height ((γ * (lv 1 1 (-HH z) * z) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) with hH
  have hH1 : 1 ≤ H := one_le_height _
  have hbM : AutomorphicForm.height b ≤ M := hM b hb
  have hM1 : 1 ≤ M := (one_le_height b).trans hbM
  obtain ⟨h3, h4⟩ := sd_key δ b (hω.2 hb) a fun i => posIdele (K := K) (ρ i) (hρ i)
  have h5 : AutomorphicForm.height b * AutomorphicForm.height (AdelicGLn.diagonal K (2 + 2) δ *
      (diagUnits (2 + 2) a * b * diagUnits (2 + 2) fun i => posIdele (K := K) (ρ i) (hρ i))) ≤ M * heightConst K (2 + 2) * H := by
    have h6 := height_mul_le ((γ * (lv 1 1 (-HH z) * z) : G1 K (2 + 2)) : AdelicGLn.AdelicGL K (2 + 2)) k⁻¹
    rw [height_inv, height_eq_one_of_mem_maxCompact hk, mul_one, ← hH, Subgroup.coe_mul, Subgroup.coe_mul, ha, ← hδ, e] at h6
    simp only [mul_assoc, mul_inv_cancel, mul_one] at h6 ⊢
    exact mul_le_mul hbM h6 (height_pos _).le (by linarith)
  rw [ha0, ideleModule_posIdele] at h3
  rw [ha3, ideleModule_posIdele] at h4
  have h7 := sd_real Module.finrank_pos hρ (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hM1 hc1) hH1)
    (by linarith) h1 h2 (h3.trans h5) (h4.trans h5)
  have h8 : 0 ≤ inR ρ := by
    have := hρ 0
    have := hρ 1
    have := hρ 2
    have := hρ 3
    unfold inR
    positivity
  calc ‖f z‖ * inR ρ ^ N ≤ ‖f z‖ * (Real.exp (3 * C) * (M * heightConst K (2 + 2) * H) ^ 4) ^ N :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h8 h7 N) (norm_nonneg _)
    _ = (Real.exp (3 * C) * (M * heightConst K (2 + 2)) ^ 4) ^ N * (‖f z‖ * H ^ (4 * N)) := by
        rw [mul_pow _ H, ← mul_assoc (Real.exp _), mul_pow _ (H ^ 4), ← pow_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hd (by positivity)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.InductionEstimates.BorelHeckeBounds.HeckeShiftSums.SumShift
section
open MeasureTheory NumberField Set Filter Topology
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum
open PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Adel PositivityTheory.Rg.Tf.IntegralApplyAeEq UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial UpperTheory.V.Z.IntegralApplyAeEq UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.K
open scoped ENNReal NumberField.AdeleRing InnerProductSpace ComplexConjugate

namespace UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.HeckeShiftDescent

private theorem mk_shift {G : Type*} [Group G] (P : Subgroup G) (a b : G) :
    (Quotient.mk (QuotientGroup.rightRel P) ((Quotient.mk (QuotientGroup.rightRel P) a).out * b)) =
      Quotient.mk (QuotientGroup.rightRel P) (a * b) := by
  have h : (QuotientGroup.rightRel P) ((Quotient.mk (QuotientGroup.rightRel P) a).out) a :=
    Quotient.mk_out (s := QuotientGroup.rightRel P) a
  refine Quotient.sound ?_
  change (QuotientGroup.rightRel P) _ _
  rw [QuotientGroup.rightRel_apply] at h ⊢
  simpa [mul_assoc] using h

private theorem shift_bij {G : Type*} [Group G] (P : Subgroup G) (b : G) :
    Function.Bijective fun q : Quotient (QuotientGroup.rightRel P) =>
      Quotient.mk (QuotientGroup.rightRel P) (q.out * b) := by
  refine Function.bijective_iff_has_inverse.2
    ⟨fun q => Quotient.mk (QuotientGroup.rightRel P) (q.out * b⁻¹), fun q => ?_, fun q => ?_⟩
  · simp only [mk_shift, mul_inv_cancel_right, Quotient.out_eq]
  · simp only [mk_shift, inv_mul_cancel_right, Quotient.out_eq]

variable {K : Type} [Field K] [NumberField K]

private theorem sum_shift {M : Type*} [AddCommMonoid M] (F : G1 K (2 + 2) → M)
    (hP : ∀ γ ∈ PK K, ∀ g, F (γ * g) = F g) (γ : G1 K (2 + 2)) (hγ : γ ∈ Gam K (2 + 2))
    (g : G1 K (2 + 2)) :
    ∑ᶠ q : Cos K, F ((q.out : G1 K (2 + 2)) * (γ * g)) = ∑ᶠ q : Cos K, F ((q.out : G1 K (2 + 2)) * g) := by
  have hout : ∀ (c : Gam K (2 + 2)) (g : G1 K (2 + 2)),
      F ((((Quotient.mk _ c : Cos K).out : Gam K (2 + 2)) : G1 K (2 + 2)) * g) = F (c * g) := fun c g => by
    obtain ⟨δ, hδ, h⟩ := (pkLaws (K := K)).2.2.2 c
    rw [h, mul_assoc, hP δ hδ]
  refine finsum_eq_of_bijective _ (shift_bij (ParΓ K 2 2) ⟨γ, hγ⟩) fun q => ?_
  rw [hout, Subgroup.coe_mul, mul_assoc]

private theorem desc_cont {Y : Type*} [TopologicalSpace Y] (f : G1 K (2 + 2) → Y) (hc : Continuous f)
    (hi : ∀ γ ∈ Gam K (2 + 2), ∀ x, f (γ * x) = f x) :
    Continuous fun y : RightCosetSpace (Gam K (2 + 2)) => f (Quotient.out y) := by
  rw [(isOpenQuotientMap_mk (Gam K (2 + 2))).isQuotientMap.continuous_iff]
  have : (fun y : RightCosetSpace (Gam K (2 + 2)) => f (Quotient.out y)) ∘ mk (Gam K (2 + 2)) = f := funext fun g => by
    obtain ⟨γ, hγ⟩ := (mk_eq_mk_iff (Γ := Gam K (2 + 2)) (g := (mk (Gam K (2 + 2)) g).out) (h := g)).1 (Quotient.out_eq _)
    change f _ = _
    rw [← hγ]
    exact hi γ γ.2 g
  rwa [this]

private theorem desc_sm {Y : Type*} [TopologicalSpace Y] [TopologicalSpace.PseudoMetrizableSpace Y]
    (f : G1 K (2 + 2) → Y) (hc : Continuous f) (hi : ∀ γ ∈ Gam K (2 + 2), ∀ x, f (γ * x) = f x) :
    StronglyMeasurable fun y : RightCosetSpace (Gam K (2 + 2)) => f (Quotient.out y) := by
  haveI : SecondCountableTopology (RightCosetSpace (Gam K (2 + 2))) :=
    (isOpenQuotientMap_mk (Gam K (2 + 2))).isQuotientMap.secondCountableTopology
      (isOpenQuotientMap_mk (Gam K (2 + 2))).isOpenMap
  exact (desc_cont f hc hi).stronglyMeasurable

private noncomputable def ramp (T : ℝ) (n : ℕ) (h : ℝ) : ℝ := max 0 (min 1 (((n : ℝ) + 1) * (h - T)))

private theorem ramp_cont (T : ℝ) (n : ℕ) : Continuous (ramp T n) := by
  unfold ramp
  fun_prop

private theorem ramp_zero {T h : ℝ} (n : ℕ) (hh : h ≤ T) : ramp T n h = 0 := by
  have : ((n : ℝ) + 1) * (h - T) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (sub_nonpos.2 hh)
  exact max_eq_left ((min_le_right _ _).trans this)

private theorem ramp_lim (T h : ℝ) :
    Tendsto (fun n : ℕ => ((ramp T n h : ℝ) : ℂ)) atTop (𝓝 (if T < h then 1 else 0)) := by
  split_ifs with hh
  · obtain ⟨N, hN⟩ := exists_nat_gt (1 / (h - T))
    have hp : 0 < h - T := sub_pos.2 hh
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with n hn
    have h1 : 1 ≤ ((n : ℝ) + 1) * (h - T) := by
      have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
      rw [div_lt_iff₀ hp] at hN
      nlinarith
    have : ramp T n h = 1 := by
      unfold ramp
      rw [min_eq_left h1]
      exact max_eq_right zero_le_one
    rw [this]
    simp
  · refine tendsto_const_nhds.congr fun n => ?_
    rw [ramp_zero n (not_lt.1 hh)]
    simp

end UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.HeckeShiftDescent

open UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.HeckeShiftDescent in
theorem UpperTheory.V.Z.InvariantSubmoduleMonicPolynomial.kT :
    ∀ {K : Type} [Field K] [NumberField K] (μ : Measure (G1 K (2 + 2))) [μ.IsHaarMeasure] (a : CC K (2 + 2)) (T : ℝ), ∃ kk : G1 K (2 + 2) → L2 μ,
      (∀ x φ, ⟪kk x, φ⟫_ℂ = lam T (rc μ a φ) x) ∧ (∀ γ ∈ Gam K (2 + 2), ∀ x, kk (γ * x) = kk x) ∧ (∀ x, Om T x → kk x = kv μ a x) ∧
      StronglyMeasurable fun y : RightCosetSpace (Gam K (2 + 2)) => kk (Quotient.out y) := by
  intro K _ _ μ _ a T
  obtain ⟨kc, hkc, hin⟩ := (ctKv μ a).1 2
  have hlaw := (ctKv μ a).2
  have hH := hpSpec (K := K)
  have hkP : ∀ γ ∈ PK K, ∀ z, kc (γ * z) = kc z := fun γ hγ z =>
    ext_inner_right ℂ fun φ => by rw [hin, hin, (hlaw φ).2.2.2.1 γ hγ z]

  let A : (ℝ → ℂ) → G1 K (2 + 2) → L2 μ := fun w x =>
    kv μ a x - ∑ᶠ q : Cos K, w (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x)
  have hAinv : ∀ w, ∀ γ ∈ Gam K (2 + 2), ∀ x, A w (γ * x) = A w x := fun w γ hγ x => by
    have h1 := (ropAe K (2 + 2) μ a).2 γ hγ x
    have h2 := sum_shift (K := K) (fun g => w (HH g) • kc g)
      (fun δ hδ g => by simp only [hkP δ hδ g, hH.2.2.1 δ hδ g]) γ hγ x
    simp only [A, h1, h2]
  let ind : ℝ → ℂ := fun h => if T < h then 1 else 0

  have hfin : ∀ x : G1 K (2 + 2), {q : Cos K | T ≤ HH ((q.out : G1 K (2 + 2)) * x)}.Finite := fun x =>
    (locFin {x} T isCompact_singleton).subset fun q hq => ⟨x, rfl, hq⟩
  have hsupp : ∀ (w : ℝ → ℂ), (∀ h, h < T → w h = 0) → ∀ x : G1 K (2 + 2),
      (Function.support fun q : Cos K => w (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x)) ⊆
        {q : Cos K | T ≤ HH ((q.out : G1 K (2 + 2)) * x)} := fun w hw x q hq => by
    by_contra hlt
    exact hq (by beta_reduce; rw [hw _ (not_le.1 hlt), zero_smul])
  have hind : ∀ h, h < T → ind h = 0 := fun h hh => if_neg (not_lt.2 hh.le)
  have hrz : ∀ n : ℕ, ∀ h, h < T → ((ramp T n h : ℝ) : ℂ) = 0 := fun n h hh => by
    rw [ramp_zero n hh.le]
    simp
  refine ⟨A ind, fun x φ => ?_, hAinv ind, fun x hx => ?_, ?_⟩
  · let ip : L2 μ →+ ℂ :=
      { toFun := fun v => ⟪v, φ⟫_ℂ, map_zero' := inner_zero_left _, map_add' := fun u v => inner_add_left _ _ _ }
    have hsum : ⟪∑ᶠ q : Cos K, ind (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x), φ⟫_ℂ =
        ∑ᶠ q : Cos K, ⟪ind (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x), φ⟫_ℂ :=
      ip.map_finsum ((hfin x).subset (hsupp ind hind x))
    simp only [A, inner_sub_left, inner_kv, hsum, lam, th, hi]
    congr 1
    refine finsum_congr fun q => ?_
    rw [inner_smul_left, hin]
    by_cases h : T < HH ((q.out : G1 K (2 + 2)) * x)
    · simp [ind, h]
    · simp [ind, h]
  · have : ∀ q : Cos K, ind (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x) = 0 := fun q => by
      have : ind (HH ((q.out : G1 K (2 + 2)) * x)) = 0 := if_neg (not_lt.2 (hx q))
      rw [this, zero_smul]
    simp only [A, this, finsum_zero, sub_zero]
  ·
    have hcont : ∀ n : ℕ, Continuous (A fun h => ((ramp T n h : ℝ) : ℂ)) := fun n => by
      refine (kvCont K (2 + 2) μ a).sub (continuous_finsum (fun q => ?_) fun x => ?_)
      · have hm : Continuous fun x : G1 K (2 + 2) => (q.out : G1 K (2 + 2)) * x :=
          continuous_const.mul continuous_id
        exact (Complex.continuous_ofReal.comp ((ramp_cont T n).comp (hH.2.2.2.1.comp hm))).smul (hkc.comp hm)
      · obtain ⟨C, hC, hx⟩ := exists_compact_mem_nhds x
        refine ⟨C, hx, (locFin C T hC).subset fun q ⟨g, hg, hgC⟩ => ⟨g, hgC, ?_⟩⟩
        exact hsupp _ (hrz n) g hg
    have hdesc : ∀ n : ℕ, StronglyMeasurable fun y : RightCosetSpace (Gam K (2 + 2)) =>
        A (fun h => ((ramp T n h : ℝ) : ℂ)) (Quotient.out y) := fun n =>
      desc_sm (A fun h => ((ramp T n h : ℝ) : ℂ)) (hcont n) (hAinv fun h => ((ramp T n h : ℝ) : ℂ))
    refine stronglyMeasurable_of_tendsto atTop hdesc (tendsto_pi_nhds.2 fun y => ?_)
    set x : G1 K (2 + 2) := Quotient.out y
    have e : ∀ w : ℝ → ℂ, (∀ h, h < T → w h = 0) →
        A w x = kv μ a x - ∑ q ∈ (hfin x).toFinset, w (HH ((q.out : G1 K (2 + 2)) * x)) • kc ((q.out : G1 K (2 + 2)) * x) := fun w hw => by
      simp only [A]
      rw [finsum_eq_sum_of_support_subset (s := (hfin x).toFinset) _ (by rw [Set.Finite.coe_toFinset]; exact hsupp w hw x)]
    simp only [e _ (hrz _), e ind hind]
    refine tendsto_const_nhds.sub (tendsto_finset_sum _ fun q _ => ?_)
    exact (ramp_lim T _).smul_const _
end

