import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsMahler
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Statements
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMeanSlice
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0011

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSphereMeanFubini
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Set

noncomputable section

namespace SphereMeanFubini

def groupSplit (k n : ℕ) : Fin n ⊕ (Fin k × Fin n) ≃ Fin (k + 1) × Fin n where
  toFun := Sum.elim (fun j => (0, j)) (fun p => (p.1.succ, p.2))
  invFun p := Fin.cases (motive := fun _ => Fin n ⊕ (Fin k × Fin n)) (Sum.inl p.2)
    (fun i => Sum.inr (i, p.2)) p.1
  left_inv := by rintro (j | ⟨i, j⟩) <;> simp
  right_inv := by
    rintro ⟨i, j⟩
    cases i using Fin.cases <;> simp

def consEquiv {n : ℕ} (k : ℕ) : ((Fin n → ℂ) × (Fin k × Fin n → ℂ)) ≃ᵐ (Fin (k + 1) × Fin n → ℂ) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ (Fin k × Fin n) => ℂ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ => ℂ) (groupSplit k n))

theorem consEquiv_apply {n k : ℕ} (p : (Fin n → ℂ) × (Fin k × Fin n → ℂ)) :
    consEquiv k p = consGroup p.1 p.2 := by
  funext ⟨i, j⟩
  cases i using Fin.cases with
  | zero =>
    have e : ((0 : Fin (k + 1)), j) = groupSplit k n (Sum.inl j) := rfl
    rw [e]
    simp [consEquiv, consGroup, MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi,
      Equiv.piCongrLeft_apply_apply]
    rfl
  | succ i =>
    have e : (i.succ, j) = groupSplit k n (Sum.inr (i, j)) := rfl
    rw [e]
    simp [consEquiv, consGroup, MeasurableEquiv.piCongrLeft, MeasurableEquiv.sumPiEquivProdPi,
      Equiv.piCongrLeft_apply_apply]
    rfl

theorem measurePreserving_consEquiv {n : ℕ} (k : ℕ) :
    MeasurePreserving (consEquiv (n := n) k) volume volume :=
  (measurePreserving_piCongrLeft (fun _ : Fin (k + 1) × Fin n => (volume : Measure ℂ))
    (groupSplit k n)).comp
    (measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ (Fin k × Fin n) => (volume : Measure ℂ)))

theorem preimage_ballProd {n : ℕ} (h : HermNorm n) (k : ℕ) :
    consEquiv k ⁻¹' ballProd h (k + 1) = ballH h ×ˢ ballProd h k := by
  ext p
  simp only [mem_preimage, consEquiv_apply, ballProd, mem_ofPred_eq, mem_prod, ballH,
    Fin.forall_fin_succ, consGroup, Fin.cases_zero, Fin.cases_succ]

theorem nrmGroups_consGroup {n : ℕ} (h : HermNorm n) (k : ℕ) (v : Fin n → ℂ) (w : Fin k × Fin n → ℂ) :
    nrmGroups h (k + 1) (consGroup v w) = consGroup (nrmv h v) (nrmGroups h k w) := by
  funext ⟨i, j⟩
  cases i using Fin.cases <;> simp [nrmGroups, consGroup, nrmv]

theorem proof : SphereMeanFubini.Statement := by
  intro n k h G hG
  have hmp := measurePreserving_consEquiv (n := n) k
  have hme := (consEquiv (n := n) k).measurableEmbedding
  have hpre := preimage_ballProd h k
  set H : (Fin n → ℂ) × (Fin k × Fin n → ℂ) → ℝ :=
    fun p => G (nrmGroups h (k + 1) (consEquiv k p)) with hH
  have hHi : IntegrableOn H (ballH h ×ˢ ballProd h k) (volume.prod volume) := by
    rw [← hpre]
    exact (hmp.integrableOn_comp_preimage hme (f := fun u => G (nrmGroups h (k + 1) u))).2 hG
  have hint : ∫ p in ballH h ×ˢ ballProd h k, H p ∂(volume.prod volume) =
      ∫ u in ballProd h (k + 1), G (nrmGroups h (k + 1) u) := by
    rw [← hpre]
    exact hmp.setIntegral_preimage_emb hme (fun u => G (nrmGroups h (k + 1) u)) _
  have hvol : volume (ballProd h (k + 1)) = volume (ballH h) * volume (ballProd h k) := by
    rw [← hmp.measure_preimage_equiv, hpre, Measure.volume_eq_prod, Measure.prod_prod]
  rw [IntegrableOn, ← Measure.prod_restrict] at hHi
  rw [← Measure.prod_restrict, integral_prod _ hHi] at hint
  have hB0 : (volume (ballProd h k)).toReal ≠ 0 :=
    ENNReal.toReal_ne_zero.2 ⟨(volume_ballProd_pos h k).ne', (volume_ballProd_lt_top h k).ne⟩
  have hinner : ∀ v, sphereMean h k (fun w => G (consGroup (nrmv h v) w)) =
      (volume (ballProd h k)).toReal⁻¹ * ∫ w in ballProd h k, H (v, w) := by
    intro v
    simp only [hH, consEquiv_apply, nrmGroups_consGroup]
    rw [sphereMean, setAverage_eq, smul_eq_mul, measureReal_def]
    rfl
  have hfun : (fun v => sphereMean h k (fun w => G (consGroup (nrmv h v) w))) =
      fun v => (volume (ballProd h k)).toReal⁻¹ * ∫ w in ballProd h k, H (v, w) :=
    funext hinner
  have hlhs : sphereMean h (k + 1) G = (volume (ballProd h (k + 1))).toReal⁻¹ *
      ∫ u in ballProd h (k + 1), G (nrmGroups h (k + 1) u) := by
    rw [sphereMean, setAverage_eq, smul_eq_mul, measureReal_def]
    rfl
  refine ⟨?_, ?_⟩
  · rw [hfun]
    exact hHi.integral_prod_left.const_mul _
  · rw [hlhs, ← hint, hvol, setAverage_eq, smul_eq_mul, measureReal_def, hfun, integral_const_mul,
      ENNReal.toReal_mul, mul_inv]
    ring

end SphereMeanFubini

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PSphereMeanLinearBall
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Set

noncomputable section

namespace SphereMeanLinearBall

theorem std_norm (n : ℕ) (v : Fin n → ℂ) : (HermNorm.std n).norm v = √(∑ j, ‖v j‖ ^ 2) := by
  simp [HermNorm.norm, HermNorm.std]

theorem std_dualNorm (n : ℕ) (y : Fin n → ℂ) :
    (HermNorm.std n).dualNorm y = √(∑ j, ‖y j‖ ^ 2) := by
  simp [HermNorm.dualNorm, HermNorm.std]

theorem sum_sq_nrmv_le (n : ℕ) (w : Fin n → ℂ) :
    ∑ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2 ≤ 1 := by
  have hS : 0 ≤ ∑ j, ‖w j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have e : ∀ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2 = (∑ j, ‖w j‖ ^ 2)⁻¹ * ‖w j‖ ^ 2 := by
    intro j
    rw [nrmv, std_norm, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg (Real.sqrt_nonneg _), mul_pow, inv_pow, Real.sq_sqrt hS]
  rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum]
  rcases eq_or_ne (∑ j, ‖w j‖ ^ 2) 0 with h | h
  · simp [h]
  · rw [inv_mul_cancel₀ h]

theorem norm_sum_mul_le (n : ℕ) (a b : Fin n → ℂ) :
    ‖∑ j, a j * b j‖ ≤ √(∑ j, ‖a j‖ ^ 2) * √(∑ j, ‖b j‖ ^ 2) := by
  refine (norm_sum_le _ _).trans ?_
  simp_rw [norm_mul]
  exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem sum_sq_pos {n : ℕ} {y : Fin n → ℂ} (hy : y ≠ 0) : 0 < ∑ j, ‖y j‖ ^ 2 := by
  refine lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => sq_nonneg _) fun h => hy ?_
  have h0 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg ‖y j‖).mp h.symm
  funext j
  simpa using h0 j (Finset.mem_univ j)

theorem fsLog_nrmv_nonpos (n : ℕ) (y w : Fin n → ℂ) :
    fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y ≤ 0 := by
  rw [fsLog, std_dualNorm]
  refine Real.log_nonpos (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)) ?_
  refine div_le_one_of_le₀ ?_ (Real.sqrt_nonneg _)
  refine (norm_sum_mul_le n _ _).trans ?_
  have h1 : √(∑ j, ‖nrmv (HermNorm.std n) w j‖ ^ 2) ≤ 1 := by
    rw [Real.sqrt_le_one]
    exact sum_sq_nrmv_le n w
  exact mul_le_of_le_one_left (Real.sqrt_nonneg _) h1

end SphereMeanLinearBall

open SphereMeanLinearBall in

theorem SphereMeanLinearBall.proof (h1 : SphereMeanLinear.Statement) : SphereMeanLinearBall.Statement := by
  intro n y hy
  set g : (Fin n → ℂ) → ℝ := fun w => fsLog (HermNorm.std n) (nrmv (HermNorm.std n) w) y with hg
  have hpos := sum_sq_pos hy
  set r : ℝ := √(∑ j, ‖y j‖ ^ 2) with hr
  have hr0 : 0 < r := Real.sqrt_pos.mpr hpos

  let p : Fin n → ℂ := fun j => ((r : ℂ))⁻¹ * star (y j)
  have hp : ∑ j, ‖p j‖ ^ 2 = 1 := by
    have e : ∀ j, ‖p j‖ ^ 2 = (∑ j, ‖y j‖ ^ 2)⁻¹ * ‖y j‖ ^ 2 := by
      intro j
      show ‖((r : ℂ))⁻¹ * star (y j)‖ ^ 2 = _
      rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg hr0.le, norm_star, mul_pow,
        inv_pow, hr, Real.sq_sqrt hpos.le]
    rw [Finset.sum_congr rfl fun j _ => e j, ← Finset.mul_sum, inv_mul_cancel₀ hpos.ne']
  have hkey : ∀ a : Fin n → ℂ, Real.log ‖∑ j, a j * star (p j)‖ = fsLog (HermNorm.std n) a y := by
    intro a
    have e : ∑ j, a j * star (p j) = ((r : ℂ))⁻¹ * ∑ j, a j * y j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [p, star_mul', star_inv₀, Complex.star_def, Complex.conj_ofReal, Complex.conj_conj]
      ring
    rw [e, fsLog, std_dualNorm, ← hr, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_of_nonneg hr0.le, div_eq_inv_mul]

  let e := (Equiv.uniqueProd (Fin n) (Fin 1)).symm
  let L1 : (Fin 1 × Fin n → ℂ) ≃L[ℝ] (Fin n → ℂ) :=
    (LinearEquiv.funCongrLeft ℝ ℂ e).toContinuousLinearEquiv
  have hL1 : ∀ u, (fun j => u (0, j)) = L1 u := by
    intro u
    funext j
    simp [L1, e]
  have hS : {u : Fin 1 × Fin n → ℂ | ∀ i, (HermNorm.std n).norm (fun j => u (i, j)) < 1} =
      L1 ⁻¹' ballH (HermNorm.std n) := by
    ext u
    simp only [mem_ofPred_eq, mem_preimage, ballH, Fin.forall_fin_one, hL1]
  have hmean : ⨍ w in ballH (HermNorm.std n), g w = -(harmonic (n - 1) : ℝ) / 2 := by
    rw [← h1 n p hp, sphereMean, hS,
      ← SphereMean.setAverage_comp_linearEquiv volume volume L1 (ballH (HermNorm.std n)) g]
    congr 1
    funext u
    rw [hkey]
    simp only [hg]
    rw [← hL1 u]
    rfl
  refine ⟨?_, fun w => fsLog_nrmv_nonpos n y w, hmean⟩
  rcases eq_or_ne (harmonic (n - 1)) 0 with hH | hH
  ·
    have hn1 : n - 1 = 0 := by
      by_contra hne
      exact (harmonic_pos hne).ne' hH
    have hn : n = 1 := by
      rcases Nat.eq_zero_or_pos n with h0 | h0
      · subst h0
        exact absurd (Subsingleton.elim y 0) hy
      · omega
    subst hn
    have hz : g = 0 := by
      funext w
      simp only [hg, Pi.zero_apply, fsLog, std_dualNorm, nrmv, std_norm, Fin.sum_univ_one]
      rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _), norm_mul, norm_mul, norm_inv,
        Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
      have hy0 : y 0 ≠ 0 := fun h => hy (funext fun j => by rw [Subsingleton.elim j 0, h]; rfl)
      rcases eq_or_ne (w 0) 0 with hw | hw
      · simp [hw]
      · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw), one_mul,
          div_self (norm_ne_zero_iff.mpr hy0), Real.log_one]
    rw [hz]
    exact integrableOn_zero
  ·
    by_contra hni
    have h0 : ⨍ w in ballH (HermNorm.std n), g w = 0 := by
      rw [setAverage_eq, integral_undef hni, smul_zero]
    rw [hmean] at h0
    exact hH (by exact_mod_cast (by linarith : (harmonic (n - 1) : ℝ) = 0))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SphereMean
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MeasureTheory Measure Set Real

noncomputable section

namespace SphereMean

theorem setAverage_log_fst_sub (m : ℕ) :
    ⨍ y in ballSet (m + 1) 1, (log ‖y 0‖ - log (sqNorm y) / 2) = -(harmonic m : ℝ) / 2 := by
  obtain ⟨h1i, h1⟩ := integral_ballSet_neg_log_fst m
  obtain ⟨h2i, h2⟩ := integral_ballSet_neg_log_sqNorm m
  have hV : 0 < volume.real (ballSet (m + 1) 1) :=
    ENNReal.toReal_pos (volume_ballSet_one_pos _).ne' (volume_ballSet_one_ne_top _)
  have hfun : (fun y : Fin (m + 1) → ℂ => log ‖y 0‖ - log (sqNorm y) / 2) =
      fun y => (-log (sqNorm y)) / 2 - (-log ‖y 0‖) := by
    funext y
    ring
  rw [setAverage_eq, hfun, integral_sub (h2i.div_const 2) h1i, integral_div, h1, h2,
    harmonic_succ]
  push_cast
  rw [smul_eq_mul]
  field_simp
  ring

theorem volume_fst_eq_zero (m : ℕ) : volume {y : Fin (m + 1) → ℂ | y 0 = 0} = 0 := by
  let K : Submodule ℝ (Fin (m + 1) → ℂ) :=
    LinearMap.ker (LinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℂ) 0)
  have hK : (K : Set (Fin (m + 1) → ℂ)) = {y | y 0 = 0} := by
    ext y
    simp only [K, SetLike.mem_coe, LinearMap.mem_ker, LinearMap.proj_apply, mem_ofPred_eq]
  have hne : K ≠ ⊤ := by
    intro h
    have : (Pi.single 0 1 : Fin (m + 1) → ℂ) ∈ K := h ▸ Submodule.mem_top
    simp only [K, LinearMap.mem_ker, LinearMap.proj_apply, Pi.single_eq_same] at this
    exact one_ne_zero this
  rw [← hK]
  exact addHaar_submodule _ _ hne

theorem setAverage_log_fst_normalized (m : ℕ) :
    ⨍ y in ballSet (m + 1) 1, log ‖((√(sqNorm y) : ℝ) : ℂ)⁻¹ * y 0‖ = -(harmonic m : ℝ) / 2 := by
  rw [← setAverage_log_fst_sub m]
  apply average_congr
  refine ae_restrict_of_ae ?_
  have h0 := measure_eq_zero_iff_ae_notMem.mp (volume_fst_eq_zero m)
  filter_upwards [h0] with y hy
  have hy' : y 0 ≠ 0 := fun h => hy h
  have hs : 0 < sqNorm y := sqNorm_pos_of_ne_zero (fun h => hy' (by simp [h]))
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    log_mul (inv_ne_zero (Real.sqrt_pos.mpr hs).ne') (norm_ne_zero_iff.mpr hy'), log_inv,
    log_sqrt hs.le]
  ring

theorem std_norm_eq (n : ℕ) (v : Fin n → ℂ) : (HermNorm.std n).norm v = √(sqNorm v) := by
  simp [HermNorm.norm, HermNorm.std, sqNorm]

end SphereMean

open SphereMean in

theorem sphereMeanLinear : SphereMeanLinear.Statement := by
  intro n p hp
  cases n with
  | zero => simp at hp
  | succ m =>

  let e := (Equiv.uniqueProd (Fin (m + 1)) (Fin 1)).symm
  let L1 : (Fin 1 × Fin (m + 1) → ℂ) ≃L[ℝ] (Fin (m + 1) → ℂ) :=
    (LinearEquiv.funCongrLeft ℝ ℂ e).toContinuousLinearEquiv
  have hL1 : ∀ u j, L1 u j = u (0, j) := by
    intro u j
    simp [L1, e]
  let G1 : (Fin (m + 1) → ℂ) → ℝ := fun v =>
    log ‖∑ j, (((√(sqNorm v) : ℝ) : ℂ)⁻¹ * v j) * star (p j)‖
  have hS : {u : Fin 1 × Fin (m + 1) → ℂ |
      ∀ i, (HermNorm.std (m + 1)).norm (fun j => u (i, j)) < 1} = L1 ⁻¹' ballSet (m + 1) 1 := by
    ext u
    simp only [mem_ofPred_eq, mem_preimage, ballSet, std_norm_eq, Fin.forall_fin_one]
    have : (fun j => u (0, j)) = L1 u := funext fun j => (hL1 u j).symm
    rw [this, Real.sqrt_lt' one_pos, one_pow]
  have hstep1 : sphereMean (HermNorm.std (m + 1)) 1
      (fun z => Real.log ‖∑ j, z (0, j) * star (p j)‖) = ⨍ u in L1 ⁻¹' ballSet (m + 1) 1, G1 (L1 u) := by
    unfold sphereMean
    rw [hS]
    congr 1
    funext u
    have : (fun j => u (0, j)) = L1 u := funext fun j => (hL1 u j).symm
    simp only [G1, std_norm_eq, this, hL1]
  rw [hstep1, setAverage_comp_linearEquiv volume volume L1 (ballSet (m + 1) 1) G1]

  let p' : EuclideanSpace ℂ (Fin (m + 1)) := WithLp.toLp 2 p
  have hp' : ‖p'‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp [p', hp]
  have hon : Orthonormal ℂ (({0} : Set (Fin (m + 1))).domRestrict fun _ => p') := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [Subsingleton.elim i j, if_pos rfl,
      show (({0} : Set (Fin (m + 1))).domRestrict fun _ => p') j = p' from rfl,
      inner_self_eq_norm_sq_to_K, hp']
    simp
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  have hb0 : b 0 = p' := hb 0 (mem_singleton 0)
  let Ulin : (Fin (m + 1) → ℂ) ≃ₗ[ℂ] (Fin (m + 1) → ℂ) :=
    (WithLp.linearEquiv 2 ℂ (Fin (m + 1) → ℂ)).symm ≪≫ₗ b.repr.toLinearEquiv ≪≫ₗ
      WithLp.linearEquiv 2 ℂ (Fin (m + 1) → ℂ)
  let U : (Fin (m + 1) → ℂ) ≃L[ℝ] (Fin (m + 1) → ℂ) :=
    (Ulin.restrictScalars ℝ).toContinuousLinearEquiv
  have hUapp : ∀ v, U v = (b.repr (WithLp.toLp 2 v)).ofLp := fun v => rfl
  have hU0 : ∀ v, U v 0 = ∑ j, v j * star (p j) := by
    intro v
    rw [hUapp, OrthonormalBasis.repr_apply_apply, hb0, PiLp.inner_apply]
    simp [p', RCLike.inner_apply]
  have hUn : ∀ v, sqNorm (U v) = sqNorm v := by
    intro v
    have h := b.repr.norm_map (WithLp.toLp 2 v)
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h
    have h2 := congrArg (· ^ 2) h
    simp only [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)] at h2
    simpa [sqNorm, hUapp] using h2
  let G2 : (Fin (m + 1) → ℂ) → ℝ := fun w => log ‖((√(sqNorm w) : ℝ) : ℂ)⁻¹ * w 0‖
  have hG : ∀ v, G1 v = G2 (U v) := by
    intro v
    simp only [G1, G2, hUn, hU0, Finset.mul_sum, mul_assoc]
  have hB : ballSet (m + 1) 1 = U ⁻¹' ballSet (m + 1) 1 := by
    ext v
    simp [ballSet, hUn]
  have hstep2 : ⨍ v in ballSet (m + 1) 1, G1 v = ⨍ v in U ⁻¹' ballSet (m + 1) 1, G2 (U v) := by
    rw [← hB]
    congr 1
    funext v
    exact hG v
  rw [hstep2, setAverage_comp_linearEquiv volume volume U (ballSet (m + 1) 1) G2]
  simp only [G2]
  rw [setAverage_log_fst_normalized m]
  simp

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartLengthAlgClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

open Classical in

def ChartLengthAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t u : Fin n → F)
    (q : MvPolynomial (Fin e × Fin n) F) (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm u ∉ I → Prime q → p = Ideal.span {q} →
      ¬ q ∣ specFirst f t →
        Module.length (Localization.AtPrime p) (ChartLoc I t e p ⧸ LinearMap.range
            (LinearMap.mulLeft (Localization.AtPrime p)
              (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u)))) =
          ∑ W ∈ (divCycle I u).support with Ideal.span {q} = incIdeal W e,
            ((divCycle I u W : ℕ) : ℕ∞)

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartNormAlgClosed
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def ChartNormAlgClosed.Statement : Prop :=
  ∀ (F : Type) [Field F] [IsAlgClosed F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime],
    IsProjPrime I → IsChowForm I (e + 1) f → (p = ⊥ ∨ ∃ q, Prime q ∧ p = Ideal.span {q}) →
      specFirst f t ∉ p → ∀ u : Fin n → F,
        algebraMap _ (Localization.AtPrime p) (specFirst f u) =
          algebraMap _ (Localization.AtPrime p) (specFirst f t) *
            LinearMap.det (LinearMap.mulLeft (Localization.AtPrime p)
              (algebraMap (ChartInc I t e) (ChartLoc I t e p) (chartLin I t e u)))

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChartNormSep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

def NormOfDividedFormSep.Statement : Prop :=
  ∀ (O B : Type) [CommRing O] [IsDomain O] [Infinite O] [CommRing B] [IsDomain B] [Algebra O B]
    [Module.Free O B] [Module.Finite O B] (n : ℕ) (η : Fin n → B) (t : Fin n → O)
    (P : MvPolynomial (Fin n) O),
    (letI := FractionRing.liftAlgebra O (FractionRing B)
     Algebra.IsSeparable (FractionRing O) (FractionRing B)) →
    Algebra.adjoin O (Set.range η) = ⊤ → ∑ m, t m • η m = 1 → Prime P →
      (∑ m, X m * C (η m)) ∣ map (algebraMap O B) P →
        ∀ u : Fin n → O,
          eval u P = eval t P * LinearMap.det (LinearMap.mulLeft O (∑ m, u m • η m))

def ChartFracSeparable.Statement : Prop :=
  ∀ (F : Type) [Field F] [PerfectField F] (n e : ℕ) (I : Ideal (MvPolynomial (Fin n) F))
    (f : MvPolynomial (Fin (e + 1) × Fin n) F) (t : Fin n → F)
    (p : Ideal (MvPolynomial (Fin e × Fin n) F)) [p.IsPrime] (K L : Type) [Field K] [Field L]
    [Algebra (Localization.AtPrime p) K] [IsFractionRing (Localization.AtPrime p) K]
    [Algebra (ChartLoc I t e p) L] [IsFractionRing (ChartLoc I t e p) L] [Algebra K L]
    [Algebra (Localization.AtPrime p) L] [IsScalarTower (Localization.AtPrime p) K L]
    [IsScalarTower (Localization.AtPrime p) (ChartLoc I t e p) L],
    IsProjPrime I → IsChowForm I (e + 1) f → linForm t ∉ I → Algebra.IsSeparable K L

section Inhabitants

end Inhabitants

end

end GroundTheory.Heights₂.Heights
end

