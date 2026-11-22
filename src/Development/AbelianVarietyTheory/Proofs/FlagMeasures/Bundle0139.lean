import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
import Formalism.RealPlaceAnalysis.FinalF
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0122
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0017
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0005
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0048
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ContinuousMulMt
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0123
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0051
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
import Formalism.LocalToGlobal.HermitianForms.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarBallGrowthUnitaryJ
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count
open scoped InnerProductSpace

namespace GlobalTheory.BallVol

lemma entry_le {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} {R : ℝ} (hR : 0 ≤ R) (hg : hs g ≤ R ^ 2)
    (i j : Fin n) : ‖g i j‖ ≤ R :=
  (pow_le_pow_iff_left₀ (norm_nonneg _) hR two_ne_zero).1 ((f1auxiliary_entry_le g i j).trans hg)

lemma inv_mul_uMat {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) : uMat g⁻¹ * uMat g = 1 := by
  have : uMat g⁻¹ * uMat g = uMat (g⁻¹ * g) := rfl
  rw [this, inv_mul_cancel]; rfl

lemma norm_inv_entry {n : ℕ} {ε : Fin n → Bool} (g : UJ ε) (i k : Fin n) :
    ‖uMat g⁻¹ i k‖ = ‖uMat g k i‖ := by
  have h1 := (uJInv n ε (uMat g) g.2).1
  have h2 : uMat g⁻¹ = Jm ε * (uMat g)ᴴ * Jm ε := by
    calc uMat g⁻¹ = uMat g⁻¹ * (uMat g * (Jm ε * (uMat g)ᴴ * Jm ε)) := by rw [h1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, inv_mul_uMat, Matrix.one_mul]
  rw [h2]
  unfold Jm
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  split_ifs <;> simp

lemma close_entry {n : ℕ} {ε : Fin n → Bool} (g t : UJ ε) {R : ℝ} (hR : 0 < R)
    (ht : hsG t ≤ R ^ 2) (j : Fin n) (hj : ∀ k, ‖uMat g k j - uMat t k j‖ ≤ 1 / R) (i : Fin n) :
    ‖uMat (t⁻¹ * g) i j‖ ≤ 1 + n := by
  have e : uMat (t⁻¹ * g) = 1 + uMat t⁻¹ * (uMat g - uMat t) := by
    rw [Matrix.mul_sub, inv_mul_uMat]
    have : uMat (t⁻¹ * g) = uMat t⁻¹ * uMat g := rfl
    rw [this]; abel
  rw [e, Matrix.add_apply, Matrix.mul_apply]
  have h3 : ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ≤ 1 := by
    rw [Matrix.one_apply]; split_ifs <;> simp
  refine (norm_add_le _ _).trans (add_le_add h3 ?_)
  refine (norm_sum_le _ _).trans ?_
  calc ∑ k, ‖uMat t⁻¹ i k * (uMat g - uMat t) k j‖ ≤ ∑ _k : Fin n, (1 : ℝ) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_mul, norm_inv_entry, Matrix.sub_apply]
        calc _ ≤ R * (1 / R) :=
              mul_le_mul (entry_le hR.le ht k i) (hj k) (norm_nonneg _) hR.le
          _ = 1 := by field_simp
    _ = n := by simp

lemma vol_sign (n : ℕ) (ε : Fin n → Bool) (s : Bool) : ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 1 ≤ R →
    muG ε {g | hsG g ≤ R ^ 2} ≤
      ENNReal.ofReal (C * R ^ (4 * n * (univ.filter fun a => ε a = s).card)) := by
  classical
  set q := (univ.filter fun a => ε a = s).card with hq
  let E := Fin n → {j // ε j = s} → ℂ
  have hfr : Module.finrank ℝ E = 2 * n * q := by
    simp only [E, Module.finrank_pi_fintype, Complex.finrank_real_complex, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, smul_eq_mul, Fintype.card_subtype, ← hq]
    ring
  let Y : UJ ε → E := fun g i j => uMat g i j.1
  let W : Set (UJ ε) := {g | hsG g ≤ n + 4 * (n * (n * (1 + n) ^ 2))}
  have hW : muG ε W < ⊤ := ballFinite n ε _
  refine ⟨3 ^ (2 * n * q) * (muG ε W).toReal, by positivity, fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith
  set S : Set (UJ ε) := {g | hsG g ≤ R ^ 2} with hS
  have hsub : Y '' S ⊆ Metric.closedBall 0 R := by
    rintro _ ⟨g, hg, rfl⟩
    rw [mem_closedBall_zero_iff, pi_norm_le_iff_of_nonneg hR0.le]
    intro i
    rw [pi_norm_le_iff_of_nonneg hR0.le]
    intro j
    exact entry_le hR0.le hg i j.1
  obtain ⟨T, hT1, hT2, hT3⟩ := GlobalTheory.exists_net_card_le_of_subset_closedBall E (Y '' S) R (1 / R) (by positivity) hR0.le hsub
  have hch : ∀ x : E, ∃ t : UJ ε, x ∈ T → t ∈ S ∧ Y t = x := by
    intro x
    by_cases hx : x ∈ T
    · obtain ⟨t, ht, rfl⟩ := hT1 hx
      exact ⟨t, fun _ => ⟨ht, rfl⟩⟩
    · exact ⟨1, fun h => absurd h hx⟩
  choose τ hτ using hch
  have hcov : S ⊆ ⋃ x ∈ T, (fun g => (τ x)⁻¹ * g) ⁻¹' W := by
    intro g hg
    obtain ⟨x, hx, hd⟩ := hT3 (Y g) ⟨g, hg, rfl⟩
    obtain ⟨h1, h2⟩ := hτ x hx
    simp only [Set.mem_iUnion]
    refine ⟨x, hx, ?_⟩
    show hs (uMat ((τ x)⁻¹ * g)) ≤ _
    refine (GlobalTheory.T.hilbertSchmidt_inUJ_le_of_sign_columns n ε s _ ((τ x)⁻¹ * g).2).trans ?_
    gcongr
    calc ∑ i, ∑ j ∈ univ.filter (fun j => ε j = s), ‖uMat ((τ x)⁻¹ * g) i j‖ ^ 2
        ≤ ∑ _i : Fin n, ∑ _j ∈ univ.filter (fun j => ε j = s), ((1 : ℝ) + n) ^ 2 := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j hj => ?_
          refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
          refine close_entry g (τ x) hR0 h1 j (fun k => ?_) i
          have hj' : ε j = s := (Finset.mem_filter.1 hj).2
          rw [← h2, dist_eq_norm] at hd
          exact ((norm_le_pi_norm ((Y g - Y (τ x)) k) ⟨j, hj'⟩).trans
            (norm_le_pi_norm (Y g - Y (τ x)) k)).trans hd
      _ ≤ ∑ _i : Fin n, ∑ _j : Fin n, ((1 : ℝ) + n) ^ 2 :=
          Finset.sum_le_sum fun i _ => Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) fun _ _ _ => by positivity
      _ = _ := by simp
  have hcard : (T.card : ℝ) ≤ 3 ^ (2 * n * q) * R ^ (4 * n * q) := by
    refine hT2.trans ?_
    rw [hfr, show 4 * n * q = 2 * (2 * n * q) by ring, pow_mul R, ← mul_pow]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    have : 2 * R / (1 / R) = 2 * R ^ 2 := by field_simp
    rw [this]; nlinarith
  calc muG ε S ≤ muG ε (⋃ x ∈ T, (fun g => (τ x)⁻¹ * g) ⁻¹' W) := measure_mono hcov
    _ ≤ ∑ x ∈ T, muG ε ((fun g => (τ x)⁻¹ * g) ⁻¹' W) := measure_biUnion_finset_le _ _
    _ = ∑ _x ∈ T, muG ε W := Finset.sum_congr rfl fun x _ => measure_preimage_mul _ _ _
    _ = ENNReal.ofReal ((T.card : ℝ) * (muG ε W).toReal) := by
        rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_toReal hW.ne, ENNReal.ofReal_natCast]
    _ ≤ _ := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc (T.card : ℝ) * (muG ε W).toReal
            ≤ 3 ^ (2 * n * q) * R ^ (4 * n * q) * (muG ε W).toReal := by gcongr
          _ = _ := by ring

lemma hs_le_of_dOp {n : ℕ} {g : Matrix (Fin n) (Fin n) ℂ} {r : ℝ} (h : dOp g ≤ r) :
    hs g ≤ ((n + 1) * Real.exp r) ^ 2 := by
  have h1 : ‖LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)‖ ≤ Real.exp r :=
    Real.le_exp_of_log_le h
  have h2 : ∀ i j, ‖g i j‖ ≤ Real.exp r := by
    intro i j
    have h3 := (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g)).le_opNorm
      (EuclideanSpace.single j (1 : ℂ))
    have h4 := PiLp.norm_apply_le ((LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g))
      (EuclideanSpace.single j (1 : ℂ))) i
    have h5 : (LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin g))
      (EuclideanSpace.single j (1 : ℂ)) i = g i j := by
      simp [Matrix.toLpLin_apply]
    rw [h5] at h4
    have h6 : ‖(EuclideanSpace.single j (1 : ℂ) : EuclideanSpace ℂ (Fin n))‖ = 1 := by simp
    rw [h6, mul_one] at h3
    exact h4.trans (h3.trans h1)
  have hp := Real.exp_pos r
  calc hs g ≤ ∑ _i : Fin n, ∑ _j : Fin n, Real.exp r ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
          pow_le_pow_left₀ (norm_nonneg _) (h2 i j) 2
    _ = (n * Real.exp r) ^ 2 := by simp; ring
    _ ≤ _ := by gcongr; linarith

theorem ballVol : ∀ (n : ℕ) (ε : Fin n → Bool), ∃ C : ℝ, (∀ R : ℝ, 1 ≤ R → muG ε {g | hsG g ≤ R ^ 2} ≤ ENNReal.ofReal (C * R ^ (4 * n * rkR ε))) ∧ ∀ r : ℝ, 0 ≤ r → muG ε {g | dOp (uMat g) ≤ r} ≤ ENNReal.ofReal (C * Real.exp (4 * n * rkR ε * r)) := by
  intro n ε
  obtain ⟨s, hs'⟩ : ∃ s : Bool, rkR ε = (univ.filter fun a => ε a = s).card := by
    unfold rkR
    rcases min_choice (univ.filter fun a => ε a = true).card
      (univ.filter fun a => ε a = false).card with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  obtain ⟨C, hC, h⟩ := vol_sign n ε s
  rw [← hs'] at h
  have hn : (1 : ℝ) ≤ n + 1 := by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
  have hn' : (1 : ℝ) ≤ (n + 1) ^ (4 * n * rkR ε) := one_le_pow₀ hn
  refine ⟨C * (n + 1) ^ (4 * n * rkR ε), fun R hR => (h R hR).trans ?_, fun r hr => ?_⟩
  · refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ R ^ (4 * n * rkR ε) := by positivity
    exact mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hC hn') this
  · have he : 1 ≤ Real.exp r := Real.one_le_exp hr
    have h1 := h ((n + 1) * Real.exp r) (one_le_mul_of_one_le_of_one_le hn he)
    refine (measure_mono fun g hg => ?_).trans (h1.trans (le_of_eq ?_))
    · exact hs_le_of_dOp hg
    · rw [mul_pow, ← Real.exp_nat_mul, ← mul_assoc]
      push_cast
      rfl

end GlobalTheory.BallVol
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HcTypeWIrreducibleAndSchurAverage
section
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Schur

theorem avg_sq {X V ι : Type} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (f : X → V) (hf : AEStronglyMeasurable f μ) (c : ℝ) (hn : ∀ᵐ x ∂μ, ‖f x‖ = c)
    (T : ι → V →L[ℂ] V) (hT : ∀ i a b, ⟪T i a, T i b⟫_ℂ = ⟪a, b⟫_ℂ)
    (m : ι → X → X) (hm : ∀ i, MeasurePreserving (m i) μ μ)
    (hfm : ∀ i, ∀ᵐ x ∂μ, f (m i x) = T i (f x))
    (hirr : ∀ S : Submodule ℂ V, (∀ i, ∀ v ∈ S, T i v ∈ S) → S = ⊥ ∨ S = ⊤) (w : V) :
    Integrable (fun x => ‖⟪w, f x⟫_ℂ‖ ^ 2) μ ∧
      ∫ x, ‖⟪w, f x⟫_ℂ‖ ^ 2 ∂μ = ‖w‖ ^ 2 * c ^ 2 / Module.finrank ℂ V := by
  have hci : ∀ s : V, Integrable (fun x => ‖⟪s, f x⟫_ℂ‖ ^ 2) μ := by
    intro s
    refine Integrable.of_bound (((aestronglyMeasurable_const (b := s)).inner hf).norm.pow 2)
      ((‖s‖ * c) ^ 2) ?_
    filter_upwards [hn] with x hx
    rw [norm_pow, norm_norm, ← hx]
    exact pow_le_pow_left₀ (norm_nonneg _) (norm_inner_le_norm _ _) 2
  refine ⟨hci w, ?_⟩
  rcases subsingleton_or_nontrivial V with hV | hV
  · rw [Subsingleton.elim w 0]; simp
  haveI : CompleteSpace V := FiniteDimensional.complete ℂ V
  let Fy : V → X → V := fun y x => ⟪f x, y⟫_ℂ • f x
  have hFm : ∀ y, AEStronglyMeasurable (Fy y) μ := fun y =>
    (hf.inner (aestronglyMeasurable_const (b := y))).smul hf
  have hFi : ∀ y, Integrable (Fy y) μ := by
    intro y
    refine Integrable.of_bound (hFm y) (c * ‖y‖ * c) ?_
    filter_upwards [hn] with x hx
    simp only [Fy]
    rw [norm_smul, ← hx]
    exact mul_le_mul_of_nonneg_right (norm_inner_le_norm _ _) (norm_nonneg _)
  let R : V →ₗ[ℂ] V :=
    { toFun := fun y => ∫ h, Fy y h ∂μ
      map_add' := by
        intro y z
        rw [← integral_add (hFi y) (hFi z)]
        congr 1; funext h; simp only [Fy, inner_add_right, add_smul]
      map_smul' := by
        intro c y
        rw [RingHom.id_apply, ← integral_smul]
        congr 1; funext h; simp only [Fy, inner_smul_right, mul_smul] }
  have hRdef : ∀ y, R y = ∫ h, Fy y h ∂μ := fun _ => rfl
  have hcomm : ∀ i y, R (T i y) = T i (R y) := by
    intro i y
    rw [hRdef, hRdef, ← (T i).integral_comp_comm (hFi y)]
    have h1 : ∫ h, Fy (T i y) h ∂μ = ∫ h, Fy (T i y) (m i h) ∂μ := by
      have := integral_map (μ := μ) (φ := m i) (hm i).measurable.aemeasurable (f := Fy (T i y))
        (by rw [(hm i).map_eq]; exact hFm _)
      rwa [(hm i).map_eq] at this
    rw [h1]
    refine integral_congr_ae ?_
    filter_upwards [hfm i] with x hx
    simp only [Fy, hx, map_smul, hT]
  obtain ⟨lam, hlam⟩ := Module.End.exists_eigenvalue R
  have hE : Module.End.eigenspace R lam = ⊤ :=
    (hirr _ (fun h x hx => by
      rw [Module.End.mem_eigenspace_iff] at hx ⊢
      rw [hcomm, hx, map_smul])).resolve_left hlam
  have hR : ∀ y, R y = lam • y := fun y =>
    Module.End.mem_eigenspace_iff.mp (hE ▸ Submodule.mem_top)
  have h4 : ∀ s : V, lam * ((‖s‖ ^ 2 : ℝ) : ℂ) = ((∫ h, ‖⟪s, f h⟫_ℂ‖ ^ 2 ∂μ : ℝ) : ℂ) := by
    intro s
    have a : ⟪s, R s⟫_ℂ = lam * ((‖s‖ ^ 2 : ℝ) : ℂ) := by
      rw [hR, inner_smul_right, inner_self_eq_norm_sq_to_K]; push_cast; rfl
    have b : ⟪s, R s⟫_ℂ = ∫ h, ⟪s, Fy s h⟫_ℂ ∂μ := (integral_inner (hFi s) s).symm
    have c : ∀ h, ⟪s, Fy s h⟫_ℂ = ((‖⟪s, f h⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro h
      simp only [Fy, inner_smul_right]
      rw [← inner_conj_symm (f h) s, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [← a, b]
    simp_rw [c]
    exact integral_ofReal
  have h5 : lam * (Module.finrank ℂ V : ℂ) = ((c ^ 2 : ℝ) : ℂ) := by
    let b := stdOrthonormalBasis ℂ V
    have e1 : ∫ h, ∑ i, ‖⟪b i, f h⟫_ℂ‖ ^ 2 ∂μ = c ^ 2 := by
      have : ∫ h, ∑ i, ‖⟪b i, f h⟫_ℂ‖ ^ 2 ∂μ = ∫ _h, c ^ 2 ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hn] with x hx
        rw [b.sum_sq_norm_inner_right, hx]
      rw [this]; simp
    rw [← e1, integral_finsetSum _ fun i _ => hci (b i)]
    push_cast
    simp_rw [← h4]
    have hb : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
    simp [hb, mul_comm]
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  apply Complex.ofReal_injective
  rw [← h4, Complex.ofReal_div, Complex.ofReal_mul, ← h5]
  push_cast
  field_simp

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]

theorem type_irred {z : Fin (2 * r + k + 1) → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)} (hT : 0 < Tz k r z)
    {u : Fin k → ℝ} (hπ : IsHCTypeW k r z u π) :
    Nontrivial Wp ∧ IsURepOn (UWset k r z) π ∧ IsIrredOn (UWset k r z) π := by
  have hπ' : PI.UpqRep.IsHCTypeW k r z u π := hπ
  obtain ⟨h1, h2, h3, h4⟩ := Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.piW_facts hT hπ'
  obtain ⟨g, hg, hρ⟩ := hπ
  refine ⟨hρ.1, ⟨⟨h1, h2⟩, h3, h4⟩, fun S _ hS => ?_⟩
  refine hρ.2.2.2.2.2.1 S le_top fun x hx v hv => hS _ ?_ v hv
  have hg' : PI.UpqRep.IsFrameW k r z g := hg
  have hx' : x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k) :=
    PI.HwUniqW.mem_UJset_allPos.mpr (Matrix.mem_unitaryGroup_iff'.mp hx.1)
  exact GlobalTheory.BesselFrame.conj_mem_UW hg' hx'

theorem avg_UW [FiniteDimensional ℂ Wp] {z : Fin (2 * r + k + 1) → ℂ} {π : Mat k r → (Wp →L[ℂ] Wp)}
    {μW : Measure (Mt k r)} (hU : IsURepOn (UWset k r z) π) (hI : IsIrredOn (UWset k r z) π)
    (hH : IsHaarOn (UWset k r z) μW) (h1 : μW Set.univ = 1) (w ξ : Wp) :
    ∫⁻ h, (‖⟪w, π (Matrix.of h) ξ⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW =
      ENNReal.ofReal (‖w‖ ^ 2 * ‖ξ‖ ^ 2 / Module.finrank ℂ Wp) := by
  haveI : IsProbabilityMeasure μW := ⟨h1⟩
  have hW := isClosedSub_UWset (k := k) (r := r) z
  have hae : ∀ᵐ x ∂μW, Matrix.of x ∈ UWset k r z := ae_iff.mpr hH.2.2.1
  have hof : Continuous (fun y : Mt k r => (Matrix.of y : Mat k r)) := continuous_id
  have hf : AEStronglyMeasurable (fun x : Mt k r => π (Matrix.of x) ξ) μW := by
    have hc : ContinuousOn (fun x : Mt k r => π (Matrix.of x) ξ) {x : Mt k r | Matrix.of x ∈ UWset k r z} :=
      hU.2.2 ξ
    have := hc.aestronglyMeasurable (μ := μW) (hW.2.1.preimage hof).measurableSet
    rwa [Measure.restrict_eq_self_of_ae_mem (s := {x : Mt k r | Matrix.of x ∈ UWset k r z}) hae] at this
  have hlm : ∀ s : Mat k r, Continuous (lmulM s : Mt k r → Mt k r) := fun s =>
    (continuous_const (y := s)).matrix_mul hof
  obtain ⟨hi, hv⟩ := avg_sq μW (fun x : Mt k r => π (Matrix.of x) ξ) hf ‖ξ‖
    (hae.mono fun x hx => hU.2.1 _ hx ξ) (fun s : UWset k r z => π s)
    (fun s => (LinearMap.norm_map_iff_inner_map_map ((π s : Wp →L[ℂ] Wp) : Wp →ₗ[ℂ] Wp)).1 (hU.2.1 s s.2))
    (fun s => lmulM (s : Mat k r))
    (fun s => ⟨(hlm s).measurable, hH.2.2.2 s s.2⟩)
    (fun s => hae.mono fun x hx => DFunLike.congr_fun (hU.1.2 s s.2 _ hx) ξ)
    (fun S hS => hI S S.closed_of_finiteDimensional fun g hg => hS ⟨g, hg⟩) w
  rw [← hv, ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun x => by positivity)]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  rfl

theorem type_irred_and_avg : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : (Fin (2 * r + k + 1) → ℂ)) (π : Mat k r → (Wp →L[ℂ] Wp)), inWb k r z → 0 < Tz k r z → (∀ u, IsHCTypeW k r z u π → Nontrivial Wp ∧ IsURepOn (UWset k r z) π ∧ IsIrredOn (UWset k r z) π) ∧ ∀ μW : Measure (Mt k r), IsURepOn (UWset k r z) π → IsIrredOn (UWset k r z) π → IsHaarOn (UWset k r z) μW → μW Set.univ = 1 → ∀ w ξ : Wp, ∫⁻ h, (‖⟪w, π (Matrix.of h) ξ⟫_ℂ‖₊ : ℝ≥0∞) ^ 2 ∂μW = ENNReal.ofReal (‖w‖ ^ 2 * ‖ξ‖ ^ 2 / Module.finrank ℂ Wp) :=
  fun _ _ _ _ _ _ _ _ _ hT => ⟨fun _ hπ => type_irred hT hπ, fun _ hU hI hH h1 w ξ => avg_UW hU hI hH h1 w ξ⟩

end GlobalTheory.Amp.Schur
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetKernelRowSumNearOneStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianDoubleCoset_kernel_row_sum_near_one : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ (j : Fin r) (β βJ : ℕ) (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → S.InFF β (j + 1) βJ d Λ → |(∑ᶠ y : {y // S.IsTerm d y ∧ S.InFF β (j + 1) βJ d y}, S.kern β (j + 1) βJ d Λ y) - 1| ≤ 24 / 7 * (S.q : ℝ) ^ (1 - ((k : ℤ) - 2 * r - 3)) := by
  first | exact @GlobalTheory.HL.kern_row_sum | exact GlobalTheory.HL.kern_row_sum | (intros; apply GlobalTheory.HL.kern_row_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesDefectOrderShareLeStatement
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitianFrames_defectOrder_share_le : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), 4 * r + 7 ≤ k → ∀ C, S.IsCls C → ∀ β : ℕ, 1 ≤ β → (S.sumData fun d => S.nT d C fun Λ => S.be d Λ = β) ≤ ENNReal.ofReal (4 * (S.q : ℝ) ^ (2 * S.a * (2 * r + 2)) * ((β : ℝ) ^ (k - 1))⁻¹) * S.sumData fun d => S.nT d C fun Λ => S.BBzero d Λ := by
  first | exact @GlobalTheory.HL.DefectShare.share_le | exact GlobalTheory.HL.DefectShare.share_le | (intros; apply GlobalTheory.HL.DefectShare.share_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianIdempotentEqIsometryMulConjTranspose
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

namespace GlobalTheory

theorem hermitian_idempotent_eq_isometry_mul_conjTranspose :
    ∀ (n : ℕ) (R : Matrix (Fin n) (Fin n) ℂ), Rᴴ = R → R * R = R →
      ∃ (r : ℕ) (P : Matrix (Fin n) (Fin r) ℂ), Pᴴ * P = 1 ∧ P * Pᴴ = R := by
  intro n R hH hI
  classical
  have hA : R.IsHermitian := hH
  have hev : ∀ i, hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 1 := by
    intro i
    have hv := hA.mulVec_eigenvectorBasis i
    have hne : (⇑(hA.eigenvectorBasis i) : Fin n → ℂ) ≠ 0 :=
      (WithLp.ofLp_eq_zero 2).ne.2 (hA.eigenvectorBasis.orthonormal.ne_zero i)
    have h2 : R *ᵥ (R *ᵥ ⇑(hA.eigenvectorBasis i)) = R *ᵥ ⇑(hA.eigenvectorBasis i) := by
      rw [mulVec_mulVec, hI]
    rw [hv, mulVec_smul, hv, smul_smul] at h2
    have h3 : (hA.eigenvalues i * hA.eigenvalues i - hA.eigenvalues i) •
        (⇑(hA.eigenvectorBasis i) : Fin n → ℂ) = 0 := by
      rw [sub_smul, h2, sub_self]
    rcases smul_eq_zero.mp h3 with h | h
    · have h4 : hA.eigenvalues i * (hA.eigenvalues i - 1) = 0 := by linear_combination h
      rcases mul_eq_zero.mp h4 with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by linarith)
    · exact absurd h hne
  set U : Matrix (Fin n) (Fin n) ℂ := (hA.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℂ) with hUdef
  have hU : Uᴴ * U = 1 := Unitary.coe_star_mul_self hA.eigenvectorUnitary
  let e : Fin (Fintype.card {i // hA.eigenvalues i ≠ 0}) ≃ {i // hA.eigenvalues i ≠ 0} :=
    (Fintype.equivFin _).symm
  let f : Fin (Fintype.card {i // hA.eigenvalues i ≠ 0}) → Fin n := fun j => (e j).1
  have hf : Function.Injective f := Subtype.val_injective.comp e.injective
  let Q : Matrix (Fin n) (Fin (Fintype.card {i // hA.eigenvalues i ≠ 0})) ℂ :=
    (1 : Matrix (Fin n) (Fin n) ℂ).submatrix id f
  have hQQ : Qᴴ * Q = 1 := by
    ext j k
    simp [Q, Matrix.mul_apply, Matrix.one_apply, hf.eq_iff]
  have hQ : Q * Qᴴ = diagonal (RCLike.ofReal ∘ hA.eigenvalues) := by
    ext i k
    rw [Matrix.mul_apply, diagonal_apply]
    simp only [Q, conjTranspose_apply, submatrix_apply, id, Matrix.one_apply, Function.comp_apply]
    by_cases h0 : hA.eigenvalues i = 0
    · have hz : ∀ j, (if i = f j then (1 : ℂ) else 0) = 0 := by
        intro j
        refine if_neg (fun h => (e j).2 ?_)
        rw [show (e j).1 = i from h.symm]
        exact h0
      simp only [hz, zero_mul, Finset.sum_const_zero, h0]
      split_ifs <;> simp
    · have h1 : hA.eigenvalues i = 1 := (hev i).resolve_left h0
      have hj0 : f (e.symm ⟨i, h0⟩) = i := by simp [f]
      rw [Finset.sum_eq_single (e.symm ⟨i, h0⟩)]
      · rw [hj0, if_pos rfl, one_mul, h1]
        by_cases hik : i = k
        · subst hik
          simp
        · rw [if_neg (Ne.symm hik), if_neg hik]
          simp
      · intro b _ hb
        have hne : i ≠ f b := by
          intro h
          apply hb
          rw [Equiv.eq_symm_apply]
          exact Subtype.ext h.symm
        rw [if_neg hne, zero_mul]
      · intro h
        exact absurd (Finset.mem_univ _) h
  refine ⟨Fintype.card {i // hA.eigenvalues i ≠ 0}, U * Q, ?_, ?_⟩
  · rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ, hU, Matrix.one_mul, hQQ]
  · have hs := hA.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at hs
    rw [conjTranspose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc Q, hQ]
    conv_rhs => rw [hs]
    simp [U, Matrix.mul_assoc, Matrix.star_eq_conjTranspose]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InitialLengthsProductMomentLe
section
open MeasureTheory Finset
open scoped ENNReal

namespace GlobalTheory.MomentHolder

theorem initial_product_moment_le :
    ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r l : ℕ) (hl : l ≤ r + 1)
      (len : Fin (r + 1) → Ω → ℝ) (Ph : Ω → ℝ) (A Rr : ℝ), (∀ a, AEMeasurable (len a) ν) →
      (∀ a, ∀ᵐ x ∂ν, 0 < len a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) →
      ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1 → 0 ≤ A → 1 ≤ Rr →
      (∀ q ≤ (r + 1) ^ 2, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q) * Ph x) ∂ν
        ≤ ENNReal.ofReal (A ^ q)) →
      (∀ a : Fin r, ∀ q ≤ (r + 1) ^ 2,
        ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q) * Ph x) ∂ν
          ≤ ENNReal.ofReal (Rr ^ (2 * q))) →
      ∫⁻ x, ENNReal.ofReal ((∏ a : Fin l, len (Fin.castLE hl a) x ^ 2) * Ph x) ∂ν
        ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ l) := by
  intro Ω _ ν r l hl len Ph A Rr hlen hpos hPh h0 hmass hA hR hm0 hrat
  rcases Nat.eq_zero_or_pos l with rfl | hl0
  · simp [hmass]
  obtain ⟨s, rfl⟩ : ∃ s, l = s + 1 := ⟨l - 1, by omega⟩
  have hs : s ≤ r := by omega
  have hq' : ∀ q, q ≤ (s + 1) ^ 2 → q ≤ (r + 1) ^ 2 :=
    fun q hq => hq.trans (Nat.pow_le_pow_left (by omega) 2)
  have h1 : ∀ q ≤ (s + 1) ^ 2,
      ∫⁻ x, ENNReal.ofReal ((fun a : Fin (s + 1) => len (Fin.castLE hl a)) 0 x ^ (2 * q) * Ph x) ∂ν
        ≤ ENNReal.ofReal (A ^ q) := by
    intro q hq
    have e : Fin.castLE hl (0 : Fin (s + 1)) = 0 := Fin.ext (by simp)
    simp only [e]
    exact hm0 q (hq' q hq)
  have h2 : ∀ a : Fin s, ∀ q ≤ (s + 1) ^ 2,
      ∫⁻ x, ENNReal.ofReal (((fun a : Fin (s + 1) => len (Fin.castLE hl a)) a.succ x /
        (fun a : Fin (s + 1) => len (Fin.castLE hl a)) a.castSucc x) ^ (2 * q) * Ph x) ∂ν
        ≤ ENNReal.ofReal (Rr ^ (2 * q)) := by
    intro a q hq
    have e1 : Fin.castLE hl a.succ = (⟨a, by omega⟩ : Fin r).succ := Fin.ext (by simp)
    have e2 : Fin.castLE hl a.castSucc = (⟨a, by omega⟩ : Fin r).castSucc := Fin.ext (by simp)
    simp only [e1, e2]
    exact hrat _ q (hq' q hq)
  have key := product_moment_le Ω ν s (fun a => len (Fin.castLE hl a)) Ph A Rr
    (fun _ => hlen _) (fun _ => hpos _) hPh h0 hmass hA hR h1 h2
  refine key.trans (ENNReal.ofReal_le_ofReal ?_)
  exact pow_le_pow_left₀ (mul_nonneg hA (pow_nonneg (zero_le_one.trans hR) _))
    (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR (by omega)) hA) _

end GlobalTheory.MomentHolder
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvUpperUnitriangularSuperdiagNegStatement
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inv_upperUnitriangular_superdiag_neg : ∀ (k : Type) [Field k] (n : ℕ) (A : Matrix (Fin n) (Fin n) k), (∀ x y : Fin n, y < x → A x y = 0) → (∀ x, A x x = 1) → (∀ x y : Fin n, y < x → A⁻¹ x y = 0) ∧ (∀ x, A⁻¹ x x = 1) ∧ ∀ x y : Fin n, x.1 + 1 = y.1 → A⁻¹ x y = - A x y := by
  first | exact @GlobalTheory.inv_upperUnitriangular | exact GlobalTheory.inv_upperUnitriangular | (intros; apply GlobalTheory.inv_upperUnitriangular <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCharacterOfFDRepCompHomAndMulStatement
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacterOfFDRep_comp_hom_and_mul : (∀ (G M : Type) [Group G] [Group M] (π : G →* M) (χ : M → ℂ), IsChar χ → IsChar (fun x => χ (π x))) ∧ ∀ (G : Type) [Group G] (α β : G → ℂ), IsChar α → IsChar β → IsChar (fun x => α x * β x) := by
  first | exact @GlobalTheory.GLm.isChar_comp_hom_and_mul | exact GlobalTheory.GLm.isChar_comp_hom_and_mul | (intros; apply GlobalTheory.GLm.isChar_comp_hom_and_mul <;> assumption)
end

