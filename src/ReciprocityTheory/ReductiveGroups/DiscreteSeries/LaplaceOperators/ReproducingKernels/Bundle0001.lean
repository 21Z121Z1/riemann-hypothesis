import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.ReproCoreStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.HermitianMeasures.OrbitIntegralAbsConvergent

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.IntSOfSIntFin
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.IntS

open Formalism.QuantumDeterminants

section frob

attribute [local instance] Matrix.frobeniusNormedAddCommGroup

theorem gN_eq_frob {k r : ℕ} (g : Mat k r) : Formalism.FourierDecayAlt.B.gN g = ‖g‖ := by
  rw [frobenius_norm_def, Formalism.FourierDecayAlt.B.gN, Real.sqrt_eq_rpow]
  congr 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.normSq_eq_norm_sq, Real.rpow_two]

theorem gN_mul_le' {k r : ℕ} (A B : Mat k r) :
    Formalism.FourierDecayAlt.B.gN (A * B) ≤ Formalism.FourierDecayAlt.B.gN A * Formalism.FourierDecayAlt.B.gN B := by
  rw [gN_eq_frob, gN_eq_frob, gN_eq_frob]
  exact frobenius_norm_mul A B

theorem gN_pos_of_ne {k r : ℕ} {g : Mat k r} (hg : g ≠ 0) : 0 < Formalism.FourierDecayAlt.B.gN g := by
  rw [gN_eq_frob]; exact norm_pos_iff.mpr hg

end frob

theorem gN_nonneg' {k r : ℕ} (g : Mat k r) : 0 ≤ Formalism.FourierDecayAlt.B.gN g := Real.sqrt_nonneg _

theorem gN_continuous (k r : ℕ) : Continuous (fun g : Mat k r => Formalism.FourierDecayAlt.B.gN g) :=
  Real.continuous_sqrt.comp (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
    Complex.continuous_normSq.comp ((continuous_apply j).comp (continuous_apply i)))

section hpk
variable (k r : ℕ)

theorem Hpk_out {i : Fin (2 * r + k + 1)} (h : i.val < r ∨ r + k < i.val) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = 2 * r + k - i.val then 1 else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mid {i : Fin (2 * r + k + 1)} (h : ¬(i.val < r ∨ r + k < i.val)) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if j.val = i.val then (if i.val = r + k then -1 else 1) else 0 := by
  rcases i with ⟨i, hi⟩; rcases j with ⟨j, hj⟩
  simp only [Hpk, Fin.mk.injEq] at h ⊢
  split_ifs <;> first | rfl | (exfalso; omega)

theorem Hpk_mulVec (v : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) i = if i.val < r ∨ r + k < i.val then v ⟨2 * r + k - i.val, by omega⟩
      else if i.val = r + k then -v i else v i := by
  simp only [mulVec, dotProduct]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1]
    simp only [Hpk_out k r h1]
    rw [Finset.sum_eq_single ⟨2 * r + k - i.val, by omega⟩]
    · simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp
  · rw [if_neg h1]
    simp only [Hpk_mid k r h1]
    rw [Finset.sum_eq_single i]
    · split_ifs <;> first | (exfalso; omega) | simp
    · intro b _ hb; rw [if_neg (fun h => hb (Fin.ext h))]; simp
    · simp

theorem Hpk_mulVec_mulVec (v : Fin (2 * r + k + 1) → ℂ) : Hpk k r *ᵥ (Hpk k r *ᵥ v) = v := by
  ext i
  rw [Hpk_mulVec]
  by_cases h1 : i.val < r ∨ r + k < i.val
  · rw [if_pos h1, Hpk_mulVec]
    have e1 : ((⟨2 * r + k - i.val, by omega⟩ : Fin (2 * r + k + 1)).val) = 2 * r + k - i.val := rfl
    rw [if_pos (by rw [e1]; omega)]
    congr 1; ext; simp; omega
  · rw [if_neg h1, Hpk_mulVec, if_neg h1]
    split_ifs <;> simp

theorem mat_eq_of_mulVec' {A B : Mat k r} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  simpa [Matrix.mulVec_single_one] using congrFun (h (Pi.single j 1)) i

theorem Hpk_sq : Hpk k r * Hpk k r = 1 :=
  mat_eq_of_mulVec' k r fun v => by rw [← Matrix.mulVec_mulVec, Hpk_mulVec_mulVec, Matrix.one_mulVec]

variable {k r}

theorem UH_left_inv {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : Hpk k r * gᴴ * Hpk k r * g = 1 := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  calc Hpk k r * gᴴ * Hpk k r * g = Hpk k r * (gᴴ * Hpk k r * g) := by simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hg', Hpk_sq]

theorem UH_mul_inv {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g * g⁻¹ = 1 := by
  have h1 : g⁻¹ = Hpk k r * gᴴ * Hpk k r := Matrix.inv_eq_left_inv (UH_left_inv hg)
  exact mul_eq_one_comm.mp (by rw [h1, UH_left_inv hg])

theorem UH_mul {g x : Mat k r} (hg : g ∈ UH (Hpk k r)) (hx : x ∈ UH (Hpk k r)) :
    g * x ∈ UH (Hpk k r) := by
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hx' : xᴴ * Hpk k r * x = Hpk k r := hx
  show (g * x)ᴴ * Hpk k r * (g * x) = Hpk k r
  rw [conjTranspose_mul]
  calc xᴴ * gᴴ * Hpk k r * (g * x) = xᴴ * (gᴴ * Hpk k r * g) * x := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [hg', hx']

theorem ne_zero_of_mem_UH {g : Mat k r} (hg : g ∈ UH (Hpk k r)) : g ≠ 0 := by
  intro h
  have := UH_mul_inv hg
  rw [h, Matrix.zero_mul] at this
  exact zero_ne_one this

end hpk

theorem orbit_bound (k r : ℕ) (x₀ s x : Mat k r) (hx₀ : x₀ ∈ UH (Hpk k r)) (hs : s ∈ UH (Hpk k r))
    (hx : x ∈ UH (Hpk k r)) (b : ℝ) (hb : 0 ≤ b) :
    Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (s * x)) ^ (-b) ≤
      (Formalism.FourierDecayAlt.B.gN x₀ * Formalism.FourierDecayAlt.B.gN x⁻¹) ^ b * Formalism.FourierDecayAlt.B.gN s ^ (-b) := by
  set y := x₀⁻¹ * (s * x) with hy
  have hsy : x₀ * y * x⁻¹ = s := by
    rw [hy, ← Matrix.mul_assoc x₀, UH_mul_inv hx₀, Matrix.one_mul, Matrix.mul_assoc, UH_mul_inv hx,
      Matrix.mul_one]
  have hs0 : 0 < Formalism.FourierDecayAlt.B.gN s := gN_pos_of_ne (ne_zero_of_mem_UH hs)
  have hyne : y ≠ 0 := by
    intro h
    rw [h, Matrix.mul_zero, Matrix.zero_mul] at hsy
    exact ne_zero_of_mem_UH hs hsy.symm
  have hy0 : 0 < Formalism.FourierDecayAlt.B.gN y := gN_pos_of_ne hyne
  set A := Formalism.FourierDecayAlt.B.gN x₀ * Formalism.FourierDecayAlt.B.gN x⁻¹ with hA
  have hle : Formalism.FourierDecayAlt.B.gN s ≤ A * Formalism.FourierDecayAlt.B.gN y := by
    rw [← hsy]
    calc Formalism.FourierDecayAlt.B.gN (x₀ * y * x⁻¹) ≤ Formalism.FourierDecayAlt.B.gN (x₀ * y) * Formalism.FourierDecayAlt.B.gN x⁻¹ := gN_mul_le' _ _
      _ ≤ Formalism.FourierDecayAlt.B.gN x₀ * Formalism.FourierDecayAlt.B.gN y * Formalism.FourierDecayAlt.B.gN x⁻¹ :=
          mul_le_mul_of_nonneg_right (gN_mul_le' _ _) (gN_nonneg' _)
      _ = A * Formalism.FourierDecayAlt.B.gN y := by rw [hA]; ring
  have hA0 : 0 < A := by
    by_contra hc
    rw [not_lt] at hc
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hc hy0.le]
  have hpow : Formalism.FourierDecayAlt.B.gN s ^ b ≤ A ^ b * Formalism.FourierDecayAlt.B.gN y ^ b := by
    rw [← Real.mul_rpow hA0.le hy0.le]
    exact Real.rpow_le_rpow hs0.le hle hb
  have hSb : 0 < Formalism.FourierDecayAlt.B.gN s ^ b := Real.rpow_pos_of_pos hs0 b
  have hYb : 0 < Formalism.FourierDecayAlt.B.gN y ^ b := Real.rpow_pos_of_pos hy0 b
  rw [Real.rpow_neg hy0.le, Real.rpow_neg hs0.le, ← div_eq_mul_inv, le_div_iff₀ hSb,
    inv_mul_le_iff₀ hYb]
  linarith [mul_comm (A ^ b) (Formalism.FourierDecayAlt.B.gN y ^ b)]

theorem bS_nonneg (k r : ℕ) : 0 ≤ bS k r := by
  unfold bS nS; positivity

theorem bS_le_bS (k r : ℕ) : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bS k r ≤ bS k r :=
  le_of_le_of_eq (ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bS_le k r) (by unfold bS nS ReciprocityTheory.ChartRestriction.DS.Mult1.nR; rfl)

theorem intS_of_sIntFin (h : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.SIntFin) : IntSStatement := by
  intro k r z μW μN hz hT hW hN x₀ hx₀ x hx b hb
  have hb0 : 0 ≤ b := le_trans (bS_nonneg k r) hb.le
  have hb1 : ReciprocityTheory.ChartRestriction.DS.Mult1.S0.bS k r < b := lt_of_le_of_lt (bS_le_bS k r) hb
  have hfin := (h k r z μW μN hz hT hW hN b hb1).1
  have : SigmaFinite μW := hW.1
  have : SigmaFinite μN := hN.1
  have hcont : Continuous (fun p : Mt k r × Mt k r =>
      Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x))) :=
    (gN_continuous k r).comp (continuous_const.matrix_mul
      ((continuous_fst.matrix_mul continuous_snd).matrix_mul continuous_const))
  have hmeas : Measurable (fun p : Mt k r × Mt k r =>
      Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) ^ (-b)) :=
    hcont.measurable.pow_const _
  have h1 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 ∈ UWset k r z := by
    rw [ae_iff]
    have e : {p : Mt k r × Mt k r | ¬ Matrix.of p.1 ∈ UWset k r z} =
        {y : Mt k r | Matrix.of y ∉ UWset k r z} ×ˢ (Set.univ : Set (Mt k r)) := by
      ext p; simp
    rw [e, Measure.prod_prod, hW.2.2.1, zero_mul]
  have h2 : ∀ᵐ p ∂(μW.prod μN), Matrix.of p.2 ∈ Nset k r := by
    rw [ae_iff]
    have e : {p : Mt k r × Mt k r | ¬ Matrix.of p.2 ∈ Nset k r} =
        (Set.univ : Set (Mt k r)) ×ˢ {y : Mt k r | Matrix.of y ∉ Nset k r} := by
      ext p; simp
    rw [e, Measure.prod_prod, hN.2.2.1, mul_zero]
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun p => Real.rpow_nonneg (gN_nonneg' _) _)]
  calc ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (x₀⁻¹ * (Matrix.of p.1 * Matrix.of p.2 * x)) ^ (-b)) ∂(μW.prod μN)
      ≤ ∫⁻ p, ENNReal.ofReal ((Formalism.FourierDecayAlt.B.gN x₀ * Formalism.FourierDecayAlt.B.gN x⁻¹) ^ b) *
          ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b)) ∂(μW.prod μN) := by
        refine lintegral_mono_ae ((h1.and h2).mono fun p hp => ?_)
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (mul_nonneg (gN_nonneg' _) (gN_nonneg' _)) _)]
        exact ENNReal.ofReal_le_ofReal
          (orbit_bound k r x₀ _ x hx₀ (UH_mul hp.1.1 hp.2.1) hx b hb0)
    _ = ENNReal.ofReal ((Formalism.FourierDecayAlt.B.gN x₀ * Formalism.FourierDecayAlt.B.gN x⁻¹) ^ b) *
          ∫⁻ p, ENNReal.ofReal (Formalism.FourierDecayAlt.B.gN (Matrix.of p.1 * Matrix.of p.2) ^ (-b)) ∂(μW.prod μN) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.IntS
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.IntegralNormSqCoef
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.Fdeg

open Formalism.QuantumDeterminants

theorem integral_normSq_coef (k r : ℕ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (w : H) (d : ℝ) (μG : Measure (Mt k r)) (hw : ‖w‖ = 1)
    (hF : IsFdegB μG σ d) :
    ∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG = 1 / d := by
  obtain ⟨_, hS⟩ := hF
  have h1 := (hS w w w w).2
  have hww : ⟪w, w⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hw]; simp
  rw [hww] at h1
  have hfun : (fun g : Mt k r => ⟪w, σ (Matrix.of g) w⟫_ℂ * star ⟪w, σ (Matrix.of g) w⟫_ℂ) =
      fun g => ((‖⟪w, σ (Matrix.of g) w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    funext g
    rw [Complex.star_def, RCLike.mul_conj]
    push_cast; rfl
  rw [hfun, integral_complex_ofReal] at h1
  have h2 : ((∫ x, ‖⟪w, σ (Matrix.of x) w⟫_ℂ‖ ^ 2 ∂μG : ℝ) : ℂ) = ((1 / d : ℝ) : ℂ) := by
    rw [h1]; push_cast; ring
  exact_mod_cast h2

theorem fdegH_eq : FdegHEqStatement := by
  intro k r H _ _ σ w d μG hw hF
  unfold Formalism.MainNotions.S.fdegH
  rw [integral_normSq_coef k r H σ w d μG hw hF, hw]
  have hd : d ≠ 0 := ne_of_gt hF.1
  field_simp

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.Fdeg
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.ReproducingKernels.MeasurableIndicatorNormSq
section
noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

namespace ReciprocityTheory.ChartRestriction.DS.Lap.S0.Fwd

open Formalism.QuantumDeterminants

theorem norm_psiGen (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (m : Mat k r) :
    ‖Formalism.MainNotions.S.psiGen k r z c m‖ = 1 := by
  unfold Formalism.MainNotions.S.psiGen
  rw [mul_comm]
  exact Complex.norm_exp_ofReal_mul_I _

theorem UH_mul_iff {n : ℕ} (H s x : Matrix (Fin n) (Fin n) ℂ) (hs : s ∈ UH H) :
    s * x ∈ UH H ↔ x ∈ UH H := by
  have hs' : sᴴ * H * s = H := hs
  have key : (s * x)ᴴ * H * (s * x) = xᴴ * H * x := by
    rw [conjTranspose_mul]
    calc xᴴ * sᴴ * H * (s * x) = xᴴ * (sᴴ * H * s) * x := by simp only [Matrix.mul_assoc]
      _ = xᴴ * H * x := by rw [hs']
  show (s * x)ᴴ * H * (s * x) = H ↔ xᴴ * H * x = H
  rw [key]

theorem Sset_mul_mem_iff (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (s x : Mat k r)
    (hs : s ∈ Sset k r z) : s * x ∈ UH (Hpk k r) ↔ x ∈ UH (Hpk k r) := by
  obtain ⟨h, hh, m, hm, rfl⟩ := hs
  have hsU : h * m ∈ UH (Hpk k r) := (UH_mul_iff _ h m hh.1).2 hm.1
  exact UH_mul_iff _ _ x hsU

theorem isClosed_setUH (k r : ℕ) : IsClosed {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := by
  have hc : Continuous (fun y : Mt k r => (Matrix.of y)ᴴ * Hpk k r * Matrix.of y) := by
    have h1 : Continuous (fun y : Mt k r => (Matrix.of y : Mat k r)) := continuous_id
    exact ((h1.matrix_conjTranspose).matrix_mul continuous_const).matrix_mul h1
  exact isClosed_eq hc continuous_const

theorem measurable_indicator_normSq (k r : ℕ) (Vp : Type) [NormedAddCommGroup Vp]
    (W : Mat k r → Vp)
    (hW : ContinuousOn (fun y : Mt k r => W (Matrix.of y)) {y | Matrix.of y ∈ UH (Hpk k r)}) :
    Measurable (Set.indicator {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)}
      (fun y => (‖W (Matrix.of y)‖₊ : ℝ≥0∞) ^ 2)) := by
  classical
  have hC := isClosed_setUH k r
  have hf : ContinuousOn (fun y : Mt k r => (‖W (Matrix.of y)‖₊ : ℝ≥0∞) ^ 2)
      {y | Matrix.of y ∈ UH (Hpk k r)} :=
    (ENNReal.continuous_pow 2).comp_continuousOn
      ((ENNReal.continuous_coe.comp continuous_nnnorm).comp_continuousOn hW)
  have := hf.measurable_piecewise (continuousOn_const (c := (0 : ℝ≥0∞))) hC.measurableSet
  rw [← Set.piecewise_eq_indicator]
  exact this

theorem lintegral_pos (k r : ℕ) (Vp : Type) [NormedAddCommGroup Vp] (μG : Measure (Mt k r))
    (W : Mat k r → Vp) (hG : Formalism.MainNotions.S.IsHaarOn (UH (Hpk k r)) μG)
    (hopen : ∀ U : Set (Mt k r), IsOpen U → (∃ y ∈ U, Matrix.of y ∈ UH (Hpk k r)) → 0 < μG U)
    (hW : ContinuousOn (fun y : Mt k r => W (Matrix.of y)) {y | Matrix.of y ∈ UH (Hpk k r)})
    (hne : ∃ y ∈ UH (Hpk k r), W y ≠ 0) :
    0 < ∫⁻ y, Set.indicator {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)}
      (fun y => (‖W (Matrix.of y)‖₊ : ℝ≥0∞) ^ 2) y ∂μG := by
  obtain ⟨y0, hy0, hWy0⟩ := hne
  rw [lintegral_pos_iff_support (measurable_indicator_normSq k r Vp W hW)]
  have hy0' : (y0 : Mt k r) ∈ {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := hy0
  have hnh : (fun y : Mt k r => W (Matrix.of y)) ⁻¹' {v | v ≠ 0} ∈
      nhdsWithin (y0 : Mt k r) {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} :=
    (hW _ hy0').preimage_mem_nhdsWithin (isOpen_ne.mem_nhds hWy0)
  obtain ⟨U, hUo, hyU, hUsub⟩ := mem_nhdsWithin.1 hnh
  have hpos : 0 < μG U := hopen U hUo ⟨y0, hyU, hy0⟩
  refine lt_of_lt_of_le hpos (measure_mono_ae ?_)
  have hae : ∀ᵐ y ∂μG, Matrix.of y ∈ UH (Hpk k r) := by
    rw [ae_iff]; simpa using hG.2.2.1
  filter_upwards [hae] with y hy hyU'
  have hyW : W (Matrix.of y) ≠ 0 := hUsub ⟨hyU', hy⟩
  show Set.indicator _ _ y ≠ 0
  rw [Set.indicator_of_mem (show y ∈ {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} from hy)]
  simpa using hyW

theorem nonzero : NonzeroStatement := by
  intro k r z c Vp _ _ π μG μS ν W hπ hG hS hQ hopen hW hEq hne h0
  set g : Mt k r → ℝ≥0∞ := Set.indicator {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)}
      (fun y => (‖W (Matrix.of y)‖₊ : ℝ≥0∞) ^ 2) with hgdef
  have hgm : Measurable g := measurable_indicator_normSq k r Vp W hW
  have hpos : 0 < ∫⁻ y, g y ∂μG := lintegral_pos k r Vp μG W hG hopen hW hne
  have hQg := hQ g hgm
  have hSae : ∀ᵐ s ∂μS, Matrix.of s ∈ Sset k r z := by
    rw [ae_iff]; simpa using hS.2.2.1
  have hin : ∀ x : Mt k r,
      ∫⁻ s, g (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS ≤ ∫⁻ _s, g x ∂μS := by
    intro x
    refine lintegral_mono_ae ?_
    filter_upwards [hSae] with s hs
    by_cases hx : Matrix.of x ∈ UH (Hpk k r)
    · have hsx : Matrix.of s * Matrix.of x ∈ UH (Hpk k r) :=
        (Sset_mul_mem_iff k r z _ _ hs).2 hx
      obtain ⟨h, hh, m, hm, hsd⟩ := hs
      have hm1 : (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r) ∈
          {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := hsx
      have hm2 : x ∈ {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := hx
      rw [hgdef, Set.indicator_of_mem hm1, Set.indicator_of_mem hm2]
      have heq : W (Matrix.of (fun i j => (Matrix.of s * Matrix.of x) i j)) =
          Formalism.MainNotions.S.psiGen k r z c m • π h (W (Matrix.of x)) := by
        show W (Matrix.of s * Matrix.of x) = _
        rw [hsd]
        exact hEq h hh m hm _ hx
      have hn : ‖Formalism.MainNotions.S.psiGen k r z c m • π h (W (Matrix.of x))‖₊ = ‖W (Matrix.of x)‖₊ :=
        NNReal.eq (by rw [coe_nnnorm, coe_nnnorm, norm_smul, norm_psiGen, one_mul, hπ h hh])
      rw [heq, hn]
    · have hm2 : x ∉ {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := hx
      have hsx : Matrix.of s * Matrix.of x ∉ UH (Hpk k r) :=
        fun hh => hx ((Sset_mul_mem_iff k r z _ _ hs).1 hh)
      have hm1 : (fun i j => (Matrix.of s * Matrix.of x) i j : Mt k r) ∉
          {y : Mt k r | Matrix.of y ∈ UH (Hpk k r)} := hsx
      rw [hgdef, Set.indicator_of_notMem hm1]
      exact zero_le
  have hle : ∫⁻ y, g y ∂μG ≤ 0 := by
    rw [hQg]
    calc ∫⁻ x, (∫⁻ s, g (fun i j => (Matrix.of s * Matrix.of x) i j) ∂μS) ∂ν
        ≤ ∫⁻ x, g x * μS Set.univ ∂ν := by
          refine lintegral_mono fun x => ?_
          refine (hin x).trans ?_
          rw [lintegral_const]
      _ = (∫⁻ x, g x ∂ν) * μS Set.univ := lintegral_mul_const _ hgm
      _ ≤ (∫⁻ x, (‖W (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν) * μS Set.univ := by
          gcongr with x
          exact Set.indicator_le_self _ _ x
      _ = 0 := by
          have : Formalism.MainNotions.S.l2SG ν W = ∫⁻ x, (‖W (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂ν := rfl
          rw [← this, h0, zero_mul]
  exact absurd (lt_of_lt_of_le hpos hle) (lt_irrefl 0)

end ReciprocityTheory.ChartRestriction.DS.Lap.S0.Fwd
end
end

