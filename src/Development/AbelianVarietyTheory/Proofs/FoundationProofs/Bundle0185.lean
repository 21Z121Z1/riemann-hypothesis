import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0178
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0166
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeLetterPreservesBasisSet
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0177
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0165
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0009
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0006
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0176
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0111
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0115
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0145
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0180

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharacterSlashSumInvariantOfStable
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

theorem GlobalTheory.EisM.hsum_inv_of_stable : ∀ (k L L' N : ℕ) (ε : DirichletCharacter ℂ N) (Δ : Set M2) (ι : Type) [Fintype ι] (β : ι → M2) (f : ℍ → ℂ), 1 ≤ k → N ∣ L → N ∣ L' → (∀ δ ∈ Δ, 0 < δ.det ∧ (N : ℤ) ∣ δ 1 0) → (∀ δ ∈ Δ, ∀ γ : SL(2, ℤ), (L' : ℤ) ∣ γ 1 0 → δ * (γ : M2) ∈ Δ) → LRep L Δ β → Inv k L (ch ε) f → Inv k L' (ch ε) (hsum k (ch ε) β f) := by
  intro k L L' N ε Δ ι _ β f hk hNL hNL' hΔ hΔγ hβ hf
  have hcoc := (GlobalTheory.T.slashIntMatrixPosDet_properties k f hk).1
  rw [(GlobalTheory.T.slashIntMatrixPosDet_properties k (hsum k (ch ε) β f) hk).2.2.1 L' (ch ε)]
  intro γ hγ
  have hNγ : (N : ℤ) ∣ γ 1 0 := (Int.natCast_dvd_natCast.mpr hNL').trans hγ
  have hβmem : ∀ i, β i ∈ Δ := fun i => by
    have := hβ.mapsTo (Set.mem_univ ((1 : Gamma0 L), i))
    simpa using this
  have hγγ : (γ : M2) * ((γ⁻¹ : SL(2,ℤ)) : M2) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hγγ' : ((γ⁻¹ : SL(2,ℤ)) : M2) * (γ : M2) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have hγinv : (L' : ℤ) ∣ (γ⁻¹ : SL(2,ℤ)) 1 0 := by
    rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
    simpa using hγ.neg_right
  set β' : ι → M2 := fun i => β i * (γ : M2) with hβ'
  have hβ'rep : LRep L Δ β' := by
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨g, i⟩ -
      have := hβ.mapsTo (Set.mem_univ (g, i))
      simp only [β', ← mul_assoc]
      exact hΔγ _ this γ hγ
    · rintro ⟨g, i⟩ - ⟨g', j⟩ - h
      have h' := congrArg (· * ((γ⁻¹ : SL(2,ℤ)) : M2)) h
      simp only [β', mul_assoc, hγγ, mul_one] at h'
      exact hβ.injOn (Set.mem_univ _) (Set.mem_univ _) h'
    · intro δ hδ
      have h1 := hΔγ δ hδ γ⁻¹ hγinv
      obtain ⟨⟨g, i⟩, -, hgi⟩ := hβ.surjOn h1
      refine ⟨(g, i), Set.mem_univ _, ?_⟩
      simp only at hgi ⊢
      rw [← mul_assoc, hgi, mul_assoc, hγγ', mul_one]
  have hsumeq := GlobalTheory.T.heckeCharacterSlashSum_indep_reps k L N ε Δ ι ι β β' f hk hNL hΔ hβ hβ'rep hf
  have hdetγ : (0 : ℤ) < (γ : M2).det := by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num
  have hch : ∀ i, ch ε (β' i 0 0) = ch ε (β i 0 0) * ch ε (γ 0 0) := by
    intro i
    have hz : ((γ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNγ
    simp only [ch, β', Matrix.mul_apply, Fin.sum_univ_two]
    push_cast
    rw [hz, mul_zero, add_zero, map_mul]
  have hγd : ch ε (γ 0 0) * ch ε (γ 1 1) = 1 := by
    have hd := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at hd
    have hz : ((γ 1 0 : ℤ) : ZMod N) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr hNγ
    have h2 : ((γ 0 0 : ℤ) : ZMod N) * ((γ 1 1 : ℤ) : ZMod N) = 1 := by
      have := congrArg (fun x : ℤ => (x : ZMod N)) hd
      push_cast at this
      rw [hz, mul_zero, sub_zero] at this
      exact this
    simp only [ch]
    rw [← map_mul, h2, map_one]
  funext τ
  have hlin : slz k (γ : M2) (hsum k (ch ε) β f) τ = ∑ i, ch ε (β i 0 0) * slz k (γ : M2) (slz k (β i) f) τ := by
    simp only [slz, hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [hlin, hsumeq]
  simp only [hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← hcoc (β i) γ (hΔ _ (hβmem i)).1 hdetγ, hch i]
  calc ch ε (β i 0 0) * slz k (β i * ↑γ) f τ
      = ch ε (β i 0 0) * (ch ε (γ 0 0) * ch ε (γ 1 1)) * slz k (β i * ↑γ) f τ := by rw [hγd, mul_one]
    _ = _ := by simp only [β']; ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeStableCongruenceConjDiamondMatrix
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory.KZ.StabHecke

theorem congruenceCondition_conj_diamond : ∀ (N l d : ℕ) (σ : SL(2, ℤ)) (r : Matrix (Fin 2) (Fin 2) ℤ), IsDiam N l d σ → PP N l r →
    PP N l ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := by
  intro N l d σ r hσ hr
  obtain ⟨h1, h2, -, h4⟩ := diam_facts hσ
  obtain ⟨r1, r2, r3, r4⟩ := hr
  have e00 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 0 0 =
      r 0 0 + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    linear_combination (r 0 0) * h4
  have e10 : ((σ : Matrix (Fin 2) (Fin 2) ℤ) * r * ((σ⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 =
      σ 1 0 * (σ 1 1 * r 0 0 - σ 1 0 * r 0 1 - σ 1 1 * r 1 1) + σ 1 1 * σ 1 1 * r 1 0 := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
    ring
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [e00, show r 0 0 + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 - 1 =
        (r 0 0 - 1) + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 by ring]
    exact dvd_add (dvd_add r1 (dvd_mul_of_dvd_left h1 _)) (dvd_mul_of_dvd_right r2 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left h1 _) (dvd_mul_of_dvd_right r2 _)
  · rw [e10]; exact dvd_add (dvd_mul_of_dvd_left h2 _) (dvd_mul_of_dvd_right r3 _)
  · rw [e00]
    obtain ⟨s, hs⟩ := h2
    obtain ⟨t, ht⟩ := r3
    have e : r 0 0 + σ 1 0 * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * r 1 0 =
        r 0 0 + (l : ℤ) * (s * (σ 0 1 * r 0 0 - σ 0 0 * r 0 1 - σ 0 1 * r 1 1) + σ 0 1 * σ 1 1 * t) := by
      rw [hs, ht]; ring
    rw [e]
    exact r4.add_mul_left_left _

end GlobalTheory.KZ.StabHecke
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HermiteRightFactorOfPrimeDvdDet
section
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.StabHecke

namespace GlobalTheory

theorem hermite_right_factor_prime_det : ∀ (p : ℕ), p.Prime → ∀ (m : Matrix (Fin 2) (Fin 2) ℤ), (p : ℤ) ∣ m.det → (∃ y : Matrix (Fin 2) (Fin 2) ℤ, m = y * !![(p : ℤ), 0; 0, 1]) ∨ ∃ k : ℕ, k < p ∧ ∃ y : Matrix (Fin 2) (Fin 2) ℤ, m = y * !![1, (k : ℤ); 0, (p : ℤ)] := by
  intro p hp m hdet
  haveI := Fact.mk hp
  obtain ⟨a, b, c, d, rfl⟩ : ∃ a b c d : ℤ, m = !![a, b; c, d] :=
    ⟨m 0 0, m 0 1, m 1 0, m 1 1, by ext i j; fin_cases i <;> fin_cases j <;> rfl⟩
  rw [Matrix.det_fin_two_of] at hdet
  have hdetZ : (a : ZMod p) * d = b * c := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd (a * d - b * c) p).2 hdet
    push_cast at this
    linear_combination this
  have fin : ∀ k : ℕ, k < p → (k : ZMod p) * a = b → (k : ZMod p) * c = d →
      ∃ k : ℕ, k < p ∧ ∃ y : Matrix (Fin 2) (Fin 2) ℤ, !![a, b; c, d] = y * !![1, (k : ℤ); 0, (p : ℤ)] := by
    intro k hk h1 h2
    obtain ⟨u, hu⟩ : (p : ℤ) ∣ b - k * a := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h1]; ring
    obtain ⟨v, hv⟩ : (p : ℤ) ∣ d - k * c := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; push_cast; rw [h2]; ring
    refine ⟨k, hk, !![a, u; c, v], ?_⟩
    rw [Matrix.mul_fin_two]
    ext i j; fin_cases i <;> fin_cases j <;> simp <;> linarith
  by_cases ha : (a : ZMod p) = 0
  · by_cases hc : (c : ZMod p) = 0
    · left
      obtain ⟨a', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd a p).1 ha
      obtain ⟨c', rfl⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd c p).1 hc
      refine ⟨!![a', b; c', d], ?_⟩
      rw [Matrix.mul_fin_two]
      ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring
    · right
      refine fin ((d : ZMod p) * (c : ZMod p)⁻¹).val (ZMod.val_lt _) ?_ ?_
      · rw [ZMod.natCast_zmod_val]
        calc (d : ZMod p) * (c : ZMod p)⁻¹ * a = (a * d) * (c : ZMod p)⁻¹ := by ring
          _ = b * c * (c : ZMod p)⁻¹ := by rw [hdetZ]
          _ = b := by rw [mul_assoc, mul_inv_cancel₀ hc, mul_one]
      · rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hc, mul_one]
  · right
    refine fin ((b : ZMod p) * (a : ZMod p)⁻¹).val (ZMod.val_lt _) ?_ ?_
    · rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ ha, mul_one]
    · rw [ZMod.natCast_zmod_val]
      calc (b : ZMod p) * (a : ZMod p)⁻¹ * c = (b * c) * (a : ZMod p)⁻¹ := by ring
        _ = (a * d) * (a : ZMod p)⁻¹ := by rw [hdetZ]
        _ = d := by rw [mul_comm (a : ZMod p) d, mul_assoc, mul_inv_cancel₀ ha, mul_one]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnImRpowMulExpUnitStripOneLe
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem im_ofComplex_xy (x y : ℝ) (hy : 0 < y) :
    (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I)).im = y := by
  have h : 0 < ((x : ℂ) + (y : ℂ) * Complex.I).im := by simpa using hy
  rw [ofComplex_apply_of_im_pos h]
  change ((x : ℂ) + (y : ℂ) * Complex.I).im = y
  simp

theorem integrableOn_rpow_sub_two_mul_exp_Ioi_one (r c : ℝ) (hc : 0 < c) :
    IntegrableOn (fun y : ℝ => y ^ (r - 2) * Real.exp (-c * y)) (Set.Ioi 1) := by
  have hI : IntegrableOn (fun y : ℝ => y ^ (max (r - 2) 0) * Real.exp (-c * y ^ (1 : ℝ)))
      (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by have := le_max_right (r - 2) 0; linarith)
      one_pos hc
  have hI' := hI.mono_set (Set.Ioi_subset_Ioi zero_le_one)
  refine Integrable.mono' hI' ?_ ?_
  · exact (Measurable.aestronglyMeasurable (by fun_prop))
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun y hy => ?_)
    have hy1 : (1 : ℝ) ≤ y := le_of_lt hy
    have hy0 : 0 < y := lt_of_lt_of_le one_pos hy1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg hy0.le _)
      (Real.exp_pos _).le), Real.rpow_one]
    exact mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow_of_exponent_le hy1 (le_max_left _ _)) (Real.exp_pos _).le

theorem integrableOn_im_rpow_mul_exp_strip_one_le :
    ∀ (r c : ℝ), 0 < c → IntegrableOn (fun τ : ℍ => τ.im ^ r * Real.exp (-c * τ.im))
      {τ | τ ∈ strip ∧ 1 ≤ τ.im} := by
  intro r c hc
  have hmim : Measurable (fun τ : ℍ => τ.im) := UpperHalfPlane.continuous_im.measurable
  have hmeas : Measurable (fun τ : ℍ => τ.im ^ r * Real.exp (-c * τ.im)) :=
    (hmim.pow_const r).mul (Real.measurable_exp.comp (measurable_const.mul hmim))
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  have hmT : MeasurableSet {τ : ℍ | 1 ≤ τ.im} := measurableSet_le measurable_const hmim
  have hS : {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im} = {τ : ℍ | 1 ≤ τ.im} ∩ strip := by
    ext τ; simp [and_comm]
  show ∫⁻ τ in {τ : ℍ | τ ∈ strip ∧ 1 ≤ τ.im}, ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ < ⊤
  rw [hS, ← Measure.restrict_restrict hmT, ← lintegral_indicator hmT,
    (GlobalTheory.T.unitStrip_integral_eq_iterated).1 _ ((hmeas.enorm).indicator hmT)]
  have hinner : Set.EqOn
      (fun y : ℝ => (∫⁻ x in Set.Ico (0 : ℝ) 1, {τ : ℍ | 1 ≤ τ.im}.indicator
        (fun τ => ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ) (ofComplex (x + y * Complex.I))) *
          ENNReal.ofReal (1 / y ^ 2))
      (fun y : ℝ => (Set.Ici (1 : ℝ)).indicator
        (fun y => ENNReal.ofReal (y ^ (r - 2) * Real.exp (-c * y))) y) (Set.Ioi 0) := by
    intro y hy
    have hy0 : (0 : ℝ) < y := hy
    have hpt : ∀ x : ℝ, {τ : ℍ | 1 ≤ τ.im}.indicator
        (fun τ => ‖τ.im ^ r * Real.exp (-c * τ.im)‖ₑ) (ofComplex (x + y * Complex.I)) =
        (Set.Ici (1 : ℝ)).indicator
          (fun y => ENNReal.ofReal (y ^ r * Real.exp (-c * y))) y := by
      intro x
      by_cases h1 : (1 : ℝ) ≤ y
      · rw [Set.indicator_of_mem (by simpa [im_ofComplex_xy x y hy0] using h1),
          Set.indicator_of_mem (by simpa using h1), im_ofComplex_xy x y hy0,
          Real.enorm_eq_ofReal (mul_nonneg (Real.rpow_nonneg hy0.le _) (Real.exp_pos _).le)]
      · rw [Set.indicator_of_notMem (by simpa [im_ofComplex_xy x y hy0] using h1),
          Set.indicator_of_notMem (by simpa using h1)]
    simp only [hpt]
    rw [setLIntegral_const, Real.volume_Ico, sub_zero, ENNReal.ofReal_one, mul_one]
    by_cases h1 : (1 : ℝ) ≤ y
    · rw [Set.indicator_of_mem (by simpa using h1), Set.indicator_of_mem (by simpa using h1),
        ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hy0.le _) (Real.exp_pos _).le)]
      congr 1
      rw [Real.rpow_sub hy0, Real.rpow_two]
      field_simp
    · rw [Set.indicator_of_notMem (by simpa using h1), Set.indicator_of_notMem (by simpa using h1),
        zero_mul]
  rw [setLIntegral_congr_fun measurableSet_Ioi hinner, lintegral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici,
    Set.inter_eq_left.2 (Set.Ici_subset_Ioi.2 one_pos)]
  have hfin := ((integrableOn_Ici_iff_integrableOn_Ioi).2
    (integrableOn_rpow_sub_two_mul_exp_Ioi_one r c hc)).hasFiniteIntegral
  exact lt_of_le_of_lt (lintegral_ofReal_le_lintegral_enorm _) hfin

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegrableOnSqQExpansionUnitStripLow
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM

theorem lintegral_sq_qs_line (b : ℕ → ℂ) (hb : PolyB b) (y : ℝ) (hy : 0 < y) :
    ∫⁻ x in Set.Ico (0 : ℝ) 1, ENNReal.ofReal (‖qs b (ofComplex (x + y * Complex.I))‖ ^ 2)
      = ∑' n : ℕ, ENNReal.ofReal (‖b n‖ ^ 2 * Real.exp (-4 * π * n * y)) := by
  have him : ∀ x : ℝ, 0 < ((x : ℂ) + y * Complex.I).im := fun x => by simpa using hy
  have hc0 : Continuous fun x : ℝ => ofComplex ((x : ℂ) + y * Complex.I) := by
    have : (fun x : ℝ => ofComplex ((x : ℂ) + y * Complex.I))
        = fun x : ℝ => (⟨(x : ℂ) + y * Complex.I, him x⟩ : ℍ) := by
      funext x; exact ofComplex_apply_of_im_pos (him x)
    rw [this, UpperHalfPlane.isEmbedding_coe.continuous_iff]
    show Continuous fun x : ℝ => (x : ℂ) + y * Complex.I
    fun_prop
  have hc : Continuous fun x : ℝ => ‖qs b (ofComplex (x + y * Complex.I))‖ ^ 2 :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb).2.comp hc0).norm.pow 2
  have hP := GlobalTheory.T.hasSum_parseval_qExpansion_horizontal_line b b y hb hb hy
  have h1 : (∫ x in (0 : ℝ)..1, conj (qs b (ofComplex (x + y * Complex.I))) * qs b (ofComplex (x + y * Complex.I)))
      = ((∫ x in (0 : ℝ)..1, ‖qs b (ofComplex (x + y * Complex.I))‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    congr 1
    funext x
    rw [Complex.conj_mul']
    push_cast
    rfl
  have h2 : (fun n : ℕ => conj (b n) * b n * (Real.exp (-4 * π * n * y) : ℝ))
      = fun n : ℕ => ((‖b n‖ ^ 2 * Real.exp (-4 * π * n * y) : ℝ) : ℂ) := by
    funext n
    rw [Complex.conj_mul', Complex.ofReal_mul, Complex.ofReal_pow]
  rw [h1, h2, Complex.hasSum_ofReal] at hP
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hP.summable, hP.tsum_eq,
    intervalIntegral.integral_of_le zero_le_one, integral_Ioc_eq_integral_Ioo,
    ← integral_Ico_eq_integral_Ioo, ofReal_integral_eq_lintegral_ofReal]
  · exact (hc.integrableOn_Icc (a := 0) (b := 1)).mono_set Set.Ico_subset_Icc_self
  · exact Eventually.of_forall fun x => by positivity

theorem lintegral_exp_rpow_le (a c : ℝ) (ha : 0 < a) (hc : 0 < c) :
    ∫⁻ y in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (y ^ (a - 1) * Real.exp (-(c * y)))
      ≤ ENNReal.ofReal ((1 / c) ^ a * Real.Gamma a) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hc
  have hpos : 0 < (1 / c) ^ a * Real.Gamma a := mul_pos (by positivity) (Real.Gamma_pos_of_pos ha)
  have hi : Integrable (fun y : ℝ => y ^ (a - 1) * Real.exp (-(c * y))) (volume.restrict (Set.Ioi 0)) :=
    Integrable.of_integral_ne_zero (by rw [h]; exact hpos.ne')
  rw [← h, ofReal_integral_eq_lintegral_ofReal hi]
  · exact lintegral_mono_set Set.Ioo_subset_Ioi_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    have : 0 < y := hy
    simp only [Pi.zero_apply]
    positivity

theorem tsum_lintegral_exp_rpow_lt_top (b : ℕ → ℂ) (a : ℝ) (ha0 : 0 < a)
    (hsum : Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ a) :
    ∑' n : ℕ, ENNReal.ofReal (‖b n‖ ^ 2) *
      ∫⁻ y in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (y ^ (a - 1) * Real.exp (-(4 * π * n * y))) < ⊤ := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  refine ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_, ?_⟩
  · have hi : IntegrableOn (fun y : ℝ => y ^ (a - 1)) (Set.Ioo 0 1) :=
      (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (by linarith)).1.mono_set Set.Ioo_subset_Ioc_self
    simpa using hi.lintegral_lt_top
  · have hs1 : Summable fun n : ℕ => ‖b (n + 1)‖ ^ 2 * ((1 / (4 * π * ((n + 1 : ℕ) : ℝ))) ^ a * Real.Gamma a) := by
      refine (((summable_nat_add_iff 1).2 hsum).mul_left ((1 / (4 * π)) ^ a * Real.Gamma a)).congr fun n => ?_
      rw [show 1 / (4 * π * ((n + 1 : ℕ) : ℝ)) = (1 / (4 * π)) / ((n + 1 : ℕ) : ℝ) by field_simp,
        Real.div_rpow (x := 1 / (4 * π)) (by positivity) (by positivity)]
      ring
    have hG0 := Real.Gamma_pos_of_pos ha0
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum (g := fun n : ℕ => ENNReal.ofReal
      (‖b (n + 1)‖ ^ 2 * ((1 / (4 * π * ((n + 1 : ℕ) : ℝ))) ^ a * Real.Gamma a))) fun n => ?_) ?_
    · rw [ENNReal.ofReal_mul (by positivity)]
      gcongr
      exact lintegral_exp_rpow_le a _ ha0 (by positivity)
    · rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hs1]
      exact ENNReal.ofReal_lt_top

theorem integrableOn_sq_qs_low : ∀ (e : ℕ) (b : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → PolyB b →
    (Summable fun n : ℕ => ‖b n‖ ^ 2 / (n : ℝ) ^ (2 * (e : ℝ) - 1 + s)) →
    IntegrableOn (fun τ : ℍ => ‖qs b τ‖ ^ 2 * τ.im ^ (2 * (e : ℝ) + s)) {τ | τ ∈ strip ∧ τ.im < 1} := by
  intro e b s he hs hb hsum
  have he' : (1 : ℝ) ≤ e := by exact_mod_cast he
  set a : ℝ := 2 * (e : ℝ) - 1 + s with ha
  have ha0 : 0 < a := by rw [ha]; linarith
  have hp : 2 * (e : ℝ) + s = a + 1 := by rw [ha]; ring
  rw [hp]
  have hcont : Continuous fun τ : ℍ => ‖qs b τ‖ ^ 2 * τ.im ^ (a + 1) :=
    ((GlobalTheory.T.qExpansion_polyGrowth_summable_continuous b hb).2.norm.pow 2).mul
      (UpperHalfPlane.continuous_im.rpow_const fun τ => Or.inr (by linarith))
  refine ⟨hcont.aestronglyMeasurable, ?_⟩
  have hmeas : MeasurableSet {τ : ℍ | τ.im < 1} :=
    (isOpen_lt UpperHalfPlane.continuous_im continuous_const).measurableSet
  set G : ℍ → ENNReal := fun τ => ENNReal.ofReal (‖qs b τ‖ ^ 2 * τ.im ^ (a + 1)) with hG
  have hGm : Measurable G := ENNReal.measurable_ofReal.comp hcont.measurable
  have e1 : ∫⁻ τ in {τ : ℍ | τ ∈ strip ∧ τ.im < 1}, ‖‖qs b τ‖ ^ 2 * τ.im ^ (a + 1)‖ₑ
      = ∫⁻ τ in strip, Set.indicator {τ : ℍ | τ.im < 1} G τ := by
    rw [lintegral_indicator hmeas, Measure.restrict_restrict hmeas]
    have : {τ : ℍ | τ ∈ strip ∧ τ.im < 1} = {τ : ℍ | τ.im < 1} ∩ strip := by
      ext τ; simp [and_comm]
    rw [this]
    refine lintegral_congr fun τ => ?_
    have := τ.im_pos
    exact Real.enorm_of_nonneg (by positivity)
  rw [hasFiniteIntegral_iff_enorm, e1, GlobalTheory.T.unitStrip_integral_eq_iterated.1 _ (hGm.indicator hmeas)]
  set T : ℕ → ℝ → ENNReal := fun n y =>
    ENNReal.ofReal (‖b n‖ ^ 2) * ENNReal.ofReal (y ^ (a - 1) * Real.exp (-(4 * π * n * y))) with hT
  have hTm : ∀ n : ℕ, Measurable fun y : ℝ => ENNReal.ofReal (y ^ (a - 1) * Real.exp (-(4 * π * n * y))) := fun n => by
    refine ENNReal.measurable_ofReal.comp ?_
    fun_prop
  have e2 : ∀ y ∈ Set.Ioi (0 : ℝ),
      (∫⁻ x in Set.Ico (0 : ℝ) 1, Set.indicator {τ : ℍ | τ.im < 1} G (ofComplex (x + y * Complex.I)))
        * ENNReal.ofReal (1 / y ^ 2) = Set.indicator (Set.Iio 1) (fun y => ∑' n, T n y) y := by
    intro y hy
    have hy : 0 < y := hy
    have him : ∀ x : ℝ, (ofComplex ((x : ℂ) + y * Complex.I)).im = y := fun x => by
      have h : 0 < ((x : ℂ) + y * Complex.I).im := by simpa using hy
      rw [ofComplex_apply_of_im_pos h]
      show ((x : ℂ) + y * Complex.I).im = y
      simp
    by_cases h1 : y < 1
    · have : ∀ x : ℝ, Set.indicator {τ : ℍ | τ.im < 1} G (ofComplex (x + y * Complex.I))
          = ENNReal.ofReal (‖qs b (ofComplex (x + y * Complex.I))‖ ^ 2) * ENNReal.ofReal (y ^ (a + 1)) := fun x => by
        rw [Set.indicator_of_mem (by simpa [him x] using h1), hG]
        simp only [him x]
        rw [ENNReal.ofReal_mul (by positivity)]
      simp only [this]
      rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, lintegral_sq_qs_line b hb y hy,
        Set.indicator_of_mem (by simpa using h1), mul_assoc, ← ENNReal.tsum_mul_right]
      refine tsum_congr fun n => ?_
      simp only [hT]
      rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      congr 1
      have : y ^ (a + 1) = y ^ (a - 1) * y ^ 2 := by
        rw [← Real.rpow_two, ← Real.rpow_add hy]; congr 1; ring
      rw [this, show -4 * π * n * y = -(4 * π * n * y) by ring]
      field_simp
    · have : ∀ x : ℝ, Set.indicator {τ : ℍ | τ.im < 1} G (ofComplex (x + y * Complex.I)) = 0 := fun x =>
        Set.indicator_of_notMem (by simpa [him x] using h1) _
      simp only [this]
      rw [Set.indicator_of_notMem (by simpa using h1)]
      simp
  rw [setLIntegral_congr_fun measurableSet_Ioi e2, lintegral_indicator measurableSet_Iio,
    Measure.restrict_restrict measurableSet_Iio, Set.inter_comm, Set.Ioi_inter_Iio,
    lintegral_tsum (f := T) fun n => ((hTm n).const_mul _).aemeasurable]
  simp only [hT, lintegral_const_mul _ (hTm _)]
  exact tsum_lintegral_exp_rpow_lt_top b a ha0 hsum

end GlobalTheory.EisM
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionFractionFieldBoundedDenominators
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_bdd_den : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε) (f : T.K),
    ∃ D : ℕ, 0 < D ∧ ∀ r : ℚ, ∃ k : ℕ, IsIntegral ℤ ((D : Ω) ^ k * (T.exp f).coeff r) := by
  intro Ω _ _ _ ε T f
  obtain ⟨a, b, hb, hab⟩ := T.io_surj f
  have hexpS : ∀ c : ring ε.range, ∃ S : Finset Ω, ∀ r, (T.exp (T.io c)).coeff r ∈ Subring.closure (S : Set Ω) := by
    intro c
    have hc : InR ε.range (c : ℍ → ℂ) := ((GlobalTheory.T.mem_modularFunctionRingOver_iff_hasSomeLevelOver ε.range).1 c).1 c.2
    exact GlobalTheory.T.cuspExpansion_coeff_mem_finitelyGenerated_subring Ω ε c _ hc (T.exp_io c)
  obtain ⟨Sa, hSa⟩ := hexpS a
  obtain ⟨Sb, hSb⟩ := hexpS b
  have hiob : T.io b ≠ 0 := by
    intro h
    apply hb
    apply T.io_inj
    rw [h, map_zero]
  have hexpb : T.exp (T.io b) ≠ 0 := by
    intro h
    apply hiob
    exact (injective_iff_map_eq_zero (T.exp : T.K →+* HahnSeries ℚ Ω)).1
      (T.exp : T.K →+* HahnSeries ℚ Ω).injective _ h
  have hf : T.exp f = T.exp (T.io a) * (T.exp (T.io b))⁻¹ := by
    rw [← hab, map_mul, mul_assoc, mul_inv_cancel₀ hexpb, mul_one]
  classical
  let S : Finset Ω := Sa ∪ Sb ∪ {(T.exp (T.io b)).leadingCoeff⁻¹}
  let A : Subring Ω := Subring.closure (S : Set Ω)
  have hA_a : ∀ r, (T.exp (T.io a)).coeff r ∈ A := fun r =>
    Subring.closure_mono (by intro x hx; simp [S, hx]) (hSa r)
  have hA_b : ∀ r, (T.exp (T.io b)).coeff r ∈ A := fun r =>
    Subring.closure_mono (by intro x hx; simp [S, hx]) (hSb r)
  have hA_l : (T.exp (T.io b)).leadingCoeff⁻¹ ∈ A := Subring.subset_closure (by simp [S])
  have hP := GlobalTheory.T.hahnSeries_subring_coeff_mul_inv_mem Ω A
  have hA_inv := hP.2 _ hA_b hA_l
  have hA_f : ∀ r, (T.exp f).coeff r ∈ A := by
    intro r
    rw [hf]
    exact hP.1 _ _ hA_a hA_inv r
  haveI : Algebra.IsAlgebraic ℚ Ω := IsAlgClosure.isAlgebraic
  obtain ⟨D, hD, hDk⟩ := GlobalTheory.T.algebraic_subring_closure_common_denominator Ω S
  exact ⟨D, hD, fun r => hDk _ (hA_f r)⟩

end GlobalTheory.FN
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.QsBddAboveOneStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_bound_norm_qs_of_one_le_im : ∀ (b : ℕ → ℂ), PolyB b → ∃ M : ℝ, ∀ τ : ℍ, 1 ≤ τ.im → ‖qs b τ‖ ≤ M := by
  first | exact @GlobalTheory.EisM.qs_bdd_above_one | exact GlobalTheory.EisM.qs_bdd_above_one | (intros; apply GlobalTheory.EisM.qs_bdd_above_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.RankinDirichletSeriesIdentityHeckeStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rankin_dirichlet_series_identity_hecke : ∀ (e : ℕ) (χ ψ θ g : ℕ → ℂ) (s : ℝ), 1 ≤ e → 0 < s → (∀ m n, ψ (m * n) = ψ m * ψ n) → (∀ m n, θ (m * n) = θ m * θ n) → (∀ n, ‖χ n‖ ≤ 1 ∧ ‖ψ n‖ ≤ 1 ∧ ‖θ n‖ ≤ 1) → (∀ m n : ℕ, 0 < m → 0 < n → g m * g n = ∑ δ ∈ (Nat.gcd m n).divisors, χ δ * (δ : ℂ) ^ (2 * e) * g (m * n / δ ^ 2)) → (∀ t : ℝ, 0 < t → Summable fun n : ℕ => ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + t)) → ∀ b : ℕ → ℂ, (∀ n, n ≠ 0 → b n = ∑ p ∈ n.divisorsAntidiagonal, ψ p.1 * (p.1 : ℂ) ^ (e - 1) * θ p.2) → LSeriesSummable (fun n => g n * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) ∧ LSeries (fun n => χ n * ψ n * θ n) ((e + 1 : ℕ) + 2 * s) * LSeries (fun n => g n * b n) ((2 * (e : ℝ) + s : ℝ) : ℂ) = LSeries (fun n => ψ n * g n) ((e + 1 : ℝ) + s : ℝ) * LSeries (fun n => θ n * g n) ((2 * (e : ℝ) + s : ℝ) : ℂ) := by
  first | exact @GlobalTheory.EisM.rankin_dirichlet_identity | exact GlobalTheory.EisM.rankin_dirichlet_identity | (intros; apply GlobalTheory.EisM.rankin_dirichlet_identity <;> assumption)
end

