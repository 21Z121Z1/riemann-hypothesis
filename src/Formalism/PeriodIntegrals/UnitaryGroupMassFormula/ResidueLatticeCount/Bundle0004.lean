import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.Bundle0002

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.LatticeCountGen
section
open NumberField NumberField.mixedEmbedding MeasureTheory
open scoped ENNReal Pointwise Classical

noncomputable section

namespace PI.Residue

theorem latticeCount_gen {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L] (B : Set E) (hB : MeasurableSet B) :
    μ B ≤ (∑' x : L, (B - B).indicator (fun _ => (1 : ℝ≥0∞)) (x : E)) *
      ENNReal.ofReal (ZLattice.covolume L μ) := by
  classical
  let b := Module.Free.chooseBasis ℤ L
  have hF := ZLattice.isAddFundamentalDomain b μ
  set F := ZSpan.fundamentalDomain (b.ofZLatticeBasis ℝ) with hFdef
  have hfin : μ F ≠ ⊤ := (ZSpan.fundamentalDomain_isBounded _).measure_lt_top.ne
  have hcov : ENNReal.ofReal (ZLattice.covolume L μ) = μ F := by
    rw [ZLattice.covolume_eq_measure_fundamentalDomain L μ hF, measureReal_def,
      ENNReal.ofReal_toReal hfin]
  haveI : VAddInvariantMeasure L E μ :=
    ⟨fun c s _ => measure_preimage_add μ (c : E) s⟩
  have hm : ∀ g : L, MeasurableSet (g +ᵥ B) := fun g => hB.const_vadd g
  have h2 : ∀ g : L, μ ((g +ᵥ B) ∩ F) =
      ∫⁻ t in F, (g +ᵥ B).indicator (fun _ => (1 : ℝ≥0∞)) t ∂μ := by
    intro g
    rw [lintegral_indicator_const (hm g), one_mul, Measure.restrict_apply (hm g)]
  have hpt : ∀ t : E, ∑' g : L, (g +ᵥ B).indicator (fun _ => (1 : ℝ≥0∞)) t ≤
      ∑' x : L, (B - B).indicator (fun _ => (1 : ℝ≥0∞)) (x : E) := by
    intro t
    by_cases h : ∃ g0 : L, t ∈ g0 +ᵥ B
    · obtain ⟨g0, hg0⟩ := h
      rw [← (Equiv.addRight g0).tsum_eq]
      refine ENNReal.tsum_le_tsum fun g => ?_
      by_cases hg : t ∈ ((Equiv.addRight g0) g) +ᵥ B
      · have : (g : E) ∈ B - B := by
          obtain ⟨b0, hb0, e0⟩ := hg0
          obtain ⟨b1, hb1, e1⟩ := hg
          refine ⟨b0, hb0, b1, hb1, ?_⟩
          have e0' : (g0 : E) + b0 = t := e0
          have e1' : ((g : E) + (g0 : E)) + b1 = t := e1
          have : (g0 : E) + b0 = ((g : E) + (g0 : E)) + b1 := e0'.trans e1'.symm
          rw [sub_eq_iff_eq_add]
          apply add_left_cancel (a := (g0 : E))
          rw [this]; abel
        rw [Set.indicator_of_mem hg, Set.indicator_of_mem this]
      · rw [Set.indicator_of_notMem hg]; exact zero_le
    · push Not at h
      have : ∀ g : L, (g +ᵥ B).indicator (fun _ => (1 : ℝ≥0∞)) t = 0 :=
        fun g => Set.indicator_of_notMem (h g) _
      simp [this]
  calc μ B = ∑' g : L, μ ((g +ᵥ B) ∩ F) := hF.measure_eq_tsum B
    _ = ∫⁻ t in F, ∑' g : L, (g +ᵥ B).indicator (fun _ => (1 : ℝ≥0∞)) t ∂μ := by
        rw [lintegral_tsum fun g => (measurable_const.indicator (hm g)).aemeasurable]
        exact tsum_congr h2
    _ ≤ ∫⁻ _ in F, ∑' x : L, (B - B).indicator (fun _ => (1 : ℝ≥0∞)) (x : E) ∂μ :=
        lintegral_mono hpt
    _ = _ := by rw [setLIntegral_const, hcov]

theorem latticeCount : LatticeCount := fun _ _ _ L _ _ B hB => latticeCount_gen volume L B hB

end PI.Residue
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.MemSmulNormLeOne
section
open NumberField NumberField.mixedEmbedding NumberField.mixedEmbedding.fundamentalCone
  NumberField.InfinitePlace NumberField.Units MeasureTheory
open scoped ENNReal Classical Pointwise

noncomputable section

namespace PI.Residue

variable (K : Type) [Field K] [NumberField K]

def cHalf : ℝ := (1 / 2 : ℝ) ^ ((1 : ℝ) / Module.finrank ℚ K)

theorem cHalf_pos : 0 < cHalf K := Real.rpow_pos_of_pos (by norm_num) _

theorem cHalf_pow : cHalf K ^ Module.finrank ℚ K = 1 / 2 := by
  have hm : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast (Module.finrank_pos (R := ℚ) (M := K)).ne'
  rw [cHalf, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), one_div_mul_cancel hm,
    Real.rpow_one]

theorem mem_smul_normLeOne (y : mixedSpace K) :
    y ∈ cHalf K • normLeOne K ↔ y ∈ fundamentalCone K ∧ mixedEmbedding.norm y ≤ 1 / 2 := by
  have hc := cHalf_pos K
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hc.ne', mem_normLeOne,
    smul_mem_iff_mem (inv_ne_zero hc.ne'), mixedEmbedding.norm_smul, abs_of_pos (inv_pos.2 hc),
    inv_pow, cHalf_pow]
  refine and_congr_right fun _ => ?_
  constructor <;> intro h <;> linarith

theorem shell_eq : shell K = normLeOne K \ (cHalf K • normLeOne K) := by
  ext y
  rw [Set.mem_sdiff, mem_smul_normLeOne, mem_normLeOne]
  simp only [shell, Set.mem_ofPred_eq, not_and, not_le]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3⟩, fun _ => h2⟩
  · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨h1, h2 h1, h3⟩

theorem smul_subset : cHalf K • normLeOne K ⊆ normLeOne K := by
  intro y hy
  rw [mem_smul_normLeOne] at hy
  exact mem_normLeOne.2 ⟨hy.1, hy.2.trans (by norm_num)⟩

theorem shellVolume : ShellVolume := by
  intro K _ _
  have hc := cHalf_pos K
  have hV : volume (normLeOne K) = vfac K * ENNReal.ofReal (regulator K) := by
    rw [volume_normLeOne, vfac]
  have hfin : volume (normLeOne K) ≠ ⊤ := (isBounded_normLeOne K).measure_lt_top.ne
  have hs : volume (cHalf K • normLeOne K) = volume (normLeOne K) / 2 := by
    rw [Measure.addHaar_smul, mixedEmbedding.finrank, cHalf_pow, abs_of_pos (by norm_num),
      ENNReal.div_eq_inv_mul]
    congr 1
    rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num)]
    norm_num
  have hm : MeasurableSet (cHalf K • normLeOne K) :=
    (measurableSet_normLeOne K).const_smul₀ _
  rw [shell_eq, measure_sdiff (smul_subset K) hm.nullMeasurableSet
    (ne_top_of_le_ne_top hfin (measure_mono (smul_subset K))), hs, ← hV]
  exact ENNReal.sub_half hfin

end PI.Residue
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ResidueLatticeCount.RealHitIneq
section
open NumberField NumberField.mixedEmbedding NumberField.InfinitePlace MeasureTheory
open scoped ENNReal Classical

noncomputable section

namespace PI.Residue

theorem real_hit_ineq (A N s : ℝ) (hA : 0 < A) (hN : 0 < N) (hs : 1 < s) (h : N ≤ 2 * A) :
    A / N ≤ A * (2 * A) ^ (s - 1) * N ^ (-s) := by
  have hP : 0 < N ^ (s - 1) := Real.rpow_pos_of_pos hN _
  have hPB : N ^ (s - 1) ≤ (2 * A) ^ (s - 1) := Real.rpow_le_rpow hN.le h (by linarith)
  have hNs : N ^ s = N ^ (s - 1) * N := by
    rw [← Real.rpow_add_one hN.ne']; ring_nf
  rw [Real.rpow_neg hN.le, hNs]
  have e : A * (2 * A) ^ (s - 1) * (N ^ (s - 1) * N)⁻¹ = A / N * ((2 * A) ^ (s - 1) / N ^ (s - 1)) := by
    field_simp
  rw [e]
  exact le_mul_of_one_le_right (by positivity) ((one_le_div hP).2 hPB)

theorem hitBound_of (hbox : BoxVolume) : HitBound := by
  intro K _ _ ρ s x hρ hs hx
  have hpos : ∀ w, 0 < normAtPlace w x := fun w =>
    lt_of_le_of_ne (normAtPlace_nonneg w x) (Ne.symm (mixedEmbedding.norm_ne_zero_iff.1 hx.ne' w))
  have hhit : hit K ρ x = box K (fun w => ρ / normAtPlace w x) := by
    ext y
    simp only [hit, box, Set.mem_ofPred_eq]
    exact forall_congr' fun w => (lt_div_iff₀ (hpos w)).symm
  have hprod : ∏ w, (ρ / normAtPlace w x) ^ mult w
      = ρ ^ Module.finrank ℚ K / mixedEmbedding.norm x := by
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum, sum_mult_eq, mixedEmbedding.norm_apply]
  have hA : 0 < ρ ^ Module.finrank ℚ K := by positivity
  by_cases h : mixedEmbedding.norm x ≤ 2 * ρ ^ Module.finrank ℚ K
  · calc volume ({y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ x) ≤ volume (hit K ρ x) :=
          measure_mono Set.inter_subset_right
      _ = vfac K * ENNReal.ofReal (ρ ^ Module.finrank ℚ K / mixedEmbedding.norm x) := by
          rw [hhit, hbox K _ (fun w => div_pos hρ (hpos w)), hprod]
      _ ≤ _ := by
          gcongr
          exact real_hit_ineq _ _ s hA hx hs h
  · have hempty : {y | 1 / 2 < mixedEmbedding.norm y} ∩ hit K ρ x = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro y ⟨hy1, hy2⟩
      rw [hhit] at hy2
      have hle : mixedEmbedding.norm y ≤ ρ ^ Module.finrank ℚ K / mixedEmbedding.norm x := by
        rw [← hprod, mixedEmbedding.norm_apply]
        exact Finset.prod_le_prod (fun w _ => pow_nonneg (normAtPlace_nonneg w y) _)
          (fun w _ => pow_le_pow_left₀ (normAtPlace_nonneg w y) (hy2 w).le _)
      have hhalf : ρ ^ Module.finrank ℚ K / mixedEmbedding.norm x ≤ 1 / 2 := by
        rw [div_le_iff₀ hx]
        rw [not_le] at h
        linarith
      have hy1' : 1 / 2 < mixedEmbedding.norm y := hy1
      linarith
    rw [hempty, measure_empty]
    exact zero_le

end PI.Residue
end
end

