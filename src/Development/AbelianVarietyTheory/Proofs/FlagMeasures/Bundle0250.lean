import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MomAllP
import Formalism.LocalRingCardinality.Bundle0003
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0134
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0165
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0240
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerDilationWeightsDualIsotropicVector
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0243
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0242
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralProdPowLeOfMomentsMassLeOne
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem lintegral_prod_pow_le_of_moments : ∀ (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r q : ℕ) (ρ : Fin r → Ω → ℝ) (Ph : Ω → ℝ) (Rr : ℝ) (s : Finset (Fin r)), (∀ a, AEMeasurable (ρ a) ν) → (∀ a, ∀ᵐ x ∂ν, 0 ≤ ρ a x) → AEMeasurable Ph ν → (∀ x, 0 ≤ Ph x) → ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν ≤ 1 → 1 ≤ Rr → (∀ a, ∫⁻ x, ENNReal.ofReal (ρ a x ^ (2 * (r * q)) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q)))) → ∫⁻ x, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ (2 * (r * q))) := by
  classical
  intro Ω _ ν r q ρ Ph Rr s hρm hρ0 hPm hP0 hP1 hR hbd
  have hR0 : (0:ℝ) ≤ Rr := le_trans zero_le_one hR
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hs : s = ∅ := Finset.eq_empty_of_isEmpty s
    subst hs
    simpa using hP1
  · set N : ℕ := 2 * (r * q) with hN
    let u : Fin r → Ω → ℝ := fun a x => if a ∈ s then ρ a x else Rr
    have hrR : (0:ℝ) < r := by exact_mod_cast hr
    have hr0 : r ≠ 0 := Nat.pos_iff_ne_zero.mp hr
    have hpt : ∀ᵐ x ∂ν, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x)
        ≤ ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (u a x ^ N * Ph x) := by
      have hall : ∀ᵐ x ∂ν, ∀ a, 0 ≤ ρ a x := ae_all_iff.mpr hρ0
      filter_upwards [hall] with x hx
      have hu0 : ∀ a, 0 ≤ u a x := fun a => by
        by_cases ha : a ∈ s <;> simp [u, ha, hx a, hR0]
      have h1 : (∏ a ∈ s, ρ a x) ^ (2 * q) ≤ ∏ a : Fin r, u a x ^ (2 * q) := by
        have : (∏ a ∈ s, ρ a x) ^ (2 * q)
            = ∏ a : Fin r, (if a ∈ s then ρ a x ^ (2 * q) else 1) := by
          rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_pow]
        rw [this]
        apply Finset.prod_le_prod
        · intro a _
          by_cases ha : a ∈ s
          · simp [ha, pow_nonneg (hx a)]
          · simp [ha]
        · intro a _
          by_cases ha : a ∈ s
          · simp [u, ha]
          · simp [u, ha, one_le_pow₀ hR]
      have h2 : ∏ a : Fin r, u a x ^ (2 * q) ≤ ∑ a : Fin r, (r:ℝ)⁻¹ * u a x ^ N := by
        have hw : ∑ _a : Fin r, (r:ℝ)⁻¹ = 1 := by
          simp [Finset.card_univ, Fintype.card_fin, hrR.ne']
        have key := Real.geom_mean_le_arith_mean_weighted (Finset.univ : Finset (Fin r))
          (fun _ => (r:ℝ)⁻¹) (fun a => (u a x ^ (2 * q)) ^ r)
          (fun _ _ => inv_nonneg.mpr hrR.le) hw (fun a _ => pow_nonneg (pow_nonneg (hu0 a) _) _)
        have e1 : ∀ a, ((u a x ^ (2 * q)) ^ r) ^ ((r:ℝ)⁻¹) = u a x ^ (2 * q) := fun a =>
          Real.pow_rpow_inv_natCast (pow_nonneg (hu0 a) _) hr0
        have e2 : ∀ a, (u a x ^ (2 * q)) ^ r = u a x ^ N := fun a => by
          rw [← pow_mul, hN]; congr 1; ring
        simp only [e1] at key
        simp only [e2] at key
        exact key
      have hP : 0 ≤ Ph x := hP0 x
      have h3 : (∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x
          ≤ ∑ a : Fin r, (r:ℝ)⁻¹ * (u a x ^ N * Ph x) := by
        calc (∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x
            ≤ (∑ a : Fin r, (r:ℝ)⁻¹ * u a x ^ N) * Ph x :=
              mul_le_mul_of_nonneg_right (h1.trans h2) hP
          _ = ∑ a : Fin r, (r:ℝ)⁻¹ * (u a x ^ N * Ph x) := by
              rw [Finset.sum_mul]; congr 1; ext a; ring
      calc ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x)
          ≤ ENNReal.ofReal (∑ a : Fin r, (r:ℝ)⁻¹ * (u a x ^ N * Ph x)) :=
            ENNReal.ofReal_le_ofReal h3
        _ = ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (u a x ^ N * Ph x) := by
            rw [ENNReal.ofReal_sum_of_nonneg]
            · congr 1; ext a
              rw [ENNReal.ofReal_mul (inv_nonneg.mpr hrR.le)]
            · intro a _
              exact mul_nonneg (inv_nonneg.mpr hrR.le) (mul_nonneg (pow_nonneg (hu0 a) _) hP)
    have hum : ∀ a, AEMeasurable (u a) ν := fun a => by
      by_cases ha : a ∈ s
      · simpa [u, ha] using hρm a
      · simp only [u, ha, if_false]; exact aemeasurable_const
    have hint : ∀ a, ∫⁻ x, ENNReal.ofReal (u a x ^ N * Ph x) ∂ν ≤ ENNReal.ofReal (Rr ^ N) := by
      intro a
      by_cases ha : a ∈ s
      · simpa [u, ha] using hbd a
      · simp only [u, ha, if_false]
        have hRN : (0:ℝ) ≤ Rr ^ N := pow_nonneg hR0 _
        simp_rw [ENNReal.ofReal_mul hRN]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        calc ENNReal.ofReal (Rr ^ N) * ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν
            ≤ ENNReal.ofReal (Rr ^ N) * 1 := by gcongr
          _ = ENNReal.ofReal (Rr ^ N) := mul_one _
    calc ∫⁻ x, ENNReal.ofReal ((∏ a ∈ s, ρ a x) ^ (2 * q) * Ph x) ∂ν
        ≤ ∫⁻ x, ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (u a x ^ N * Ph x) ∂ν :=
          lintegral_mono_ae hpt
      _ = ∑ a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ∫⁻ x, ENNReal.ofReal (u a x ^ N * Ph x) ∂ν := by
          rw [lintegral_finset_sum']
          · congr 1; ext a
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
          · intro a _
            exact (((hum a).pow_const N).mul hPm).ennreal_ofReal.const_mul _
      _ ≤ ∑ _a : Fin r, ENNReal.ofReal ((r:ℝ)⁻¹) * ENNReal.ofReal (Rr ^ N) := by
          gcongr with a
          exact hint a
      _ = ENNReal.ofReal (Rr ^ N) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
          have : (r : ℝ≥0∞) * ENNReal.ofReal ((r:ℝ)⁻¹) = 1 := by
            rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg r),
              mul_inv_cancel₀ hrR.ne', ENNReal.ofReal_one]
          rw [this, one_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantLengthTailBoundOfMoments
section
open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp GlobalTheory.TypeAsm Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Amp.TailTwo

theorem cheb_le {X : Type*} [MeasurableSpace X] (ν : Measure X) (l : X → ℝ) (f : X → ℝ≥0∞) (E : Set X)
    (hE : MeasurableSet E) (T : ℝ) (hT : 0 < T) (hl : ∀ x ∈ E, T ≤ l x) (n : ℕ) :
    ∫⁻ x in E, f x ∂ν ≤ ENNReal.ofReal ((T ^ n)⁻¹) * ∫⁻ x, ENNReal.ofReal (l x ^ n) * f x ∂ν := by
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans (setLIntegral_mono' hE fun x hx => ?_) (setLIntegral_le_lintegral E _)
  have hTn : 0 < T ^ n := pow_pos hT n
  rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hTn.le)]
  refine le_mul_of_one_le_left' ?_
  rw [ENNReal.one_le_ofReal, inv_mul_eq_div, one_le_div hTn]
  exact pow_le_pow_left₀ hT.le (hl x hx) n

theorem meas_closed (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ) (hg : ContinuousOn g (GG k r)) (t : Set ℝ) (ht : IsClosed t) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} := by
  obtain ⟨u, hu, h⟩ := (continuousOn_iff_isClosed.1 hg) t ht
  have h1 : MeasurableSet (α := Mt k r) u := IsClosed.measurableSet (α := Mt k r) hu
  have h2 : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (Cheb.isClosed_GG k r)
  have h3 : {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} = u ∩ GG k r := by
    rw [← h]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  rw [h3]
  exact h1.inter h2

theorem meas_open (k r : ℕ) (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → ℝ) (hg : ContinuousOn g (GG k r)) (t : Set ℝ) (ht : IsOpen t) :
    MeasurableSet {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} := by
  obtain ⟨u, hu, h⟩ := continuousOn_iff'.1 hg t ht
  have h1 : MeasurableSet (α := Mt k r) u := IsOpen.measurableSet (α := Mt k r) hu
  have h2 : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (Cheb.isClosed_GG k r)
  have h3 : {x : Mt k r | Matrix.of x ∈ GG k r ∧ g (Matrix.of x) ∈ t} = u ∩ GG k r := by
    rw [← h]
    ext x
    exact ⟨fun hx => ⟨hx.2, hx.1⟩, fun hx => ⟨hx.2, hx.1⟩⟩
  rw [h3]
  exact h1.inter h2

end GlobalTheory.Amp.TailTwo

namespace GlobalTheory.Amp.TailTwo

theorem tailBd_of_moments : ∀ (k r : ℕ) {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (νS : Measure (Mt k r)) (Φ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → Wp) (q : ℕ) (H₁ : ℝ), inWb k r z → 0 < H₁ → νS {x | Matrix.of x ∉ GG k r} = 0 → ContinuousOn Φ (GG k r) → MomBd z νS Φ q H₁ → (∀ a : Fin (r + 1), ∫⁻ x, ENNReal.ofReal ((lA k r z (Matrix.of x) a)⁻¹ ^ (2 * q)) * (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 ∂νS ≤ ENNReal.ofReal (H₁ ^ (2 * q)) * l2SG νS Φ) → TailBd z νS Φ q H₁ := by
  intro k r Wp _ _ _ z νS Φ q H₁ _ hH hG _ hM hI la hla
  set T : ℝ := la * H₁ with hTdef
  have hT : 0 < T := mul_pos hla hH
  set f : Mt k r → ℝ≥0∞ := fun x => (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2 with hf
  set A : Fin (r + 1) → Set (Mt k r) := fun a =>
    {x : Mt k r | Matrix.of x ∈ GG k r ∧ (fun g => lA k r z g a) (Matrix.of x) ∈ Set.Ici T} with hA
  set B : Fin (r + 1) → Set (Mt k r) := fun a =>
    {x : Mt k r | Matrix.of x ∈ GG k r ∧ (fun g => lA k r z g a) (Matrix.of x) ∈ Set.Ioi 0} ∩
    {x : Mt k r | Matrix.of x ∈ GG k r ∧ (fun g => lA k r z g a) (Matrix.of x) ∈ Set.Iic T⁻¹} with hB
  set N : Set (Mt k r) := {x | Matrix.of x ∉ GG k r} with hN
  have hGc : MeasurableSet (α := Mt k r) (GG k r) := IsClosed.measurableSet (α := Mt k r) (Cheb.isClosed_GG k r)
  have hNm : MeasurableSet N := hGc.compl
  have hAm : ∀ a, MeasurableSet (A a) := fun a =>
    meas_closed k r _ ((LenCont.lA_Sg_continuousOn k r z).1 a) _ isClosed_Ici
  have hBm : ∀ a, MeasurableSet (B a) := fun a =>
    (meas_open k r _ ((LenCont.lA_Sg_continuousOn k r z).1 a) _ isOpen_Ioi).inter
      (meas_closed k r _ ((LenCont.lA_Sg_continuousOn k r z).1 a) _ isClosed_Iic)
  set U : Set (Mt k r) := N ∪ ⋃ a, (A a ∪ B a) with hU
  have hUm : MeasurableSet U := hNm.union (MeasurableSet.iUnion fun a => (hAm a).union (hBm a))
  have hsub : {x : Mt k r | ∃ a : Fin (r + 1), la * H₁ ≤ max (lA k r z (Matrix.of x) a) (lA k r z (Matrix.of x) a)⁻¹} ⊆ U := by
    rintro x ⟨a, ha⟩
    by_cases hx : Matrix.of x ∈ GG k r
    · refine Or.inr (Set.mem_iUnion.2 ⟨a, ?_⟩)
      rcases le_max_iff.1 ha with h | h
      · exact Or.inl ⟨hx, h⟩
      · have hpos : 0 < lA k r z (Matrix.of x) a := inv_pos.1 (lt_of_lt_of_le hT h)
        refine Or.inr ⟨⟨hx, hpos⟩, hx, ?_⟩
        show lA k r z (Matrix.of x) a ≤ T⁻¹
        exact (le_inv_comm₀ hT hpos).1 h
    · exact Or.inl hx
  have hc : ∀ a, ∫⁻ x in A a ∪ B a, f x ∂νS ≤ 2 * (ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ) := by
    intro a
    have key : ENNReal.ofReal ((T ^ (2 * q))⁻¹) * (ENNReal.ofReal (H₁ ^ (2 * q)) * l2SG νS Φ) =
        ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      congr 2
      rw [Real.rpow_neg hla.le, hTdef, mul_pow]
      have : la ^ (2 * (q : ℝ)) = la ^ (2 * q) := by
        rw [← Real.rpow_natCast]; push_cast; ring_nf
      rw [this]
      have h1 : H₁ ^ (2 * q) ≠ 0 := pow_ne_zero _ hH.ne'
      field_simp
    have hA' : ∫⁻ x in A a, f x ∂νS ≤ ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
      refine (cheb_le νS (fun x => lA k r z (Matrix.of x) a) f (A a) (hAm a) T hT (fun x hx => hx.2) (2 * q)).trans ?_
      rw [← key]
      gcongr
      exact hM a
    have hB' : ∫⁻ x in B a, f x ∂νS ≤ ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
      refine (cheb_le νS (fun x => (lA k r z (Matrix.of x) a)⁻¹) f (B a) (hBm a) T hT (fun x hx => ?_) (2 * q)).trans ?_
      · have hpos : 0 < lA k r z (Matrix.of x) a := hx.1.2
        exact (le_inv_comm₀ hT hpos).2 hx.2.2
      · rw [← key]
        gcongr
        exact hI a
    refine (lintegral_union_le _ _ _).trans ?_
    exact (add_le_add hA' hB').trans (le_of_eq (two_mul _).symm)
  calc ∫⁻ x, Set.indicator {x : Mt k r | ∃ a : Fin (r + 1), la * H₁ ≤ max (lA k r z (Matrix.of x) a) (lA k r z (Matrix.of x) a)⁻¹}
          (fun x => (‖Φ (Matrix.of x)‖₊ : ℝ≥0∞) ^ 2) x ∂νS
        ≤ ∫⁻ x, U.indicator f x ∂νS := lintegral_mono fun x => Set.indicator_le_indicator_of_subset hsub (fun _ => by simp) x
    _ = ∫⁻ x in U, f x ∂νS := lintegral_indicator hUm _
    _ ≤ ∫⁻ x in N, f x ∂νS + ∫⁻ x in ⋃ a, (A a ∪ B a), f x ∂νS := lintegral_union_le _ _ _
    _ ≤ 0 + ∑ a : Fin (r + 1), ∫⁻ x in A a ∪ B a, f x ∂νS := by
        gcongr
        · exact (setLIntegral_measure_zero _ _ hG).le
        · exact (lintegral_iUnion_le _ _).trans (le_of_eq (tsum_fintype _))
    _ ≤ ∑ _a : Fin (r + 1), 2 * (ENNReal.ofReal (la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ) := by
        rw [zero_add]; exact Finset.sum_le_sum fun a _ => hc a
    _ ≤ ENNReal.ofReal (2 * (2 * r + 2 : ℝ) * la ^ (-(2 * (q : ℝ)))) * l2SG νS Φ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc, ← mul_assoc,
          ENNReal.ofReal_mul (by positivity)]
        gcongr ?_ * _ * _
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        push_cast
        have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        nlinarith

end GlobalTheory.Amp.TailTwo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInverseDifferentIdealPowRealIffUnramifiedCm
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

noncomputable section

namespace GlobalTheory.SnMass.SkewVol

section Fixed

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem differentIdeal_eq_map_of_unramified (hu : Algebra.FormallyUnramified (𝓞 F) (𝓞 E)) :
    differentIdeal ℤ (𝓞 E) = (differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E)) := by
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 F) (𝓞 E),
    (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top F E).1 hu, Ideal.top_mul]

theorem dInv_eq_inv_coe (K : Type) [Field K] [NumberField K] (j : ℕ) :
    dInv K j = ((↑(differentIdeal ℤ (𝓞 K) ^ j) : FractionalIdeal (𝓞 K)⁰ K))⁻¹ := by
  rw [dInv, FractionalIdeal.coeIdeal_pow, inv_pow]

theorem algebraMap_mem_inv_map_iff (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (y : F) :
    algebraMap F E y ∈ ((↑(I.map (algebraMap (𝓞 F) (𝓞 E))) : FractionalIdeal (𝓞 E)⁰ E))⁻¹ ↔
      y ∈ ((↑I : FractionalIdeal (𝓞 F)⁰ F))⁻¹ := by
  have hIE : I.map (algebraMap (𝓞 F) (𝓞 E)) ≠ ⊥ := Ideal.map_ne_bot_of_ne_bot hI
  rw [FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hIE),
    FractionalIdeal.mem_inv_iff (FractionalIdeal.coeIdeal_ne_zero.2 hI)]
  have key : ∀ a : 𝓞 F, algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) =
      algebraMap F E (algebraMap (𝓞 F) F a) := fun a => by
    rw [← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  constructor
  · intro h z hz
    obtain ⟨a, ha, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    have h1 := h (algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a))
      ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, Ideal.mem_map_of_mem _ ha, rfl⟩)
    obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1 h1
    rw [key, ← map_mul] at hc
    have hint : IsIntegral ℤ (y * algebraMap (𝓞 F) F a) := by
      rw [← isIntegral_algHom_iff ((algebraMap F E).toIntAlgHom) (algebraMap F E).injective]
      show IsIntegral ℤ (algebraMap F E (y * algebraMap (𝓞 F) F a))
      rw [← hc]
      exact c.2
    exact (FractionalIdeal.mem_one_iff _).2 ⟨⟨_, hint⟩, rfl⟩
  · intro h z hz
    obtain ⟨b, hb, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hz
    let T : Ideal (𝓞 E) := Submodule.comap
      ((LinearMap.mulLeft (𝓞 E) (algebraMap F E y)) ∘ₗ Algebra.linearMap (𝓞 E) E)
      ((1 : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) E)
    have hle : I.map (algebraMap (𝓞 F) (𝓞 E)) ≤ T := by
      rw [Ideal.map_le_iff_le_comap]
      intro a ha
      obtain ⟨c, hc⟩ := (FractionalIdeal.mem_one_iff _).1
        (h _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨a, ha, rfl⟩))
      show algebraMap F E y * algebraMap (𝓞 E) E (algebraMap (𝓞 F) (𝓞 E) a) ∈
        (1 : FractionalIdeal (𝓞 E)⁰ E)
      rw [key, ← map_mul, ← hc]
      exact (FractionalIdeal.mem_one_iff _).2 ⟨algebraMap (𝓞 F) (𝓞 E) c, key c⟩
    exact hle hb

theorem cm_sigma_ne_id {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : σ ≠ AlgHom.id F E := by
  intro hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have := h.2.1
  apply IsTotallyComplex.complexEmbedding_not_isReal τ
  rw [ComplexEmbedding.isReal_iff]
  ext x
  have := h.2.2.2 τ x
  rw [hσ] at this
  simpa [ComplexEmbedding.conjugate_coe_eq] using this.symm

theorem mem_range_of_cm_fixed {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {x : E} (hx : σ x = x) :
    x ∈ Set.range (algebraMap F E) := by
  have hne := cm_sigma_ne_id h
  have hxS : x ∈ AlgHom.equalizer σ (AlgHom.id F E) := hx
  have hle : Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) ≤ 2 := by
    rw [← Subalgebra.finrank_toSubmodule, ← h.2.2.1]
    exact Submodule.finrank_le _
  have hpos : 0 < Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) := Module.finrank_pos
  have hS : AlgHom.equalizer σ (AlgHom.id F E) = ⊥ := by
    rcases (by omega : Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) = 1 ∨
        Module.finrank F (AlgHom.equalizer σ (AlgHom.id F E)) = 2) with h1 | h2
    · exact Subalgebra.finrank_eq_one_iff.1 h1
    · exfalso
      apply hne
      have htop : Subalgebra.toSubmodule (AlgHom.equalizer σ (AlgHom.id F E)) = ⊤ :=
        Submodule.eq_top_of_finrank_eq (by rw [Subalgebra.finrank_toSubmodule, h2, h.2.2.1])
      ext z
      have hz : z ∈ Subalgebra.toSubmodule (AlgHom.equalizer σ (AlgHom.id F E)) :=
        htop ▸ Submodule.mem_top
      exact hz
  rw [hS] at hxS
  exact Algebra.mem_bot.1 hxS

theorem imV_eq_zero_iff {σ : E →ₐ[F] E} (h : IsCMExt F E σ) (x : E) : imV x = 0 ↔ σ x = x := by
  constructor
  · intro hx
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    let w : InfinitePlace E := InfinitePlace.mk τ
    have him : (w.embedding x).im = 0 := congrFun hx w
    apply w.embedding.injective
    rw [h.2.2.2]
    exact Complex.conj_eq_iff_im.2 him
  · intro hx
    funext w
    show (w.embedding x).im = 0
    have := h.2.2.2 w.embedding x
    rw [hx] at this
    exact Complex.conj_eq_iff_im.1 this.symm

end Fixed

theorem mem_dInv_imV_iff : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) →
    ∀ (j : ℕ) (x : E), (x ∈ dInv E j ∧ imV x = 0) ↔ ∃ y ∈ dInv F j, algebraMap F E y = x := by
  intro F E _ _ _ _ _ σ h hu j x
  have hIne : differentIdeal ℤ (𝓞 F) ^ j ≠ ⊥ := pow_ne_zero _ differentIdeal_ne_bot
  have hE : dInv E j = ((↑((differentIdeal ℤ (𝓞 F) ^ j).map (algebraMap (𝓞 F) (𝓞 E))) :
      FractionalIdeal (𝓞 E)⁰ E))⁻¹ := by
    rw [dInv_eq_inv_coe, differentIdeal_eq_map_of_unramified hu, Ideal.map_pow]
  constructor
  · rintro ⟨hx, him⟩
    obtain ⟨y, rfl⟩ := mem_range_of_cm_fixed h ((imV_eq_zero_iff h x).1 him)
    refine ⟨y, ?_, rfl⟩
    rw [dInv_eq_inv_coe]
    rw [hE] at hx
    exact (algebraMap_mem_inv_map_iff _ hIne y).1 hx
  · rintro ⟨y, hy, rfl⟩
    refine ⟨?_, (imV_eq_zero_iff h _).2 (σ.commutes y)⟩
    rw [hE]
    rw [dInv_eq_inv_coe] at hy
    exact (algebraMap_mem_inv_map_iff _ hIne y).2 hy

end GlobalTheory.SnMass.SkewVol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormStabilizerMeasureEqAnyNormalForm
section
open NumberField MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.Amp.StabHaar

theorem normalFormStabilizerMeasure_eq_any_normalForm : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : Fin (2 * r + k + 1) → ℂ) (n₁ n₂ g₀ : Mat k r) (β : Fin r → ℕ) (c : ℂ) (μR : Measure (Mt k r)), n₁ ∈ Nset k r → n₂ ∈ Nset k r → IsNormal0 k r hj β c z z' g₀ → IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) 1 μR → μR = (lebR0 k r j β).map (conjM n₂⁻¹) ∧ SigmaFinite (lebR0 k r j β) := by
  intro k r j hj z z' n₁ n₂ g₀ β c μR hn₁ hn₂ hg₀ hR
  obtain ⟨hz, hz', hT, -⟩ := id hR

  have hN : IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) 1 ((lebR0 k r j β).map (conjM n₂⁻¹)) := by
    unfold IsNormalFormStabilizerMeasure
    exact ⟨hz, hz', hT, n₁, hn₁, n₂, hn₂, g₀, β, c, hg₀, rfl, by rw [ENNReal.ofReal_one, one_smul]⟩
  obtain ⟨-, hcl, hHaar, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z z' _ 1 _ one_pos hN
  obtain ⟨-, -, hHaarR, -⟩ := GlobalTheory.Amp.StabMeas.stabilizer_measure_normalisation k r j hj z z' _ 1 μR one_pos hR

  obtain ⟨huniq, -, -⟩ := GlobalTheory.MatHaar.haar_unique_locFinite_openPos (2 * r + k + 1)
    (Rset k r (n₁ * g₀ * n₂)) ((lebR0 k r j β).map (conjM n₂⁻¹)) (matGroup hcl) hHaar
  obtain ⟨t, -, htop, ht⟩ := huniq μR hHaarR

  have hNt : IsNormalFormStabilizerMeasure k r hj z z' (n₁ * g₀ * n₂) t.toReal μR := by
    unfold IsNormalFormStabilizerMeasure
    exact ⟨hz, hz', hT, n₁, hn₁, n₂, hn₂, g₀, β, c, hg₀, rfl, by
      rw [ht, ENNReal.ofReal_toReal htop.ne, Measure.map_smul]⟩
  have h1 := normalFormStabilizerMeasure_scalar_le hj z z' _ 1 t.toReal μR hR hNt
  have h2 := normalFormStabilizerMeasure_scalar_le hj z z' _ t.toReal 1 μR hNt hR
  rw [ENNReal.ofReal_one, ENNReal.ofReal_toReal htop.ne] at h1 h2
  have ht1 : t = 1 := le_antisymm h2 h1
  obtain ⟨hH, -⟩ := GlobalTheory.T.stabilizer_haar_unimodular_normal k r j hj z z' g₀ β c hz hz' hT hg₀
  obtain ⟨hσ, -⟩ := hH
  exact ⟨by rw [ht, ht1, one_smul], hσ⟩

end GlobalTheory.Amp.StabHaar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdFundamentalDomainOfExtension
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN GlobalTheory.SnMass.SkewVol
open scoped TensorProduct ENNReal nonZeroDivisors Classical

namespace GlobalTheory

theorem prod_fundamentalDomain_of_extension : ∀ {V₁ V₂ : Type} [AddCommGroup V₁] [AddCommGroup V₂] (Λ : AddSubgroup (V₁ × V₂)) (D₁ : Set V₁) (D₂ : Set V₂), (∀ a : V₁, ∃! l, l ∈ {a : V₁ | (a, (0 : V₂)) ∈ Λ} ∧ a + l ∈ D₁) → (∀ b : V₂, ∃! l, l ∈ {b : V₂ | ∃ a : V₁, (a, b) ∈ Λ} ∧ b + l ∈ D₂) → ∀ v : V₁ × V₂, ∃! l, l ∈ Λ ∧ v + l ∈ D₁ ×ˢ D₂ := by
  intro V₁ V₂ _ _ Λ D₁ D₂ h1 h2 v
  obtain ⟨l₂, ⟨⟨s, hs⟩, hl₂D⟩, -⟩ := h2 v.2
  obtain ⟨l₁, ⟨hl₁, hl₁D⟩, -⟩ := h1 (v.1 + s)
  have hl₁' : ((l₁, 0) : V₁ × V₂) ∈ Λ := hl₁
  refine ⟨(s + l₁, l₂), ⟨?_, ?_⟩, ?_⟩
  · have e : ((s + l₁, l₂) : V₁ × V₂) = (s, l₂) + (l₁, 0) := by simp
    rw [e]; exact Λ.add_mem hs hl₁'
  · refine ⟨?_, ?_⟩
    · show v.1 + (s + l₁) ∈ D₁
      rw [← add_assoc]; exact hl₁D
    · exact hl₂D
  · rintro ⟨m₁, m₂⟩ ⟨hm, hmD⟩
    have hmD1 : v.1 + m₁ ∈ D₁ := hmD.1
    have hmD2 : v.2 + m₂ ∈ D₂ := hmD.2
    have e2 : m₂ = l₂ := (h2 v.2).unique ⟨⟨m₁, hm⟩, hmD2⟩ ⟨⟨s, hs⟩, hl₂D⟩
    subst e2
    have hx : ((m₁ - s, 0) : V₁ × V₂) ∈ Λ := by
      have := Λ.sub_mem hm hs
      simpa using this
    have e1 : m₁ - s = l₁ := (h1 (v.1 + s)).unique
      ⟨hx, by show v.1 + s + (m₁ - s) ∈ D₁; simpa using hmD1⟩ ⟨hl₁, hl₁D⟩
    have : m₁ = s + l₁ := by rw [← e1]; abel
    rw [this]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ReAntidiagonalEntryEqZeroOfFlagDepthStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.re_antidiagonal_entry_eq_zero_of_flagDepth : ∀ (k r : ℕ) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (a : Fin r), x ∈ Nset k r → Dep k r (2 * r - 2 * a.val) (x - 1) → (x (eI k r a) (esI k r a)).re = 0 := by
  first | exact @GlobalTheory.SnMass.VolN.re_corner_eq_zero | exact GlobalTheory.SnMass.VolN.re_corner_eq_zero | (intros; apply GlobalTheory.SnMass.VolN.re_corner_eq_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowEmbeddingMemIntegralOrthogonalGroupStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowE_mem_GN_of_form_add_trace_eq_zero : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (y : Fin (2 * r + k + 1) → E) (t : E), (∀ c : Fin r, c ≤ a → form (σ : E →+* E) J y (fun i => P i c.castSucc) = 0) → form (σ : E →+* E) J y y + t + σ t = 0 → (∀ c ∈ (dInv E (r - a.val))⁻¹, c • y ∈ Λ) → t ∈ dInv E (2 * (r - a.val)) → rowE (σ : E →+* E) J (fun i => P i a.castSucc) y t ∈ GN (σ : E →+* E) J Λ P := by
  first | exact @GlobalTheory.SnMass.VolN.RowIso.rowE_mem_GN | exact GlobalTheory.SnMass.VolN.RowIso.rowE_mem_GN | (intros; apply GlobalTheory.SnMass.VolN.RowIso.rowE_mem_GN <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RowIsometryEntriesInModelCoordinatesStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowIsometry_entries_in_modelCoordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ (a : Fin r) (y : Fin (2 * r + k + 1) → E) (t : E) (w : InfinitePlace E) (i j : Fin (2 * r + k + 1)), gM A (rowE (σ : E →+* E) J (fun i => P i a.castSucc) y t) w i j = (if i = j then 1 else 0) + (if j = esI k r a then (s a : ℂ) * (((A w).mulVec fun l => w.embedding (y l)) i + (if i = eI k r a then (s a : ℂ) * w.embedding t else 0)) else 0) - (if i = eI k r a then (s a : ℂ) * herm (Hpk k r) (bvec j) ((A w).mulVec fun l => w.embedding (y l)) else 0) := by
  first | exact @GlobalTheory.SnMass.VolN.rowE_entries | exact GlobalTheory.SnMass.VolN.rowE_entries | (intros; apply GlobalTheory.SnMass.VolN.rowE_entries <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualLatticeFrameEqStandardTranslateStatement
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG GlobalTheory.LocOver
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_lattice_frame_eq_standard_translate : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r : ℕ), ∀ (Fr : FrameD H r) (Λ : Submodule M.L.O V), H.IsSelfDual Λ → H.IsFrame Λ r Fr.f Fr.T → ∃ L : Submodule M.L.O (H.Wb Fr.f), Fr.IsInner L ∧ (L : Set (H.Wb Fr.f)) = H.Lset Λ Fr.f ∧ ∃ n ∈ Fr.N, (∀ b, n (Fr.f b) = Fr.f b) ∧ Λ = img n (Fr.LamStd L) := by
  first | exact @GlobalTheory.StdLat.eq_img_lamStd | exact GlobalTheory.StdLat.eq_img_lamStd | (intros; apply GlobalTheory.StdLat.eq_img_lamStd <;> assumption)
end

