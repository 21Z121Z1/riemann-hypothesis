import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.FrameInvMulVecNegativeVector
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsWeightBasisFiltration
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsAbsoluteValueOfIsDiscreteValuationRing
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0043
import Formalism.RealPlaceAnalysis.Bundle0003
import Formalism.RealPlaceAnalysis.Bundle0002
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0002
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ChainRuleSmooth.ExpIntertwine

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsFrameConjUnitaryBlockEqUnitaryComplement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.BesselFrame

open Formalism.FourierDecayAlt.P.SettingConstruction

section forms
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (H : Matrix ι ι ℂ)

lemma quasi_reflection (hH : Hᴴ = H) (u v : ι → ℂ)
    (huv : Formalism.QuantumDeterminants.herm H u u = Formalism.QuantumDeterminants.herm H v v)
    (hne : Formalism.QuantumDeterminants.herm H u u ≠ Formalism.QuantumDeterminants.herm H u v) :
    ∃ g : Matrix ι ι ℂ, gᴴ * H * g = H ∧ g *ᵥ u = v ∧
      ∀ x, Formalism.QuantumDeterminants.herm H x u = 0 → Formalism.QuantumDeterminants.herm H x v = 0 → g *ᵥ x = x := by
  set d := u - v with hd
  set s := Formalism.QuantumDeterminants.herm H u d with hs
  have hs' : s = Formalism.QuantumDeterminants.herm H u u - Formalism.QuantumDeterminants.herm H u v := by rw [hs, hd, herm_sub_right]
  have hs0 : s ≠ 0 := by rw [hs']; exact sub_ne_zero.mpr hne
  have hss : star s = Formalism.QuantumDeterminants.herm H u u - Formalism.QuantumDeterminants.herm H v u := by
    rw [hs, herm_symm H hH, hd, herm_sub_left]
  have hq : Formalism.QuantumDeterminants.herm H d d = s + star s := by
    rw [hss, hs', hd]
    simp only [herm_sub_left, herm_sub_right]
    linear_combination -huv
  set a : ℂ := s⁻¹ with ha'
  have ha : a * s = 1 := inv_mul_cancel₀ hs0
  have hsa : star a * star s = 1 := by rw [← star_mul', ha, star_one]
  refine ⟨rk H d 1 (-a), unitary_of_form H _ fun x y => ?_, ?_, fun x hxu hxv => ?_⟩
  · rw [rk_mulVec, rk_mulVec]
    have hY : star (Formalism.QuantumDeterminants.herm H y d) = Formalism.QuantumDeterminants.herm H d y := herm_symm H hH y d
    simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, star_mul', hY, hq,
      star_neg, star_one]
    linear_combination (star a * Formalism.QuantumDeterminants.herm H x d * Formalism.QuantumDeterminants.herm H d y) * ha +
      (a * Formalism.QuantumDeterminants.herm H x d * Formalism.QuantumDeterminants.herm H d y) * hsa
  · rw [rk_mulVec, ← hs, neg_mul, ha, hd]
    simp
  · rw [rk_mulVec, hd, herm_sub_right, hxu, hxv]
    simp

lemma exists_isometry (hH : Hᴴ = H) (u v : ι → ℂ)
    (huv : Formalism.QuantumDeterminants.herm H u u = Formalism.QuantumDeterminants.herm H v v) (h0 : Formalism.QuantumDeterminants.herm H u u ≠ 0) :
    ∃ g : Matrix ι ι ℂ, gᴴ * H * g = H ∧ g *ᵥ u = v ∧
      ∀ x, Formalism.QuantumDeterminants.herm H x u = 0 → Formalism.QuantumDeterminants.herm H x v = 0 → g *ᵥ x = x := by
  by_cases hne : Formalism.QuantumDeterminants.herm H u u = Formalism.QuantumDeterminants.herm H u v
  swap
  · exact quasi_reflection H hH u v huv hne
  have e1 : Formalism.QuantumDeterminants.herm H ((-1 : ℂ) • u) ((-1 : ℂ) • u) = Formalism.QuantumDeterminants.herm H u u := by
    simp only [herm_smul_left, herm_smul_right]; simp
  obtain ⟨g₁, h1, h2, h3⟩ := quasi_reflection H hH u ((-1 : ℂ) • u) e1.symm (by
    rw [herm_smul_right]
    intro h; apply h0
    simp only [star_neg, star_one] at h
    linear_combination h / 2)
  obtain ⟨g₂, k1, k2, k3⟩ := quasi_reflection H hH ((-1 : ℂ) • u) v (e1.trans huv) (by
    rw [e1, herm_smul_left, ← hne]
    intro h; apply h0
    linear_combination h / 2)
  refine ⟨g₂ * g₁, ?_, ?_, fun x hxu hxv => ?_⟩
  · calc (g₂ * g₁)ᴴ * H * (g₂ * g₁) = g₁ᴴ * (g₂ᴴ * H * g₂) * g₁ := by
          rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
      _ = H := by rw [k1, h1]
  · rw [← Matrix.mulVec_mulVec, h2, k2]
  · have : Formalism.QuantumDeterminants.herm H x ((-1 : ℂ) • u) = 0 := by rw [herm_smul_right, hxu, mul_zero]
    rw [← Matrix.mulVec_mulVec, h3 x hxu this, k3 x this hxv]

end forms

open PI.UpqRep PI.HwUniqW

variable {k r : ℕ}

lemma herm_right_bvec (y : Fin (2 * r + k + 1) → ℂ) (i : Fin (2 * r + k + 1)) :
    Formalism.QuantumDeterminants.herm (Hpk k r) y (bvec i) = epsI k r i * y (piI k r i) := by
  rw [← Hpk_mulVec_apply]
  simp [Formalism.QuantumDeterminants.herm, bvec, Pi.star_single]

lemma herm_bvec_eq_zero {y : Fin (2 * r + k + 1) → ℂ} (hy : inWb k r y) {i : Fin (2 * r + k + 1)}
    (hi : i.val < r ∨ r + k < i.val) : Formalism.QuantumDeterminants.herm (Hpk k r) (bvec i) y = 0 := by
  rw [← herm_symm _ Hpk_conjTranspose, herm_right_bvec, hy (piI k r i), mul_zero, star_zero]
  rw [piI_val]
  have := i.isLt
  split_ifs <;> omega

lemma exists_isFrameW (z : Fin (2 * r + k + 1) → ℂ) (hz : inWb k r z) (hT : 0 < Tz k r z) :
    ∃ g, IsFrameW k r z g := by
  set T := Tz k r z with hTdef
  set u : Fin (2 * r + k + 1) → ℂ := ((Real.sqrt T : ℝ) : ℂ) • bvec (wI k r (Fin.last k)) with hu
  have hw : Formalism.QuantumDeterminants.herm (Hpk k r) (bvec (wI k r (Fin.last k))) (bvec (wI k r (Fin.last k))) = -1 := by
    have hp : piI k r (wI k r (Fin.last k)) = wI k r (Fin.last k) := by
      unfold piI; rw [if_pos (by simp [wI])]
    rw [herm_right_bvec, hp, bvec_apply, if_pos rfl]
    simp [epsI, wI]
  have huu : Formalism.QuantumDeterminants.herm (Hpk k r) u u = -(T : ℂ) := by
    rw [hu, herm_smul_left, herm_smul_right, hw]
    have h1 : star ((Real.sqrt T : ℝ) : ℂ) = ((Real.sqrt T : ℝ) : ℂ) := Complex.conj_ofReal _
    have h2 : ((Real.sqrt T : ℝ) : ℂ) * ((Real.sqrt T : ℝ) : ℂ) = (T : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hT.le]
    rw [h1]
    linear_combination -h2
  have hzz : Formalism.QuantumDeterminants.herm (Hpk k r) z z = -(T : ℂ) := by
    have h1 : star (Formalism.QuantumDeterminants.herm (Hpk k r) z z) = Formalism.QuantumDeterminants.herm (Hpk k r) z z :=
      herm_symm _ Hpk_conjTranspose z z
    have h2 : T = -(Formalism.QuantumDeterminants.herm (Hpk k r) z z).re := rfl
    rw [h2, Complex.ofReal_neg, neg_neg]
    exact (Complex.conj_eq_iff_re.mp h1).symm
  have huW : inWb k r u := by
    intro i hi
    rw [hu, Pi.smul_apply, bvec_apply, if_neg, smul_zero]
    rintro rfl
    simp [wI] at hi
  obtain ⟨g, h1, h2, h3⟩ := exists_isometry (Hpk k r) Hpk_conjTranspose u z (huu.trans hzz.symm) (by
    rw [huu, neg_ne_zero]; exact_mod_cast hT.ne')
  refine ⟨g, h1, fun a => ⟨?_, ?_⟩, h2⟩
  · have ha : (eI k r a).val < r ∨ r + k < (eI k r a).val := Or.inl a.isLt
    exact h3 _ (herm_bvec_eq_zero huW ha) (herm_bvec_eq_zero hz ha)
  · have ha : (esI k r a).val < r ∨ r + k < (esI k r a).val := by
      have := a.isLt
      right; simp only [esI]; omega
    exact h3 _ (herm_bvec_eq_zero huW ha) (herm_bvec_eq_zero hz ha)

lemma blockW_fix (x : Matrix (Fin k) (Fin k) ℂ) {j : Fin (2 * r + k + 1)} (hj : ¬ InB k r j) :
    blockW k r x *ᵥ bvec j = bvec j := by
  funext i
  rw [mulVec_bvec_apply, bvec_apply]
  by_cases hi : InB k r i
  · rw [blockW_in_out _ hi hj, if_neg (ne_of_inB hi hj)]
  · rw [blockW_out _ hi]

lemma blockW_mem_UH {x : Matrix (Fin k) (Fin k) ℂ} (hx : x ∈ UJset (allPos k)) :
    blockW k r x ∈ UH (Hpk k r) := by
  show (blockW k r x)ᴴ * Hpk k r * blockW k r x = Hpk k r
  rw [blockW_conjTranspose, ← Hpk_blockW_comm, Matrix.mul_assoc, blockW_mul, mem_UJset_allPos.mp hx,
    blockW_one, Matrix.mul_one]

lemma conj_mem_UW {z : Fin (2 * r + k + 1) → ℂ} {g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hg : IsFrameW k r z g) {x : Matrix (Fin k) (Fin k) ℂ} (hx : x ∈ UJset (allPos k)) :
    g * blockW k r x * g⁻¹ ∈ UWset k r z := by
  refine ⟨mul_mem_UH (mul_mem_UH hg.1 (blockW_mem_UH hx)) (inv_mem_UH hg.1), fun a => ⟨?_, ?_⟩, ?_⟩
  · have := a.isLt
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_fix hg.1 (hg.2.1 a).1,
      blockW_fix x (by unfold InB eI; simp only; omega), (hg.2.1 a).1]
  · have := a.isLt
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, inv_fix hg.1 (hg.2.1 a).2,
      blockW_fix x (by unfold InB esI; simp only; omega), (hg.2.1 a).2]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, frame_inv_mulVec_negativeVector hg, Matrix.mulVec_smul,
      blockW_fix x (by unfold InB wI; simp), hg.2.2]

theorem frame_exists : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → ∃ g, PI.UpqRep.IsFrameW k r z g ∧ (∀ x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), g * PI.UpqRep.blockW k r x * g⁻¹ ∈ Formalism.QuantumDeterminants.UWset k r z) ∧ ∀ y ∈ Formalism.QuantumDeterminants.UWset k r z, ∃ x ∈ PI.UpqRep.UJset (PI.UpqRep.allPos k), y = g * PI.UpqRep.blockW k r x * g⁻¹ := by
  intro k r z hz hT
  have hT' : 0 < PI.UpqRep.Tz k r z := hT
  obtain ⟨g, hg⟩ := exists_isFrameW z hz hT'
  refine ⟨g, hg, fun x hx => conj_mem_UW hg hx, fun y hy => ?_⟩
  obtain ⟨x, hx, -, e⟩ := UW_eq_conj hT' hg hy
  exact ⟨x, hx, e⟩

end GlobalTheory.BesselFrame
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsAlgClosedAddValuationIsAdicComplete
section
namespace GlobalTheory

open scoped NNReal

theorem expNegTop_inj_of_eq {a b : WithTop ℚ} (h : expNegTop a = expNegTop b) : a = b :=
  le_antisymm ((expNegTop_le_iff _ _).1 h.ge) ((expNegTop_le_iff _ _).1 h.le)

noncomputable def expNegAbsoluteValue {F : Type} [Field F] (v : AddValuation F (WithTop ℚ)) :
    AbsoluteValue F ℝ where
  toFun x := (expNegValuation v x : ℝ)
  map_mul' x y := by rw [map_mul, NNReal.coe_mul]
  nonneg' x := NNReal.coe_nonneg _
  eq_zero' x := by rw [NNReal.coe_eq_zero, Valuation.zero_iff]
  add_le' x y := by
    have h := (expNegValuation v).map_add x y
    have h' : expNegValuation v (x + y) ≤ expNegValuation v x + expNegValuation v y :=
      h.trans (max_le le_self_add le_add_self)
    exact_mod_cast h'

theorem isNonarchimedean_expNegAbsoluteValue {F : Type} [Field F]
    (v : AddValuation F (WithTop ℚ)) : IsNonarchimedean (expNegAbsoluteValue v) := by
  intro x y
  have h := (expNegValuation v).map_add x y
  change ((expNegValuation v (x + y) : ℝ≥0) : ℝ) ≤
    max ((expNegValuation v x : ℝ≥0) : ℝ) ((expNegValuation v y : ℝ≥0) : ℝ)
  exact_mod_cast h

theorem exists_norm_eq_of_completion {K : Type*} [NormedField K] [IsUltrametricDist K]
    (x : UniformSpace.Completion K) : ∃ y : K, ‖x‖ = ‖y‖ := by
  haveI : IsUltrametricDist (UniformSpace.Completion K) := IsUltrametricDist.of_normedAlgebra K
  rcases eq_or_ne x 0 with rfl | hx
  · exact ⟨0, by simp⟩
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.1 (UniformSpace.Completion.denseRange_coe (α := K)) x
    ‖x‖ (norm_pos_iff.2 hx)
  refine ⟨y, ?_⟩
  rw [← UniformSpace.Completion.norm_coe y]
  rw [dist_comm, dist_eq_norm] at hy
  have h := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := x) (y := y - x) hy.ne'
  rw [add_sub_cancel, max_eq_left hy.le] at h
  exact h.symm

theorem exists_addValuation_expNegTop_eq_nnnorm {C : Type} [NormedField C] [IsUltrametricDist C]
    (h : ∀ x : C, ∃ t : WithTop ℚ, expNegTop t = ‖x‖₊) :
    ∃ v : AddValuation C (WithTop ℚ), ∀ x, expNegTop (v x) = ‖x‖₊ := by
  choose f hf using h
  refine ⟨AddValuation.of f ?_ ?_ ?_ ?_, hf⟩
  · apply expNegTop_inj_of_eq
    rw [hf, nnnorm_zero, expNegTop_top]
  · apply expNegTop_inj_of_eq
    rw [hf, nnnorm_one, expNegTop_zero]
  · intro x y
    rcases le_max_iff.1 (IsUltrametricDist.nnnorm_add_le_max x y) with h | h
    · exact min_le_of_left_le ((expNegTop_le_iff _ _).1 (by rwa [hf, hf]))
    · exact min_le_of_right_le ((expNegTop_le_iff _ _).1 (by rwa [hf, hf]))
  · intro x y
    apply expNegTop_inj_of_eq
    rw [expNegTop_add, hf, hf, hf, nnnorm_mul]

theorem exists_isAlgClosed_addValuation_isAdicComplete :
    ∀ (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [CharZero F₀] (v₀ : AddValuation F₀ (WithTop ℚ))
      (p : ℕ), p.Prime → 0 < v₀ (p : F₀) →
      ∃ (F : Type) (_ : Field F) (_ : IsAlgClosed F) (_ : CharZero F) (e : F₀ →+* F)
        (v : AddValuation F (WithTop ℚ)), (∀ x, v (e x) = v₀ x) ∧
        IsAdicComplete (Ideal.span {(p : ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v)})
          (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) := by
  intro F₀ _ _ _ v₀ p hp hv
  let w := expNegAbsoluteValue v₀
  have hw : ∀ x, w x = (expNegTop (v₀ x) : ℝ) := fun _ => rfl
  have hp1 : w (p : F₀) < 1 := by
    rw [hw, ← NNReal.coe_one, NNReal.coe_lt_coe, ← expNegTop_zero, ← not_le, expNegTop_le_iff]
    exact not_le.2 hv
  have hp0 : 0 < w (p : F₀) := w.pos (Nat.cast_ne_zero.2 hp.ne_zero)
  letI : NontriviallyNormedField (WithAbs w) :=
    { (inferInstance : NormedField (WithAbs w)) with
      non_trivial := ⟨(WithAbs.toAbs w (p : F₀))⁻¹, by
        rw [norm_inv]
        change 1 < (w (p : F₀))⁻¹
        exact (one_lt_inv₀ hp0).2 hp1⟩ }
  haveI : IsUltrametricDist (WithAbs w) :=
    IsUltrametricDist.isUltrametricDist_of_forall_norm_add_le_max_norm fun x y =>
      isNonarchimedean_expNegAbsoluteValue v₀ x.ofAbs y.ofAbs
  haveI : IsAlgClosed (WithAbs w) := IsAlgClosed.of_ringEquiv F₀ _ (WithAbs.equiv w).symm
  let C := UniformSpace.Completion (WithAbs w)
  letI : NontriviallyNormedField C := completionNontriviallyNormedField (WithAbs w)
  haveI : IsUltrametricDist C := IsUltrametricDist.of_normedAlgebra (WithAbs w)
  haveI : IsAlgClosed C :=
    isAlgClosed_of_denseRange (K := WithAbs w) UniformSpace.Completion.denseRange_coe
  let e : F₀ →+* C := (algebraMap (WithAbs w) C).comp (WithAbs.equiv w).symm.toRingHom
  have he : ∀ x, ‖e x‖₊ = expNegTop (v₀ x) := fun x =>
    NNReal.coe_injective (UniformSpace.Completion.norm_coe (WithAbs.toAbs w x))
  haveI : CharZero C := charZero_of_injective_ringHom e.injective
  obtain ⟨v, hvC⟩ := exists_addValuation_expNegTop_eq_nnnorm (C := C) fun x => by
    obtain ⟨y, hy⟩ := exists_norm_eq_of_completion x
    exact ⟨v₀ y.ofAbs, NNReal.coe_injective hy.symm⟩
  have hmem : ∀ x : C, NormedField.valuation x ≤ 1 ↔ 0 ≤ v x := fun x => by
    rw [NormedField.valuation_apply, ← hvC, ← expNegTop_zero, expNegTop_le_iff]
  have hO : (NormedField.valuation (K := C)).Integers (ReciprocityTheory.ChartRestriction.G.DVR.TWO.Ov v) :=
    ⟨Subtype.val_injective, fun x => (hmem _).2 x.2, fun r hr => ⟨⟨r, (hmem r).1 hr⟩, rfl⟩⟩
  refine ⟨C, inferInstance, inferInstance, inferInstance, e, v,
    fun x => expNegTop_inj_of_eq (by rw [hvC, he]),
    NormIntegers.isAdicComplete_span_singleton hO ?_⟩
  rw [map_natCast, ← map_natCast e, ← coe_nnnorm, he, ← hw]
  exact hp1

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExpMemUnipotentAndHasDerivAtCharacter
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal Nat

noncomputable section

namespace GlobalTheory.UnipotentExp

set_option backward.isDefEq.respectTransparency false in

theorem exp_apply_of_pattern {n : ℕ} (P : Fin n → Fin n → Prop)
    (htr : ∀ i m j, P i m → P m j → P i j) (Y : Matrix (Fin n) (Fin n) ℂ)
    (hY : ∀ i j, ¬ P i j → Y i j = 0) (i j : Fin n) (hij : ¬ P i j) :
    NormedSpace.exp Y i j = if i = j then 1 else 0 := by
  have hp : ∀ m : ℕ, ∀ i j, ¬ P i j → (Y ^ (m + 1)) i j = 0 := by
    intro m
    induction m with
    | zero => simpa using hY
    | succ m ih =>
      intro i j h
      rw [pow_succ, Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases h1 : P i l
      · rw [hY l j (fun h2 => h (htr _ _ _ h1 h2)), mul_zero]
      · rw [ih i l h1, zero_mul]
  have h1 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m)) (NormedSpace.exp Y) := by
    open scoped Matrix.Norms.Operator in
    exact NormedSpace.exp_series_hasSum_exp' (𝕂 := ℂ) Y
  have h2 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) i j) (NormedSpace.exp Y i j) :=
    Pi.hasSum.1 (Pi.hasSum.1 h1 i) j
  have h3 : HasSum (fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) i j) (((0 ! : ℂ)⁻¹ • Y ^ 0) i j) := by
    refine hasSum_single (f := fun m : ℕ => ((m ! : ℂ)⁻¹ • Y ^ m) i j) 0 ?_
    intro m hm
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [Matrix.smul_apply, hp m i j hij, smul_zero]
  rw [h2.unique h3]
  simp [Matrix.one_apply]

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hasDerivAt_exp_apply {k r : ℕ} (X : Mx k r) (i j : Fin (2 * r + k + 1)) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X) i j) (X i j) 0 := by
  have hγ := Formalism.REAL.hasDerivAt_mul_exp_smul_zero (1 : Mx k r) X
  simp only [Matrix.one_mul] at hγ
  exact hasDerivAt_pi.1 (hasDerivAt_pi.1 hγ i) j

theorem hasDerivAt_ell {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r) :
    HasDerivAt (fun t : ℝ => Formalism.QuantumDeterminants.ell k r z (NormedSpace.exp ((t : ℂ) • X)))
      (Formalism.QuantumDeterminants.ell k r z X) 0 := by
  unfold Formalism.QuantumDeterminants.ell
  refine HasDerivAt.fun_sum fun a _ => ?_
  by_cases h : a.val + 1 < r
  · simp only [dif_pos h]
    exact hasDerivAt_exp_apply X _ _
  · simp only [dif_neg h, Matrix.mulVec, dotProduct]
    exact HasDerivAt.fun_sum fun j _ => (hasDerivAt_exp_apply X _ _).mul_const _

theorem ell_one {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : Formalism.QuantumDeterminants.inWb k r z) :
    Formalism.QuantumDeterminants.ell k r z 1 = 0 := by
  unfold Formalism.QuantumDeterminants.ell
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with h
  · refine Matrix.one_apply_ne ?_
    intro e
    have := congrArg Fin.val e
    simp [Formalism.QuantumDeterminants.eI] at this
  · rw [Matrix.one_mulVec]
    exact hz _ (Or.inl a.isLt)

theorem exp_mem_and_deriv : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (X : Mx k r), Formalism.QuantumDeterminants.inWb k r z → PI.UpqRep.InLieHpk k r X → (∀ i j : Fin (2 * r + k + 1), ¬ (i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k)) → X i j = 0) → (∀ t : ℝ, NormedSpace.exp ((t : ℂ) • X) ∈ Formalism.QuantumDeterminants.Nset k r) ∧ HasDerivAt (fun t : ℝ => Formalism.QuantumDeterminants.psi k r z Formalism.QuantumDeterminants.cStd (NormedSpace.exp ((t : ℂ) • X))) (Formalism.QuantumDeterminants.ell k r z X - star (Formalism.QuantumDeterminants.ell k r z X)) 0 := by
  intro k r z X hz hX hP
  refine ⟨fun t => ?_, ?_⟩
  · have key := exp_apply_of_pattern
      (fun i j : Fin (2 * r + k + 1) => i < j ∧ ¬ (r ≤ i.val ∧ j.val ≤ r + k))
      (fun i m j h1 h2 => by
        simp only [Fin.lt_def] at h1 h2 ⊢
        omega)
      ((t : ℂ) • X) (fun i j h => by rw [Matrix.smul_apply, hP i j h, smul_zero])
    refine ⟨CCRuleCW.exp_mem_UH _ _ (CCRuleCW.lie_smul _ X hX t), fun a i h => key _ _ ?_,
      fun i j h1 h2 h3 => key _ _ ?_⟩
    · simp only [Fin.lt_def, Formalism.QuantumDeterminants.eI]
      omega
    · tauto
  · have h1 := (hasDerivAt_ell z X).const_mul Formalism.QuantumDeterminants.cStd
    have h2 : HasDerivAt (fun t : ℝ => (Formalism.QuantumDeterminants.cStd *
        Formalism.QuantumDeterminants.ell k r z (NormedSpace.exp ((t : ℂ) • X))).re)
        (Formalism.QuantumDeterminants.cStd * Formalism.QuantumDeterminants.ell k r z X).re 0 :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    have h3 := (h2.ofReal_comp.const_mul Complex.I).cexp
    unfold Formalism.QuantumDeterminants.psi
    convert h3 using 1
    simp only [Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero, ell_one hz, mul_zero,
      Complex.zero_re, Complex.exp_zero, one_mul]
    apply Complex.ext <;> simp [Formalism.QuantumDeterminants.cStd]
    ring

end GlobalTheory.UnipotentExp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FactorisationOfConjHomogeneousAndHomogeneous
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem factorisation_of_two_partial_integrations : ∀ (T Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] (l : T → Wp) (l' : T → Wq) (J : T → T → (Wq →L[ℂ] Wp) → (Wq →L[ℂ] Wp)) (A : T → Wq → Wq → Wp) (Bb : T → Wp → Wq → Wp), (∀ y a c (t : ℂ), A y (t • a) c = star t • A y a c) → (∀ x b c (t : ℂ), Bb x (t • b) c = t • Bb x b c) → (∀ x y X c, J x y X c = A y (ContinuousLinearMap.adjoint X (l x)) c) → (∀ x y X c, J x y X c = Bb x (X (l' y)) c) → ∃ OO : Wq →L[ℂ] Wp, ∀ x y X, J x y X = ⟪l x, X (l' y)⟫_ℂ • OO := by
  intro T Wp Wq _ _ _ _ _ _ l l' J A Bb hA hB hJA hJB
  by_cases h1 : ∀ x, l x = 0
  · refine ⟨0, fun x y X => ?_⟩
    ext c
    have h0 := hA y 0 c 0
    rw [hJA, h1 x, map_zero]
    simpa using h0
  by_cases h2 : ∀ y, l' y = 0
  · refine ⟨0, fun x y X => ?_⟩
    ext c
    have h0 := hB x 0 c 0
    rw [hJB, h2 y, map_zero]
    simpa using h0
  push Not at h1 h2
  obtain ⟨x₀, hx⟩ := h1
  obtain ⟨y₀, hy⟩ := h2
  have hadj : ∀ (a : Wq) (b v : Wp),
      ContinuousLinearMap.adjoint ((innerSL ℂ a).smulRight b) v = ⟪b, v⟫_ℂ • a := by
    intro a b v
    refine ext_inner_right ℂ fun w => ?_
    rw [ContinuousLinearMap.adjoint_inner_left, inner_smul_left]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_right,
      inner_conj_symm]
    ring
  have hp : ⟪l x₀, l x₀⟫_ℂ ≠ 0 := fun h => hx (inner_self_eq_zero.mp h)
  have hq : ⟪l' y₀, l' y₀⟫_ℂ ≠ 0 := fun h => hy (inner_self_eq_zero.mp h)
  have key : ∀ y a c, A y a c = (⟪a, l' y⟫_ℂ * (⟪l x₀, l x₀⟫_ℂ)⁻¹) • Bb x₀ (l x₀) c := by
    intro y a c
    have e1 := hJA x₀ y ((innerSL ℂ a).smulRight (l x₀)) c
    have e2 := hJB x₀ y ((innerSL ℂ a).smulRight (l x₀)) c
    rw [hadj, hA] at e1
    rw [ContinuousLinearMap.smulRight_apply, hB, innerSL_apply_apply, e1] at e2
    have hs : star ⟪l x₀, l x₀⟫_ℂ = ⟪l x₀, l x₀⟫_ℂ := inner_conj_symm (𝕜 := ℂ) _ _
    rw [hs] at e2
    rw [mul_comm, mul_smul, ← e2, smul_smul, inv_mul_cancel₀ hp, one_smul]
  refine ⟨((⟪l' y₀, l' y₀⟫_ℂ)⁻¹ * (⟪l x₀, l x₀⟫_ℂ)⁻¹) •
    J x₀ y₀ ((innerSL ℂ (l' y₀)).smulRight (l x₀)), fun x y X => ?_⟩
  ext c
  rw [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply, hJB x₀,
    ContinuousLinearMap.smulRight_apply, hB, innerSL_apply_apply, hJA, key,
    ContinuousLinearMap.adjoint_inner_left, smul_smul, smul_smul]
  congr 1
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FreeAlgebraActionCapelliDeterminantEqOperator
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CapelliFreeAction

theorem map_qdet {A B : Type} [Ring A] [Algebra ℂ A] [Ring B] [Algebra ℂ B] {n : ℕ}
    (φ : A →ₐ[ℂ] B) (E : Fin n → Fin n → A) (u : ℂ) :
    φ (Formalism.REAL.qdet E u) = Formalism.REAL.qdet (fun a b => φ (E a b)) u := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, map_intCast, map_list_prod, List.map_ofFn]
  congr 3
  funext k
  simp only [Function.comp, Formalism.REAL.Tm]
  split_ifs <;> simp

theorem actU_qdet : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H) (E : Fin n → Fin n → Module.End ℂ S), (∀ a b (v : S), ((E a b v : S) : H) = PI.DSInfCharCap.dsigC ε σ (PI.DSInfCharCap.unitM (a, b)) v) → ∀ (u : ℂ) (v : S), PI.DSInfCharCap.actU ε σ (Formalism.REAL.qdet (PI.DSInfCharCap.Egl n) u) v = ((Formalism.REAL.qdet E u v : S) : H) := by
  intro n ε H _ _ σ S E hE u v
  let F : FreeMonoid (Fin n × Fin n) →* Module.End ℂ S := FreeMonoid.lift fun ab => E ab.1 ab.2
  let ψ : MonoidAlgebra ℂ (FreeMonoid (Fin n × Fin n)) →ₐ[ℂ] Module.End ℂ S :=
    MonoidAlgebra.lift ℂ _ _ F
  let φ : FreeAlgebra ℂ (Fin n × Fin n) →ₐ[ℂ] Module.End ℂ S :=
    ψ.comp (FreeAlgebra.equivMonoidAlgebraFreeMonoid : FreeAlgebra ℂ (Fin n × Fin n) ≃ₐ[ℂ] _).toAlgHom
  have hw : ∀ l : List (Fin n × Fin n),
      PI.DSInfCharCap.dsigCW ε σ (l.map PI.DSInfCharCap.unitM) (v : H) =
        ((F (FreeMonoid.ofList l) v : S) : H) := by
    intro l
    induction l with
    | nil => simp [PI.DSInfCharCap.dsigCW]
    | cons a l ih =>
      rw [List.map_cons, PI.DSInfCharCap.dsigCW, ih, FreeMonoid.ofList_cons, map_mul,
        Module.End.mul_apply, ← hE a.1 a.2]
      simp [F]
  have hφ : ∀ p, PI.DSInfCharCap.actU ε σ p v = ((φ p v : S) : H) := by
    intro p
    have : φ p = ψ (FreeAlgebra.equivMonoidAlgebraFreeMonoid p) := rfl
    rw [this]
    simp only [ψ, MonoidAlgebra.lift_apply, PI.DSInfCharCap.actU, Finsupp.sum,
      LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply, Submodule.coe_smul]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [hw]
    rfl
  have hE' : (fun a b => φ (PI.DSInfCharCap.Egl n a b)) = E := by
    funext a b
    simp [φ, ψ, F, PI.DSInfCharCap.Egl, FreeAlgebra.equivMonoidAlgebraFreeMonoid]
  rw [hφ, map_qdet, hE']

end GlobalTheory.CapelliFreeAction
end

