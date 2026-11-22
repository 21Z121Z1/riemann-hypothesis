import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0043
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.IsSmoothHermConstLine
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0029
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0033
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0084
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0064
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0072
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0011
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MemDivSuppOfDivCycleNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.DimOfMinimal

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PShiftIntersectionPolynomial
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
open GroundTheory.Heights₂.Heights.Inter (famExt famExt_apply)

noncomputable section

namespace ShiftIntersectionPolynomial

theorem prod_weights {n : ℕ} (q : ℝ) (s : Fin n → Fin 2) :
    ∏ j, (![q, 1] : Fin 2 → ℝ) (s j) = q ^ (Finset.univ.filter fun j => s j = 0).card := by
  have h : ∀ j, (![q, 1] : Fin 2 → ℝ) (s j) = if s j = 0 then q else 1 := by
    intro j
    rcases Fin.exists_fin_two.mp ⟨s j, rfl⟩ with h | h <;> rw [h] <;> simp
  simp only [h, Finset.prod_ite, Finset.prod_const, one_pow, mul_one]

theorem proof : ShiftIntersectionPolynomial.Statement := by
  intro K _ ι _ II P n A B hII hP hA hB
  have hI : IsIntersectionFamily (II K ι) := hII K ι
  set e : Fin 2 → HermLine ι := ![A, B] with he_def
  have he : ∀ i, IsSmoothHerm (e i) := by
    intro i
    rcases Fin.exists_fin_two.mp ⟨i, rfl⟩ with h | h <;> rw [h] <;> simpa [e]
  refine ⟨∑ s : Fin n → Fin 2, Polynomial.C (II K ι P n (e ∘ s)) *
      Polynomial.X ^ (Finset.univ.filter fun j => s j = 0).card, ?_, ?_, ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun s _ => ?_
    refine (Polynomial.natDegree_C_mul_X_pow_le _ _).trans ?_
    exact (Finset.card_filter_le _ _).trans (by simp)
  · rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single (fun _ => 0)]
    · rw [Polynomial.coeff_C_mul_X_pow]
      have hc : (Finset.univ.filter fun j : Fin n => (fun _ : Fin n => (0 : Fin 2)) j = 0).card = n := by simp
      rw [if_pos hc.symm]
      rfl
    · intro s _ hs
      rw [Polynomial.coeff_C_mul_X_pow, if_neg]
      intro hc
      apply hs
      have hu : (Finset.univ.filter fun j => s j = 0) = Finset.univ :=
        Finset.eq_univ_of_card _ (by rw [← hc, Fintype.card_fin])
      funext j
      have := Finset.filter_eq_self.mp hu j (Finset.mem_univ j)
      exact this
    · intro h
      exact absurd (Finset.mem_univ _) h
  · intro q
    set Z := HermLine.zcomb A B (q : ℤ) 1 with hZ_def
    have hZ : IsSmoothHerm Z := ZCombLimit.isSmoothHerm_zcomb_int hA hB _ _
    have hposition : ∀ (L : Fin n → HermLine ι) (a : Fin n), (∀ j, IsSmoothHerm (L j)) →
        II K ι P n (Function.update L a Z) =
          (![(q : ℝ), 1] : Fin 2 → ℝ) 0 * II K ι P n (Function.update L a (e 0)) +
            (![(q : ℝ), 1] : Fin 2 → ℝ) 1 * II K ι P n (Function.update L a (e 1)) := by
      intro L a hL
      cases n with
      | zero => exact a.elim0
      | succ m =>
        have h := ZCombLimit.fam_update_zcomb_int hI hP L hL a hA hB (q : ℤ) 1
        simp only [Int.cast_natCast, Int.cast_one, one_mul] at h
        simpa [e] using h
    have key := ZCombLimit.eq_famExt_of_position (J := II K ι) (P := P) IsSmoothHerm e Z ![(q : ℝ), 1] he hZ hposition
      Finset.univ (fun _ => 0)
    simp only [Finset.mem_univ, if_true] at key
    rw [key, famExt_apply, Polynomial.eval_finsetSum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [prod_weights, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

end ShiftIntersectionPolynomial

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PSmallSectionPointHeight
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

noncomputable section

set_option linter.unusedSectionVars false

namespace SmallSectionPointHeight

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem aeval_eq_eval_mConeMap (y : (Σ k, ι k) → Ω) (f : MRing ι) :
    aeval y f = eval (fun _ ↦ (1 : Ω)) (mConeMap y f) := by
  induction f using MvPolynomial.induction_on with
  | C c => simp [mConeMap]
  | add p q hp hq => rw [map_add, map_add, map_add, hp, hq]
  | mul_X p n hp =>
    rw [map_mul, map_mul, map_mul, hp]
    simp [mConeMap]

theorem notMem_mCoordIdeal {y : (Σ k, ι k) → Ω} {f : MRing ι} (hf : aeval y f ≠ 0) :
    f ∉ mCoordIdeal y := by
  intro h
  rw [mCoordIdeal, RingHom.mem_ker] at h
  exact hf (by rw [aeval_eq_eval_mConeMap, h, map_zero])

theorem coord_ne_zero {y : (Σ k, ι k) → Ω} {p : Σ k, ι k} (hp : (X p : MRing ι) ∉ mCoordIdeal y) :
    y p ≠ 0 := by
  intro h0
  apply hp
  rw [mCoordIdeal, RingHom.mem_ker]
  simp [mConeMap, h0]

theorem powLine_h (A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (m : ℕ) (z : (Σ k, ι k) → ℂ) :
    (IndefiniteRowSideFullHecke.HeightsSet.powLine A m).h z = A.h z ^ m := by
  induction m with
  | zero => simp [IndefiniteRowSideFullHecke.HeightsSet.powLine, IndefiniteRowSideFullHecke.HeightsSet.constLine]
  | succ m ih => simp [IndefiniteRowSideFullHecke.HeightsSet.powLine, ReciprocityTheory.ChartRestriction.G.Geo.HermLine.tensor, ih, pow_succ]

theorem aeval_chartMon (y : (Σ k, ι k) → Ω) (c : (k : K) → ι k) (e : K → ℕ) :
    aeval y (IndefiniteRowSideFullHecke.HeightsSet.chartMon c e) = ∏ k, y ⟨k, c k⟩ ^ e k := by
  simp [IndefiniteRowSideFullHecke.HeightsSet.chartMon, map_prod, map_pow]

theorem vertR_le {W : Ideal (MRing ι)} {G H : MRing ι}
    (h : ∀ V ∈ divSupp W H, V ∈ divSupp W G ∧
      multAt (W ⊔ Ideal.span {H}) V ≤ multAt (W ⊔ Ideal.span {G}) V) :
    vertR W (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) H ≤ vertR W (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) G := by
  classical
  unfold vertR
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite W H),
    finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite W G)]
  have hsub : (divSupp_finite W H).toFinset ⊆ (divSupp_finite W G).toFinset := fun V hV ↦ by
    rw [Set.Finite.mem_toFinset] at hV ⊢
    exact (h V hV).1
  have hc : ∀ V : Ideal (MRing ι), 0 ≤ (if IsHorizontal V then (0 : ℝ) else
      (geoNum 0 V (fun j ↦ ((Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j).a) : ℝ) * Real.log (charOf V)) := by
    intro V
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (by exact_mod_cast IndefiniteRowSideFullHecke.HeightsSet.geoNum_zero_nonneg V _)
        (Real.log_natCast_nonneg _)
  refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg hsub fun V _ _ ↦
    mul_nonneg (Nat.cast_nonneg _) (hc V))
  refine Finset.sum_le_sum fun V hV ↦ ?_
  rw [Set.Finite.mem_toFinset] at hV
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast (h V hV).2) (hc V)

end SmallSectionPointHeight

open SmallSectionPointHeight in

theorem SmallSectionPointHeight.proof (hOrd : SectionOrderAtPoint.Statement) :
    SmallSectionPointHeight.Statement := by
  intro K _ ι _ Ω _ y D A τ s II hII hP hbir hA hτ hs hs0 hsmall
  classical

  choose c hc using hP.2.1.2.2
  have hyc : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k ↦ coord_ne_zero (hc k)

  set ap : K → ℕ := fun k ↦ ((τ : ℤ) * A.a k).toNat with hap
  set an : K → ℕ := fun k ↦ (-((τ : ℤ) * A.a k)).toNat with han
  have hpn : ∀ k, (ap k : ℤ) = an k + τ * A.a k := fun k ↦ by
    have := Int.toNat_sub_toNat_neg ((τ : ℤ) * A.a k)
    simp only [hap, han]
    linarith
  obtain ⟨d, g0, h0, hg0, hh0, hh0y, hgh0⟩ := hbir (s * ∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * A.a k)))
  set G := g0 * IndefiniteRowSideFullHecke.HeightsSet.chartMon c ap with hGdef
  set H := h0 * IndefiniteRowSideFullHecke.HeightsSet.chartMon c an with hHdef
  have hG : IsMultiHomog G (d + ap) :=
    IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hg0 (IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_chartMon c ap)
  have hH : IsMultiHomog H (d + an) :=
    IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hh0 (IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_chartMon c an)
  have hdeg : ∀ k, ((d + ap) k : ℤ) = (d + an) k + τ * A.a k := fun k ↦ by
    simp only [Pi.add_apply, Nat.cast_add, hpn k]
    ring
  have hGH : aeval y G = s * aeval y H := by
    have hprod : ∀ k, y ⟨k, c k⟩ ^ ap k = y ⟨k, c k⟩ ^ ((τ : ℤ) * A.a k) * y ⟨k, c k⟩ ^ an k := fun k ↦ by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hyc k), hpn k, add_comm]
    have h1 : (∏ k, y ⟨k, c k⟩ ^ (-((τ : ℤ) * A.a k))) * ∏ k, y ⟨k, c k⟩ ^ ((τ : ℤ) * A.a k) = 1 := by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one fun k _ ↦ by rw [← zpow_add₀ (hyc k), neg_add_cancel, zpow_zero]
    rw [hGdef, hHdef, map_mul, map_mul, aeval_chartMon, aeval_chartMon, hgh0,
      Finset.prod_congr rfl fun k _ ↦ hprod k, Finset.prod_mul_distrib]
    linear_combination (s * aeval y h0 * ∏ k, y ⟨k, c k⟩ ^ an k) * h1
  have hHy : aeval y H ≠ 0 := by
    rw [hHdef, map_mul, aeval_chartMon]
    exact mul_ne_zero hh0y (Finset.prod_ne_zero_iff.mpr fun k _ ↦ pow_ne_zero _ (hyc k))
  have hGy : aeval y G ≠ 0 := by
    rw [hGH]
    exact mul_ne_zero hs0 hHy
  refine ⟨G * H, ⟨_, IndefiniteRowSideFullHecke.HeightsSet.isMultiHomog_mul hG hH⟩,
    notMem_mCoordIdeal (by rw [map_mul]; exact mul_ne_zero hGy hHy), ?_⟩
  intro W hW hPW hfW
  have hGW : G ∉ W := fun h ↦ hfW (W.mul_mem_right H h)
  have hHW : H ∉ W := fun h ↦ hfW (W.mul_mem_left G h)

  have hI : IsIntersectionFamily (II K ι) := hII K ι
  set E := IndefiniteRowSideFullHecke.HeightsSet.powLine A τ with hEdef
  have hE : IsSmoothHerm E := IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_powLine hA τ
  set B := HermLine.sqMetric (ι := ι) (d + an) with hBdef
  have hB : IsSmoothHerm B := isSmoothHerm_sqMetric _
  have hEB : IsSmoothHerm (E.tensor B) := IndefiniteRowSideFullHecke.HeightsSet.isSmoothHerm_tensor hE hB
  have hEBa : ∀ k, (E.tensor B).a k = ((d + ap) k : ℕ) := fun k ↦ by
    show E.a k + B.a k = _
    rw [hEdef, IndefiniteRowSideFullHecke.HeightsSet.powLine_a, hdeg k]
    show _ + ((d + an) k : ℤ) = _
    ring
  have hsecG : IsSectionOn W (E.tensor B) G := ⟨_, hEBa, hG, hGW⟩
  have hsecH : IsSectionOn W B H := ⟨_, fun k ↦ rfl, hH, hHW⟩
  have hRG := IndefiniteRowSideFullHecke.HeightsSet.inter_eq_recR (II K ι) hI hW hEB hEBa hG hGW
  have hRH := IndefiniteRowSideFullHecke.HeightsSet.inter_eq_recR (II K ι) hI hW hB (fun k ↦ rfl) hH hHW
  have hadd := IndefiniteRowSideFullHecke.HeightsSet.inter_tensor (II K ι) hI hW hE hB
  have hpow := IndefiniteRowSideFullHecke.HeightsSet.inter_powLine (II K ι) hI hW hA τ
  rw [recR_eq, Inter.cycR_eq_vertR_of_dimOne Inter.arithVarZero _ hW hsecG] at hRG
  rw [recR_eq, Inter.cycR_eq_vertR_of_dimOne Inter.arithVarZero _ hW hsecH] at hRH

  have hvert := vertR_le (hOrd K ι Ω y A.a τ s W G H (d + ap) (d + an) hW hPW hs hG hH hdeg hGH hGW hHW)

  have harch : arInt W G (E.tensor B) (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) ≤
      arInt W H B (Fin.elim0 : Fin 0 → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) := by
    unfold arInt
    rw [Inter.ptsIntegral_add_of_dimOne fibreFinite hW _ (g₁ := logNorm B H)
      (g₂ := fun z ↦ logNorm (E.tensor B) G z - logNorm B H z) fun z _ ↦ by ring]
    refine add_le_of_nonpos_right (IndefiniteRowSideFullHecke.HeightsSet.ptsIntegral_nonpos W _ fun z hz ↦ ?_)
    show logNorm (E.tensor B) G z - logNorm B H z ≤ 0
    have hGz := norm_pos_iff.mpr (Inter.eval_ne_zero_of_dimOne Inter.arithVarZero hW hsecG hz)
    have hHz := norm_pos_iff.mpr (Inter.eval_ne_zero_of_dimOne Inter.arithVarZero hW hsecH hz)
    have hAz := A.pos z hz.1
    have hBz := B.pos z hz.1
    have hEz : E.h z = A.h z ^ τ := powLine_h A τ z
    have hEz0 : 0 < E.h z := hEz ▸ pow_pos hAz τ
    have hzP : z ∈ mcPts (mCoordIdeal y) := ⟨hz.1, fun f hf ↦ hz.2 f (hPW hf)⟩
    have hsm := hsmall (d + ap) (d + an) G H z hG hH hdeg hGH hzP
    rw [← hEz] at hsm
    refine sub_nonpos.mpr (Real.log_le_log (div_pos hGz (mul_pos hEz0 hBz)) ?_)
    show _ / (E.h z * B.h z) ≤ _ / B.h z
    rw [div_le_div_iff₀ (mul_pos hEz0 hBz) hBz]
    nlinarith [mul_le_mul_of_nonneg_right hsm hBz.le]

  have hτI : 0 ≤ (τ : ℝ) * II K ι W 1 ![A] := by
    rw [← hpow]
    linarith
  have hτ0 : (0 : ℝ) < τ := by exact_mod_cast hτ
  exact le_of_mul_le_mul_left (by rw [mul_zero]; exact hτI) hτ0

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PTwoBlockModuleCycle
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

namespace TwoBlockModuleCycleAlt

section General

variable {K : Type} {ι : K → Type} {τ : Type}

theorem mem_minimalPrimes_iff_of {R : Type*} [CommRing R] {J J' W : Ideal R} (hJ : J ≤ J')
    (key : ∀ Q : Ideal R, Q.IsPrime → Q ≤ W → J ≤ Q → J' ≤ Q) :
    W ∈ J.minimalPrimes ↔ W ∈ J'.minimalPrimes := by
  constructor
  · intro h
    exact ⟨⟨h.1.1, key W h.1.1 le_rfl h.1.2⟩, fun Q hQ hQW => h.2 ⟨hQ.1, hJ.trans hQ.2⟩ hQW⟩
  · intro h
    exact ⟨⟨h.1.1, hJ.trans h.1.2⟩, fun Q hQ hQW => h.2 ⟨hQ.1, key Q hQ.1 hQW hQ.2⟩ hQW⟩

theorem sup_range_le {R : Type*} [CommRing R] (P : Ideal R) (s : R) (v : τ → R) :
    P ⊔ Ideal.span (Set.range fun j => s * v j) ≤ P ⊔ Ideal.span {s} := by
  refine sup_le le_sup_left (Ideal.span_le.mpr ?_)
  rintro _ ⟨j, rfl⟩
  exact Ideal.mem_sup_right (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))

theorem mul_mem_sup_range {R : Type*} [CommRing R] {P : Ideal R} {s : R} {v : τ → R} (i : τ) {y : R}
    (hy : y ∈ P ⊔ Ideal.span {s}) : v i * y ∈ P ⊔ Ideal.span (Set.range fun j => s * v j) := by
  obtain ⟨p, hp, r, hr, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.mp hr
  rw [mul_add]
  refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.mul_mem_left _ _ hp)) (Ideal.mem_sup_right ?_)
  have e : v i * (t * s) = t * (s * v i) := by ring
  rw [e]
  exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)

theorem multAt_sup_range_eq {P W : Ideal (MRing ι)} {s : MRing ι} {v : τ → MRing ι} (hW : W.IsPrime) {i : τ}
    (hi : v i ∉ W) : multAt (P ⊔ Ideal.span (Set.range fun j => s * v j)) W = multAt (P ⊔ Ideal.span {s}) W := by
  have := hW
  unfold multAt
  rw [dif_pos hW, dif_pos hW, GroundTheory.Heights₂.Heights.NumbersDVR.length_localizedQuot_eq_of_mul_le
    (sup_range_le P s v) hi (fun y hy => mul_mem_sup_range i hy)]

theorem multAt_eq_zero_of_not_le {J W : Ideal (MRing ι)} (hW : W.IsPrime) (h : ¬ J ≤ W) : multAt J W = 0 := by
  have := hW
  unfold multAt
  rw [dif_pos hW, Module.length_eq_zero_iff.mpr
    (GroundTheory.Heights₂.Heights.NumbersDVR.localizedQuot_subsingleton_of_not_le _ W h)]
  rfl

theorem log_charOf_of_horizontal {W : Ideal (MRing ι)} (h : IsHorizontal W) : Real.log (charOf W) = 0 := by
  have hg : Submodule.IsPrincipal.generator (W.comap (C : ℤ →+* MRing ι)) = 0 :=
    (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero _).mp h
  simp [charOf, hg]

open Classical in

theorem vert_weight_eq (W : Ideal (MRing ι)) (g : ℤ) :
    (if IsHorizontal W then 0 else (g : ℝ) * Real.log (charOf W)) = Real.log (charOf W) * g := by
  split_ifs with h
  · rw [log_charOf_of_horizontal h, zero_mul]
  · ring

end General

section TwoBlock

variable {Ω : Type} [Field Ω] {κ : Type}

theorem mem_twoBlockIdeal {x x' : Ix κ → Ω} {f : MRing (FinTwoTypeFamily κ)} :
    f ∈ twoBlockIdeal x x' ↔ mConeMap (ι := FinTwoTypeFamily κ) (pair x x') f = 0 :=
  RingHom.mem_ker

theorem mConeMap_X_zero (x x' : Ix κ → Ω) (i : κ) :
    mConeMap (ι := FinTwoTypeFamily κ) (pair x x') (X ⟨0, i⟩) = MvPolynomial.C (x ⟨(), i⟩) * MvPolynomial.X 0 := by
  simp [mConeMap, pair]

theorem mConeMap_num [Fintype κ] (x x' : Ix κ → Ω) (l : Ix κ → ℤ) :
    mConeMap (ι := FinTwoTypeFamily κ) (pair x x') (twoBlockNum l) =
      MvPolynomial.C (∑ j, (l j : Ω) * x' j) * MvPolynomial.X 1 := by
  simp [twoBlockNum, mConeMap, pair, Finset.sum_mul, mul_assoc, map_sum]

theorem rel_mem [Fintype κ] (x x' : Ix κ → Ω) (c : κ) (l m : Ix κ → ℤ) (i : κ)
    (hl : x ⟨(), c⟩ = ∑ j, (l j : Ω) * x' j) (hm : x ⟨(), i⟩ = ∑ j, (m j : Ω) * x' j) :
    X ⟨0, i⟩ * twoBlockNum l - twoBlockDen c * twoBlockNum m ∈ twoBlockIdeal x x' := by
  rw [mem_twoBlockIdeal, map_sub, map_mul, map_mul, mConeMap_num, mConeMap_num, twoBlockDen,
    mConeMap_X_zero, mConeMap_X_zero, ← hl, ← hm]
  ring

end TwoBlock

end TwoBlockModuleCycleAlt

open TwoBlockModuleCycleAlt in

theorem TwoBlockModuleCycle.proof : TwoBlockModuleCycle.Statement := by
  classical
  intro D Ω _ _ κ _ x B c l hX hx hB hsp hl e

  obtain ⟨hFp, -⟩ := TwoBlockFnField.proof Ω κ x B hB
  have hxA : IsArithVar (mCoordIdeal (ι := GlobalTheory κ) x) (D + 1) := by
    rw [← coordIdeal_eq_mCoordIdeal]
    exact hX
  have hxc : x ⟨(), c⟩ ≠ 0 := hx.ne_zero _
  have hx0 : x ≠ 0 := fun h => hxc (by rw [h]; rfl)
  obtain ⟨B', -, hB'⟩ := isInvMat_mul hB
  have hBx0 : matAct B x ≠ 0 := fun h => hx0 ((matAct_eq_zero_iff hB' x).mp h)
  obtain ⟨⟨⟨⟩, i₀⟩, hi₀⟩ := Function.ne_iff.mp hx0
  obtain ⟨⟨⟨⟩, i₁⟩, hi₁⟩ := Function.ne_iff.mp hBx0
  have hpA : IsArithVar (twoBlockIdeal x (matAct B x)) (D + 1) :=
    CoordArithOfFnField.proof Unit (GlobalTheory κ) (Fin 2) (FinTwoTypeFamily κ) Ω x (pair x (matAct B x)) (D + 1) ⟨0⟩
      (fun k => by
        fin_cases k
        · exact ⟨i₀, by simpa [pair] using hi₀⟩
        · exact ⟨i₁, by simpa [pair] using hi₁⟩) hFp.symm hxA
  have hPp : (twoBlockIdeal x (matAct B x)).IsPrime := hpA.2.1.1
  have hdim := hpA.2.2.2

  have hnumP : twoBlockNum l ∉ twoBlockIdeal x (matAct B x) := by
    rw [mem_twoBlockIdeal, mConeMap_num, ← hl]
    simp [hxc]

  have hm : ∀ i : κ, ∃ m : Ix κ → ℤ, x ⟨(), i⟩ = ∑ j, (m j : Ω) * matAct B x j := by
    intro i
    have h := hsp (Submodule.subset_span ⟨⟨(), i⟩, rfl⟩)
    obtain ⟨m, hm⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp h
    exact ⟨m, by rw [← hm]; simp [zsmul_eq_mul]⟩
  choose m hm using hm

  have hden_num : ∀ Q : Ideal (MRing (FinTwoTypeFamily κ)), Q.IsPrime → twoBlockIdeal x (matAct B x) ≤ Q →
      (∃ i, (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ)) ∉ Q) → twoBlockDen c ∈ Q → twoBlockNum l ∈ Q := by
    rintro Q hQ hPQ ⟨i, hi⟩ hd
    have h1 := hPQ (rel_mem x (matAct B x) c l (m i) i hl (hm i))
    have h2 : X ⟨0, i⟩ * twoBlockNum l ∈ Q := by
      have e : X ⟨0, i⟩ * twoBlockNum l =
          (X ⟨0, i⟩ * twoBlockNum l - twoBlockDen c * twoBlockNum (m i)) + twoBlockDen c * twoBlockNum (m i) := by
        ring
      rw [e]
      exact Q.add_mem h1 (Q.mul_mem_right _ hd)
    exact (hQ.mem_or_mem h2).resolve_left hi

  have hmin : ∀ W : Ideal (MRing (FinTwoTypeFamily κ)), IsRelevant W →
      (W ∈ (twoBlockMInner x (matAct B x) l).minimalPrimes ↔
        W ∈ (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l}).minimalPrimes) := by
    intro W hrel
    refine mem_minimalPrimes_iff_of (sup_range_le _ _ _) fun Q hQ hQW hJQ => ?_
    obtain ⟨i, hi⟩ := hrel 0
    have hiQ : (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ)) ∉ Q := fun h => hi (hQW h)
    have hn : twoBlockNum l * X ⟨0, i⟩ ∈ Q :=
      hJQ (Ideal.mem_sup_right (Ideal.subset_span ⟨i, rfl⟩))
    exact sup_le (le_sup_left.trans hJQ)
      ((Ideal.span_singleton_le_iff_mem _).mpr ((hQ.mem_or_mem hn).resolve_right hiQ))
  have hT : topComps (twoBlockMInner x (matAct B x) l) D = divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l) := by
    ext W
    constructor
    · rintro ⟨hW, hrel, -⟩
      exact ⟨(hmin W hrel).mp hW, hrel⟩
    · rintro ⟨hW, hrel⟩
      exact ⟨(hmin W hrel).mpr hW, hrel, dim_of_minimal hnumP hW hdim⟩

  have hsub : divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c) ⊆
      divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l) := by
    rintro W ⟨hW, hrel⟩
    have hWp : W.IsPrime := hW.1.1
    have hPW : twoBlockIdeal x (matAct B x) ≤ W := le_sup_left.trans hW.1.2
    have hdW : twoBlockDen c ∈ W := hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))
    have hnW := hden_num W hWp hPW (hrel 0) hdW
    obtain ⟨Q, hQ, hQW⟩ := Ideal.exists_minimalPrimes_le
      (sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hnW))
    have hQeq : Q = W := ReciprocityTheory.ChartRestriction.G.AI.I1.eq_of_le_of_mem_minimalPrimes hPp hW hQ.1.1
      (le_sup_left.trans hQ.1.2) (hQ.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _))) hnumP hQW
    exact ⟨hQeq ▸ hQ, hrel⟩

  have hback : ∀ W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l), twoBlockDen c ∈ W →
      W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c) := by
    rintro W ⟨hW, hrel⟩ hdW
    refine ⟨⟨⟨hW.1.1, sup_le (le_sup_left.trans hW.1.2) ((Ideal.span_singleton_le_iff_mem _).mpr hdW)⟩,
      fun Q hQ hQW => hW.2 ⟨hQ.1, ?_⟩ hQW⟩, hrel⟩
    have hPQ := le_sup_left.trans hQ.2
    have hrQ : ∃ i, (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ)) ∉ Q := by
      obtain ⟨i, hi⟩ := hrel 0
      exact ⟨i, fun h => hi (hQW h)⟩
    exact sup_le hPQ ((Ideal.span_singleton_le_iff_mem _).mpr
      (hden_num Q hQ.1 hPQ hrQ (hQ.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))))

  rw [hT]
  unfold twoBlockVert vertCycleNum
  have hfin := divSupp_finite (twoBlockIdeal x (matAct B x)) (twoBlockNum l)
  have hden_sum :
      ∑ᶠ W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockDen c),
          (multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W : ℝ) *
            (if IsHorizontal W then 0 else (geoNum D W e : ℝ) * Real.log (charOf W)) =
        ∑ᶠ W ∈ divSupp (twoBlockIdeal x (matAct B x)) (twoBlockNum l),
          (multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W : ℝ) *
            (if IsHorizontal W then 0 else (geoNum D W e : ℝ) * Real.log (charOf W)) := by
    refine finsum_mem_inter_support_eq' _ _ _ fun W hW => ⟨fun h => hsub h, fun h => hback W h ?_⟩
    by_contra hd
    apply hW
    show (multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W : ℝ) * _ = 0
    rw [multAt_eq_zero_of_not_le h.1.1.1 fun hle =>
      hd (hle (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))]
    simp
  rw [hden_sum, ← finsum_mem_sub_distrib _ _ hfin]
  refine finsum_mem_congr rfl fun W hW => ?_
  obtain ⟨i, hi⟩ := hW.2 0
  obtain ⟨j, hj⟩ := hW.2 1
  have h1 : multAt (twoBlockMInner x (matAct B x) l) W =
      multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockNum l}) W :=
    multAt_sup_range_eq (s := twoBlockNum l) (v := fun i : κ => (X ⟨0, i⟩ : MRing (FinTwoTypeFamily κ))) hW.1.1.1 hi
  have h2 : multAt (twoBlockMOuter x (matAct B x) c) W =
      multAt (twoBlockIdeal x (matAct B x) ⊔ Ideal.span {twoBlockDen c}) W :=
    multAt_sup_range_eq (s := twoBlockDen c) (v := fun j : κ => (X ⟨1, j⟩ : MRing (FinTwoTypeFamily κ))) hW.1.1.1 hj
  rw [h1, h2, vert_weight_eq]
  ring

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

