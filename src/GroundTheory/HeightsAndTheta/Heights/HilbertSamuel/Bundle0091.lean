import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0084
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0037
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0076
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0006
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0030
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombLimit
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0060
import GroundTheory.HeightsAndTheta.Heights.Intersections.QuotientMapImageZInjective
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0082
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.Bundle0083

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PVeroneseTop
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace VeroneseTop

theorem sum_le_weighted {n : ℕ} (f : Fin n × Fin n → ℝ) (hf : ∀ i j, f (i, j) = f (j, i)) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2), (if p.1 = p.2 then (1 : ℝ) else 2) * f p =
      ∑ p, f p := by
  have h1 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1), f p =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), f p := by
    refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
    · intro p hp
      simpa using hp
    · intro p hp
      simpa using hp
    · intro p _
      rfl
    · intro p _
      rfl
    · intro p _
      exact hf p.1 p.2
  have h2 : ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 < p.2), f p =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≤ p.2), (if p.1 = p.2 then 0 else f p) := by
    rw [Finset.sum_ite, Finset.sum_const_zero, zero_add, Finset.filter_filter]
    congr 1
    ext p
    simp [lt_iff_le_and_ne]
  have h3 : Finset.univ.filter (fun p : Fin n × Fin n => ¬ p.1 ≤ p.2) =
      Finset.univ.filter (fun p : Fin n × Fin n => p.2 < p.1) := by
    ext p
    simp
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun p : Fin n × Fin n => p.1 ≤ p.2), h3, h1, h2,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  split_ifs <;> ring

theorem sum_wt_mul {D : ℕ} (a : Fin (D + 1) → ℝ) :
    ∑ q : Ix (Veronese.Idx D), Veronese.wt q * (a q.2.1.1 * a q.2.1.2) = (∑ i, a i) ^ 2 := by
  rw [Fintype.sum_sigma, Fintype.sum_unique]
  calc ∑ y : Veronese.Idx D, Veronese.wt (⟨default, y⟩ : Ix (Veronese.Idx D)) * (a y.1.1 * a y.1.2)
      = ∑ y : Veronese.Idx D, (if y.1.1 = y.1.2 then (1 : ℝ) else 2) * (a y.1.1 * a y.1.2) := rfl
    _ = ∑ p ∈ Finset.univ.filter (fun p : Fin (D + 1) × Fin (D + 1) => p.1 ≤ p.2),
          (if p.1 = p.2 then (1 : ℝ) else 2) * (a p.1 * a p.2) := by
      rw [← Finset.sum_subtype_eq_sum_filter, Finset.subtype_univ]
    _ = ∑ p : Fin (D + 1) × Fin (D + 1), a p.1 * a p.2 :=
      sum_le_weighted (fun p => a p.1 * a p.2) (fun i j => mul_comm _ _)
    _ = (∑ i, a i) ^ 2 := by
      rw [sq, Finset.sum_mul_sum, ← Finset.sum_product', Finset.univ_product_univ]

theorem fs_sq {J : Type} [Fintype J] (z : J → ℂ) : (fsMetric J).ρ z ^ 2 = ∑ i, ‖z i‖ ^ 2 := by
  show ‖WithLp.toLp 2 z‖ ^ 2 = _
  rw [EuclideanSpace.norm_sq_eq]

theorem fs_nonneg {J : Type} [Fintype J] (z : J → ℂ) : 0 ≤ (fsMetric J).ρ z :=
  norm_nonneg (WithLp.toLp 2 z)

theorem metric_nonneg (D : ℕ) (u : Ix (Veronese.Idx D) → ℂ) : 0 ≤ (Veronese.metric D).ρ u :=
  fs_nonneg (Veronese.scale D u)

theorem metric_sq (D : ℕ) (u : Ix (Veronese.Idx D) → ℂ) :
    (Veronese.metric D).ρ u ^ 2 = ∑ q, Veronese.wt q * ‖u q‖ ^ 2 := by
  show (fsMetric _).ρ (Veronese.scale D u) ^ 2 = _
  rw [fs_sq]
  refine Finset.sum_congr rfl fun q _ => ?_
  have hw : 0 ≤ Veronese.wt q := (Veronese.wt_pos q).le
  rw [Veronese.scale, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _), mul_pow,
    Real.sq_sqrt hw]

theorem formApply_forms (D : ℕ) (w : Ix (Fin (D + 1)) → ℂ) (q : Ix (Veronese.Idx D)) :
    formApply (Veronese.forms D) w q = w ⟨(), q.2.1.1⟩ * w ⟨(), q.2.1.2⟩ := by
  simp [formApply, Veronese.forms]

theorem metric_forms (D : ℕ) (w : Ix (Fin (D + 1)) → ℂ) :
    (Veronese.metric D).ρ (formApply (Veronese.forms D) w) =
      (fsMetric (Ix (Fin (D + 1)))).ρ w * (fsMetric (Ix (Fin (D + 1)))).ρ w := by
  have h0 : 0 ≤ (Veronese.metric D).ρ (formApply (Veronese.forms D) w) :=
    metric_nonneg D _
  have h1 : 0 ≤ (fsMetric (Ix (Fin (D + 1)))).ρ w * (fsMetric (Ix (Fin (D + 1)))).ρ w :=
    mul_nonneg (fs_nonneg w) (fs_nonneg w)
  refine (sq_eq_sq₀ h0 h1).1 ?_
  have hw : (fsMetric (Ix (Fin (D + 1)))).ρ w * (fsMetric (Ix (Fin (D + 1)))).ρ w =
      ∑ i : Fin (D + 1), ‖w ⟨(), i⟩‖ ^ 2 := by
    rw [← sq, fs_sq, Fintype.sum_sigma, Fintype.sum_unique]
  rw [hw, metric_sq, ← sum_wt_mul]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [formApply_forms, norm_mul, mul_pow]

theorem isMultiHomog_forms (D : ℕ) (q : Ix (Veronese.Idx D)) :
    IsMultiHomog (Veronese.forms D q) ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) := by
  have h := Inter.AvoidRing.isMultiHomog_mul
    (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.1)
    (Inter.AvoidRing.isMultiHomog_X (R := ℤ) (ι := GlobalTheory (Fin (D + 1))) () q.2.1.2)
  have e : ((fun _ _ => 2 : Unit → Unit → ℕ) q.1) = Pi.single () 1 + Pi.single () 1 := by
    funext k
    cases k
    simp
  rw [e]
  exact h

theorem isBasePtFree_forms (D : ℕ) : IsBasePtFree (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (Veronese.forms D) := by
  intro k₂ i
  refine ⟨2, Ideal.mem_sup_right (Ideal.subset_span ⟨⟨(i (), i ()), le_rfl⟩, ?_⟩)⟩
  cases k₂
  simp [Veronese.forms, pow_two]

theorem tensor_self {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {F : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} (hF : IsIntersectionFamily F)
    {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P n) {T : HermLine ι} (hT : IsSmoothHerm T) :
    F P n (fun _ => T.tensor T) = 2 ^ n * F P n (fun _ => T) := by
  have hTT : IsSmoothHerm (T.tensor T) := hT.mul hT
  have intersection_update_fsHerm_neg_one : ∀ L : Fin n → HermLine ι, (∀ i, IsSmoothHerm (L i)) → ∀ j : Fin n,
      F P n (Function.update L j (T.tensor T)) = 2 * F P n (Function.update L j T) := by
    intro L hL j
    cases n with
    | zero => exact j.elim0
    | succ m =>
      have e : ∀ X : HermLine ι, IsSmoothHerm X →
          F P (m + 1) (Function.update L j X) =
            F P (m + 1) (Fin.snoc (fun i : Fin m => L (Equiv.swap j (Fin.last m) i.castSucc)) X) := by
        intro X hX
        rw [← Inter.ThmIMultilin.update_comp_swap]
        exact (hF.1 P (m + 1) _ _ hP (Inter.ThmIMultilin.smooth_update hL j hX)).symm
      rw [e _ hTT, e T hT, hF.2.1 P m _ T T hP (fun i => hL _) hT hT]
      ring
  have step : ∀ k, k ≤ n →
      F P n (fun i => if (i : ℕ) < k then T.tensor T else T) = 2 ^ k * F P n (fun _ => T) := by
    intro k
    induction k with
    | zero =>
      intro _
      simp
    | succ k ih =>
      intro hk
      have hL : ∀ i : Fin n, IsSmoothHerm (if (i : ℕ) < k then T.tensor T else T) := by
        intro i
        split_ifs
        · exact hTT
        · exact hT
      have h1 : (fun i : Fin n => if (i : ℕ) < k + 1 then T.tensor T else T) =
          Function.update (fun i : Fin n => if (i : ℕ) < k then T.tensor T else T) ⟨k, hk⟩ (T.tensor T) := by
        funext i
        by_cases h : i = ⟨k, hk⟩
        · subst h
          simp
        · have h' : (i : ℕ) ≠ k := fun e => h (Fin.ext e)
          rw [Function.update_of_ne h]
          by_cases hi : (i : ℕ) < k
          · simp [hi, show (i : ℕ) < k + 1 by omega]
          · simp [hi, show ¬ (i : ℕ) < k + 1 by omega]
      have h2 : Function.update (fun i : Fin n => if (i : ℕ) < k then T.tensor T else T) ⟨k, hk⟩ T =
          fun i : Fin n => if (i : ℕ) < k then T.tensor T else T := by
        funext i
        by_cases h : i = ⟨k, hk⟩
        · subst h
          simp
        · rw [Function.update_of_ne h]
      rw [h1, intersection_update_fsHerm_neg_one _ hL, h2, ih (by omega), pow_succ]
      ring
  have hn := step n le_rfl
  simp only [Fin.is_lt, if_true] at hn
  exact hn

end VeroneseTop

open VeroneseTop in

theorem VeroneseTop.proof (hCM : GraphChangeOfModel.Statement) (hA : VeroneseArith.Statement)
    (hIm : VeroneseGraphImage.Statement) (hDeg : VeroneseGraphDeg.Statement) : VeroneseTop.Statement := by
  intro D hD I hI
  obtain ⟨G, J, hJ, hJ1⟩ := hDeg D hD
  have hfs : IsSmoothHerm (HermLine.ofCone (fsMetric (Ix (Fin (D + 1))))) :=
    BlockImageTop.isSmoothHerm_ofCone ProjLine.isSmoothMetric_fs
  have hP : IsArithVar (⊥ : Ideal (MRing (GlobalTheory (Fin (D + 1))))) (D + 1) := IndefiniteRowSideFullHecke.Inter.isArithVar_bot D
  have key := hCM I hI Unit (GlobalTheory (Fin (D + 1))) Unit (GlobalTheory (Veronese.Idx D)) ⊥ (D + 1) (Veronese.forms D)
    (fun _ _ => 2) G J (fun _ => HermLine.ofCone (Veronese.metric D))
    (fun _ => (HermLine.ofCone (fsMetric (Ix (Fin (D + 1))))).tensor (HermLine.ofCone (fsMetric (Ix (Fin (D + 1))))))
    hP (isMultiHomog_forms D) (isBasePtFree_forms D) (by rw [hIm D]; exact hA D hD) hJ
    (fun _ => BlockImageTop.isSmoothHerm_ofCone (Veronese.isSmoothMetric_metric D)) (fun _ => hfs.mul hfs)
    (fun _ k => by cases k; simp [HermLine.tensor, HermLine.ofCone])
    (fun _ z _ => (metric_forms D z).symm)
  rw [hIm D, hJ1] at key
  have h2 := tensor_self (hI Unit (GlobalTheory (Fin (D + 1)))) hP hfs
  rw [Int.cast_one, one_mul] at key
  rw [top, hhOf, ← key, ← h2]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.PZCombExpand
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI
open GroundTheory.Heights₂.Heights.Inter (famExt famExt_apply famExt_basis famExt_symm)

noncomputable section

set_option linter.unusedSectionVars false

namespace ZCombExpand

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {J : Ideal (MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ} {P : Ideal (MRing ι)} {n : ℕ}

theorem famExt_symm_of (e : Fin 2 → HermLine ι) (he : ∀ i, IsSmoothHerm (e i))
    (hJ : ∀ (L : Fin n → HermLine ι) (σ : Equiv.Perm (Fin n)), (∀ j, IsSmoothHerm (L j)) →
      J P n (L ∘ σ) = J P n L) :
    IsSymmForm (famExt J P n e) := by
  intro σ v
  rw [famExt_apply, famExt_apply]
  refine Fintype.sum_equiv (Equiv.arrowCongr σ (Equiv.refl (Fin 2))) _ _ fun s => ?_
  have h1 : e ∘ (Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) = (e ∘ s) ∘ σ.symm := rfl
  have h2 : ∏ j, v j ((Equiv.arrowCongr σ (Equiv.refl (Fin 2)) s) j) = ∏ j, (v ∘ σ) j (s j) := by
    refine (Equiv.prod_comp σ fun j => v j (s (σ.symm j))).symm.trans ?_
    simp
  rw [h1, h2, hJ (e ∘ s) σ.symm fun j => he _]

theorem famExt_expand (e : Fin 2 → HermLine ι) (hs : IsSymmForm (famExt J P n e)) (q p : ℝ) :
    famExt J P n e (fun _ => ![q, p]) =
      ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * q ^ (n - i) * p ^ i *
        J P n (fun j : Fin n => if (j : ℕ) < n - i then e 0 else e 1) := by
  classical
  have hw : (fun _ : Fin n => (![q, p] : Fin 2 → ℝ)) =
      fun _ => p • (Pi.single 1 1 : Fin 2 → ℝ) + q • (Pi.single 0 1 : Fin 2 → ℝ) := by
    funext j i
    fin_cases i <;> simp
  rw [hw, symm_expand _ hs, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  rw [show n + 1 - 1 - i = n - i by omega]
  have hmix : (mix (n - i) (Pi.single 0 1) (p • Pi.single 1 1) : Fin n → Fin 2 → ℝ) =
      (Finset.univ.filter fun j : Fin n => ¬ (j : ℕ) < n - i).piecewise
        (fun j => p • (mix (n - i) (Pi.single 0 1) (Pi.single 1 1) : Fin n → Fin 2 → ℝ) j)
        (mix (n - i) (Pi.single 0 1) (Pi.single 1 1)) := by
    funext j
    by_cases h : (j : ℕ) < n - i
    · rw [Finset.piecewise_eq_of_notMem _ _ _ (by simp; omega)]
      simp [mix, h]
    · rw [Finset.piecewise_eq_of_mem _ _ _ (by simp; omega)]
      simp [mix, h]
  have hcard : (Finset.univ.filter fun j : Fin n => ¬ (j : ℕ) < n - i).card = i := by
    rw [Finset.filter_not, Finset.card_sdiff_of_subset (Finset.filter_subset _ _), Finset.card_univ,
      Fintype.card_fin, Fin.card_filter_val_lt]
    omega
  have hbasis : (mix (n - i) (Pi.single 0 1) (Pi.single 1 1) : Fin n → Fin 2 → ℝ) =
      fun j => Pi.single ((fun j : Fin n => if (j : ℕ) < n - i then (0 : Fin 2) else 1) j) 1 := by
    funext j
    simp only [mix]
    split_ifs <;> rfl
  have hlist : (e ∘ fun j : Fin n => if (j : ℕ) < n - i then (0 : Fin 2) else 1) =
      fun j : Fin n => if (j : ℕ) < n - i then e 0 else e 1 := by
    funext j
    simp only [Function.comp]
    split_ifs <;> rfl
  rw [hmix, MultilinearMap.map_piecewise_smul, Finset.prod_const, hcard, hbasis, famExt_basis, hlist,
    smul_eq_mul, Nat.choose_symm hin]
  ring

end ZCombExpand

theorem ZCombExpand.proof : ZCombExpand.Statement := by
  intro K _ ι _ I hI P d M H q p hP hM hH
  set e : Fin 2 → HermLine ι := ![M, H] with he_def
  have he : ∀ i, IsSmoothHerm (e i) := by
    intro i
    fin_cases i
    · exact hM
    · exact hH
  set Z := HermLine.zcomb M H (q : ℤ) (p : ℤ) with hZ_def
  have hZ : IsSmoothHerm Z := ZCombLimit.isSmoothHerm_zcomb_int hM hH _ _
  refine ⟨?_, ?_⟩
  · have hposition : ∀ (L : Fin d → HermLine ι) (a : Fin d), (∀ j, IsSmoothHerm (L j)) →
        I P d (Function.update L a Z) =
          (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 0 * I P d (Function.update L a (e 0)) +
            (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 1 * I P d (Function.update L a (e 1)) := by
      intro L a hL
      cases d with
      | zero => exact a.elim0
      | succ m =>
        have h := ZCombLimit.fam_update_zcomb_int hI hP L hL a hM hH (q : ℤ) (p : ℤ)
        simpa [e] using h
    have key := ZCombLimit.eq_famExt_of_position (J := I) (P := P) IsSmoothHerm e Z ![(q : ℝ), (p : ℝ)] he hZ
      hposition Finset.univ (fun _ => 0)
    simp only [Finset.mem_univ, if_true] at key
    rw [key, ZCombExpand.famExt_expand e (famExt_symm hI hP e he)]
    rfl
  · intro hd
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    let J : Ideal (MRing ι) → (m : ℕ) → (Fin m → HermLine ι) → ℝ :=
      fun P' m L => I P' (m + 1) (Fin.cons (α := fun _ => HermLine ι) M L)
    have hcons : ∀ L : Fin n → HermLine ι, (∀ j, IsSmoothHerm (L j)) →
        ∀ j, IsSmoothHerm (Fin.cons (α := fun _ => HermLine ι) M L j) := by
      intro L hL j
      refine Fin.cases ?_ (fun j => ?_) j
      · simpa using hM
      · simpa using hL j
    have hsymm : ∀ (L : Fin n → HermLine ι) (σ : Equiv.Perm (Fin n)), (∀ j, IsSmoothHerm (L j)) →
        J P n (L ∘ σ) = J P n L := by
      intro L σ hL
      have hc : (Fin.cons (α := fun _ => HermLine ι) M (L ∘ σ) : Fin (n + 1) → HermLine ι) =
          (Fin.cons (α := fun _ => HermLine ι) M L) ∘ (Equiv.Perm.decomposeFin.symm (0, σ)) := by
        funext j
        refine Fin.cases ?_ (fun j => ?_) j
        · simp [Equiv.Perm.decomposeFin_symm_apply_zero]
        · simp [Equiv.Perm.decomposeFin_symm_apply_succ]
      show I P (n + 1) _ = I P (n + 1) _
      rw [hc, hI.1 P (n + 1) _ _ hP (hcons L hL)]
    have hposition : ∀ (L : Fin n → HermLine ι) (a : Fin n), (∀ j, IsSmoothHerm (L j)) →
        J P n (Function.update L a Z) =
          (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 0 * J P n (Function.update L a (e 0)) +
            (![(q : ℝ), (p : ℝ)] : Fin 2 → ℝ) 1 * J P n (Function.update L a (e 1)) := by
      intro L a hL
      show I P (n + 1) _ = _ * I P (n + 1) _ + _ * I P (n + 1) _
      rw [Fin.cons_update, Fin.cons_update, Fin.cons_update]
      have h := ZCombLimit.fam_update_zcomb_int hI hP _ (hcons L hL) a.succ hM hH (q : ℤ) (p : ℤ)
      simpa [e] using h
    have key := ZCombLimit.eq_famExt_of_position (J := J) (P := P) IsSmoothHerm e Z ![(q : ℝ), (p : ℝ)] he hZ
      hposition Finset.univ (fun _ => 0)
    simp only [Finset.mem_univ, if_true] at key
    have hl : (fun j : Fin (n + 1) => if (j : ℕ) = 0 then M else Z) =
        Fin.cons (α := fun _ => HermLine ι) M (fun _ : Fin n => Z) := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp
      · simp
    rw [hl, show I P (n + 1) (Fin.cons (α := fun _ => HermLine ι) M (fun _ : Fin n => Z)) =
      J P n (fun _ => Z) from rfl, key,
      ZCombExpand.famExt_expand e (ZCombExpand.famExt_symm_of e he hsymm), Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hl2 : (Fin.cons (α := fun _ => HermLine ι) M
        (fun j : Fin n => if (j : ℕ) < n - i then e 0 else e 1) : Fin (n + 1) → HermLine ι) =
        fun j : Fin (n + 1) => if (j : ℕ) < n + 1 - i then M else H := by
      funext j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp only [Fin.cons_zero]
        exact (if_pos (show ((0 : Fin (n + 1)) : ℕ) < n + 1 - i by simp; omega)).symm
      · simp only [Fin.cons_succ, Fin.val_succ]
        split_ifs with h1 h2 h2
        · rfl
        · exact absurd (by omega) h2
        · exact absurd (by omega) h1
        · rfl
    show _ * I P (n + 1) _ = _
    rw [hl2]

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.ProjFrameGraphChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

namespace ProjFrameGraph

variable {κ : Type} {D : ℕ}

theorem linForm_projMat [Fintype κ] (e : Fin (D + 1) → Ix κ) (k : Fin (D + 1)) :
    linForm (ι := GlobalTheory κ) (ι₂ := GlobalTheory (Fin (D + 1))) (projMat e) ⟨(), k⟩ = X (e k) := by
  classical
  simp only [linForm, projMat]
  rw [Finset.sum_eq_single (e k).2]
  · simp
  · intro i _ hi
    simp [Ne.symm hi]
  · simp

theorem graphIdeal_isPrime {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    (P : Ideal (MRing ι)) [P.IsPrime] (g : (Σ k, ι₂ k) → MRing ι) : (graphIdeal P g).IsPrime :=
  RingHom.ker_isPrime _

variable {Ω : Type} [Field Ω]

theorem frame_ne_zero {x : Ix κ → Ω} {e : Fin (D + 1) → Ix κ} (hF : IsProjFrame x e) (k : Fin (D + 1)) :
    x (e k) ≠ 0 := by
  intro h
  have hX : (X k : MvPolynomial (Fin (D + 1)) ℤ) ∈ coordIdeal ℤ (x ∘ e) := by
    rw [coordIdeal, RingHom.mem_ker]
    simp [coneMap, h]
  rw [hF.free, Ideal.mem_bot] at hX
  exact X_ne_zero k hX

theorem genFibre_x'_ne_zero {x : Ix κ → Ω} {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    [Fintype κ] {g : (Σ k, ι₂ k) → MRing (GlobalTheory κ)}
    (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := ι₂)) (graphIdeal (coordIdeal ℤ x) g)) (j : κ) (hj : x ⟨(), j⟩ ≠ 0) :
    G.x' ⟨Sum.inl (), j⟩ ≠ 0 := by
  intro h
  have h1 : (X ⟨Sum.inl (), j⟩ : MRing (Sum.elim (GlobalTheory κ) ι₂)) ∈ graphIdeal (coordIdeal ℤ x) g := by
    rw [← G.genericFibre_ker_target, RingHom.mem_ker]
    simpa using h
  rw [graphIdeal, RingHom.mem_ker, graphMap, eval₂Hom_X'] at h1
  have h2 : (X ⟨(), j⟩ : MvPolynomial (Ix κ) ℤ) ∈ coordIdeal ℤ x := by
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact MvPolynomial.C_eq_zero.1 h1
  rw [coordIdeal, RingHom.mem_ker] at h2
  simp [coneMap] at h2
  exact hj h2

def fibreChart {K₂ : Type} {ι₂ : K₂ → Type} (j : κ) :
    (k : FibreBlock (Sum.inr : K₂ → Unit ⊕ K₂)) → fibreIdx (Sum.elim (GlobalTheory κ) ι₂) Sum.inr k
  | ⟨Sum.inl _, _⟩ => j
  | ⟨Sum.inr k, h⟩ => absurd ⟨k, rfl⟩ h

theorem isChart_fibreChart {x : Ix κ → Ω} {K₂ : Type} [Fintype K₂] {ι₂ : K₂ → Type} [∀ k, Fintype (ι₂ k)]
    [Fintype κ] {g : (Σ k, ι₂ k) → MRing (GlobalTheory κ)}
    (G : GenFibre (inrV (ι := GlobalTheory κ) (ι₂ := ι₂)) (graphIdeal (coordIdeal ℤ x) g)) (j : κ) (hj : x ⟨(), j⟩ ≠ 0) :
    IsChart (ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal Sum.inr G) (fibreChart (ι₂ := ι₂) j) := by
  rintro ⟨(u | k), h⟩
  · cases u
    rw [ReciprocityTheory.ChartRestriction.G.AI.I4.fibreIdeal, RingHom.mem_ker, aeval_X]
    exact genFibre_x'_ne_zero G j hj
  · exact absurd ⟨k, rfl⟩ h

end ProjFrameGraph

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsChartPrimePowerInverse
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry MvPolynomial

noncomputable section

def ChartPrimePowerInverse.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω]
    (y : (Σ k, ι k) → Ω) (D : ℕ) (e : K → ℕ) (L : Fin (D + 1) → MRing ι),
    (∀ j, IsMultiHomog (L j) e) →
    (∀ z ∈ mcPts (mCoordIdeal y), ∃ j, eval z (map (Int.castRingHom ℂ) (L j)) ≠ 0) →
    ∀ p : ℕ, p.Prime → ∀ j : Fin (D + 1), aeval y (L j) ≠ 0 →
      ∃ M : ℕ, ∀ c : ∀ k, ι k, (∀ k, y ⟨k, c k⟩ ≠ 0) →
        (p : Ω) ^ M * (∏ k, y ⟨k, c k⟩ ^ e k) / aeval y (L j) ∈
          Subring.closure (Set.range (fun q : Σ k, ι k => y q / y ⟨q.1, c q.1⟩) ∪
            Set.range (fun i => aeval y (L i) / aeval y (L j)) ∪ {z | ∃ r : ℕ, ¬ p ∣ r ∧ z = (r : Ω)⁻¹})

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsClosedPtFibreLift
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

noncomputable section

def ClosedPtFibreLift.Statement : Prop :=
  ∀ (S : Type) [CommRing S] (K : Type) [Fintype K] [LinearOrder K] (ι : K → Type)
    [∀ k, Fintype (ι k)] [∀ k, LinearOrder (ι k)]
    (M : Type) [AddCommGroup M] [Module (MRingOver S ι) M] [Module S M] [IsScalarTower S (MRingOver S ι) M]
    (𝓜 : (K → ℤ) → Submodule S M) (P : Ideal (MRingOver S ι)) (d : K → ℤ),
    IsNoetherianRing S → Module.Finite (MRingOver S ι) M → KH.IsMGraded S ι 𝓜 → IsClosedMultiPt P →
    Subsingleton (KH.cechHc ι (subGrading 𝓜 (P • ⊤ : Submodule (MRingOver S ι) M)) d 1) →
    ∀ I : KH.Cell K ι 0, (∀ k, ∀ i ∈ I.1 k, (X ⟨k, i⟩ : MRingOver S ι) ∉ P) →
    ∀ x ∈ KH.locPart ι 𝓜 (KH.cellMon S I.1) d, ∃ z ∈ KH.cechZc ι 𝓜 d 0,
      x - z I ∈ locIdealPart 𝓜 (KH.cellMon S I.1) P d

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
end

