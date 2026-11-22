import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0001
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.T2SpaceOfIsNonarchimedeanLocalFieldFlagMeasures

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFrameClassProperties
section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.FrameClass

theorem exists_inv {E : Type} [CommRing E] {σ : Type} [SetLike σ E] [SubringClass σ E] (O : σ) {n : ℕ}
    (A : Matrix (Fin n) (Fin n) E) (hO : ∀ i j, A i j ∈ O) (ht : ∀ i j, j < i → A i j = 0)
    (hd : ∀ i, A i i = 1) :
    ∃ B : Matrix (Fin n) (Fin n) E, (∀ i j, B i j ∈ O) ∧ (∀ i j, j < i → B i j = 0) ∧ (∀ i, B i i = 1) ∧
      A * B = 1 ∧ B * A = 1 := by
  let M : Matrix (Fin n) (Fin n) O := fun i j => ⟨A i j, hO i j⟩
  have hM : M.BlockTriangular id := fun i j h => Subtype.ext (ht i j h)
  have hMd : ∀ i, M i i = 1 := fun i => Subtype.ext (hd i)
  have hdet : M.det = 1 := by
    rw [Matrix.det_of_isUpperTriangular hM]; simp [hMd]
  have hu : IsUnit M.det := by rw [hdet]; exact isUnit_one
  let _ : Invertible M := Matrix.invertibleOfIsUnitDet M hu
  have hI : (M⁻¹).BlockTriangular id := Matrix.blockTriangular_inv_of_blockTriangular hM
  have h1 : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hu
  have h2 : M⁻¹ * M = 1 := Matrix.nonsing_inv_mul M hu
  have hA : M.map (SubringClass.subtype O) = A := rfl
  refine ⟨(M⁻¹).map (SubringClass.subtype O), fun i j => (M⁻¹ i j).2, fun i j h => ?_, fun i => ?_, ?_, ?_⟩
  · have : M⁻¹ i j = 0 := hI h
    simp [Matrix.map_apply, this]
  · have h := congrFun (congrFun h1 i) i
    rw [Matrix.mul_apply, Finset.sum_eq_single i, hMd, one_mul] at h
    · simp [Matrix.map_apply, h]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with hk | hk
      · have : M i k = 0 := hM hk
        rw [this, zero_mul]
      · have : M⁻¹ k i = 0 := hI hk
        rw [this, mul_zero]
    · simp
  · rw [← hA, ← Matrix.map_mul, h1]; simp
  · rw [← hA, ← Matrix.map_mul, h2]; simp

theorem sum_comp {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) E) (g p q : Fin n → V) (hp : ∀ j, p j = ∑ i, A i j • g i)
    (hq : ∀ j, q j = ∑ i, B i j • p i) (j : Fin n) : q j = ∑ i, (A * B) i j • g i := by
  rw [hq]
  simp only [hp, Finset.smul_sum, Matrix.mul_apply, Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem th_ne_zero : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · intro h
    exact S.ϖ_irr.ne_zero (Subtype.ext h)
  · exact one_ne_zero

theorem intM_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : IsIntM L A) (hB : IsIntM L B) :
    IsIntM L (A * B) := fun i j => by
  rw [Matrix.mul_apply]
  exact sum_mem fun l _ => mul_mem (hA i l) (hB l j)

theorem cong_iff {n : ℕ} (t : E) (A A' : Matrix (Fin n) (Fin n) E) :
    (∀ i j, ∃ c ∈ L.O, A' i j - A i j = t * c) ↔ ∃ C, IsIntM L C ∧ A' - A = t • C := by
  constructor
  · intro h
    choose C hC hC' using h
    exact ⟨C, hC, by ext i j; exact hC' i j⟩
  · rintro ⟨C, hC, h⟩ i j
    exact ⟨C i j, hC i j, congrFun (congrFun h i) j⟩

theorem refl_mem (g g' : Fin (r + 1) → S.V) : (g, g') ∈ S.frameCls g g' := by
  have h1 : IsIntM L (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E) := fun i j => by
    rw [Matrix.one_apply]; split_ifs
    exacts [one_mem _, zero_mem _]
  refine ⟨1, 1, h1, h1, fun i j h => ?_, fun i => by simp, fun i j => ⟨0, zero_mem _, by simp⟩, fun j => ?_,
    fun j => ?_⟩
  · simp [Matrix.one_apply_ne h.ne']
  · simp [Matrix.one_apply]
  · simp [Matrix.one_apply]

omit [TopologicalSpace E] in
theorem tri_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) : ∀ i j, j < i → (A * B) i j = 0 := fun i j h => by
  have hA' : A.BlockTriangular id := fun i j h => hA i j h
  have hB' : B.BlockTriangular id := fun i j h => hB i j h
  exact hA'.mul hB' h

omit [TopologicalSpace E] in
theorem diag_mul {n : ℕ} {A B : Matrix (Fin n) (Fin n) E} (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) (i : Fin n) : (A * B) i i = A i i * B i i := by
  rw [Matrix.mul_apply, Finset.sum_eq_single i]
  · intro l _ hl
    rcases lt_or_gt_of_ne hl with hl | hl
    · rw [hA i l hl, zero_mul]
    · rw [hB l i hl, mul_zero]
  · simp

theorem trans_mem {g g' : Fin (r + 1) → S.V} {p q : S.FrP} (hp : p ∈ S.frameCls g g')
    (hq : q ∈ S.frameCls p.1 p.2) : q ∈ S.frameCls g g' := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  obtain ⟨B, B', hB, hB', kt, kd, kc, k1, k2⟩ := hq
  obtain ⟨C, hC, hc⟩ := (cong_iff _ _ _).1 hc
  obtain ⟨D, hD, kc⟩ := (cong_iff _ _ _).1 kc
  refine ⟨A * B, A' * B', intM_mul hA hB, intM_mul hA' hB', fun i j h => ⟨?_, ?_⟩, fun i => ⟨?_, ?_⟩, ?_,
    sum_comp A B g p.1 q.1 h1 k1, sum_comp A' B' g' p.2 q.2 h2 k2⟩
  · exact tri_mul (fun i j h => (ht i j h).1) (fun i j h => (kt i j h).1) i j h
  · exact tri_mul (fun i j h => (ht i j h).2) (fun i j h => (kt i j h).2) i j h
  · rw [diag_mul (fun i j h => (ht i j h).1) (fun i j h => (kt i j h).1), (hd i).1, (kd i).1, one_mul]
  · rw [diag_mul (fun i j h => (ht i j h).2) (fun i j h => (kt i j h).2), (hd i).2, (kd i).2, one_mul]
  · refine (cong_iff _ _ _).2 ⟨C * B' + A * D, fun i j => ?_, ?_⟩
    · exact add_mem (intM_mul hC hB' i j) (intM_mul hA hD i j)
    · rw [smul_add, ← Matrix.smul_mul, ← Matrix.mul_smul, ← hc, ← kc, sub_mul, mul_sub]; abel

theorem symm_mem {g g' : Fin (r + 1) → S.V} {p : S.FrP} (hp : p ∈ S.frameCls g g') :
    (g, g') ∈ S.frameCls p.1 p.2 := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  obtain ⟨C, hC, hc⟩ := (cong_iff _ _ _).1 hc
  obtain ⟨B, hB, bt, bd, hAB, hBA⟩ := exists_inv L.O A hA (fun i j h => (ht i j h).1) (fun i => (hd i).1)
  obtain ⟨B', hB', bt', bd', hAB', hBA'⟩ :=
    exists_inv L.O A' hA' (fun i j h => (ht i j h).2) (fun i => (hd i).2)
  refine ⟨B, B', hB, hB', fun i j h => ⟨bt i j h, bt' i j h⟩, fun i => ⟨bd i, bd' i⟩, ?_, fun j => ?_,
    fun j => ?_⟩
  · refine (cong_iff _ _ _).2 ⟨-(B' * C * B), fun i j => ?_, ?_⟩
    · exact neg_mem (intM_mul (intM_mul hB' hC) hB i j)
    · rw [smul_neg, ← Matrix.smul_mul, ← Matrix.mul_smul, ← hc, mul_sub, sub_mul, hBA', mul_assoc, hAB]
      simp
  · have := sum_comp A B g p.1 (fun j => ∑ i, B i j • p.1 i) h1 (fun _ => rfl) j
    rw [this, hAB]; simp [Matrix.one_apply]
  · have := sum_comp A' B' g' p.2 (fun j => ∑ i, B' i j • p.2 i) h2 (fun _ => rfl) j
    rw [this, hAB']; simp [Matrix.one_apply]

theorem Mof_le {g g' : Fin (r + 1) → S.V} {p : S.FrP} (hp : p ∈ S.frameCls g g') :
    S.Mof p.1 p.2 ≤ S.Mof g g' := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  have hsm : ∀ c ∈ L.O, ∀ v ∈ S.Mof g g', c • v ∈ S.Mof g g' := fun c hc v hv =>
    (S.Mof g g').smul_mem ⟨c, hc⟩ hv
  have hg : ∀ i, g i ∈ S.Mof g g' := fun i => Submodule.subset_span (Or.inl ⟨i, rfl⟩)
  have hg' : ∀ i, algebraMap F E S.th⁻¹ • (g' i - g i) ∈ S.Mof g g' := fun i =>
    Submodule.subset_span (Or.inr ⟨i, rfl⟩)
  have hth : algebraMap F E S.th⁻¹ * algebraMap F E S.th = 1 := by
    rw [← map_mul, inv_mul_cancel₀ (th_ne_zero S), map_one]
  choose C hC hC' using hc
  refine Submodule.span_le.2 ?_
  rintro _ (⟨j, rfl⟩ | ⟨j, rfl⟩)
  · rw [h1]
    exact sum_mem fun i _ => hsm _ (hA i j) _ (hg i)
  · have : algebraMap F E S.th⁻¹ • (p.2 j - p.1 j) =
        ∑ i, (A' i j • (algebraMap F E S.th⁻¹ • (g' i - g i)) + C i j • g i) := by
      rw [h1, h2, ← Finset.sum_sub_distrib, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hCi : C i j = algebraMap F E S.th⁻¹ * (A' i j - A i j) := by
        rw [hC', ← mul_assoc, hth, one_mul]
      rw [hCi]; module
    show algebraMap F E S.th⁻¹ • (p.2 j - p.1 j) ∈ S.Mof g g'
    rw [this]
    exact sum_mem fun i _ => add_mem (hsm _ (hA' i j) _ (hg' i)) (hsm _ (hC i j) _ (hg i))

theorem smul_mem (h : S.GLV) {g g' : Fin (r + 1) → S.V} {p : S.FrP} (hp : p ∈ S.frameCls g g') :
    h • p ∈ S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by
  obtain ⟨A, A', hA, hA', ht, hd, hc, h1, h2⟩ := hp
  refine ⟨A, A', hA, hA', ht, hd, hc, fun j => ?_, fun j => ?_⟩
  · show h (p.1 j) = _
    rw [h1]; simp
  · show h (p.2 j) = _
    rw [h2]; simp

theorem smul_cls (h : S.GLV) (g g' : Fin (r + 1) → S.V) :
    h • S.frameCls g g' = S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact smul_mem S h hq
  · intro hp
    have := smul_mem S h⁻¹ hp
    refine ⟨h⁻¹ • p, ?_, smul_inv_smul h p⟩
    have e : ∀ v : S.V, h⁻¹ (h v) = v := fun v => h.symm_apply_apply v
    simpa only [e] using this

theorem frame_classes : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ g g' : Fin (r + 1) → S.V, (g, g') ∈ S.frameCls g g' ∧ (∀ p ∈ S.frameCls g g', S.frameCls p.1 p.2 = S.frameCls g g' ∧ S.Mof p.1 p.2 = S.Mof g g') ∧ ∀ h : S.GLV, h • S.frameCls g g' = S.frameCls (fun b => h (g b)) (fun b => h (g' b)) := by
  intro F _ _ _ _ _ E _ _ _ L r k S g g'
  refine ⟨refl_mem S g g', fun p hp => ⟨?_, ?_⟩, fun h => smul_cls S h g g'⟩
  · ext q
    exact ⟨fun hq => trans_mem S hp hq, fun hq => trans_mem S (symm_mem S hp) hq⟩
  · exact le_antisymm (Mof_le S hp) (Mof_le S (p := (g, g')) (symm_mem S hp))

end GlobalTheory.HL.FrameClass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianDoubleCosetFramesLevelLeIffCongrFlagSte
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FrameLevel

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem exists_coords {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g : Fin (r + 1) → S.V) (j : ℕ)
    {y : S.V} (hy : y ∈ S.spanTo g j) :
    ∃ a : Fin (r + 1) → E, y = ∑ i, a i • g i ∧ ∀ i : Fin (r + 1), j ≤ (i : ℕ) → a i = 0 := by
  obtain ⟨c, hc, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination E).mp hy
  refine ⟨c, ?_, fun i hi => ?_⟩
  · rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
  · by_contra hne
    have hmem : i ∈ {i : Fin (r + 1) | (i : ℕ) < j} :=
      (Finsupp.mem_supported _ _).mp hc (Finsupp.mem_support_iff.mpr hne)
    exact absurd hi (not_le.mpr hmem)

theorem exists_coords_Mof {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g g' : Fin (r + 1) → S.V)
    {y : S.V} (hy : y ∈ S.Mof g g') :
    ∃ β γ : Fin (r + 1) → L.O, y = ∑ i, (β i : E) • g i +
      ∑ i, (γ i : E) • (algebraMap F E S.th⁻¹ • (g' i - g i)) := by
  unfold Frames.Mof at hy
  rw [Submodule.span_union, Submodule.mem_sup] at hy
  obtain ⟨u, hu, u', hu', rfl⟩ := hy
  obtain ⟨β, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).mp hu
  obtain ⟨γ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun L.O).mp hu'
  exact ⟨β, γ, rfl⟩

theorem th_ne_zero {L : LocE F E} {r k : ℕ} (S : Frames L r k) : S.th ≠ 0 := by
  unfold Frames.th
  split_ifs
  · exact fun h => S.ϖ_irr.ne_zero (by simpa using h)
  · exact one_ne_zero

theorem lev_le_iff {L : LocE F E} {r k : ℕ} (S : Frames L r k) (g g' : Fin (r + 1) → S.V)
    (y : S.V) (hy : y ∈ S.spanTo g (r + 1) ⊔ S.spanTo g' (r + 1)) (j : ℕ) :
    S.lev g g' (algebraMap F E S.th • y) ≤ j ↔
      ∃ y₁ ∈ S.spanTo g j ⊔ S.spanTo g' j, y - y₁ ∈ S.Mof g g' := by
  constructor
  · intro hle
    unfold Frames.lev at hle
    obtain ⟨u, hu, u', hu', huy⟩ := Submodule.mem_sup.mp hy
    obtain ⟨c, hc, -⟩ := exists_coords S g (r + 1) hu
    obtain ⟨c', hc', -⟩ := exists_coords S g' (r + 1) hu'
    obtain ⟨al, al', hrep, hRR⟩ := Nat.sInf_mem (s := {j | ∃ al al' : Fin (r + 1) → E,
        algebraMap F E S.th • y = ∑ i, al i • g i + ∑ i, al' i • g' i ∧
        ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i)})
      ⟨r + 1, fun i => algebraMap F E S.th * c i, fun i => algebraMap F E S.th * c' i, by
        rw [← huy, hc, hc', smul_add, Finset.smul_sum, Finset.smul_sum]
        simp only [smul_smul], fun i hi => absurd hi (not_le.mpr i.isLt)⟩
    have hRR' : ∀ i : Fin (r + 1), j ≤ (i : ℕ) → S.RR (al i) (al' i) := fun i hi => hRR i (le_trans hle hi)
    have htt : algebraMap F E S.th⁻¹ * algebraMap F E S.th = 1 := by
      rw [← map_mul, inv_mul_cancel₀ (th_ne_zero S), map_one]
    have hyy : y = algebraMap F E S.th⁻¹ • (∑ i, al i • g i + ∑ i, al' i • g' i) := by
      rw [← hrep, smul_smul, htt, one_smul]
    refine ⟨algebraMap F E S.th⁻¹ • (∑ i : Fin (r + 1), (if (i : ℕ) < j then al i else 0) • g i +
      ∑ i : Fin (r + 1), (if (i : ℕ) < j then al' i else 0) • g' i), ?_, ?_⟩
    · refine Submodule.smul_mem _ _ (Submodule.add_mem_sup (Submodule.sum_mem _ fun i _ => ?_)
        (Submodule.sum_mem _ fun i _ => ?_))
      · split_ifs with hi
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
        · rw [zero_smul]
          exact Submodule.zero_mem _
      · split_ifs with hi
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
        · rw [zero_smul]
          exact Submodule.zero_mem _
    · have hdiff : y - algebraMap F E S.th⁻¹ • (∑ i : Fin (r + 1), (if (i : ℕ) < j then al i else 0) • g i +
          ∑ i : Fin (r + 1), (if (i : ℕ) < j then al' i else 0) • g' i) =
          ∑ i : Fin (r + 1), algebraMap F E S.th⁻¹ • (if (i : ℕ) < j then 0 else al i • g i + al' i • g' i) := by
        rw [hyy, ← smul_sub, ← Finset.smul_sum]
        congr 1
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs <;> simp
      rw [hdiff]
      refine Submodule.sum_mem _ fun i _ => ?_
      split_ifs with hi
      · rw [smul_zero]
        exact Submodule.zero_mem _
      · obtain ⟨hO, cc, hcc, hsum⟩ := hRR' i (not_lt.mp hi)
        have hal : al i = algebraMap F E S.th * cc - al' i := eq_sub_of_add_eq hsum
        have heq : algebraMap F E S.th⁻¹ • (al i • g i + al' i • g' i) =
            cc • g i + al' i • (algebraMap F E S.th⁻¹ • (g' i - g i)) := by
          rw [hal]
          calc algebraMap F E S.th⁻¹ • ((algebraMap F E S.th * cc - al' i) • g i + al' i • g' i)
              = (algebraMap F E S.th⁻¹ * algebraMap F E S.th * cc) • g i +
                  al' i • (algebraMap F E S.th⁻¹ • (g' i - g i)) := by module
            _ = cc • g i + al' i • (algebraMap F E S.th⁻¹ • (g' i - g i)) := by rw [htt, one_mul]
        rw [heq]
        refine Submodule.add_mem _ ?_ ?_
        · exact Submodule.smul_mem (S.Mof g g') (⟨cc, hcc⟩ : L.O)
            (Submodule.subset_span (Set.mem_union_left _ ⟨i, rfl⟩))
        · exact Submodule.smul_mem (S.Mof g g') (⟨al' i, hO⟩ : L.O)
            (Submodule.subset_span (Set.mem_union_right _ ⟨i, rfl⟩))
  · rintro ⟨y₁, hy₁, hm⟩
    obtain ⟨u, hu, u', hu', rfl⟩ := Submodule.mem_sup.mp hy₁
    obtain ⟨a, rfl, ha⟩ := exists_coords S g j hu
    obtain ⟨a', rfl, ha'⟩ := exists_coords S g' j hu'
    obtain ⟨β, γ, hβγ⟩ := exists_coords_Mof S g g' hm
    have htt : algebraMap F E S.th * algebraMap F E S.th⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel₀ (th_ne_zero S), map_one]
    have hy' : y = ∑ i, ((a i + (β i : E)) • g i + a' i • g' i +
        (γ i : E) • (algebraMap F E S.th⁻¹ • (g' i - g i))) := by
      simp only [add_smul, Finset.sum_add_distrib]
      rw [eq_add_of_sub_eq hβγ]
      abel
    unfold Frames.lev
    apply Nat.sInf_le
    refine ⟨fun i => algebraMap F E S.th * a i + algebraMap F E S.th * (β i : E) - (γ i : E),
      fun i => algebraMap F E S.th * a' i + (γ i : E), ?_, fun i hi => ?_⟩
    · rw [hy', Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_add, smul_comm (algebraMap F E S.th) (γ i : E),
        smul_smul (algebraMap F E S.th) (algebraMap F E S.th⁻¹), htt, one_smul]
      module
    · unfold Frames.RR
      refine ⟨?_, (β i : E), (β i).2, ?_⟩
      · dsimp only
        rw [ha' i hi, mul_zero, zero_add]
        exact (γ i).2
      · dsimp only
        rw [ha i hi, ha' i hi]
        ring

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k) (g g' : Fin (r + 1) → S.V), ∀ y ∈ S.spanTo g (r + 1) ⊔ S.spanTo g' (r + 1), ∀ j : ℕ, S.lev g g' (algebraMap F E S.th • y) ≤ j ↔ ∃ y₁ ∈ S.spanTo g j ⊔ S.spanTo g' j, y - y₁ ∈ S.Mof g g' := by
  intro F _ _ _ _ _ E _ _ _ L r k S g g' y hy j
  exact lev_le_iff S g g' y hy j

end GlobalTheory.FrameLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalModelModulusPropertiesOnUnits
section
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc MeasureTheory
open scoped Pointwise ENNReal Classical NNReal

namespace GlobalTheory.ModuleUnits

theorem modK_units : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK → (∀ x y : E, IsUnit x → IsUnit y → M.modK (x * y) = M.modK x * M.modK y) ∧ (∀ x : E, IsUnit x → 0 < M.modK x ∧ M.modK (M.L.cj x) = M.modK x) ∧ ∀ x : E, x ∈ M.L.O → (∃ y ∈ M.L.O, x * y = 1) → M.modK x = 1 := by
  intro F _ _ _ E _ _ _ _ M hM
  obtain ⟨h1, h2, h3, h4, h5, hRc, hRo, hOc, hOo, -⟩ := GlobalTheory.SgLoc.Top.model_topology M hM
  have := hM.borel
  have := hM.loc
  have := hM.char0
  have := hM.haar.haar
  have hreg : M.mu.Regular := inferInstance
  have hO0 : M.mu (M.L.O : Set E) ≠ 0 := hOo.measure_ne_zero M.mu ⟨0, M.L.O.zero_mem⟩
  have hOt : M.mu (M.L.O : Set E) ≠ ∞ := hOc.measure_lt_top.ne
  have hmodK : ∀ u : Eˣ, M.modK u = (distribHaarChar E u : ℝ) := by
    intro u
    have h := distribHaarChar_mul M.mu u (M.R : Set E)
    rw [hM.haar.volR, mul_one] at h
    change (M.mu (u • (M.R : Set E))).toReal = _
    rw [← h]
    rfl
  refine ⟨?_, ?_, ?_⟩
  · intro x y hx hy
    obtain ⟨u, rfl⟩ := hx
    obtain ⟨v, rfl⟩ := hy
    rw [← Units.val_mul, hmodK, hmodK, hmodK, map_mul, NNReal.coe_mul]
  · intro x hx
    obtain ⟨u, rfl⟩ := hx
    refine ⟨by rw [hmodK]; exact NNReal.coe_pos.mpr distribHaarChar_pos, ?_⟩
    have hcjO : ∀ z, z ∈ M.L.O → M.L.cj z ∈ M.L.O := by
      intro z hz
      rw [M.L.O_def] at hz ⊢
      exact hz.map ((M.L.cj : E →ₐ[F] E).restrictScalars 𝒪[F])
    have hcjO' : ∀ z, M.L.cj z ∈ M.L.O ↔ z ∈ M.L.O := fun z =>
      ⟨fun h => by simpa [M.L.cj_cj] using hcjO _ h, hcjO z⟩
    have : IsModuleTopology F E := M.L.top
    have hc1 : Continuous M.L.cj := IsModuleTopology.continuous_of_linearMap M.L.cj.toLinearMap
    have hc2 : Continuous M.L.cj.symm :=
      IsModuleTopology.continuous_of_linearMap M.L.cj.symm.toLinearMap
    let φ : E ≃ₜ+ E := { M.L.cj.toAddEquiv with continuous_toFun := hc1, continuous_invFun := hc2 }
    have hpre : ∀ X : Set E, addEquivAddHaarChar φ • M.mu (φ ⁻¹' X) = M.mu X := fun X =>
      addEquivAddHaarChar_smul_preimage M.mu φ
    have hφO : φ ⁻¹' (M.L.O : Set E) = M.L.O := by
      ext z
      exact hcjO' z
    have hc : (addEquivAddHaarChar φ : ℝ≥0∞) = 1 := by
      have h := hpre M.L.O
      rw [hφO] at h
      simp only [ENNReal.smul_def, smul_eq_mul] at h
      calc _ = (addEquivAddHaarChar φ : ℝ≥0∞) * M.mu M.L.O / M.mu M.L.O :=
            (ENNReal.mul_div_cancel_right hO0 hOt).symm
        _ = 1 := by rw [h, ENNReal.div_self hO0 hOt]
    let w : Eˣ := Units.map (M.L.cj : E →* E) u
    have hw : φ ⁻¹' (u • (M.L.O : Set E)) = w • (M.L.O : Set E) := by
      ext z
      rw [Set.mem_preimage, Set.mem_smul_set_iff_inv_smul_mem, Set.mem_smul_set_iff_inv_smul_mem]
      change ((u⁻¹ : Eˣ) : E) * M.L.cj z ∈ M.L.O ↔ ((w⁻¹ : Eˣ) : E) * z ∈ M.L.O
      rw [← hcjO' (((w⁻¹ : Eˣ) : E) * z), map_mul]
      simp [w, M.L.cj_cj]
    have hχ : distribHaarChar E w = distribHaarChar E u := by
      apply distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOt
      rw [← hw, distribHaarChar_mul M.mu u]
      have h := hpre (u • (M.L.O : Set E))
      simp only [ENNReal.smul_def, smul_eq_mul, hc, one_mul] at h
      exact h
    rw [show M.L.cj (u : E) = (w : E) from rfl, hmodK, hmodK, hχ]
  · rintro x hx ⟨y, hy, hxy⟩
    let u : Eˣ := ⟨x, y, hxy, by rw [mul_comm]; exact hxy⟩
    have hset : u • (M.L.O : Set E) = M.L.O := by
      ext z
      rw [Set.mem_smul_set_iff_inv_smul_mem]
      change y * z ∈ M.L.O ↔ z ∈ M.L.O
      constructor
      · intro h
        have h' := M.L.O.mul_mem hx h
        rwa [← mul_assoc, hxy, one_mul] at h'
      · intro h
        exact M.L.O.mul_mem hy h
    have h1 : distribHaarChar E u = 1 :=
      distribHaarChar_eq_of_measure_smul_eq_mul hO0 hOt (by rw [hset]; simp)
    rw [show x = (u : E) from rfl, hmodK, h1]
    simp

end GlobalTheory.ModuleUnits
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PowEqZeroOfMemHermitianFrameUnipotent
section
noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.FlagUnipotent

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem hf_sub_left (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (a b y : Fin n → E) :
    hf L H (a - b) y = hf L H a y - hf L H b y := by
  simp [hf, sub_mul, Finset.sum_sub_distrib]

theorem hf_sub_right (L : LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x a b : Fin n → E) :
    hf L H x (a - b) = hf L H x a - hf L H x b := by
  simp [hf, mul_sub, Finset.sum_sub_distrib]

theorem pow_eq_zero_of_mem_Nof {L : LocE F E} {r k : ℕ} (S : Frames L r k)
    (f : Fin (r + 1) → S.V) (g : S.GLV) (hg : g ∈ S.Nof f) :
    ((g : S.V →ₗ[E] S.V) - 1) ^ (2 * r + 1) = 0 := by
  obtain ⟨⟨hiso, hfl⟩, hmid⟩ := hg
  have hfl' : ∀ j, j < r → g ∈ unipOn (S.spanTo f (j + 1)) (S.spanTo f j) := fun j hj =>
    (Subgroup.mem_iInf.1 hfl) ⟨j, hj⟩
  set A : S.V →ₗ[E] S.V := (g : S.V →ₗ[E] S.V) - 1 with hA
  have hAv : ∀ v, A v = g v - v := fun v => rfl
  have h0 : S.spanTo f 0 = ⊥ := by simp [Frames.spanTo]
  have ha : ∀ j, j ≤ r → ∀ v, (A ^ j) v ∈ perp L S.Hm (S.spanTo f j) := by
    intro j
    induction j with
    | zero =>
      intro _ v y hy
      rw [h0, Submodule.mem_bot] at hy
      simp [hy, hf]
    | succ j ih =>
      intro hj v x hx
      obtain ⟨h1, h2⟩ := hfl' j hj
      have hw := ih (by omega) v
      rw [pow_succ', Module.End.mul_apply, hAv]
      generalize (A ^ j) v = w at hw
      obtain ⟨y, rfl⟩ := g.surjective x
      have h3 : hf L S.Hm w (g y - y) = 0 := hw _ (h2 y ((h1 y).1 hx))
      have h4 : hf L S.Hm (g w) (g y) = hf L S.Hm w y := hiso w y
      rw [hf_sub_right] at h3
      rw [hf_sub_left, h4]
      linear_combination -h3
  have hc : ∀ j, j ≤ r → ∀ v ∈ S.spanTo f j, (A ^ j) v = 0 := by
    intro j
    induction j with
    | zero =>
      intro _ v hv
      rw [h0, Submodule.mem_bot] at hv
      simp [hv]
    | succ j ih =>
      intro hj v hv
      rw [pow_succ, Module.End.mul_apply, hAv]
      exact ih (by omega) _ ((hfl' j hj).2 v hv)
  refine LinearMap.ext fun v => ?_
  have e : 2 * r + 1 = r + (1 + r) := by omega
  rw [e, pow_add, pow_add, pow_one, Module.End.mul_apply, Module.End.mul_apply, hAv]
  exact hc r le_rfl _ (hmid.2 _ (ha r le_rfl v))

theorem main : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ g ∈ S.N, ((g : S.V →ₗ[E] S.V) - 1) ^ (2 * r + 1) = 0 :=
  fun _ _ _ S g hg => pow_eq_zero_of_mem_Nof S S.f g hg

end GlobalTheory.FlagUnipotent
end
end

