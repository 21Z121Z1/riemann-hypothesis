import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.Bundle0002

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.GelFlagB
section
noncomputable section

open Matrix Module
open scoped ContDiff

namespace PositivityTheory.RgBcC.VC.GFB

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def lmul (a b : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => a * y * b
      map_add' := fun y z => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c y => by simp [Matrix.mul_smul, Matrix.smul_mul] }

theorem lmul_apply (a b y : Mat n) : lmul a b y = a * y * b := rfl

theorem mul_mem_GLs {a y b : Mat n} (ha : a ∈ GLs n) (hy : y ∈ GLs n) (hb : b ∈ GLs n) : a * y * b ∈ GLs n := by
  show (a * y * b).det ≠ 0
  rw [Matrix.det_mul, Matrix.det_mul]
  exact mul_ne_zero (mul_ne_zero ha hy) hb

theorem comp_lmul {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {F : Mat n → V} (hF : ContDiffOn ℝ ∞ F (GLs n))
    {a b : Mat n} (ha : a ∈ GLs n) (hb : b ∈ GLs n) : ContDiffOn ℝ ∞ (fun y => F (a * y * b)) (GLs n) :=
  hF.comp (lmul a b).contDiff.contDiffOn fun _ hy => mul_mem_GLs ha hy hb

theorem gel_sub (hGC : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (s : Bool) (m : ℕ)
    {F₁ F₂ : Mat n → V} (h₁ : ContDiffOn ℝ ∞ F₁ (GLs n)) (h₂ : ContDiffOn ℝ ∞ F₂ (GLs n)) {g₀ : Mat n} (hg₀ : g₀ ∈ GLs n) :
    gel s m (fun y => F₁ y - F₂ y) g₀ = gel s m F₁ g₀ - gel s m F₂ g₀ := by
  have hP : ContDiffOn ℝ ∞ (fun y => (F₁ y, F₂ y)) (GLs n) := h₁.prodMk h₂
  have hc := (hGC n (V × V) V s m _ hP).2 g₀ hg₀
  have c1 := hc.2.2 (ContinuousLinearMap.fst ℂ V V - ContinuousLinearMap.snd ℂ V V)
  have c2 := hc.2.2 (ContinuousLinearMap.fst ℂ V V)
  have c3 := hc.2.2 (ContinuousLinearMap.snd ℂ V V)
  have e1 : (fun y => (ContinuousLinearMap.fst ℂ V V - ContinuousLinearMap.snd ℂ V V) (F₁ y, F₂ y)) =
      fun y => F₁ y - F₂ y := by funext y; simp
  have e2 : (fun y => (ContinuousLinearMap.fst ℂ V V) (F₁ y, F₂ y)) = F₁ := by funext y; simp
  have e3 : (fun y => (ContinuousLinearMap.snd ℂ V V) (F₁ y, F₂ y)) = F₂ := by funext y; simp
  rw [e1] at c1; rw [e2] at c2; rw [e3] at c3
  rw [c1, c2, c3]; simp

theorem gel_transport (hGC : GelComm) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (s : Bool) (m : ℕ)
    {F : Mat n → V} (hF : ContDiffOn ℝ ∞ F (GLs n)) {a b : Mat n} (ha : a ∈ GLs n) (hb : b ∈ GLs n) :
    gel s m (fun y => F (a * y * b)) 1 = gel s m F (a * b) := by
  have hF' : ContDiffOn ℝ ∞ (fun y => F (a * y)) (GLs n) := by
    simpa using comp_lmul hF ha (show (1 : Mat n) ∈ GLs n by show (1 : Mat n).det ≠ 0; simp)
  have h1 := ((hGC n V V s m _ hF').2 1 (show (1 : Mat n) ∈ GLs n by show (1 : Mat n).det ≠ 0; simp)).2.1 b hb
  have h2 := ((hGC n V V s m _ hF).2 b hb).2.1 a ha
  have e : (fun y => F (a * y * b)) = fun y => (fun y' => F (a * y')) (y * b) := by
    funext y; simp [Matrix.mul_assoc]
  rw [e, h1.2, one_mul, h2.1]

theorem map_eq_of_le {W : Submodule ℂ (Fin n → ℂ)} {q : Mat n} (hq : IsUnit q) (h : ∀ v ∈ W, q *ᵥ v ∈ W) :
    W.map (Matrix.mulVecLin q) = W := by
  have hinj : Function.Injective (Matrix.mulVecLin q) := Matrix.mulVec_injective_iff_isUnit.2 hq
  refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩; exact h v hv
  · exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W)).symm

end PositivityTheory.RgBcC.VC.GFB
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.KerNIdC
section
noncomputable section

open MeasureTheory Matrix Filter Topology

namespace PositivityTheory.RgBcC.VC.KN

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

theorem contOn_avg (hLg : LgCpt) [MeasurableSpace (G n)] [BorelSpace (G n)] {N : Subgroup (G n)}
    (hNc : IsClosed (N : Set (G n))) (ν : Measure N) [IsFiniteMeasureOnCompacts ν] {X : Type} [NormedAddCommGroup X]
    [NormedSpace ℝ X] (h : Mat n → X) (hc : ContinuousOn h (GLs n)) (R : ℝ)
    (hR : ∀ y ∈ GLs n, R < lg y → h y = 0) :
    ContinuousOn (fun y => ∫ u : N, h ((u : G n).val * y) ∂ν) (GLs n) := by
  haveI : LocallyCompactSpace (Mat n) := inferInstanceAs (LocallyCompactSpace (Fin n → Fin n → ℂ))
  haveI : FirstCountableTopology (Mat n) := inferInstanceAs (FirstCountableTopology (Fin n → Fin n → ℂ))
  intro y₀ hy₀
  obtain ⟨K, hKn, hKs, hK⟩ := local_compact_nhds (isOpen_GLs.mem_nhds hy₀)
  obtain ⟨M, hM⟩ := hK.bddAbove_image (lg_contOn.mono hKs)
  set S : Set N := {u : N | lg ((u : G n) : Mat n) ≤ R + M} with hSdef
  have hS : IsCompact S := cptN hLg hNc (R + M)
  have hcu : Continuous (fun u : N => ((u : G n) : Mat n)) := by fun_prop
  set T : Set (Mat n) := (fun p : N × Mat n => ((p.1 : G n) : Mat n) * p.2) '' (S ×ˢ K) with hTdef
  have hT : IsCompact T := (hS.prod hK).image (by fun_prop)
  have hTs : T ⊆ GLs n := by
    rintro _ ⟨p, hp, rfl⟩
    exact mul_memGL _ _ (hKs hp.2)
  obtain ⟨C, hC⟩ := hT.exists_bound_of_continuousOn (hc.mono hTs)
  have hlc : Continuous (fun u : N => lg ((u : G n) : Mat n)) :=
    lg_contOn.comp_continuous hcu (fun u => memGL _)
  have hSm : MeasurableSet S := (isClosed_le hlc continuous_const).measurableSet
  have hbound : ∀ y ∈ K, ∀ u : N, ‖h (((u : G n) : Mat n) * y)‖ ≤ S.indicator (fun _ => C) u := by
    intro y hy u
    by_cases hu : u ∈ S
    · rw [Set.indicator_of_mem hu]
      exact hC _ ⟨(u, y), ⟨hu, hy⟩, rfl⟩
    · rw [Set.indicator_of_notMem hu]
      have hu' : ¬ lg ((u : G n) : Mat n) ≤ R + M := hu
      have hyM : lg y ≤ M := hM ⟨y, hy, rfl⟩
      have h1 := lg_le_of_mul ((u : G n) : Mat n) y (hKs hy)
      have h2 : R + M < lg ((u : G n) : Mat n) := lt_of_not_ge hu'
      rw [hR _ (mul_memGL _ _ (hKs hy)) (by linarith), norm_zero]
  apply continuousWithinAt_of_dominated (bound := S.indicator (fun _ => C))
  · filter_upwards [self_mem_nhdsWithin] with y hy
    exact (integrable_N hLg hNc ν h hc R hR y hy).aestronglyMeasurable
  · filter_upwards [mem_nhdsWithin_of_mem_nhds hKn] with y hy
    exact Filter.Eventually.of_forall (hbound y hy)
  · exact (integrable_indicator_iff hSm).2 (integrableOn_const hS.measure_ne_top)
  · refine Filter.Eventually.of_forall (fun u => ?_)
    have hm : Continuous (fun y : Mat n => ((u : G n) : Mat n) * y) := by fun_prop
    exact (hc.comp hm.continuousOn (fun y hy => mul_memGL _ _ hy)) y₀ hy₀

theorem key (hLg : LgCpt) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (E : KMod n) (k B : Mat n → (E.V →L[ℂ] E.V)) (hkc : ContinuousOn k (GLs n)) (Rk : ℝ)
    (hkR : ∀ y ∈ GLs n, Rk < lg y → k y = 0) {N : Subgroup (G n)} (hNc : IsClosed (N : Set (G n)))
    (ν : Measure N) [ν.IsHaarMeasure] [ν.IsInvInvariant] (hBc : ContinuousOn B (GLs n))
    (hBN : ∀ u : N, ∀ y ∈ GLs n, B ((u : G n).val * y) = B y) (φ : Mat n → E.V) (hφc : ContinuousOn φ (GLs n))
    (Rφ : ℝ) (hφR : ∀ y ∈ GLs n, Rφ < lg y → φ y = 0) :
    ∫ y : G n, k y.val (B y.val (∫ u : N, φ ((u : G n).val * y.val) ∂ν)) ∂μ =
      ∫ y : G n, (∫ u : N, k ((u : G n).val * y.val) ∂ν) (B y.val (φ y.val)) ∂μ := by
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ) :=
    inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℂ))
  haveI : SecondCountableTopology (Matrix (Fin n) (Fin n) ℂ)ᵐᵒᵖ :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin n) (Fin n) ℂ)).symm.isEmbedding.secondCountableTopology
  haveI : SecondCountableTopology (G n) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SigmaCompactSpace (G n) := ⟨⟨fun m : ℕ => {y : G n | lg y.val ≤ m}, fun m => hLg n m, by
    ext y
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact exists_nat_ge _⟩⟩
  haveI : SigmaCompactSpace N := ⟨⟨fun m : ℕ => {u : N | lg ((u : G n) : Mat n) ≤ m},
    fun m => cptN hLg hNc m, by
    ext y
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact exists_nat_ge _⟩⟩
  have iφ : ∀ y : G n, Integrable (fun u : N => φ ((u : G n).val * y.val)) ν := fun y =>
    integrable_N hLg hNc ν φ hφc Rφ hφR y.val (memGL y)
  have ik : ∀ y : G n, Integrable (fun u : N => k ((u : G n).val * y.val)) ν := fun y =>
    integrable_N hLg hNc ν k hkc Rk hkR y.val (memGL y)
  set F : G n → N → E.V := fun y u => k y.val (B y.val (φ ((u : G n).val * y.val))) with hF
  set H : G n → N → E.V := fun y u => k ((u : G n).val * y.val) (B y.val (φ y.val)) with hH
  have cu1 : Continuous (fun p : G n × N => p.1.val) := Units.continuous_val.comp continuous_fst
  have cu2 : Continuous (fun p : G n × N => ((p.2 : G n).val * p.1.val)) := by fun_prop
  have hB1 : Continuous (fun p : G n × N => B p.1.val) := hBc.comp_continuous cu1 (fun p => memGL _)
  have iF : Integrable (Function.uncurry F) (μ.prod ν) := by
    have cF : Continuous (Function.uncurry F) :=
      (hkc.comp_continuous cu1 (fun p => memGL _)).clm_apply
        (hB1.clm_apply (hφc.comp_continuous cu2 (fun p => mul_memGL _ _ (memGL _))))
    have KF : IsCompact ({y : G n | lg y.val ≤ Rk} ×ˢ {u : N | lg ((u : G n) : Mat n) ≤ Rk + Rφ}) :=
      (hLg n Rk).prod (cptN hLg hNc (Rk + Rφ))
    refine cF.integrable_of_hasCompactSupport (HasCompactSupport.intro KF ?_)
    rintro ⟨y, u⟩ hp
    simp only [Set.mem_prod, Set.mem_setOf_eq, not_and_or, not_le] at hp
    show k y.val (B y.val (φ ((u : G n).val * y.val))) = 0
    by_cases hy : lg y.val ≤ Rk
    · have hu : Rk + Rφ < lg ((u : G n) : Mat n) := by
        rcases hp with h | h
        · exact absurd hy (not_le.mpr h)
        · exact h
      have h1 := lg_le_of_mul ((u : G n) : Mat n) y.val (memGL y)
      rw [hφR _ (mul_memGL _ _ (memGL y)) (by linarith), map_zero, map_zero]
    · rw [hkR _ (memGL y) (lt_of_not_ge hy), ContinuousLinearMap.zero_apply]
  have iH : Integrable (Function.uncurry H) (μ.prod ν) := by
    have cH : Continuous (Function.uncurry H) :=
      (hkc.comp_continuous cu2 (fun p => mul_memGL _ _ (memGL _))).clm_apply
        (hB1.clm_apply (hφc.comp_continuous cu1 (fun p => memGL _)))
    have KH : IsCompact ({y : G n | lg y.val ≤ Rφ} ×ˢ {u : N | lg ((u : G n) : Mat n) ≤ Rk + Rφ}) :=
      (hLg n Rφ).prod (cptN hLg hNc (Rk + Rφ))
    refine cH.integrable_of_hasCompactSupport (HasCompactSupport.intro KH ?_)
    rintro ⟨y, u⟩ hp
    simp only [Set.mem_prod, Set.mem_setOf_eq, not_and_or, not_le] at hp
    show k ((u : G n).val * y.val) (B y.val (φ y.val)) = 0
    by_cases hy : lg y.val ≤ Rφ
    · have hu : Rk + Rφ < lg ((u : G n) : Mat n) := by
        rcases hp with h | h
        · exact absurd hy (not_le.mpr h)
        · exact h
      have h1 := lg_le_of_mul ((u : G n) : Mat n) y.val (memGL y)
      rw [hkR _ (mul_memGL _ _ (memGL y)) (by linarith), ContinuousLinearMap.zero_apply]
    · rw [hφR _ (memGL y) (lt_of_not_ge hy), map_zero, map_zero]
  have s1 : ∀ y : G n, k y.val (B y.val (∫ u : N, φ ((u : G n).val * y.val) ∂ν)) = ∫ u : N, F y u ∂ν := by
    intro y
    exact (ContinuousLinearMap.integral_comp_comm ((k y.val).comp (B y.val)) (iφ y)).symm
  have s6 : ∀ y : G n, (∫ u : N, k ((u : G n).val * y.val) ∂ν) (B y.val (φ y.val)) = ∫ u : N, H y u ∂ν :=
    fun y => ContinuousLinearMap.integral_apply (ik y) _
  have s3 : ∀ u : N, ∫ y : G n, F y u ∂μ = ∫ y : G n, H y u⁻¹ ∂μ := by
    intro u
    rw [← integral_mul_left_eq_self (μ := μ) (fun x : G n => H x u⁻¹) (u : G n)]
    congr 1
    ext x
    have e1 : (((u⁻¹ : N) : G n)).val * (((u : G n) * x)).val = x.val := by
      rw [← Units.val_mul, Subgroup.coe_inv, inv_mul_cancel_left]
    have e2 : B (((u : G n) * x)).val = B x.val := by
      rw [Units.val_mul]
      exact hBN u x.val (memGL x)
    simp only [hF, hH]
    rw [e1, e2, Units.val_mul]
  calc ∫ y : G n, k y.val (B y.val (∫ u : N, φ ((u : G n).val * y.val) ∂ν)) ∂μ
      = ∫ y : G n, ∫ u : N, F y u ∂ν ∂μ := integral_congr_ae (Filter.Eventually.of_forall s1)
    _ = ∫ u : N, ∫ y : G n, F y u ∂μ ∂ν := integral_integral_swap iF
    _ = ∫ u : N, ∫ y : G n, H y u⁻¹ ∂μ ∂ν := integral_congr_ae (Filter.Eventually.of_forall s3)
    _ = ∫ u : N, ∫ y : G n, H y u ∂μ ∂ν := integral_inv_eq_self (fun u => ∫ y : G n, H y u ∂μ) ν
    _ = ∫ y : G n, ∫ u : N, H y u ∂ν ∂μ := (integral_integral_swap iH).symm
    _ = ∫ y : G n, (∫ u : N, k ((u : G n).val * y.val) ∂ν) (B y.val (φ y.val)) ∂μ :=
      integral_congr_ae (Filter.Eventually.of_forall (fun y => (s6 y).symm))

end PositivityTheory.RgBcC.VC.KN
end
end

