import ReciprocityTheory.SemistableReduction.SphereLogIntegrableStatement
import ReciprocityTheory.SemistableReduction.Bundle0002

-- bundled from ReciprocityTheory.SemistableReduction.SJCoreB
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights

open MeasureTheory Metric Set Real

theorem integral_volumeIoiPow (k : ℕ) (g : ℝ → ℝ) :
    ∫ r : Ioi (0 : ℝ), g r ∂(Measure.volumeIoiPow k) = ∫ r in Ioi (0 : ℝ), r ^ k * g r := by
  rw [Measure.volumeIoiPow, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  rw [← integral_subtype_comap measurableSet_Ioi (fun r : ℝ => r ^ k * g r)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) k)]

theorem integrable_volumeIoiPow {k : ℕ} {g : ℝ → ℝ}
    (h : IntegrableOn (fun r ↦ r ^ k * g r) (Ioi 0)) :
    Integrable (fun r : Ioi (0 : ℝ) ↦ g r) (Measure.volumeIoiPow k) := by
  rw [Measure.volumeIoiPow, integrable_withDensity_iff (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  have h2 := (integrableOn_iff_comap_subtypeVal measurableSet_Ioi).mp h
  refine h2.congr (Filter.Eventually.of_forall fun r => ?_)
  simp only [Function.comp_apply]
  rw [ENNReal.toReal_ofReal (pow_nonneg (le_of_lt r.2) k), mul_comm]

theorem finrank_euclidean_complex (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) = 2 * n := by
  rw [← Module.finrank_mul_finrank ℝ ℂ, Complex.finrank_real_complex, finrank_euclideanSpace,
    Fintype.card_fin]

private theorem homeomorphUnitSphereProd_smul_eq {n : ℕ} (x : ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n)))) :
    ((homeomorphUnitSphereProd _ x).2 : ℝ) •
      ((homeomorphUnitSphereProd _ x).1 : EuclideanSpace ℂ (Fin n)) = x := by
  have hx : ‖(x : EuclideanSpace ℂ (Fin n))‖ ≠ 0 := norm_ne_zero_iff.mpr x.2
  simp [homeomorphUnitSphereProd, homeomorphSphereProd, smul_smul, hx]

theorem integral_polar {n : ℕ} (hn : 0 < n) (f : EuclideanSpace ℂ (Fin n) → ℝ) :
    ∫ x, f x = ∫ p : UnitSphereC n × Ioi (0 : ℝ), f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n)))
      ∂((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1))) := by
  rw [← (Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℂ (Fin n)))).integral_comp
      (homeomorphUnitSphereProd _).measurableEmbedding
      (fun p : UnitSphereC n × Ioi (0 : ℝ) ↦ f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n))))]
  simp only [homeomorphUnitSphereProd_smul_eq]
  rw [integral_subtype_comap (measurableSet_singleton 0).compl
    (fun x : EuclideanSpace ℂ (Fin n) ↦ f x)]
  haveI : Nontrivial (EuclideanSpace ℂ (Fin n)) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclidean_complex]; omega)
  rw [Measure.restrict_congr_set (show ({0}ᶜ : Set (EuclideanSpace ℂ (Fin n))) =ᵐ[volume] univ from
    ae_eq_univ.mpr (by rw [compl_compl]; exact measure_singleton 0)), Measure.restrict_univ]

theorem integrable_polar (n : ℕ) {f : EuclideanSpace ℂ (Fin n) → ℝ} (hf : Integrable f) :
    Integrable (fun p : UnitSphereC n × Ioi (0 : ℝ) ↦ f (p.2.1 • (p.1 : EuclideanSpace ℂ (Fin n))))
      ((volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere.prod
        (Measure.volumeIoiPow (Module.finrank ℝ (EuclideanSpace ℂ (Fin n)) - 1))) := by
  rw [← (Measure.measurePreserving_homeomorphUnitSphereProd
      (volume : Measure (EuclideanSpace ℂ (Fin n)))).integrable_comp_emb
      (homeomorphUnitSphereProd _).measurableEmbedding]
  have h2 := (integrableOn_iff_comap_subtypeVal (measurableSet_singleton
    (0 : EuclideanSpace ℂ (Fin n))).compl).mp hf.integrableOn
  refine h2.congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Function.comp_apply, homeomorphUnitSphereProd_smul_eq]

def conjVec {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (fun i ↦ star (WithLp.ofLp c i))

theorem inner_conjVec {n : ℕ} (c x : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (conjVec c) x = ∑ i, WithLp.ofLp c i * WithLp.ofLp x i := by
  simp [conjVec, PiLp.inner_apply, mul_comm]

theorem norm_conjVec {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) : ‖conjVec c‖ = ‖c‖ := by
  simp [conjVec, EuclideanSpace.norm_eq]

theorem sphere_linear_zero_null {n : ℕ} (c : EuclideanSpace ℂ (Fin n)) (hc : c ≠ 0) :
    (volume : Measure (EuclideanSpace ℂ (Fin n))).toSphere
      {z : UnitSphereC n | ∑ i, WithLp.ofLp c i * spherePoint z i = 0} = 0 := by
  let K : Submodule ℝ (EuclideanSpace ℂ (Fin n)) :=
    (LinearMap.ker (innerₛₗ ℂ (conjVec c))).restrictScalars ℝ
  have hK : K ≠ ⊤ := by
    intro h
    have hm : conjVec c ∈ K := h ▸ Submodule.mem_top
    have hm' : inner ℂ (conjVec c) (conjVec c) = 0 := hm
    rw [inner_self_eq_zero] at hm'
    exact hc (by rw [← norm_eq_zero, ← norm_conjVec c, hm', norm_zero])
  have hset : {z : UnitSphereC n | ∑ i, WithLp.ofLp c i * spherePoint z i = 0} =
      {z : UnitSphereC n | inner ℂ (conjVec c) (z : EuclideanSpace ℂ (Fin n)) = 0} := by
    ext z
    simp only [Set.mem_setOf_eq, spherePoint, inner_conjVec]
  have hs : MeasurableSet
      {z : UnitSphereC n | inner ℂ (conjVec c) (z : EuclideanSpace ℂ (Fin n)) = 0} :=
    (isClosed_eq (continuous_const.inner continuous_subtype_val) continuous_const).measurableSet
  rw [hset, Measure.toSphere_apply' _ hs,
    measure_mono_null ?_ (Measure.addHaar_submodule _ K hK), mul_zero]
  rintro _ ⟨t, -, _, ⟨z, hz, rfl⟩, rfl⟩
  exact K.smul_mem t hz

def gaussLogC (a : ℝ) : ℝ := ∫ z : ℂ, log (a * ‖z‖) * exp (-‖z‖ ^ 2)

def gaussOneC : ℝ := ∫ z : ℂ, exp (-‖z‖ ^ 2)

private theorem integrableOn_rpow_mul_exp_neg_sq_Ioi (s : ℝ) (hs : -1 < s) :
    IntegrableOn (fun y : ℝ ↦ y ^ s * exp (-1 * y ^ 2)) (Ioi 0) :=
  integrableOn_rpow_mul_exp_neg_mul_sq one_pos hs

theorem integrable_gaussOneC : Integrable (fun z : ℂ ↦ exp (-‖z‖ ^ 2)) := by
  refine (integrable_fun_norm_addHaar volume (f := fun y : ℝ ↦ exp (-y ^ 2))).mpr ?_
  have hd : Module.finrank ℝ ℂ - 1 = 1 := by simp [Complex.finrank_real_complex]
  simp only [hd, pow_one, smul_eq_mul]
  refine (integrableOn_rpow_mul_exp_neg_sq_Ioi 1 (by norm_num)).congr_fun
    (fun y _ ↦ by simp [Real.rpow_one]) measurableSet_Ioi

private theorem mul_abs_log_mul_le {a : ℝ} (ha : 0 < a) (y : ℝ) (hy : 0 < y) :
    y * |log (a * y)| ≤ |log a| * y ^ (1 : ℝ) + 2 * y ^ (3 / 2 : ℝ) + 2 * y ^ (1 / 2 : ℝ) := by
  have h1 : log y ≤ 2 * y ^ (1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div hy.le (show (0 : ℝ) < 1 / 2 by norm_num)
    linarith
  have h2 : -log y ≤ 2 * y ^ (-1 / 2 : ℝ) := by
    have := Real.log_le_rpow_div (inv_pos.mpr hy).le (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [Real.log_inv, Real.inv_rpow hy.le, ← Real.rpow_neg hy.le] at this
    have e : (-(1 / 2 : ℝ)) = -1 / 2 := by norm_num
    rw [e] at this
    linarith
  have p1 := Real.rpow_nonneg hy.le (1 / 2 : ℝ)
  have p2 := Real.rpow_nonneg hy.le (-1 / 2 : ℝ)
  have habs : |log y| ≤ 2 * y ^ (1 / 2 : ℝ) + 2 * y ^ (-1 / 2 : ℝ) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  have hlog : |log (a * y)| ≤ |log a| + |log y| := by
    rw [Real.log_mul ha.ne' hy.ne']; exact abs_add_le _ _
  have e1 : y * y ^ (1 / 2 : ℝ) = y ^ (3 / 2 : ℝ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hy, Real.rpow_one]
  have e2 : y * y ^ (-1 / 2 : ℝ) = y ^ (1 / 2 : ℝ) := by
    rw [show (1 / 2 : ℝ) = 1 + (-1 / 2) by norm_num, Real.rpow_add hy, Real.rpow_one]
  calc y * |log (a * y)| ≤ y * (|log a| + (2 * y ^ (1 / 2 : ℝ) + 2 * y ^ (-1 / 2 : ℝ))) := by
        gcongr; exact hlog.trans (by linarith)
    _ = |log a| * y ^ (1 : ℝ) + 2 * y ^ (3 / 2 : ℝ) + 2 * y ^ (1 / 2 : ℝ) := by
        rw [Real.rpow_one]; linear_combination 2 * e1 + 2 * e2

theorem integrable_gaussLogC {a : ℝ} (ha : 0 < a) :
    Integrable (fun z : ℂ ↦ log (a * ‖z‖) * exp (-‖z‖ ^ 2)) := by
  refine (integrable_fun_norm_addHaar volume
    (f := fun y : ℝ ↦ log (a * y) * exp (-y ^ 2))).mpr ?_
  have hd : Module.finrank ℝ ℂ - 1 = 1 := by simp [Complex.finrank_real_complex]
  simp only [hd, pow_one, smul_eq_mul]
  have hg : IntegrableOn (fun y : ℝ ↦ (|log a| * y ^ (1 : ℝ) + 2 * y ^ (3 / 2 : ℝ) +
      2 * y ^ (1 / 2 : ℝ)) * exp (-1 * y ^ 2)) (Ioi 0) := by
    have := (((integrableOn_rpow_mul_exp_neg_sq_Ioi 1 (by norm_num)).const_mul |log a|).add
      ((integrableOn_rpow_mul_exp_neg_sq_Ioi (3 / 2) (by norm_num)).const_mul 2)).add
      ((integrableOn_rpow_mul_exp_neg_sq_Ioi (1 / 2) (by norm_num)).const_mul 2)
    refine this.congr (ae_restrict_of_forall_mem measurableSet_Ioi fun y _ ↦ ?_)
    simp only [Pi.add_apply]
    ring
  refine Integrable.mono' hg (by fun_prop) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun y hy ↦ ?_
  have hy' : (0 : ℝ) < y := hy
  rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos hy', abs_of_pos (exp_pos _), neg_one_mul, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_abs_log_mul_le ha y hy') (exp_pos _).le

end ReciprocityTheory.MultiplicativeHeights
end
end

-- bundled from ReciprocityTheory.SemistableReduction.SemiDegCB
section
noncomputable section

namespace ReciprocityTheory.MultiplicativeHeights.SemiDegIdx

open NumberField
open scoped nonZeroDivisors

def consZero (K : Type) [Field K] (k : ℕ) : (Fin k → K) →ₗ[K] (Fin (k + 1) → K) where
  toFun y := Fin.cons 0 y
  map_add' x y := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' a x := by
    ext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

@[simp] theorem consZero_zero (K : Type) [Field K] {k : ℕ} (y : Fin k → K) :
    consZero K k y 0 = 0 := rfl

@[simp] theorem consZero_succ (K : Type) [Field K] {k : ℕ} (y : Fin k → K) (i : Fin k) :
    consZero K k y i.succ = y i := rfl

theorem consZero_injective (K : Type) [Field K] (k : ℕ) : Function.Injective (consZero K k) := by
  intro x y h
  funext i
  simpa using congrFun h i.succ

theorem consZero_tail (K : Type) [Field K] {k : ℕ} (x : Fin (k + 1) → K) (hx : x 0 = 0) :
    consZero K k (Fin.tail x) = x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [hx]
  · simp [Fin.tail]

theorem single_mem_intVec (K : Type) [Field K] [NumberField K] {k : ℕ} (i : Fin k) {a : K}
    (ha : a ∈ (1 : Submodule (𝓞 K) K)) : Pi.single i a ∈ intVec K k := by
  classical
  simp only [intVec, Submodule.mem_pi, Set.mem_univ, forall_const]
  intro j
  by_cases h : j = i
  · subst h
    simpa using ha
  · simp [Pi.single_apply, h, Submodule.zero_mem]

theorem consZero_mem_intVec (K : Type) [Field K] [NumberField K] {k : ℕ} {y : Fin k → K} :
    consZero K k y ∈ intVec K (k + 1) ↔ y ∈ intVec K k := by
  simp only [intVec, Submodule.mem_pi, Set.mem_univ, forall_const]
  constructor
  · intro h i
    simpa using h i.succ
  · intro h i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Submodule.zero_mem]
    · simpa using h j

theorem lattice_split (K : Type) [Field K] [NumberField K] : ∀ (k : ℕ)
    (X : Submodule (𝓞 K) (Fin k → K)), X.FG → intVec K k ≤ X →
    ∃ (C : Fin k → Submodule (𝓞 K) K) (z : Fin k → Fin k → K),
      (∀ i, (C i).FG) ∧ (∀ i, 1 ≤ C i) ∧ (∀ j i : Fin k, i < j → z j i = 0) ∧
      (∀ j, z j j = 1) ∧
      (∀ t : Fin k → K, (∀ i, t i ∈ C i) → ∑ i, t i • z i ∈ X) ∧
      (∀ x ∈ X, ∃ t : Fin k → K, (∀ i, t i ∈ C i) ∧ x = ∑ i, t i • z i) ∧
      (intVec K k).toAddSubgroup.relIndex X.toAddSubgroup =
        ∏ i, (1 : Submodule (𝓞 K) K).toAddSubgroup.relIndex (C i).toAddSubgroup
  | 0, X, _, _ => by
    refine ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun j => j.elim0,
      fun j => j.elim0, fun t _ => ?_, fun x _ => ⟨Fin.elim0, fun i => i.elim0, ?_⟩, ?_⟩
    · convert X.zero_mem using 1
    · ext i
      exact i.elim0
    · simp only [Finset.univ_eq_empty, Finset.prod_empty]
      rw [AddSubgroup.relIndex_eq_one]
      intro x _
      rw [Submodule.mem_toAddSubgroup, mem_intVec]
      intro i
      exact i.elim0
  | k + 1, X, hfg, hstd => by
    let p0 : (Fin (k + 1) → K) →ₗ[K] K := LinearMap.proj 0
    set C0 := X.map (p0.restrictScalars (𝓞 K)) with hC0
    have hC0fg : C0.FG := hfg.map _
    have hC01 : 1 ≤ C0 := by
      intro a ha
      exact Submodule.mem_map.2 ⟨Pi.single 0 a, hstd (single_mem_intVec K 0 ha), by simp [p0]⟩
    obtain ⟨v, hv1, hv⟩ := exists_section_of_image X p0 hC0fg hC01
    let cz := (consZero K k).restrictScalars (𝓞 K)
    let X' : Submodule (𝓞 K) (Fin k → K) := X.comap cz
    have hX'fg : X'.FG := by
      apply Submodule.fg_of_fg_map_injective cz (consZero_injective K k)
      have : IsNoetherian (𝓞 K) X := isNoetherian_of_fg_of_noetherian X hfg
      exact Submodule.FG.of_le_of_isNoetherian (Submodule.map_comap_le _ _)
    have hstd' : intVec K k ≤ X' := fun y hy =>
      hstd ((consZero_mem_intVec K).2 hy)
    obtain ⟨C', z', hfg', h1', htri', hdiag', hin', hdec', hidx'⟩ :=
      lattice_split K k X' hX'fg hstd'
    let C : Fin (k + 1) → Submodule (𝓞 K) K := Fin.cons C0 C'
    let z : Fin (k + 1) → Fin (k + 1) → K := Fin.cons v fun j => consZero K k (z' j)
    have hsum : ∀ t : Fin (k + 1) → K,
        ∑ i, t i • z i = t 0 • v + consZero K k (∑ j, t j.succ • z' j) := by
      intro t
      rw [Fin.sum_univ_succ, map_sum]
      simp [z, map_smul]
    refine ⟨C, z, fun i => Fin.cases hC0fg hfg' i, fun i => Fin.cases hC01 h1' i, ?_, ?_, ?_, ?_, ?_⟩
    · intro j i hij
      induction j using Fin.cases with
      | zero => exact absurd hij (Fin.not_lt_zero i)
      | succ j =>
        induction i using Fin.cases with
        | zero => rfl
        | succ i => exact htri' j i (Fin.succ_lt_succ_iff.1 hij)
    · intro j
      induction j using Fin.cases with
      | zero => exact hv1
      | succ j => exact hdiag' j
    · intro t ht
      rw [hsum]
      refine X.add_mem (hv _ (ht 0)) ?_
      exact hin' (fun j => t j.succ) (fun j => ht j.succ)
    · intro x hx
      have ht0 : x 0 ∈ C0 := Submodule.mem_map.2 ⟨x, hx, rfl⟩
      set y := x - x 0 • v with hy
      have hyX : y ∈ X := X.sub_mem hx (hv _ ht0)
      have hy0 : y 0 = 0 := by
        have : p0 v = v 0 := rfl
        simp [hy, ← this, hv1]
      have hyX' : Fin.tail y ∈ X' := by
        show cz (Fin.tail y) ∈ X
        exact (consZero_tail K y hy0).symm ▸ hyX
      obtain ⟨t', ht', hyt⟩ := hdec' _ hyX'
      refine ⟨Fin.cons (x 0) t', fun i => Fin.cases ht0 ht' i, ?_⟩
      rw [hsum]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [← hyt, consZero_tail K y hy0, hy]
      abel
    · have hA : (intVec K (k + 1)).toAddSubgroup.map p0.toAddMonoidHom =
          (1 : Submodule (𝓞 K) K).toAddSubgroup := by
        ext a
        simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup]
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact mem_intVec.1 hx 0
        · intro ha
          exact ⟨Pi.single 0 a, single_mem_intVec K 0 ha, by simp [p0]⟩
      have hB : X.toAddSubgroup.map p0.toAddMonoidHom = C0.toAddSubgroup := by
        ext a
        simp [C0, Submodule.mem_map]
      have hAk : (intVec K (k + 1)).toAddSubgroup ⊓ p0.toAddMonoidHom.ker =
          (intVec K k).toAddSubgroup.map (consZero K k).toAddMonoidHom := by
        ext x
        simp only [AddSubgroup.mem_inf, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup,
          AddMonoidHom.mem_ker]
        constructor
        · rintro ⟨hx, h0⟩
          refine ⟨Fin.tail x, ?_, consZero_tail K x h0⟩
          rw [← consZero_mem_intVec K, consZero_tail K x h0]
          exact hx
        · rintro ⟨y, hy, rfl⟩
          exact ⟨(consZero_mem_intVec K).2 hy, rfl⟩
      have hBk : X.toAddSubgroup ⊓ p0.toAddMonoidHom.ker =
          X'.toAddSubgroup.map (consZero K k).toAddMonoidHom := by
        ext x
        simp only [AddSubgroup.mem_inf, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup,
          AddMonoidHom.mem_ker]
        constructor
        · rintro ⟨hx, h0⟩
          refine ⟨Fin.tail x, ?_, consZero_tail K x h0⟩
          show cz (Fin.tail x) ∈ X
          exact (consZero_tail K x h0).symm ▸ hx
        · rintro ⟨y, hy, rfl⟩
          exact ⟨hy, rfl⟩
      rw [relIndex_eq_map_mul_ker p0.toAddMonoidHom
          ((Submodule.toAddSubgroup_le _ _).2 hstd), hA, hB, hAk, hBk,
        AddSubgroup.relIndex_map_map_of_injective _ _ (consZero_injective K k), hidx',
        Fin.prod_univ_succ]
      rfl

end ReciprocityTheory.MultiplicativeHeights.SemiDegIdx
end
end

-- bundled from ReciprocityTheory.SemistableReduction.TorusLexB
section
namespace ReciprocityTheory.MultiplicativeHeights.TorusLexOrder

open MeasureTheory ComplexConjugate

theorem torusProb_isProb (ι : Type) [Fintype ι] : IsProbabilityMeasure (torusProb ι) := by
  constructor
  rw [torusProb, Measure.pi_univ]
  simp [Real.volume_Ioc]

noncomputable def torusFactor (a b : ℕ) (x : ℝ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) ^ a *
    conj (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ b

theorem torus_one_dim (a b : ℕ) :
    ∫ x in Set.Ioc (0 : ℝ) 1, torusFactor a b x = if a = b then 1 else 0 := by
  have key : ∀ x : ℝ, torusFactor a b x =
      Complex.exp ((2 * Real.pi * Complex.I * ((a : ℂ) - b)) * x) := by
    intro x
    simp only [torusFactor, ← Complex.exp_conj, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [← intervalIntegral.integral_of_le zero_le_one]
  simp_rw [key]
  split_ifs with h
  · subst h; simp
  · have hab : ((a : ℂ) - b) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast h)
    have hc : (2 * Real.pi * Complex.I * ((a : ℂ) - b)) ≠ 0 := by
      refine mul_ne_zero (mul_ne_zero (mul_ne_zero two_ne_zero ?_) Complex.I_ne_zero) hab
      exact_mod_cast Real.pi_ne_zero
    rw [integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) - b) * ((1 : ℝ) : ℂ)) = 1 := by
      rw [Complex.exp_eq_one_iff]
      exact ⟨(a : ℤ) - b, by push_cast; ring⟩
    rw [h1]; simp

noncomputable def torusMono {ι : Type} [Fintype ι] (θ : ι → ℝ) (s : ι →₀ ℕ) : ℂ :=
  ∏ i, torusPoint θ i ^ s i

theorem norm_torusPoint {ι : Type} (θ : ι → ℝ) (i : ι) : ‖torusPoint θ i‖ = 1 := by
  simp only [torusPoint]
  have h : 2 * (Real.pi : ℂ) * Complex.I * (θ i : ℂ) = ((2 * Real.pi * θ i : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

theorem norm_torusMono {ι : Type} [Fintype ι] (θ : ι → ℝ) (s : ι →₀ ℕ) :
    ‖torusMono θ s‖ = 1 := by
  simp [torusMono, norm_prod, norm_pow, norm_torusPoint]

theorem continuous_torusPoint {ι : Type} : Continuous (fun θ : ι → ℝ => torusPoint θ) := by
  exact continuous_pi fun i => by simp only [torusPoint]; fun_prop

theorem continuous_torusMono {ι : Type} [Fintype ι] (s : ι →₀ ℕ) :
    Continuous (fun θ : ι → ℝ => torusMono θ s) := by
  unfold torusMono
  exact continuous_finset_prod _ fun i _ => ((continuous_apply i).comp continuous_torusPoint).pow _

theorem torus_orth {ι : Type} [Fintype ι] (s t : ι →₀ ℕ) :
    ∫ θ, torusMono θ t * conj (torusMono θ s) ∂(torusProb ι) = if t = s then 1 else 0 := by
  classical
  have h : ∀ θ : ι → ℝ, torusMono θ t * conj (torusMono θ s) =
      ∏ i, torusFactor (t i) (s i) (θ i) := by
    intro θ
    simp only [torusMono, torusFactor, torusPoint, map_prod, map_pow, ← Finset.prod_mul_distrib]
  simp_rw [h]
  rw [torusProb, integral_fintype_prod_eq_prod (f := fun i x => torusFactor (t i) (s i) x)]
  simp_rw [torus_one_dim]
  split_ifs with hts
  · subst hts; simp
  · have : ∃ i, t i ≠ s i := by
      by_contra hc; push_neg at hc; exact hts (Finsupp.ext hc)
    obtain ⟨i, hi⟩ := this
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

theorem integrable_of_bdd {ι : Type} [Fintype ι] {E : Type*} [NormedAddCommGroup E]
    {g : (ι → ℝ) → E} (hg : Continuous g) (C : ℝ) (hC : ∀ θ, ‖g θ‖ ≤ C) :
    Integrable g (torusProb ι) := by
  haveI := torusProb_isProb ι
  exact Integrable.of_bound hg.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem eval_torus {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) (θ : ι → ℝ) :
    MvPolynomial.eval (torusPoint θ) f = ∑ s ∈ f.support, f.coeff s * torusMono θ s := by
  rw [MvPolynomial.eval_eq']; rfl

theorem norm_eval_torus_le {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) (θ : ι → ℝ) :
    ‖MvPolynomial.eval (torusPoint θ) f‖ ≤ ∑ s ∈ f.support, ‖f.coeff s‖ := by
  rw [eval_torus]
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [norm_mul, norm_torusMono, mul_one]

theorem continuous_eval_torus {ι : Type} [Fintype ι] (f : MvPolynomial ι ℂ) :
    Continuous (fun θ : ι → ℝ => MvPolynomial.eval (torusPoint θ) f) := by
  exact (MvPolynomial.continuous_eval f).comp continuous_torusPoint

end ReciprocityTheory.MultiplicativeHeights.TorusLexOrder
end

