import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0493
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0507
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntiJMulApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0388
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EmbGLMemRealSU
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormGramDetEqIndex
section
open NumberField

namespace GlobalTheory.DualIndex

theorem relIndex_dvd_of_le_right {G : Type*} [AddCommGroup G] (H K K' : AddSubgroup G)
    (h1 : H ≤ K') (h2 : K ≤ K') : H.relIndex K ∣ H.relIndex K' := by
  rw [← AddSubgroup.relIndex_sup_left K H,
    ← AddSubgroup.relIndex_mul_relIndex H (H ⊔ K) K' le_sup_left (sup_le h1 h2)]
  exact dvd_mul_right _ _

theorem absNorm_eq_index' {F : Type} [Field F] [NumberField F] (I : Ideal (𝓞 F)) :
    Ideal.absNorm I = I.toAddSubgroup.index := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]; rfl

theorem inv_relIndex_dvd {F : Type} [Field F] [NumberField F] (I : Ideal (𝓞 F))
    (K : AddSubgroup F) (hK : ∀ f ∈ K, ∀ i ∈ I, i • f ∈ (1 : Submodule (𝓞 F) F)) :
    (1 : Submodule (𝓞 F) F).toAddSubgroup.relIndex K ∣ I.toAddSubgroup.index := by
  by_cases hI : I = ⊥
  · rw [← absNorm_eq_index', hI]; simp
  obtain ⟨a, haI, ha⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨J, hJ⟩ : I ∣ Ideal.span {a} := Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 haI)
  have hinj : Function.Injective (algebraMap (𝓞 F) F) := FaithfulSMul.algebraMap_injective _ _
  have haF : algebraMap (𝓞 F) F a ≠ 0 := by simpa using ha
  have hmul : Function.Injective (AddMonoidHom.mulLeft (algebraMap (𝓞 F) F a)) :=
    mul_right_injective₀ haF
  have hJ0 : Ideal.absNorm J ≠ 0 := by
    intro h
    rw [Ideal.absNorm_eq_zero_iff] at h
    rw [h, Ideal.mul_bot, Ideal.span_singleton_eq_bot] at hJ
    exact ha hJ
  have hle : (Ideal.span {a}).toAddSubgroup ≤ J.toAddSubgroup := by
    have : Ideal.span {a} ≤ J := Ideal.dvd_iff_le.1 ⟨I, by rw [hJ, mul_comm]⟩
    exact this
  have h1 : (Ideal.span {a}).toAddSubgroup.relIndex J.toAddSubgroup = I.toAddSubgroup.index := by
    have := AddSubgroup.relIndex_mul_index hle
    rw [← absNorm_eq_index', ← absNorm_eq_index', hJ, map_mul] at this
    rw [← absNorm_eq_index', hJ]
    exact mul_right_cancel₀ hJ0 this
  rw [← h1, ← AddSubgroup.relIndex_map_map_of_injective _ _ hmul,
    ← AddSubgroup.relIndex_map_map_of_injective (f := (algebraMap (𝓞 F) F).toAddMonoidHom)
      (Ideal.span {a}).toAddSubgroup _ hinj]
  have e : AddSubgroup.map (AddMonoidHom.mulLeft (algebraMap (𝓞 F) F a))
      (1 : Submodule (𝓞 F) F).toAddSubgroup =
      AddSubgroup.map (algebraMap (𝓞 F) F).toAddMonoidHom (Ideal.span {a}).toAddSubgroup := by
    ext z
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_one,
      Ideal.mem_span_singleton']
    constructor
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨c * a, ⟨c, rfl⟩, by simp [mul_comm]⟩
    · rintro ⟨_, ⟨c, rfl⟩, rfl⟩
      exact ⟨_, ⟨c, rfl⟩, by simp [mul_comm]⟩
  rw [e]
  refine relIndex_dvd_of_le_right _ _ _ (AddSubgroup.map_mono hle) ?_
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hK f hf a haI)
  refine ⟨c, ?_, by simpa [Algebra.smul_def] using hc⟩
  have : I * Ideal.span {c} ≤ I * J := by
    rw [← hJ, Ideal.mul_le]
    intro i hi s hs
    obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hs
    obtain ⟨d, hd⟩ := Submodule.mem_one.1 (hK f hf i hi)
    refine Ideal.mem_span_singleton'.2 ⟨t * d, hinj ?_⟩
    simp only [map_mul, hc, hd, Algebra.smul_def]
    ring
  have h2 : J ∣ Ideal.span {c} := by
    rw [← Ideal.dvd_iff_le] at this
    exact (mul_dvd_mul_iff_left hI).1 this
  exact (Ideal.span_singleton_le_iff_mem _).1 (Ideal.dvd_iff_le.1 h2)

variable {F : Type} [Field F] [NumberField F] {V : Type} [AddCommGroup V] [Module F V]
  [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (B : LinearMap.BilinForm F V)

theorem dual_anti {M L : Submodule (𝓞 F) V} (h : M ≤ L) :
    B.dualSubmodule L ≤ B.dualSubmodule M := fun _ hy x hx => hy x (h hx)

theorem dual_step (M : Submodule (𝓞 F) V) (x : V) :
    (B.dualSubmodule (M ⊔ Submodule.span (𝓞 F) {x})).toAddSubgroup.relIndex
      (B.dualSubmodule M).toAddSubgroup ∣
    M.toAddSubgroup.relIndex (M ⊔ Submodule.span (𝓞 F) {x}).toAddSubgroup := by
  have e1 : M.toAddSubgroup.relIndex (M ⊔ Submodule.span (𝓞 F) {x}).toAddSubgroup =
      (M.comap (LinearMap.toSpanSingleton (𝓞 F) V x)).toAddSubgroup.index := by
    rw [Submodule.sup_toAddSubgroup, AddSubgroup.relIndex_sup_left]
    have := AddSubgroup.index_comap M.toAddSubgroup
      (LinearMap.toSpanSingleton (𝓞 F) V x).toAddMonoidHom
    rw [show (LinearMap.toSpanSingleton (𝓞 F) V x).toAddMonoidHom.range =
      (Submodule.span (𝓞 F) {x}).toAddSubgroup from by
        ext z; simp [Submodule.mem_span_singleton]] at this
    exact this.symm
  have e2 : (B.dualSubmodule (M ⊔ Submodule.span (𝓞 F) {x})).toAddSubgroup =
      ((1 : Submodule (𝓞 F) F).toAddSubgroup.comap (B.flip x).toAddMonoidHom) ⊓
        (B.dualSubmodule M).toAddSubgroup := by
    ext y
    simp only [Submodule.mem_toAddSubgroup, LinearMap.BilinForm.mem_dualSubmodule,
      AddSubgroup.mem_inf, AddSubgroup.mem_comap]
    constructor
    · intro h
      exact ⟨h x (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)),
        fun z hz => h z (Submodule.mem_sup_left hz)⟩
    · rintro ⟨h1, h2⟩ z hz
      obtain ⟨m, hm, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [map_add, LinearMap.map_smul_of_tower]
      exact add_mem (h2 m hm) (Submodule.smul_mem _ c h1)
  rw [e1, e2, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap]
  refine inv_relIndex_dvd _ _ ?_
  rintro _ ⟨y, hy, rfl⟩ i hi
  have := hy (i • x) hi
  rwa [LinearMap.map_smul_of_tower] at this

theorem dual_relIndex_dvd (M : Submodule (𝓞 F) V) (s : Finset V) :
    (B.dualSubmodule (M ⊔ Submodule.span (𝓞 F) (s : Set V))).toAddSubgroup.relIndex
      (B.dualSubmodule M).toAddSubgroup ∣
    M.toAddSubgroup.relIndex (M ⊔ Submodule.span (𝓞 F) (s : Set V)).toAddSubgroup := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s _ ih =>
    have e : M ⊔ Submodule.span (𝓞 F) ((insert x s : Finset V) : Set V) =
        (M ⊔ Submodule.span (𝓞 F) (s : Set V)) ⊔ Submodule.span (𝓞 F) {x} := by
      rw [Finset.coe_insert, Submodule.span_insert, sup_assoc, sup_comm (Submodule.span _ {x})]
    rw [e]
    set N := M ⊔ Submodule.span (𝓞 F) (s : Set V) with hN
    have hMN : M ≤ N := le_sup_left
    rw [← AddSubgroup.relIndex_mul_relIndex M.toAddSubgroup N.toAddSubgroup
      (N ⊔ Submodule.span (𝓞 F) {x}).toAddSubgroup hMN (le_sup_left (a := N)),
      ← AddSubgroup.relIndex_mul_relIndex _ (B.dualSubmodule N).toAddSubgroup
      (B.dualSubmodule M).toAddSubgroup (dual_anti B (le_sup_left (a := N))) (dual_anti B hMN),
      mul_comm]
    exact mul_dvd_mul ih (dual_step B N x)

theorem dual_relIndex_dvd' {M L : Submodule (𝓞 F) V} (h : M ≤ L) (hL : L.FG) :
    (B.dualSubmodule L).toAddSubgroup.relIndex (B.dualSubmodule M).toAddSubgroup ∣
    M.toAddSubgroup.relIndex L.toAddSubgroup := by
  obtain ⟨s, hs⟩ := hL
  have := dual_relIndex_dvd B M s
  rwa [hs, sup_eq_right.2 h] at this

theorem span_eq_closure [Module ℚ V] [IsScalarTower ℚ F V] {n : ℕ} (b : Module.Basis (Fin n) F V) :
    (Submodule.span (𝓞 F) (Set.range b)).toAddSubgroup =
      AddSubgroup.closure (Set.range ((integralBasis F).smulTower b)) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨f, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hx
    refine sum_mem fun j _ => ?_
    rw [← (RingOfIntegers.basis F).sum_repr (f j), Finset.sum_smul]
    refine sum_mem fun i _ => ?_
    rw [smul_assoc]
    refine AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure
      (Set.mem_range.2 ⟨(i, j), ?_⟩)) _
    rw [Module.Basis.smulTower_apply, integralBasis_apply, algebraMap_smul]
  · rw [AddSubgroup.closure_le]
    rintro _ ⟨⟨i, j⟩, rfl⟩
    rw [Module.Basis.smulTower_apply, integralBasis_apply, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem relIndex_span_eq_norm {n : ℕ} (b c : Module.Basis (Fin n) F V)
    (h : Submodule.span (𝓞 F) (Set.range b) ≤ Submodule.span (𝓞 F) (Set.range c)) :
    (((Submodule.span (𝓞 F) (Set.range b)).toAddSubgroup.relIndex
      (Submodule.span (𝓞 F) (Set.range c)).toAddSubgroup : ℕ) : ℚ) =
      |Algebra.norm ℚ (c.det b)| := by
  classical
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ F)
  haveI : IsScalarTower ℚ F V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : Module.Free F V := Module.Free.of_basis b
  rw [AddSubgroup.relIndex_eq_abs_det _ _ h _ _ (span_eq_closure b) (span_eq_closure c)]
  set f : V →ₗ[F] V := (c.equiv b (Equiv.refl _)).toLinearMap with hf
  have h1 : (b : Fin n → V) = f ∘ c := by ext i; simp [hf]
  have h2 : (((integralBasis F).smulTower b : Module.Basis _ ℚ V) : _ → V) =
      (f.restrictScalars ℚ) ∘ ((integralBasis F).smulTower c) := by
    ext ⟨i, j⟩
    simp only [Function.comp_apply, Module.Basis.smulTower_apply, LinearMap.restrictScalars_apply,
      map_smul]
    rw [h1]; rfl
  rw [h2, Module.Basis.det_comp, Module.Basis.det_self, mul_one, LinearMap.det_restrictScalars]
  conv_rhs => rw [h1, Module.Basis.det_comp, Module.Basis.det_self, mul_one]

theorem mem_one_iff (z : F) : z ∈ (1 : Submodule (𝓞 F) F) ↔ IsIntegral ℤ z := by
  rw [Submodule.mem_one]
  constructor
  · rintro ⟨c, rfl⟩; exact c.isIntegral_coe
  · intro h; exact ⟨⟨z, h⟩, rfl⟩

end GlobalTheory.DualIndex

open GlobalTheory.DualIndex in

theorem GlobalTheory.abs_norm_det_gram_eq_relIndex : ∀ (F : Type) [Field F] [NumberField F] (V : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] (n : ℕ) (b : Module.Basis (Fin n) F V) (B : LinearMap.BilinForm F V) (L : AddSubgroup V), B.IsSymm → B.Nondegenerate → (∀ i, b i ∈ L) → (∀ (a : 𝓞 F) x, x ∈ L → a • x ∈ L) → (∀ x ∈ L, ∀ y ∈ L, IsIntegral ℤ (B x y)) → |((Algebra.norm ℚ (Matrix.of fun i j => B (b i) (b j)).det : ℚ) : ℝ)| = (L.relIndex (AddSubgroup.closure {y | ∀ x ∈ L, IsIntegral ℤ (B x y)}) : ℝ) * ((Submodule.span (𝓞 F) (Set.range b)).toAddSubgroup.relIndex L : ℝ) ^ 2 := by
  intro F _ _ V _ _ _ _ n b B L hs hB hb hL hint
  classical
  let Λ : Submodule (𝓞 F) V :=
    { L.toAddSubmonoid with smul_mem' := fun a x hx => hL a x hx }
  have hΛ : Λ.toAddSubgroup = L := rfl
  set M := Submodule.span (𝓞 F) (Set.range b) with hM
  have hcl : AddSubgroup.closure {y | ∀ x ∈ L, IsIntegral ℤ (B x y)} =
      (B.dualSubmodule Λ).toAddSubgroup := by
    rw [← AddSubgroup.closure_eq (B.dualSubmodule Λ).toAddSubgroup]
    congr 1
    ext y
    change (∀ x ∈ L, IsIntegral ℤ (B x y)) ↔ ∀ x ∈ L, B y x ∈ (1 : Submodule (𝓞 F) F)
    refine forall₂_congr fun x _ => ?_
    rw [mem_one_iff, hs.eq x y]
  have hML : M ≤ Λ := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i)
  have hLL : Λ ≤ B.dualSubmodule Λ := fun x hx y hy => (mem_one_iff _).2 (hint x hx y hy)
  have hLM : B.dualSubmodule Λ ≤ B.dualSubmodule M := dual_anti B hML
  have hdual := B.dualSubmodule_span_of_basis (R := 𝓞 F) hB b
  have hdd := B.dualSubmodule_dualSubmodule_of_basis (R := 𝓞 F) hB hs b
  rw [← hM] at hdual hdd
  have hfg : (B.dualSubmodule M).FG := by
    rw [hdual]; exact Submodule.fg_span (Set.finite_range _)
  have hfgΛ : Λ.FG := Submodule.FG.of_le hfg (hLL.trans hLM)
  have d1 := dual_relIndex_dvd' B hML hfgΛ
  have d2 := dual_relIndex_dvd' B hLM hfg
  rw [hdd] at d2
  have hΛdd : Λ ≤ B.dualSubmodule (B.dualSubmodule Λ) := fun x hx y hy => by
    rw [hs.eq x y]; exact hy x hx
  have d3 := relIndex_dvd_of_le_right M.toAddSubgroup Λ.toAddSubgroup
    (B.dualSubmodule (B.dualSubmodule Λ)).toAddSubgroup (hML.trans hΛdd) hΛdd
  have hb' := Nat.dvd_antisymm d1 (d3.trans d2)
  have hle : M ≤ Submodule.span (𝓞 F) (Set.range (B.dualBasis hB b)) := by
    rw [← hdual]; exact hML.trans (hLL.trans hLM)
  have ha := relIndex_span_eq_norm b (B.dualBasis hB b) hle
  rw [← hM, ← hdual, ← AddSubgroup.relIndex_mul_relIndex M.toAddSubgroup Λ.toAddSubgroup
      (B.dualSubmodule M).toAddSubgroup hML (hLL.trans hLM),
    ← AddSubgroup.relIndex_mul_relIndex Λ.toAddSubgroup (B.dualSubmodule Λ).toAddSubgroup
      (B.dualSubmodule M).toAddSubgroup hLL hLM, hb'] at ha
  have hdet : (B.dualBasis hB b).det b = (Matrix.of fun i j => B (b i) (b j)).det := by
    rw [Module.Basis.det_apply, ← Matrix.det_transpose]
    congr 1
    ext i j
    simp [Module.Basis.toMatrix_apply, LinearMap.BilinForm.dualBasis_repr_apply]
  rw [hdet, hΛ] at ha
  rw [hcl, ← Rat.cast_abs, ← ha]
  push_cast
  ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicBoundedGaussianSummableCmType
section
open NumberField MeasureTheory

noncomputable section

namespace GlobalTheory.HeckeLat

variable {K : Type} [Field K] [NumberField K] {I : Type} [Fintype I]

theorem exists_one_le_norm {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {α : 𝓞 K} (hα : α ≠ 0) :
    ∃ i, 1 ≤ ‖φ i (α : K)‖ := by
  by_contra h
  push_neg at h
  have hlt : ∀ w : InfinitePlace K, w (α : K) < 1 := by
    intro w
    obtain ⟨i, hi, -⟩ := hφ w.embedding
    rw [← InfinitePlace.norm_embedding_eq]
    rcases hi with hi | hi
    · rw [hi]; exact h i
    · rw [hi, ComplexEmbedding.conjugate_coe_eq, Complex.norm_conj]; exact h i
  obtain ⟨w⟩ : Nonempty (InfinitePlace K) := inferInstance
  exact absurd (InfinitePlace.one_le_of_lt_one hα (fun z _ => hlt z)) (not_le.2 (hlt w))

theorem one_le_norm_emb {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {α : 𝓞 K}
    (hα : GlobalTheory.HeckeTheta.emb φ (α : K) ≠ 0) : 1 ≤ ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ := by
  have h0 : α ≠ 0 := by
    rintro rfl
    apply hα
    funext i
    simp [GlobalTheory.HeckeTheta.emb]
  obtain ⟨i, hi⟩ := exists_one_le_norm hφ h0
  exact hi.trans (norm_le_pi_norm (GlobalTheory.HeckeTheta.emb φ (α : K)) i)

def embHom (φ : I → K →+* ℂ) : 𝓞 K →+ (I → ℂ) where
  toFun α := GlobalTheory.HeckeTheta.emb φ (α : K)
  map_zero' := by funext i; simp [GlobalTheory.HeckeTheta.emb]
  map_add' a b := by funext i; simp [GlobalTheory.HeckeTheta.emb]

theorem embHom_injective {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) : Function.Injective (embHom φ) := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra h0
  obtain ⟨i, hi⟩ := exists_one_le_norm hφ h0
  have : φ i (a : K) = 0 := congrFun ha i
  rw [this, norm_zero] at hi
  exact absurd hi (by norm_num)

omit [Fintype I] in

theorem summable_exp_neg_mul_norm_sq {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (L : Submodule ℤ E) [DiscreteTopology L] {a : ℝ} (ha : 0 < a) :
    Summable fun x : L ↦ Real.exp (-a * ‖(x : E)‖ ^ 2) := by
  set k := Module.finrank ℤ L + 1 with hk
  have h := (ZLattice.summable_norm_pow_inv L (2 * k) (by omega)).mul_left
    ((k.factorial : ℝ) / a ^ k)
  refine .of_norm_bounded_eventually h ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with x h0
  have hn : 0 < ‖(x : E)‖ := norm_pos_iff.2 (by simpa using h0)
  have h1 := Real.pow_div_factorial_le_exp (a * ‖(x : E)‖ ^ 2) (by positivity) k
  rw [Real.norm_of_nonneg (Real.exp_pos _).le, neg_mul, Real.exp_neg]
  refine (inv_anti₀ (by positivity) h1).trans_eq ?_
  change _ = _ * ‖(x : E)‖⁻¹ ^ (2 * k)
  rw [mul_pow, ← pow_mul, inv_pow]
  field_simp

def embLat (φ : I → K →+* ℂ) : Submodule ℤ (I → ℂ) := LinearMap.range (embHom φ).toIntLinearMap

theorem discrete_embLat {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) : DiscreteTopology (embLat φ) := by
  refine DiscreteTopology.of_forall_le_dist one_pos fun x y hxy => ?_
  obtain ⟨a, ha⟩ := x.2
  obtain ⟨b, hb⟩ := y.2
  rw [Subtype.dist_eq, dist_eq_norm]
  have hsub : (x : I → ℂ) - y = GlobalTheory.HeckeTheta.emb φ ((a - b : 𝓞 K) : K) := by
    rw [← ha, ← hb]
    funext i
    simp [embHom, GlobalTheory.HeckeTheta.emb]
  rw [hsub]
  apply one_le_norm_emb hφ
  rw [← hsub, sub_ne_zero]
  exact fun h => hxy (Subtype.ext h)

theorem summable_exp_emb {φ : I → K →+* ℂ} (hφ : GlobalTheory.CMVal.IsCMType φ) {ε : ℝ} (hε : 0 < ε) :
    Summable fun α : 𝓞 K => Real.exp (-ε * ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ ^ 2) := by
  haveI := discrete_embLat hφ
  have hs : Summable fun x : embLat φ ↦ Real.exp (-ε * ‖(x : I → ℂ)‖ ^ 2) :=
    summable_exp_neg_mul_norm_sq (embLat φ) hε
  have hmem : ∀ α : 𝓞 K, embHom φ α ∈ embLat φ := fun α => LinearMap.mem_range_self _ α
  let j : 𝓞 K → embLat φ := fun α => ⟨embHom φ α, hmem α⟩
  have hj : Function.Injective j := fun a b h => embHom_injective hφ (congrArg Subtype.val h)
  have h2 := hs.comp_injective hj
  refine h2.congr fun α => ?_
  simp only [Function.comp_apply, j]
  rfl

theorem bounded_of_periodic {M : Ideal (𝓞 K)} (F : 𝓞 K → ℂ) (hM : M ≠ ⊥)
    (hF : ∀ α μ : 𝓞 K, μ ∈ M → F (α + μ) = F α) : ∃ C : ℝ, ∀ α, ‖F α‖ ≤ C := by
  haveI := Ideal.finiteQuotientOfFreeOfNeBot M hM
  haveI := Fintype.ofFinite (𝓞 K ⧸ M)
  refine ⟨∑ q : 𝓞 K ⧸ M, ‖F (Quotient.out q)‖, fun α => ?_⟩
  have hmem : α - Quotient.out (Ideal.Quotient.mk M α) ∈ M := by
    rw [← Ideal.Quotient.eq, Ideal.Quotient.mk_out]
  have hα : F α = F (Quotient.out (Ideal.Quotient.mk M α)) := by
    have := hF (Quotient.out (Ideal.Quotient.mk M α)) _ hmem
    rwa [add_sub_cancel] at this
  rw [hα]
  exact Finset.single_le_sum (f := fun q : 𝓞 K ⧸ M => ‖F (Quotient.out q)‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ _)

theorem periodic_bound_summable_norm :
    ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ),
      GlobalTheory.CMVal.IsCMType φ → ∀ (M : Ideal (NumberField.RingOfIntegers K)) (F : NumberField.RingOfIntegers K → ℂ),
      M ≠ ⊥ → (∀ α μ : NumberField.RingOfIntegers K, μ ∈ M → F (α + μ) = F α) → (∃ C : ℝ, ∀ α, ‖F α‖ ≤ C) ∧
      (∀ ε : ℝ, 0 < ε → Summable (fun α : NumberField.RingOfIntegers K =>
        ‖F α‖ * Real.exp (-ε * ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ ^ 2))) ∧
      ∀ α : NumberField.RingOfIntegers K, GlobalTheory.HeckeTheta.emb φ (α : K) ≠ 0 → 1 ≤ ‖GlobalTheory.HeckeTheta.emb φ (α : K)‖ := by
  intro K _ _ _ I _ φ hφ M F hM hF
  obtain ⟨C, hC⟩ := bounded_of_periodic F hM hF
  refine ⟨⟨C, hC⟩, fun ε hε => ?_, fun α hα => one_le_norm_emb hφ hα⟩
  refine ((summable_exp_emb hφ hε).mul_left C).of_nonneg_of_le (fun α => by positivity) fun α => ?_
  exact mul_le_mul_of_nonneg_right (hC α) (Real.exp_pos _).le

end GlobalTheory.HeckeLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelIndexCosetSumUnimodularityOfFiniteIndex
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem finsum_quotient_subgroupOf {A : Type} [Group A] (Γ W : Subgroup A) (F : A → ℂ)
    (hΓ : ∀ a, F a ≠ 0 → a ∈ Γ) (hF : ∀ w ∈ W, ∀ a, F (a * w) = F a) :
    ∑ᶠ y : A ⧸ W, F y.out = ∑ᶠ y : Γ ⧸ W.subgroupOf Γ, F (y.out : Γ) := by
  have hout : ∀ a : A, F (QuotientGroup.mk a : A ⧸ W).out = F a := by
    intro a
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul W a
    rw [hw, hF w w.2]
  let e : Γ ⧸ W.subgroupOf Γ → A ⧸ W := fun y => QuotientGroup.mk ((y.out : Γ) : A)
  have hinj : Function.Injective e := by
    intro y z h
    have h1 : ((y.out : Γ) : A)⁻¹ * ((z.out : Γ) : A) ∈ W := QuotientGroup.eq.1 h
    have h2 : (QuotientGroup.mk y.out : Γ ⧸ W.subgroupOf Γ) = QuotientGroup.mk z.out :=
      QuotientGroup.eq.2 (Subgroup.mem_subgroupOf.2 (by simpa using h1))
    simpa using h2
  have hsupp : (Function.support fun y : A ⧸ W => F y.out) ⊆ Set.range e := by
    intro y hy
    have hm : y.out ∈ Γ := hΓ _ hy
    refine ⟨QuotientGroup.mk ⟨y.out, hm⟩, ?_⟩
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (W.subgroupOf Γ) ⟨y.out, hm⟩
    have hw' : ((w : Γ) : A) ∈ W := Subgroup.mem_subgroupOf.1 w.2
    show (QuotientGroup.mk _ : A ⧸ W) = y
    rw [hw, Subgroup.coe_mul, QuotientGroup.mk_mul_of_mem _ hw']
    exact QuotientGroup.out_eq' y
  calc ∑ᶠ y : A ⧸ W, F y.out = ∑ᶠ y ∈ Set.range e, F y.out := by
        rw [← finsum_mem_univ]
        apply finsum_mem_inter_support_eq
        rw [Set.univ_inter, Set.inter_eq_right.2 hsupp]
    _ = ∑ᶠ y, F (e y).out := finsum_mem_range hinj
    _ = _ := finsum_congr fun y => hout _

theorem unimod_of_unimodFin : UnimodFin → Unimod := by
  intro H A _ Γ U V f _ _ hUi hVi hΓ hfV hfU
  have h := H Γ (U.subgroupOf Γ) (V.subgroupOf Γ) (fun a => f a) hUi hVi
    (fun v hv a => hfV _ (Subgroup.mem_subgroupOf.1 hv) _)
    (fun u hu a => hfU _ (Subgroup.mem_subgroupOf.1 hu) _)
  rw [finsum_quotient_subgroupOf Γ U f hΓ hfU,
    finsum_quotient_subgroupOf Γ V (fun a => f a⁻¹) (fun a ha => (inv_mem_iff.1 (hΓ _ ha)))
      (fun w hw a => by rw [mul_inv_rev, hfV _ (inv_mem hw)])]
  exact h

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialSpectralRowExactZeroOfAcyclicStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite Simplicial GlobalTheory.EtC GlobalTheory.EtC.GmStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simplicialSpectralRowExact_zero_of_acyclic : ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc),
  (∀ (p : ℕ) (s : ℤ), 0 < s → Subsingleton (H R (disc.obj (E.obj (op ⦋p⦌))) F s)) →
  (∀ m : ℤ, 0 < m → Subsingleton (H R E F m)) → ∀ p : ℕ, RowExact R E F 0 p := by
  first | (exact @GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic) | (exact GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic) | (intros; apply GlobalTheory.EtC.GmStep.rowExact_zero_of_acyclic  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallerUnitaryEmbeddingPreservesIntegralParts
section
open Formalism.UG GlobalTheory.SatakeWeyl

namespace GlobalTheory.SatakeWeyl

theorem embMem : EmbMem := by
  intro L _ _ σ n r e β γ ι hσ hD hι g
  obtain ⟨he, -, -, -, -, hβγ⟩ := hD
  obtain ⟨h1, h2⟩ := hι g
  have hcases : ∀ a b : Fin n, (∃ i j, a = e i ∧ b = e j) ∨ (a ∉ Set.range e ∨ b ∉ Set.range e) := by
    intro a b
    by_cases ha : a ∈ Set.range e
    · by_cases hb : b ∈ Set.range e
      · obtain ⟨i, rfl⟩ := ha
        obtain ⟨j, rfl⟩ := hb
        exact Or.inl ⟨i, j, rfl, rfl⟩
      · exact Or.inr (Or.inr hb)
    · exact Or.inr (Or.inl ha)
  refine ⟨?_, ?_, ?_⟩
  · rw [mem_KU_iff hσ, mem_KU_iff hσ]
    refine ⟨fun h i j => h1 i j ▸ h (e i) (e j), fun h a b => ?_⟩
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | hab
    · rw [h1]; exact h i j
    · rw [h2 a b hab, Matrix.one_apply]
      split_ifs
      · exact one_mem _
      · exact zero_mem _
  · intro hg a b hab
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | h
    · rw [h1]
      exact hg i j fun hij => hab ((hβγ i j).2 hij)
    · rw [h2 a b h]
      exact Matrix.one_apply_ne fun h' => hab (h' ▸ rfl)
  · intro hg a b hab
    rcases hcases a b with ⟨i, j, rfl, rfl⟩ | h
    · have hji : j ≤ i := he.le_iff_le.1 hab
      rw [h1, hg i j hji, Matrix.one_apply, Matrix.one_apply]
      simp only [he.injective.eq_iff]
    · exact h2 a b h

end GlobalTheory.SatakeWeyl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryKottwitzEquivalenceStatement
section
open NumberField
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.special_unitary_kottwitz_equivalence : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (L : Set (Fin r → E)) (s s' M : Matrix (Fin r) (Fin r) (GlobalTheory.AdLat.RA (maximalRealSubfield E) E)) (γ : Matrix (Fin r) (Fin r) E), GlobalTheory.SUVol.IsSA G s → GlobalTheory.SUVol.IsSA G s' → GlobalTheory.UCls.IsKM (IsCMField.complexConj E) G L 1 M → s' * M = GlobalTheory.UCls.ratM (maximalRealSubfield E) γ * s → γ.det = 1 → GlobalTheory.SUVol.SEquiv G L 1 s' s := by
  first | exact @GlobalTheory.SEquivOfRat.sequiv_of_rat | exact GlobalTheory.SEquivOfRat.sequiv_of_rat | (intros; apply GlobalTheory.SEquivOfRat.sequiv_of_rat <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitLatticeLevelTraceDenominatorStatement
section
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splitLattice_level_trace_denominator : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (N : ℕ) (𝔞 𝔟 : Frac F) (x ξ : F), HasLevel N (split 𝔞 𝔟 x) → ξ ∈ ((𝔞 * 𝔟 : Frac F) : FractionalIdeal (𝓞 F)⁰ F) → (∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F ξ = n) ∧ ∃ n : ℤ, (N : ℚ) * Algebra.trace ℚ F (ξ * x) = n := by
  first | exact @GlobalTheory.HilbFam.trace_denominator_of_hasLevel | exact GlobalTheory.HilbFam.trace_denominator_of_hasLevel | (intros; apply GlobalTheory.HilbFam.trace_denominator_of_hasLevel <;> assumption)
end

