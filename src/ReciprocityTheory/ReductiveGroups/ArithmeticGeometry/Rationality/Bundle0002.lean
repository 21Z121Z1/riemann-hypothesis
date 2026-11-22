import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.Bundle0001
import ReciprocityTheory.SemistableReduction.ComapInclusionIsLocalHom
import Lemmata.MiscLemmasJ.Imports

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.BasisChangePf
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

namespace BasisChangePf

open MvPolynomial

variable {K : Type*} [NormedField K] [IsUltrametricDist K] {ι : Type*}

def CB (Q : MvPolynomial ι K) (c : ℝ) : Prop := ∀ μ, ‖coeff μ Q‖ ≤ c

lemma cb_sum {α : Type*} (s : Finset α) (g : α → MvPolynomial ι K) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a ∈ s, CB (g a) c) : CB (∑ a ∈ s, g a) c := by
  classical
  intro μ
  rw [MvPolynomial.coeff_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hc (fun a ha => h a ha μ)

lemma cb_mul {Q R : MvPolynomial ι K} {c d : ℝ} (hc : 0 ≤ c) (hQ : CB Q c) (hR : CB R d)
    (hd : 0 ≤ d) : CB (Q * R) (c * d) := by
  classical
  intro μ
  rw [MvPolynomial.coeff_mul]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hc hd) (fun x _ => ?_)
  rw [norm_mul]
  exact mul_le_mul (hQ _) (hR _) (norm_nonneg _) hc

lemma cb_one : CB (1 : MvPolynomial ι K) 1 := by
  classical
  intro μ
  rw [MvPolynomial.coeff_one]
  split_ifs <;> simp

lemma cb_pow {Q : MvPolynomial ι K} {c : ℝ} (hc : 0 ≤ c) (hQ : CB Q c) (n : ℕ) : CB (Q ^ n) (c ^ n) := by
  induction n with
  | zero => simpa using (cb_one : CB (1 : MvPolynomial ι K) 1)
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact cb_mul (pow_nonneg hc n) ih hQ hc

lemma cb_prod {α : Type*} (s : Finset α) (g : α → MvPolynomial ι K) (c : α → ℝ) (hc : ∀ a, 0 ≤ c a)
    (h : ∀ a ∈ s, CB (g a) (c a)) : CB (∏ a ∈ s, g a) (∏ a ∈ s, c a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (cb_one : CB (1 : MvPolynomial ι K) 1)
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact cb_mul (hc a) (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))
      (Finset.prod_nonneg fun b _ => hc b)

lemma cb_C_mul (a : K) {Q : MvPolynomial ι K} {c : ℝ} (hQ : CB Q c) : CB (C a * Q) (‖a‖ * c) := by
  classical
  intro μ
  rw [MvPolynomial.coeff_C_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left (hQ μ) (norm_nonneg a)

lemma cb_lin [Fintype ι] (A : ι → ι → K) {c : ℝ} (hc : 0 ≤ c) (hA : ∀ i k, ‖A i k‖ ≤ c) (i : ι) :
    CB (∑ k, C (A i k) * X k) c := by
  classical
  refine cb_sum _ _ hc (fun k _ => fun μ => ?_)
  rw [MvPolynomial.coeff_C_mul, norm_mul]
  calc ‖A i k‖ * ‖MvPolynomial.coeff μ (X k : MvPolynomial ι K)‖ ≤ ‖A i k‖ * 1 := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [MvPolynomial.coeff_X']
        split_ifs <;> simp
    _ ≤ c := by simpa using hA i k

end BasisChangePf

open BasisChangePf in
theorem basisChange_holds : BasisChangeStatement := by
  intro K _ _ ι _ P d hP hP1 A C hC hA μ
  classical
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hL : ∀ i, CB (∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k : MvPolynomial ι K) C :=
    fun i => cb_lin A hC0 hA i
  have key : CB (MvPolynomial.bind₁ (fun i => ∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) P) (C ^ d) := by
    conv => arg 1; rw [P.as_sum]
    rw [map_sum]
    refine cb_sum _ _ (pow_nonneg hC0 d) (fun v hv => ?_)
    rw [MvPolynomial.bind₁_monomial]
    have hdeg : v.degree = d := by
      rw [Finsupp.degree_eq_weight_one]
      exact hP (MvPolynomial.mem_support_iff.1 hv)
    have hprod : CB (∏ i ∈ v.support, (∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) ^ v i)
        (∏ i ∈ v.support, C ^ v i) :=
      cb_prod _ _ _ (fun i => pow_nonneg hC0 _) (fun i _ => cb_pow hC0 (hL i) (v i))
    have hb := cb_C_mul (MvPolynomial.coeff v P) hprod
    have hpow : ∏ i ∈ v.support, C ^ v i = C ^ d := by
      rw [Finset.prod_pow_eq_pow_sum, ← hdeg]
      rfl
    intro ν
    calc ‖MvPolynomial.coeff ν (MvPolynomial.C (MvPolynomial.coeff v P) *
          ∏ i ∈ v.support, (∑ k, MvPolynomial.C (A i k) * MvPolynomial.X k) ^ v i)‖
        ≤ ‖MvPolynomial.coeff v P‖ * ∏ i ∈ v.support, C ^ v i := hb ν
      _ ≤ 1 * C ^ d := by
          rw [hpow]
          exact mul_le_mul_of_nonneg_right (hP1 v) (pow_nonneg hC0 d)
      _ = C ^ d := one_mul _
  exact key μ

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DescSt
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct

section Defs

variable {K K₂ : Type*} [Field K] [Field K₂] [Algebra K K₂] {V : Type*} [AddCommGroup V]
  [Module K V]

noncomputable def galAct (σ : K₂ ≃ₐ[K] K₂) : K₂ ⊗[K] V →ₗ[K] K₂ ⊗[K] V :=
  LinearMap.rTensor V σ.toLinearMap

def kPoints (W : Submodule K₂ (K₂ ⊗[K] V)) : Submodule K V :=
  (W.restrictScalars K).comap (TensorProduct.mk K K₂ V 1)

end Defs

def GaloisDescentStatement : Prop :=
  ∀ (K K₂ V : Type) [Field K] [Field K₂] [Algebra K K₂] [FiniteDimensional K K₂] [IsGalois K K₂]
    [AddCommGroup V] [Module K V] (W : Submodule K₂ (K₂ ⊗[K] V)),
    (∀ σ : K₂ ≃ₐ[K] K₂, ∀ x ∈ W, galAct σ x ∈ W) →
    W = baseSpan K₂ (kPoints W)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.DiscSt
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

def DiscStatement : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (K₀ : Subfield K),
    ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K) →
    ∀ S : Set K, (∀ t ∈ S, 0 < ‖t‖ ∧ ‖t‖ < 1) →
    (∀ r : ℝ, 0 < r → r < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ S, |‖t‖ - r| < ε) →
    ∀ (c : ℤ → K) (b : ℕ), (∀ n, n < -(b : ℤ) → c n = 0) →
      (∀ t ∈ S,
        Filter.Tendsto (fun n => ‖c n * t ^ n‖) Filter.cofinite (nhds 0) ∧
        ∀ τ ∈ K₀, ‖τ‖ = 1 → ‖∑' n, c n * (t * τ) ^ n‖ ≤ 1) →
      ∀ n, ‖c n‖ ≤ 1 ∧ (n < 0 → c n = 0)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FinCoreSt
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

def FinCoreStatement : Prop :=
  ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (K₀ : Subfield K),
    ReciprocityTheory.MultiplicativeHeights.ResidueFieldInfiniteOn (K₀ : Set K) →
    ∀ S : Set K, (∀ t ∈ S, 0 < ‖t‖ ∧ ‖t‖ < 1) →
    (∀ r : ℝ, 0 < r → r < 1 → ∀ ε > (0 : ℝ), ∃ t ∈ S, |‖t‖ - r| < ε) →
    (∀ t ∈ S, ∀ τ ∈ K₀, ‖τ‖ = 1 → t * τ ∈ S) →
    ∀ (ι : Type) [Fintype ι] (δ : MvPolynomial ι K),
      (∀ μ, ‖MvPolynomial.coeff μ δ‖ ≤ 1) → (∃ μ, ‖MvPolynomial.coeff μ δ‖ = 1) →
    ∀ (P : ℤ → MvPolynomial ι K) (b : ℕ), (∀ n, n < -(b : ℤ) → P n = 0) →
      (∀ t ∈ S, ∀ x : ι → K, (∀ i, x i ∈ K₀ ∧ ‖x i‖ ≤ 1) → ‖MvPolynomial.eval x δ‖ = 1 →
        Filter.Tendsto (fun n => ‖MvPolynomial.eval x (P n) * t ^ n‖) Filter.cofinite (nhds 0) ∧
        ‖∑' n, MvPolynomial.eval x (P n) * t ^ n‖ ≤ 1) →
      ∀ n, (∀ μ, ‖MvPolynomial.coeff μ (P n)‖ ≤ 1) ∧ (n < 0 → P n = 0)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FinDetPf
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

theorem finiteDetect_holds : FiniteDetectStatement := by
  intro L E _ _ _ _ W FF hkill hdet
  classical
  let S : Set (Submodule L E) :=
    {P | ∃ s : Finset (Module.Dual L E), ↑s ⊆ FF ∧ (⨅ c ∈ s, LinearMap.ker c) = P}
  have hS : S.Nonempty := ⟨_, ∅, by simp, rfl⟩
  obtain ⟨P, ⟨s, hsFF, rfl⟩, hmin⟩ := IsArtinian.set_has_minimal S hS
  refine ⟨s, hsFF, le_antisymm ?_ ?_⟩
  · intro x hx
    by_contra hxW
    obtain ⟨c, hcFF, hcx⟩ := hdet x hxW
    have hmem : (⨅ d ∈ insert c s, LinearMap.ker d) ∈ S :=
      ⟨insert c s, by
        intro d hd
        rcases Finset.mem_insert.mp hd with rfl | hd
        · exact hcFF
        · exact hsFF hd, rfl⟩
    apply hmin _ hmem
    refine lt_of_le_of_ne ?_ ?_
    · exact le_iInf₂ fun d hd => iInf₂_le d (Finset.mem_insert_of_mem hd)
    · intro heq
      have hx' : x ∈ ⨅ d ∈ insert c s, LinearMap.ker d := heq ▸ hx
      have : x ∈ LinearMap.ker c :=
        (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp hx' c) (Finset.mem_insert_self c s)
      exact hcx this
  · exact le_iInf₂ fun c hc => hkill c (hsFF hc)

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FiniteDimensionalBaseSpan
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct
open TensorProduct

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

noncomputable def incU (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    F ⊗[K] U →ₗ[F] F ⊗[K] V :=
  AlgebraTensorModule.map (LinearMap.id : F →ₗ[F] F) U.subtype

theorem incU_apply_eq_lTensor (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    (y : F ⊗[K] U) : incU F U y = LinearMap.lTensor F U.subtype y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a u => simp [incU]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem baseSpan_eq_range (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    baseSpan F U = LinearMap.range (incU F U) := by
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨u, hu, rfl⟩
    exact ⟨(1 : F) ⊗ₜ[K] (⟨u, hu⟩ : U), by simp [incU]⟩
  · rintro _ ⟨y, rfl⟩
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a u =>
      have : incU F U (a ⊗ₜ[K] u) = a • ((1 : F) ⊗ₜ[K] (u : V)) := by
        simp [incU, TensorProduct.smul_tmul']
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, u.2, rfl⟩)
    | add y z hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz

theorem mem_baseSpan_iff (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    (x : F ⊗[K] V) : x ∈ baseSpan F U ↔ LinearMap.lTensor F U.mkQ x = 0 := by
  have hex := lTensor_exact F (LinearMap.exact_subtype_mkQ U) (Submodule.mkQ_surjective U)
  rw [hex x, baseSpan_eq_range, LinearMap.mem_range]
  constructor
  · rintro ⟨y, rfl⟩; exact ⟨y, (incU_apply_eq_lTensor F U y).symm⟩
  · rintro ⟨y, rfl⟩; exact ⟨y, incU_apply_eq_lTensor F U y⟩

variable {Ω : Type*} [Field Ω] [Algebra K Ω]

noncomputable def fldIncl (K₁ : IntermediateField K Ω) : K₁ →ₗ[K] Ω :=
  (IsScalarTower.toAlgHom K K₁ Ω).toLinearMap

theorem fldIncl_injective (K₁ : IntermediateField K Ω) : Function.Injective (fldIncl K₁) :=
  (algebraMap K₁ Ω).injective

theorem inclT_tmul' (K₁ : IntermediateField K Ω) (a : K₁) (v : V) :
    inclT K₁ V (a ⊗ₜ[K] v) = (a : Ω) ⊗ₜ[K] v := rfl

theorem lTensor_mkQ_inclT (K₁ : IntermediateField K Ω) (U : Submodule K V) (x : K₁ ⊗[K] V) :
    LinearMap.lTensor Ω U.mkQ (inclT K₁ V x) =
      LinearMap.rTensor (V ⧸ U) (fldIncl K₁) (LinearMap.lTensor K₁ U.mkQ x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a v => simp [inclT_tmul', fldIncl]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem mem_baseSpan_of_inclT (K₁ : IntermediateField K Ω) (U : Submodule K V) (x : K₁ ⊗[K] V)
    (h : inclT K₁ V x ∈ baseSpan Ω U) : x ∈ baseSpan K₁ U := by
  rw [mem_baseSpan_iff] at h ⊢
  rw [lTensor_mkQ_inclT] at h
  apply Module.Flat.rTensor_preserves_injective_linearMap (M := V ⧸ U) _ (fldIncl_injective K₁)
  rw [h, map_zero]

theorem inclT_mem_baseSpan (K₁ : IntermediateField K Ω) (U : Submodule K V) (x : K₁ ⊗[K] V)
    (h : x ∈ baseSpan K₁ U) : inclT K₁ V x ∈ baseSpan Ω U := by
  rw [mem_baseSpan_iff] at h ⊢
  rw [lTensor_mkQ_inclT, h, map_zero]

theorem inclT_tmul (K₁ : IntermediateField K Ω) (a : K₁) (v : V) :
    inclT K₁ V (a ⊗ₜ[K] v) = (a : Ω) • ((1 : Ω) ⊗ₜ[K] v) := by
  rw [inclT_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem definedOver_iff (c : Module.Dual Ω (Ω ⊗[K] V)) (K' : IntermediateField K Ω) :
    DefinedOver c K' ↔ ∀ v : V, c ((1 : Ω) ⊗ₜ[K] v) ∈ K' := by
  constructor
  · intro h v
    obtain ⟨y, hy⟩ := h ((1 : K') ⊗ₜ[K] v)
    rw [inclT_tmul] at hy
    simp only [OneMemClass.coe_one, one_smul] at hy
    rw [← hy]; exact y.2
  · intro h x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a v =>
      refine ⟨a * ⟨_, h v⟩, ?_⟩
      rw [inclT_tmul, map_smul, smul_eq_mul]
      simp
    | add y z hy hz =>
      obtain ⟨a, ha⟩ := hy
      obtain ⟨b, hb⟩ := hz
      exact ⟨a + b, by rw [map_add, map_add, map_add, ha, hb]⟩

theorem DefinedOver.mono {c : Module.Dual Ω (Ω ⊗[K] V)} {K' K₁ : IntermediateField K Ω}
    (h : DefinedOver c K') (hle : K' ≤ K₁) : DefinedOver c K₁ := by
  rw [definedOver_iff] at h ⊢
  exact fun v => hle (h v)

theorem incU_injective (F : Type*) [Field F] [Algebra K F] (U : Submodule K V) :
    Function.Injective (incU F U) := by
  intro x y h
  rw [incU_apply_eq_lTensor, incU_apply_eq_lTensor] at h
  exact Module.Flat.lTensor_preserves_injective_linearMap (M := F) U.subtype U.injective_subtype h

theorem finrank_baseSpan (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    [FiniteDimensional K U] : Module.finrank F (baseSpan F U) = Module.finrank K U := by
  rw [baseSpan_eq_range, LinearMap.finrank_range_of_inj (incU_injective F U),
    Module.finrank_baseChange]

theorem finiteDimensional_baseSpan (F : Type*) [Field F] [Algebra K F] (U : Submodule K V)
    [FiniteDimensional K U] : FiniteDimensional F (baseSpan F U) := by
  rw [baseSpan_eq_range]; infer_instance

theorem exists_ratFun {c : Module.Dual Ω (Ω ⊗[K] V)} {K₁ : IntermediateField K Ω}
    (h : DefinedOver c K₁) :
    ∃ φ : Module.Dual K₁ (K₁ ⊗[K] V), ∀ x, algebraMap K₁ Ω (φ x) = c (inclT K₁ V x) := by
  let ψ : K₁ ⊗[K] V →ₗ[K₁] Ω := (c.restrictScalars K₁).comp (inclT K₁ V)
  have hr : ∀ x, ψ x ∈ LinearMap.range (Algebra.linearMap K₁ Ω) := fun x => by
    obtain ⟨y, hy⟩ := h x; exact ⟨y, hy⟩
  let e := LinearEquiv.ofInjective (Algebra.linearMap K₁ Ω) (algebraMap K₁ Ω).injective
  refine ⟨e.symm.toLinearMap ∘ₗ ψ.codRestrict _ hr, fun x => ?_⟩
  have h1 : ((e (e.symm ⟨ψ x, hr x⟩) : LinearMap.range (Algebra.linearMap K₁ Ω)) : Ω) = ψ x := by
    rw [e.apply_symm_apply]
  exact h1

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.FreeQuotPf
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open Module

section
variable {R F X : Type} [CommRing R] [IsDomain R] [Field F] [Algebra R F]
    [IsFractionRing R F] [AddCommGroup X] [Module F X] [Module R X] [IsScalarTower R F X]

theorem freeQuot_exists_smul_mem (S : Submodule R X) {x : X}
    (hx : x ∈ Submodule.span F (S : Set X)) : ∃ d : R, d ≠ 0 ∧ d • x ∈ S := by
  exact Bl.SecondBlockLemmaK.goal1 S hx

theorem freeQuot_rank_span (S : Submodule R X) :
    Module.rank R S = Module.rank F (Submodule.span F (S : Set X)) := by
  set T := Submodule.span F (S : Set X)
  have hST : S ≤ T.restrictScalars R := fun x hx => Submodule.subset_span hx
  let S' : Submodule R (T.restrictScalars R) := S.comap (T.restrictScalars R).subtype
  have h0 : Module.rank R ((T.restrictScalars R) ⧸ S') = 0 := by
    rw [rank_eq_zero_iff]
    intro q
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective S' q
    obtain ⟨d, hd, hd'⟩ := freeQuot_exists_smul_mem S (y.2 : (y : X) ∈ T)
    refine ⟨d, hd, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact hd'
  have h1 := rank_quotient_add_rank_of_isDomain S'
  rw [h0, zero_add, (Submodule.comapSubtypeEquivOfLe hST).rank_eq] at h1
  rw [h1, IsLocalization.rank_eq (N := T) F (nonZeroDivisors R) le_rfl]
  rfl

end

theorem freeQuot_holds : FreeQuotStatement := by
  intro R F X _ _ _ _ _ _ _ _ _ _ M₁ hM₁ N
  have : Module.Finite R M₁ := Module.Finite.iff_fg.mpr hM₁
  have ne : ∀ r : R, r ≠ 0 → algebraMap R F r ≠ 0 := fun r hr =>
    (map_ne_zero_iff _ (IsFractionRing.injective R F)).mpr hr
  have htf : Module.IsTorsionFree R (M₁ ⧸ (N.restrictScalars R).comap M₁.subtype) := by
    rw [Module.isTorsionFree_iff_smul_eq_zero]
    intro r q hq
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hq
    rw [Submodule.Quotient.mk_eq_zero]
    have hq' : algebraMap R F r • (m : X) ∈ N := by
      rw [algebraMap_smul]
      simpa using hq
    show (m : X) ∈ N
    have h2 := N.smul_mem (algebraMap R F r)⁻¹ hq'
    rwa [smul_smul, inv_mul_cancel₀ (ne r hr), one_smul] at h2
  refine ⟨inferInstance, ?_⟩
  have hspan : Submodule.span F ((M₁ ⊓ N.restrictScalars R : Submodule R X) : Set X) =
      Submodule.span F (M₁ : Set X) ⊓ N := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      exact Submodule.mem_inf.mpr ⟨Submodule.subset_span hx1, hx2⟩
    · intro x hx
      obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
      obtain ⟨d, hd, hd'⟩ := freeQuot_exists_smul_mem M₁ hx1
      have hN : d • x ∈ N := by
        rw [← algebraMap_smul F d x]
        exact N.smul_mem _ hx2
      have hmem : d • x ∈ Submodule.span F
          ((M₁ ⊓ N.restrictScalars R : Submodule R X) : Set X) :=
        Submodule.subset_span (Submodule.mem_inf.mpr ⟨hd', hN⟩)
      rw [← algebraMap_smul F d x] at hmem
      have h2 := Submodule.smul_mem _ (algebraMap R F d)⁻¹ hmem
      rwa [smul_smul, inv_mul_cancel₀ (ne d hd), one_smul] at h2
  have hrn := Submodule.finrank_quotient_add_finrank ((N.restrictScalars R).comap M₁.subtype)
  have hM : finrank R M₁ = finrank F (Submodule.span F (M₁ : Set X)) :=
    congrArg Cardinal.toNat (freeQuot_rank_span M₁)
  have hP : finrank R ((N.restrictScalars R).comap M₁.subtype) =
      finrank F ↥(Submodule.span F (M₁ : Set X) ⊓ N) := by
    rw [(Submodule.equivMapOfInjective M₁.subtype M₁.injective_subtype
      ((N.restrictScalars R).comap M₁.subtype)).finrank_eq, Submodule.map_comap_subtype, ← hspan]
    exact congrArg Cardinal.toNat (freeQuot_rank_span _)
  rw [← hP, ← hM]
  exact hrn

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.GlobSt
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open NumberField

noncomputable def logN {K₁ : Type*} [Field K₁] [NumberField K₁]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁)) : ℝ :=
  Real.log (Ideal.absNorm w.asIdeal : ℝ)

def GlobalQuotStatement : Prop :=
  ∀ (K₁ : Type) [Field K₁] [NumberField K₁] (ρ : ℕ) (m : Matrix (Fin ρ) (Fin ρ) K₁),
    m.det ≠ 0 →
    ∀ (s : Fin ρ → IsDedekindDomain.HeightOneSpectrum (𝓞 K₁) → ℝ)
      (β : IsDedekindDomain.HeightOneSpectrum (𝓞 K₁) → ℝ)
      (a b : Fin ρ → InfinitePlace K₁ → ℝ) (B : Fin ρ → ℝ) (Bfin : ℝ),
      (∀ i, (Function.support (s i)).Finite) → (Function.support β).Finite →
      (∀ (σ : InfinitePlace K₁) (i j : Fin ρ), m i j ≠ 0 →
        Real.log (σ (m i j)) + a i σ ≤ b j σ) →
      (∀ i, ((∑ᶠ w, s i w * logN w) - ∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * a i σ) /
          (Module.finrank ℚ K₁ : ℝ) ≤ B i) →
      (∑ᶠ w, β w * logN w) / (Module.finrank ℚ K₁ : ℝ) ≤ Bfin →
      (∑ᶠ w, ((ordAt w m.det : ℝ) + ∑ i, s i w + ρ * β w) * logN w) /
          (Module.finrank ℚ K₁ : ℝ) ≤
        ∑ j, (∑ σ : InfinitePlace K₁, (σ.mult : ℝ) * b j σ) / (Module.finrank ℚ K₁ : ℝ) +
          (ρ : ℝ) / 2 * Real.log ρ + ∑ i, B i + ρ * Bfin

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.Rationality.KerCoreSt
section
namespace ReciprocityTheory.ChartRestriction.G.FreeQuotientRank

open scoped TensorProduct

def KerCoreStatement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (W : Submodule K V)
    (Fam : ∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁], (V →ₗ[K] K₁) → Prop),
    (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (f : V →ₗ[K] K₁), Fam K₁ f →
      W ≤ LinearMap.ker f) →
    (∀ v : V, (∀ (K₁ : Type) [Field K₁] [NumberField K₁] [Algebra K K₁] (f : V →ₗ[K] K₁),
      Fam K₁ f → f v = 0) → v ∈ W) →
    (∀ (K' K₁ : Type) [Field K'] [NumberField K'] [Algebra K K'] [Field K₁] [NumberField K₁]
      [Algebra K K₁] (e : K' →ₐ[K] K₁) (f : V →ₗ[K] K'), Fam K' f →
      ∃ f₁ : V →ₗ[K] K₁, Fam K₁ f₁ ∧ ∀ v, f₁ v = e (f v)) →
    ∃ (K₁ : Type) (_ : Field K₁) (_ : NumberField K₁) (_ : Algebra K K₁) (ρ : ℕ)
      (g : Fin ρ → (V →ₗ[K] K₁)) (cfL : Fin ρ → Module.Dual K₁ (K₁ ⊗[K] V)),
      (∀ i, Fam K₁ (g i)) ∧ (∀ i v, cfL i ((1 : K₁) ⊗ₜ[K] v) = g i v) ∧
      (∀ x : K₁ ⊗[K] V, (∀ i, cfL i x = 0) ↔ x ∈ baseSpan K₁ W) ∧
      Module.finrank K W + ρ = Module.finrank K V

end ReciprocityTheory.ChartRestriction.G.FreeQuotientRank
end

