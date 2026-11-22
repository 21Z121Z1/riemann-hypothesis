import Mathlib

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalDet
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qi25.UG :
    ℕ → Type :=
    fun (N : ℕ) ↦ ↥(Matrix.unitaryGroup (Fin N) ℂ)

noncomputable def UpperTheory.Reformulated.B.Qi25.ent :
    {N : ℕ} → UpperTheory.Reformulated.B.Qi25.UG N → Fin N × Fin N → ℂ :=
    fun {N : ℕ} (g : UpperTheory.Reformulated.B.Qi25.UG N) (ij : Fin N × Fin N) ↦ (↑g : Matrix (Fin N) (Fin N) ℂ) ij.1 ij.2

noncomputable def UpperTheory.Reformulated.B.Qi25.IsPD :
    {N : ℕ} → (UpperTheory.Reformulated.B.Qi25.UG N → ℂ) → Prop :=
    fun {N : ℕ} (f : UpperTheory.Reformulated.B.Qi25.UG N → ℂ) ↦
      ∃ (k : ℕ) (P : MvPolynomial (Fin N × Fin N) ℂ),
        ∀ (g : UpperTheory.Reformulated.B.Qi25.UG N),
          f g * (↑g : Matrix (Fin N) (Fin N) ℂ).det ^ k =
            (MvPolynomial.eval (UpperTheory.Reformulated.B.Qi25.ent g) : MvPolynomial (Fin N × Fin N) ℂ → ℂ) P

private theorem UpperTheory.Reformulated.B.Qi25.eval_det {N : ℕ} (g : UpperTheory.Reformulated.B.Qi25.UG N) :
    MvPolynomial.eval (UpperTheory.Reformulated.B.Qi25.ent g)
        (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det =
      (↑g : Matrix (Fin N) (Fin N) ℂ).det := by
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp [UpperTheory.Reformulated.B.Qi25.ent]

theorem UpperTheory.Reformulated.B.Qi25.sum.{u_1} :
    ∀ {N : ℕ} {ι : Type u_1} (s : Finset ι) {F : ι → UpperTheory.Reformulated.B.Qi25.UG N → ℂ},
      (∀ i ∈ s, UpperTheory.Reformulated.B.Qi25.IsPD (F i)) → UpperTheory.Reformulated.B.Qi25.IsPD fun (g : UpperTheory.Reformulated.B.Qi25.UG N) ↦ ∑ i ∈ s, F i g := by
  intro N ι s F
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨0, 0, fun g ↦ by simp⟩
  | insert a s ha ih =>
    intro h
    obtain ⟨k, P, hP⟩ := h a (Finset.mem_insert_self a s)
    obtain ⟨l, Q, hQ⟩ := ih fun i hi ↦ h i (Finset.mem_insert_of_mem hi)
    refine ⟨k + l,
      P * (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det ^ l
        + Q * (Matrix.of fun i j : Fin N ↦ (MvPolynomial.X (i, j) : MvPolynomial (Fin N × Fin N) ℂ)).det ^ k,
      fun g ↦ ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, UpperTheory.Reformulated.B.Qi25.eval_det, ← hP g, ← hQ g]
    simp only [Finset.sum_insert ha]
    ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalProd
section
namespace UpperTheory.Reformulated.B.Gr23

open Polynomial

private theorem eval_prod (m : Multiset ℂ) (u : ℂ) :
    ((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ X - C x)).prod.eval u
      = (m.map (fun x : ℂ ↦ u + x)).prod := by
  rw [eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun x _ ↦ ?_
  simp

private theorem eq_of_prod_eq {m m' : Multiset ℂ}
    (h : ∀ u : ℂ, (m.map (fun x : ℂ ↦ u + x)).prod = (m'.map (fun x : ℂ ↦ u + x)).prod) :
    m = m' := by
  have hp : ((m.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ X - C x)).prod
      = ((m'.map (fun x : ℂ ↦ -x)).map (fun x : ℂ ↦ X - C x)).prod := by
    refine Polynomial.funext fun u ↦ ?_
    rw [eval_prod, eval_prod, h u]
  have hr := congrArg Polynomial.roots hp
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at hr
  exact Multiset.map_injective neg_injective hr

theorem abs {M : Type*} [AddCommGroup M] [Module ℂ M] {V : Submodule ℂ M} (hV : V ≠ ⊥)
    (T : ℂ → Module.End ℂ M) {a : ℕ} {m m' : Multiset ℂ}
    (h : m.card = a ∧ ∀ (u : ℂ), ∀ φ ∈ V,
      (T u) φ = (Multiset.map (fun (x : ℂ) ↦ u + x) m).prod • φ)
    (h' : m'.card = a ∧ ∀ (u : ℂ), ∀ φ ∈ V,
      (T u) φ = (Multiset.map (fun (x : ℂ) ↦ u + x) m').prod • φ) :
    m = m' := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV
  refine eq_of_prod_eq fun u ↦ ?_
  exact smul_left_injective ℂ hφ0 ((h.2 u φ hφ).symm.trans (h'.2 u φ hφ))

end UpperTheory.Reformulated.B.Gr23
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalSmulOfIsHomogeneous
section
theorem UpperTheory.Reformulated.B.HomogeneousEvalSmul.eval_smul_of_isHomogeneous :
    ∀ {σ : Type} [Fintype σ] {h : MvPolynomial σ ℂ} {d : ℕ},
      h.IsHomogeneous d →
        ∀ (t : ℂ) (v : σ → ℂ),
          (MvPolynomial.eval (t • v) : MvPolynomial σ ℂ → ℂ) h = t ^ d * (MvPolynomial.eval v : MvPolynomial σ ℂ → ℂ) h := by
  intro σ _ h d hh t v
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : ∑ i, m i = d := by
    have h1 := hh (MvPolynomial.mem_support_iff.mp hm)
    rw [← h1, Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvalSmulOfIsHomogeneousAlt
section
theorem UpperTheory.Reformulated.B.Ydc1.eval_smul_of_isHomogeneous.{u_1} :
    ∀ {τ : Type u_1} {φ : MvPolynomial τ ℂ} {n : ℕ},
      φ.IsHomogeneous n →
        ∀ (c : ℂ) (w : τ → ℂ),
          (MvPolynomial.eval (c • w) : MvPolynomial τ ℂ → ℂ) φ = c ^ n * (MvPolynomial.eval w : MvPolynomial τ ℂ → ℂ) φ := by
  intro τ φ n hφ c w
  rw [MvPolynomial.eval_eq, MvPolynomial.eval_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i ∈ d.support, d i = n := by
    have h := hφ (MvPolynomial.mem_support_iff.mp hd)
    rw [← h, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EvaluationMap
section
noncomputable def UpperTheory.Reformulated.B.EvaluationMap.coeffSpan :
    {K W : Type} →
      [inst : Group K] →
        [inst_1 : AddCommGroup W] → [inst_2 : _root_.Module ℂ W] → Representation ℂ K W → Submodule ℂ (K → ℂ) :=
    fun {K W : Type} [Group K] [AddCommGroup W] [_root_.Module ℂ W] (ρ : Representation ℂ K W) ↦
      Submodule.span ℂ
        {f : K → ℂ | ∃ (ℓ : Module.Dual ℂ W) (w : W), f = fun (k : K) ↦ (ℓ : W → ℂ) (((ρ : K → W →ₗ[ℂ] W) k : W → W) w)}

namespace UpperTheory.Reformulated.B.EvaluationMap.Helpers

private noncomputable def Φ {K W : Type} [Group K] [AddCommGroup W] [_root_.Module ℂ W]
    (ρ : Representation ℂ K W) : Module.Dual ℂ (W →ₗ[ℂ] W) →ₗ[ℂ] (K → ℂ) where
  toFun φ := fun k => φ (ρ k)
  map_add' φ ψ := by funext k; simp
  map_smul' c φ := by funext k; simp

private noncomputable def evw {W : Type} [AddCommGroup W] [_root_.Module ℂ W]
    (ℓ : Module.Dual ℂ W) (w : W) : Module.Dual ℂ (W →ₗ[ℂ] W) where
  toFun A := ℓ (A w)
  map_add' A B := by simp
  map_smul' c A := by simp

end UpperTheory.Reformulated.B.EvaluationMap.Helpers

open UpperTheory.Reformulated.B.EvaluationMap.Helpers in
theorem UpperTheory.Reformulated.B.EvaluationMap.main :
    ∀ {K W : Type} [inst : Group K] [inst_1 : AddCommGroup W] [inst_2 : _root_.Module ℂ W] [FiniteDimensional ℂ W]
      (ρ : Representation ℂ K W), FiniteDimensional ℂ ↥(UpperTheory.Reformulated.B.EvaluationMap.coeffSpan ρ) := by
  intro K W _ _ _ _ ρ
  have hle : UpperTheory.Reformulated.B.EvaluationMap.coeffSpan ρ ≤ LinearMap.range (Φ ρ) := by
    unfold UpperTheory.Reformulated.B.EvaluationMap.coeffSpan
    rw [Submodule.span_le]
    rintro f ⟨ℓ, w, rfl⟩
    exact ⟨evw ℓ w, rfl⟩
  exact Submodule.finiteDimensional_of_le hle
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EventualValue
section
open scoped Classical

@[reducible] noncomputable def UpperTheory.Reformulated.B.Yfa2.MRing.{u_1, u_2, u_3} :
    {K : Type u_1} → (K → Type u_2) → (R : Type u_3) → [CommRing R] → Type (max u_3 u_2 u_1) :=
    fun {K : Type u_1} (ι : K → Type u_2) (R : Type u_3) [CommRing R] ↦ MvPolynomial ((k : K) × ι k) R

noncomputable def UpperTheory.Reformulated.B.Yfa2.cycEval.{u_1, u_2, u_3} :
    {K : Type u_1} →
      {ι : K → Type u_2} →
        {R : Type u_3} →
          [inst : CommRing R] → (Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι R) → ℤ) → (Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι R) → ℤ) → ℤ :=
    fun {K : Type u_1} {ι : K → Type u_2} {R : Type u_3} [CommRing R] (n Z : Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι R) → ℤ) ↦
      ∑ᶠ (W : Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι R)), Z W * n W

noncomputable def UpperTheory.Reformulated.B.Yfa2.eventualValue.{u_1} :
    {K : Type u_1} → ((K → ℤ) → ℤ) → ℤ :=
    fun {K : Type u_1} (f : (K → ℤ) → ℤ) ↦
      if h : ∃ (c : ℤ), ∀ᶠ (m : K → ℤ) in Filter.atTop, f m = c then h.choose else (0 : ℤ)

noncomputable def UpperTheory.Reformulated.B.Yfa2.diffStep.{u_1} :
    {K : Type u_1} → (K → ℤ) → ((K → ℤ) → ℤ) → (K → ℤ) → ℤ :=
    fun {K : Type u_1} (b : K → ℤ) (h : (K → ℤ) → ℤ) (m : K → ℤ) ↦ h m - h (m - b)

noncomputable def UpperTheory.Reformulated.B.Yfa2.mixedDiff.{u_1} :
    {K : Type u_1} → {n : ℕ} → (Fin n → K → ℤ) → ((K → ℤ) → ℤ) → (K → ℤ) → ℤ :=
    fun {K : Type u_1} {n : ℕ} (bs : Fin n → K → ℤ) (h : (K → ℤ) → ℤ) ↦
      List.foldr UpperTheory.Reformulated.B.Yfa2.diffStep h (List.ofFn bs)

noncomputable def UpperTheory.Reformulated.B.Yfa2.blockWeight.{u_1, u_2} :
    {K : Type u_1} → (ι : K → Type u_2) → [DecidableEq K] → (k : K) × ι k → K → ℕ :=
    fun {K : Type u_1} (ι : K → Type u_2) [DecidableEq K] (v : (k : K) × ι k) ↦ Pi.single v.fst (1 : ℕ)

noncomputable def UpperTheory.Reformulated.B.Yfa2.gradedPiece.{u_1, u_2, u_3} :
    {K : Type u_1} →
      [DecidableEq K] →
        {ι : K → Type u_2} →
          {F : Type u_3} →
            [inst : Field F] →
              (P : Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι F)) → (K → ℕ) → Submodule F (UpperTheory.Reformulated.B.Yfa2.MRing ι F ⧸ P) :=
    fun {K : Type u_1} [DecidableEq K] {ι : K → Type u_2} {F : Type u_3} [Field F] (P : Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι F))
        (m : K → ℕ) ↦
      Submodule.map (Ideal.Quotient.mkₐ F P).toLinearMap
        (MvPolynomial.weightedHomogeneousSubmodule F (UpperTheory.Reformulated.B.Yfa2.blockWeight ι) m)

noncomputable def UpperTheory.Reformulated.B.Yfa2.hilbFn.{u_1, u_2, u_3} :
    {K : Type u_1} →
      [DecidableEq K] →
        {ι : K → Type u_2} → {F : Type u_3} → [inst : Field F] → Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι F) → (K → ℤ) → ℤ :=
    fun {K : Type u_1} [DecidableEq K] {ι : K → Type u_2} {F : Type u_3} [Field F] (P : Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι F))
        (m : K → ℤ) ↦
      if ∀ (k : K), (0 : ℤ) ≤ m k then (↑(Module.finrank F ↥(UpperTheory.Reformulated.B.Yfa2.gradedPiece P fun (k : K) ↦ (m k).toNat)) : ℤ)
      else (0 : ℤ)

noncomputable def UpperTheory.Reformulated.B.Yfa2.intNum.{u_1, u_2, u_4} :
    {K : Type u_1} →
      [DecidableEq K] →
        {ι : K → Type u_2} →
          (F : Type u_4) → [inst : Field F] → Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι F) → {n : ℕ} → (Fin n → K → ℤ) → ℤ :=
    fun {K : Type u_1} [DecidableEq K] {ι : K → Type u_2} (F : Type u_4) [Field F] (P : Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι F))
        {n : ℕ} (bs : Fin n → K → ℤ) ↦
      UpperTheory.Reformulated.B.Yfa2.eventualValue (UpperTheory.Reformulated.B.Yfa2.mixedDiff bs (UpperTheory.Reformulated.B.Yfa2.hilbFn P))

noncomputable def UpperTheory.Reformulated.B.Yfa2.specialIdeal.{u_1, u_2, u_3} :
    {K : Type u_1} →
      {ι : K → Type u_2} →
        {O : Type u_3} →
          [inst : CommRing O] →
            [inst_1 : IsDomain O] →
              [inst_2 : IsDiscreteValuationRing O] →
                Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι O) → Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι (IsLocalRing.ResidueField O)) :=
    fun {K : Type u_1} {ι : K → Type u_2} {O : Type u_3} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        (W : Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι O)) ↦
      Ideal.map (MvPolynomial.map (IsLocalRing.residue O)) W

noncomputable def UpperTheory.Reformulated.B.Yfa2.vNum.{u_1, u_2, u_3} :
    {K : Type u_1} →
      [DecidableEq K] →
        {ι : K → Type u_2} →
          {O : Type u_3} →
            [inst : CommRing O] →
              [inst_1 : IsDomain O] →
                [IsDiscreteValuationRing O] → Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι O) → {n : ℕ} → (Fin n → K → ℤ) → ℤ :=
    fun {K : Type u_1} [DecidableEq K] {ι : K → Type u_2} {O : Type u_3} [CommRing O] [IsDomain O]
        [IsDiscreteValuationRing O] (W : Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι O)) {n : ℕ} (bs : Fin n → K → ℤ) ↦
      UpperTheory.Reformulated.B.Yfa2.intNum (IsLocalRing.ResidueField O) (UpperTheory.Reformulated.B.Yfa2.specialIdeal W) bs

noncomputable def UpperTheory.Reformulated.B.Yfa2.vNumL.{u_1, u_2, u_3} :
    {K : Type u_1} →
      [DecidableEq K] →
        {ι : K → Type u_2} →
          {O : Type u_3} →
            [inst : CommRing O] →
              [inst_1 : IsDomain O] → [IsDiscreteValuationRing O] → Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι O) → List (K → ℤ) → ℤ :=
    fun {K : Type u_1} [DecidableEq K] {ι : K → Type u_2} {O : Type u_3} [CommRing O] [IsDomain O]
        [IsDiscreteValuationRing O] (W : Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι O)) (l : List (K → ℤ)) ↦
      UpperTheory.Reformulated.B.Yfa2.vNum W l.get

noncomputable def UpperTheory.Reformulated.B.Yfa2.cycList :
    {K : Type} →
      {ι : K → Type} →
        [DecidableEq K] →
          {O : Type} →
            [inst : CommRing O] →
              [inst_1 : IsDomain O] →
                [IsDiscreteValuationRing O] → (Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι O) → ℤ) → List (K → ℤ) → ℤ :=
    fun {K : Type} {ι : K → Type} [DecidableEq K] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
        (Z : Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι O) → ℤ) (l : List (K → ℤ)) ↦
      UpperTheory.Reformulated.B.Yfa2.cycEval (fun (W : Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι O)) ↦ UpperTheory.Reformulated.B.Yfa2.vNumL W l) Z

noncomputable def UpperTheory.Reformulated.B.Yfa2.classList.{u_1, u_3} :
    {K : Type u_1} → {σ : Type u_3} → (σ → K → ℤ) → (σ →₀ ℕ) → List (K → ℤ) :=
    fun {K : Type u_1} {σ : Type u_3} (cls : σ → K → ℤ) (μ : σ →₀ ℕ) ↦
      (Multiset.map cls ((Finsupp.toMultiset : (σ →₀ ℕ) → Multiset σ) μ)).toList

noncomputable def UpperTheory.Reformulated.B.Yfa2.cycNum :
    {K : Type} →
      {ι : K → Type} →
        {σ : Type} →
          [DecidableEq K] →
            {O : Type} →
              [inst : CommRing O] →
                [inst_1 : IsDomain O] →
                  [IsDiscreteValuationRing O] →
                    (Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι O) → ℤ) → (σ → K → ℤ) → MvPolynomial σ ℝ → List (K → ℤ) → ℝ :=
    fun {K : Type} {ι : K → Type} {σ : Type} [DecidableEq K] {O : Type} [CommRing O] [IsDomain O]
        [IsDiscreteValuationRing O] (Z : Ideal (UpperTheory.Reformulated.B.Yfa2.MRing ι O) → ℤ) (cls : σ → K → ℤ) (H : MvPolynomial σ ℝ)
        (Q : List (K → ℤ)) ↦
      ∑ μ ∈ H.support, MvPolynomial.coeff μ H * (↑(UpperTheory.Reformulated.B.Yfa2.cycList Z (UpperTheory.Reformulated.B.Yfa2.classList cls μ ++ Q)) : ℝ)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExComp
section
theorem UpperTheory.Reformulated.B.Qh44.ex_comp :
    ∀ {F M Ω : Type} [inst : Field F] [NumberField F] [inst_2 : Field M]
    [NumberField M] [inst_4 : Field Ω] [inst_5 : Algebra F Ω] [Algebra.IsAlgebraic F Ω] (g : M →+* Ω),
    FiniteDimensional F ↥(IntermediateField.adjoin F (Set.range (⇑g : M → Ω))) := by
  intro F M Ω _ _ _ _ _ _ _ g
  let b := Module.finBasis ℚ M
  have h : IntermediateField.adjoin F (Set.range (⇑g : M → Ω))
      = IntermediateField.adjoin F (Set.range (fun i => g (b i))) := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨x, rfl⟩
      rw [← b.sum_repr x, map_sum]
      refine sum_mem (fun i _ => ?_)
      rw [Rat.smul_def, map_mul, map_ratCast]
      exact mul_mem (SubfieldClass.ratCast_mem _ _)
        (IntermediateField.subset_adjoin _ _ ⟨i, rfl⟩)
    · apply IntermediateField.adjoin.mono
      rintro _ ⟨i, rfl⟩
      exact ⟨_, rfl⟩
  rw [h]
  haveI : Finite (Set.range (fun i => g (b i))) := Set.finite_range _
  exact IntermediateField.finiteDimensional_adjoin
    (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExLift
section
theorem UpperTheory.Reformulated.B.Qj6.ex_lift :
    ∀ {M Ω C : Type} [inst : Field M] [NumberField M] [inst_2 : Field Ω]
    [CharZero Ω] [IsAlgClosed Ω] [inst_5 : Field C] [CharZero C] (j : Ω →+* C) (f : M →+* C),
    ∃ (g : M →+* Ω), ∀ (x : M), (j : Ω → C) ((g : M → Ω) x) = (f : M → C) x := by
  intro M Ω C _ _ _ _ _ _ _ j f
  have key : ∀ x : M, f x ∈ j.fieldRange := by
    intro x
    have hx : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
    have hs : ((minpoly ℚ x).map (algebraMap ℚ Ω)).Splits := IsAlgClosed.splits _
    have hm : ((minpoly ℚ x).map (algebraMap ℚ Ω)).map j = (minpoly ℚ x).map (algebraMap ℚ C) := by
      rw [Polynomial.map_map]
      congr 1
      exact Subsingleton.elim _ _
    have hne : ((minpoly ℚ x).map (algebraMap ℚ Ω)).map j ≠ 0 := by
      rw [hm]
      exact ((minpoly.monic hx).map _).ne_zero
    have hr : f x ∈ (((minpoly ℚ x).map (algebraMap ℚ Ω)).map j).roots := by
      rw [Polynomial.mem_roots hne, hm, Polynomial.IsRoot.def, Polynomial.eval_map_algebraMap]
      have h := Polynomial.aeval_algHom_apply f.toRatAlgHom x (minpoly ℚ x)
      rw [minpoly.aeval, map_zero] at h
      exact h
    rw [hs.roots_map, Multiset.mem_map] at hr
    obtain ⟨y, -, hy⟩ := hr
    exact ⟨y, hy⟩
  choose g hg using fun x => RingHom.mem_fieldRange.mp (key x)
  refine ⟨{ toFun := g, map_one' := ?_, map_mul' := ?_, map_zero' := ?_, map_add' := ?_ }, hg⟩
  · exact j.injective (by simp [hg])
  · intro a b
    exact j.injective (by simp [hg])
  · exact j.injective (by simp [hg])
  · intro a b
    exact j.injective (by simp [hg])
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsAnti
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh37.Lp :
    (L : Type) → [Field L] → Type :=
    fun (L : Type) [Field L] ↦ ↥(NumberField.maximalRealSubfield L)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh37.Lsq :
    (R : Type) → [CommRing R] → R → Type :=
    fun (R : Type) [CommRing R] (Δ : R) ↦ QuadraticAlgebra R Δ (0 : R)

open NumberField NumberField.IsCMField in

private theorem UpperTheory.Reformulated.B.Qh37.exists_anti (L : Type) [Field L] [NumberField L] [IsCMField L] :
    ∃ δ : L, δ ≠ 0 ∧ complexConj L δ = -δ := by
  have h : ∃ x : L, complexConj L x ≠ x := by
    by_contra h
    push Not at h
    exact complexConj_ne_one L (AlgEquiv.ext h)
  obtain ⟨x, hx⟩ := h
  refine ⟨x - complexConj L x, sub_ne_zero.mpr hx.symm, ?_⟩
  rw [map_sub, complexConj_apply_apply, neg_sub]

theorem UpperTheory.Reformulated.B.Qh37.globEx :
    ∀ (L : Type) [inst : Field L] [inst_1 : NumberField L] [inst_2 : NumberField.IsCMField L],
      ∃ (Δ : UpperTheory.Reformulated.B.Qh37.Lp L) (e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ ≃+* L),
        (∀ (x : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ),
            (e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ → L) (Star.star x) =
              (NumberField.IsCMField.complexConj L : L → L) ((e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ → L) x)) ∧
          (∀ (a : UpperTheory.Reformulated.B.Qh37.Lp L),
              (e : UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ → L)
                  ((Algebra.algebraMap (UpperTheory.Reformulated.B.Qh37.Lp L) (UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ) :
                      UpperTheory.Reformulated.B.Qh37.Lp L → UpperTheory.Reformulated.B.Qh37.Lsq (UpperTheory.Reformulated.B.Qh37.Lp L) Δ)
                    a) =
                (Algebra.algebraMap (UpperTheory.Reformulated.B.Qh37.Lp L) L : UpperTheory.Reformulated.B.Qh37.Lp L → L) a) ∧
            ∀ (σ : UpperTheory.Reformulated.B.Qh37.Lp L →+* ℝ), (σ : UpperTheory.Reformulated.B.Qh37.Lp L → ℝ) Δ < (0 : ℝ) := by
  intro L _ _ _
  obtain ⟨δ, hδ0, hδ⟩ := UpperTheory.Reformulated.B.Qh37.exists_anti L
  have hmem : δ * δ ∈ NumberField.maximalRealSubfield L := by
    rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_mul, hδ, neg_mul_neg]
  let Δ : NumberField.maximalRealSubfield L := ⟨δ * δ, hmem⟩
  have hΔ : algebraMap (NumberField.maximalRealSubfield L) L Δ = δ * δ := rfl
  let f : QuadraticAlgebra (NumberField.maximalRealSubfield L) Δ 0 →ₐ[NumberField.maximalRealSubfield L] L :=
    QuadraticAlgebra.lift ⟨δ, by rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one, hΔ]⟩
  have hω : f QuadraticAlgebra.omega = δ := by
    have := (QuadraticAlgebra.lift (R := NumberField.maximalRealSubfield L) (a := Δ) (b := 0)
      (A := L)).symm_apply_apply ⟨δ, by rw [zero_smul, add_zero, ← Algebra.algebraMap_eq_smul_one, hΔ]⟩
    exact congrArg Subtype.val this
  have hf : ∀ x y, f ⟨x, y⟩ = algebraMap _ L x + algebraMap _ L y * δ := by
    intro x y
    rw [QuadraticAlgebra.mk_eq_add_smul_omega, map_add, map_smul, AlgHom.commutes, hω,
      Algebra.smul_def]
  have hstar : ∀ z, f (star z) = NumberField.IsCMField.complexConj L (f z) := by
    rintro ⟨x, y⟩
    rw [QuadraticAlgebra.star_mk, hf, hf, map_add, map_add, map_mul, map_mul,
      AlgEquiv.commutes, AlgEquiv.commutes, hδ, map_neg, map_zero]
    ring
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, y⟩ h
    have h' := hstar ⟨x, y⟩
    rw [h, map_zero, QuadraticAlgebra.star_mk, hf, map_add, map_mul, map_neg, map_zero] at h'
    rw [hf] at h
    have hx : algebraMap _ L x = 0 := by linear_combination (h + h') / 2
    have hy : algebraMap _ L y * δ = 0 := by linear_combination (h - h') / 2
    have hy' := (mul_eq_zero.mp hy).resolve_right hδ0
    rw [map_eq_zero] at hx hy'
    subst hx hy'
    rfl
  have hsurj : Function.Surjective f := by
    intro z
    have h1 : (z + NumberField.IsCMField.complexConj L z) / 2 ∈
        NumberField.maximalRealSubfield L := by
      rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_div₀, map_add, map_ofNat,
        NumberField.IsCMField.complexConj_apply_apply, add_comm]
    have h2 : (z - NumberField.IsCMField.complexConj L z) / (2 * δ) ∈
        NumberField.maximalRealSubfield L := by
      rw [← NumberField.IsCMField.complexConj_eq_self_iff, map_div₀, map_sub, map_mul, map_ofNat,
        NumberField.IsCMField.complexConj_apply_apply, hδ]
      field_simp
      ring
    refine ⟨⟨⟨_, h1⟩, ⟨_, h2⟩⟩, ?_⟩
    rw [hf]
    change (z + NumberField.IsCMField.complexConj L z) / 2 +
      (z - NumberField.IsCMField.complexConj L z) / (2 * δ) * δ = z
    field_simp
    ring
  refine ⟨Δ, RingEquiv.ofBijective f.toRingHom ⟨hinj, hsurj⟩, hstar, f.commutes, fun σ ↦ ?_⟩
  let φ : L →+* ℂ := NumberField.ComplexEmbedding.lift L (Complex.ofRealHom.comp σ)
  have h1 : φ δ * φ δ = (σ Δ : ℂ) := by
    rw [← map_mul, ← hΔ]
    exact NumberField.ComplexEmbedding.lift_algebraMap_apply L (Complex.ofRealHom.comp σ) Δ
  have h2 : (starRingEnd ℂ) (φ δ) = -φ δ := by
    rw [← NumberField.IsCMField.complexEmbedding_complexConj, hδ, map_neg]
  have h3 : ((Complex.normSq (φ δ) : ℝ) : ℂ) = ((-σ Δ : ℝ) : ℂ) := by
    rw [← Complex.mul_conj, h2, mul_neg, h1, Complex.ofReal_neg]
  have h4 : 0 < Complex.normSq (φ δ) := Complex.normSq_pos.mpr ((map_ne_zero φ).mpr hδ0)
  rw [Complex.ofReal_injective h3] at h4
  exact neg_pos.mp h4
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsBoundPolyMulExp
section
theorem UpperTheory.Reformulated.B.Rc4.exists_bound_poly_mul_exp :
    ∀ (c : ℝ),
    (0 : ℝ) < c →
      ∀ (N : ℕ), ∃ (C : ℝ), ∀ (r : ℝ), (0 : ℝ) ≤ r → ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ))) ≤ C := by
  intro c hc N
  refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * c)), fun r hr => ?_⟩
  have h1 : (1 + r) ^ N ≤ Real.exp r ^ N := by
    apply pow_le_pow_left₀ (by linarith)
    linarith [Real.add_one_le_exp r]
  have h2 : (N : ℝ) * r + -(c * r ^ 2) ≤ (N : ℝ) ^ 2 / (4 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((N : ℝ) - 2 * c * r)]
  calc (1 + r) ^ N * Real.exp (-(c * r ^ 2))
      ≤ Real.exp r ^ N * Real.exp (-(c * r ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((N : ℝ) * r + -(c * r ^ 2)) := by
        rw [Real.exp_add, Real.exp_nat_mul]
    _ ≤ Real.exp ((N : ℝ) ^ 2 / (4 * c)) := Real.exp_le_exp.mpr h2
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsBoundPolyMulExpAlt
section
theorem UpperTheory.Reformulated.B.Rd2.exists_bound_poly_mul_exp :
    ∀ (c : ℝ),
    (0 : ℝ) < c →
      ∀ (N : ℕ), ∃ (C : ℝ), ∀ (r : ℝ), (0 : ℝ) ≤ r → ((1 : ℝ) + r) ^ N * Real.exp (-(c * r ^ (2 : ℕ))) ≤ C := by
  intro c hc N
  refine ⟨Real.exp ((N : ℝ) ^ 2 / (4 * c)), fun r hr => ?_⟩
  have h1 : (1 + r) ^ N ≤ Real.exp ((N : ℝ) * r) := by
    rw [Real.exp_nat_mul]
    refine pow_le_pow_left₀ (by positivity) ?_ N
    linarith [Real.add_one_le_exp r]
  have h2 : (N : ℝ) * r + -(c * r ^ 2) ≤ (N : ℝ) ^ 2 / (4 * c) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg ((N : ℝ) - 2 * c * r)]
  calc (1 + r) ^ N * Real.exp (-(c * r ^ 2))
      ≤ Real.exp ((N : ℝ) * r) * Real.exp (-(c * r ^ 2)) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp ((N : ℝ) * r + -(c * r ^ 2)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp ((N : ℝ) ^ 2 / (4 * c)) := Real.exp_le_exp.mpr h2
end

