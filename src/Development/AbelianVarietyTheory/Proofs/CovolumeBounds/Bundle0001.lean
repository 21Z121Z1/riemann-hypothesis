import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.ConjTransposeBoostMulSignatureMulBoost
section
open Matrix WithLp
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

namespace GlobalTheory
namespace MatrixBall

section general

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

omit [DecidableEq m] in
lemma norm_toEuclideanLin_le (M : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ‖toEuclideanLin M x‖ ≤ ‖M‖ * ‖x‖ :=
  M.l2_opNorm_mulVec x

lemma dotProduct_mulVec_eq_inner (M : Matrix n n ℂ) (v : n → ℂ) :
    star v ⬝ᵥ M *ᵥ v = ⟪(toLp 2 v : EuclideanSpace ℂ n), toEuclideanLin M (toLp 2 v)⟫_ℂ := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  rfl

lemma inner_conjTranspose_mul (M N : Matrix m n ℂ) (x y : EuclideanSpace ℂ n) :
    ⟪x, toEuclideanLin (Mᴴ * N) y⟫_ℂ = ⟪toEuclideanLin M x, toEuclideanLin N y⟫_ℂ := by
  rw [toLpLin_mul (q := 2), LinearMap.comp_apply, Matrix.toEuclideanLin_conjTranspose_eq_adjoint,
    LinearMap.adjoint_inner_right]

lemma inner_one_sub (M : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    ⟪x, toEuclideanLin (1 - Mᴴ * M) x⟫_ℂ = ((‖x‖ ^ 2 - ‖toEuclideanLin M x‖ ^ 2 : ℝ) : ℂ) := by
  rw [map_sub, LinearMap.sub_apply, inner_sub_right, inner_conjTranspose_mul, toLpLin_one,
    LinearMap.id_apply, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K]
  simp

omit [DecidableEq n] in
lemma isHermitian_one_sub [DecidableEq n] (M : Matrix m n ℂ) : (1 - Mᴴ * M).IsHermitian :=
  isHermitian_one.sub (isHermitian_conjTranspose_mul_self M)

lemma posDef_one_sub_conjTranspose_mul {Z : Matrix m n ℂ} (hZ : ‖Z‖ < 1) :
    (1 - Zᴴ * Z).PosDef := by
  refine PosDef.of_dotProduct_mulVec_pos (isHermitian_one_sub Z) fun v hv => ?_
  rw [dotProduct_mulVec_eq_inner, inner_one_sub]
  have hx : 0 < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ := by
    rw [norm_pos_iff]; intro h; exact hv (by simpa using h)
  have h1 := norm_toEuclideanLin_le Z (toLp 2 v)
  have h2 : ‖toEuclideanLin Z (toLp 2 v)‖ < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ := by nlinarith
  have h3 := norm_nonneg (toEuclideanLin Z (toLp 2 v))
  exact_mod_cast (by nlinarith : (0 : ℝ) < ‖(toLp 2 v : EuclideanSpace ℂ n)‖ ^ 2 -
    ‖toEuclideanLin Z (toLp 2 v)‖ ^ 2)

theorem norm_lt_one_of_posDef {Z : Matrix m n ℂ} (hP : (1 - Zᴴ * Z).PosDef) : ‖Z‖ < 1 := by
  rcases isEmpty_or_nonempty n with hn | hn
  · have : Z = 0 := by ext i j; exact hn.elim j
    simp [this]
  obtain ⟨x, hx, hmax⟩ := (isCompact_sphere (0 : EuclideanSpace ℂ n) 1).exists_isMaxOn
    (NormedSpace.sphere_nonempty.2 zero_le_one)
    (f := fun x => ‖toEuclideanLin Z x‖)
    ((toEuclideanLin Z).continuous_of_finiteDimensional.norm.continuousOn)
  have hx1 : ‖x‖ = 1 := by simpa using hx
  have hx0 : ofLp x ≠ 0 := by
    intro h
    have : x = 0 := by simpa using h
    simp [this] at hx1
  have h1 := hP.dotProduct_mulVec_pos hx0
  rw [dotProduct_mulVec_eq_inner, inner_one_sub, toLp_ofLp, hx1] at h1
  have h2 : (0 : ℝ) < 1 ^ 2 - ‖toEuclideanLin Z x‖ ^ 2 := by exact_mod_cast h1
  have h3 := norm_nonneg (toEuclideanLin Z x)
  have h4 : ‖toEuclideanLin Z x‖ < 1 := by nlinarith
  refine lt_of_le_of_lt ?_ h4
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_of_unit_norm h3 fun y hy => ?_
  exact hmax (by simpa using hy)

theorem posDef_iff_norm_lt_one (Z : Matrix m n ℂ) : (1 - Zᴴ * Z).PosDef ↔ ‖Z‖ < 1 :=
  ⟨norm_lt_one_of_posDef, posDef_one_sub_conjTranspose_mul⟩

omit [DecidableEq m] in

theorem l2_opNorm_le_hilbertSchmidt (Z : Matrix m n ℂ) :
    ‖Z‖ ≤ Real.sqrt (∑ i, ∑ j, ‖Z i j‖ ^ 2) := by
  rw [l2_opNorm_def]
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.sqrt_nonneg _) fun x => ?_
  refine (sq_le_sq₀ (by positivity) (by positivity)).mp ?_
  rw [mul_pow, Real.sq_sqrt (by positivity), EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : ‖∑ j, Z i j * x j‖ ≤ ∑ j, ‖Z i j‖ * ‖x j‖ :=
    (norm_sum_le _ _).trans (le_of_eq (by simp))
  calc _ = ‖∑ j, Z i j * x j‖ ^ 2 := rfl
    _ ≤ (∑ j, ‖Z i j‖ * ‖x j‖) ^ 2 := by gcongr
    _ ≤ _ := Finset.sum_mul_sq_le_sq_mul_sq _ _ _

end general

section hermitian

variable {n : Type*} [Fintype n] [DecidableEq n]

end hermitian

section boost

variable {p q : Type*} [Fintype p] [Fintype q] [DecidableEq p] [DecidableEq q]

def invSqrt {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) : Matrix n n ℂ :=
  (CFC.sqrt M)⁻¹

def boost (Z : Matrix p q ℂ) : Matrix (p ⊕ q) (p ⊕ q) ℂ :=
  fromBlocks (invSqrt (1 - Z * Zᴴ)) (Z * invSqrt (1 - Zᴴ * Z))
    (Zᴴ * invSqrt (1 - Z * Zᴴ)) (invSqrt (1 - Zᴴ * Z))

section invSqrt

variable {n : Type*} [Fintype n] [DecidableEq n] {M : Matrix n n ℂ}

end invSqrt

variable {Z : Matrix p q ℂ}

end boost

end MatrixBall

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EntireApplyEqOfPeriodicOfSpanReal
section
open Set Metric Filter Topology
open scoped Nat

namespace GlobalTheory

section Periodic

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem entire_apply_eq_of_values_on_compact {F : E → V} (hF : Differentiable ℂ F) {K : Set E}
    (hK : IsCompact K) (hcov : ∀ x, ∃ k ∈ K, F x = F k) (z w : E) : F z = F w := by
  refine hF.apply_eq_apply_of_bounded ((hK.image hF.continuous).isBounded.subset ?_) z w
  rintro _ ⟨x, rfl⟩
  obtain ⟨k, hk, h⟩ := hcov x
  exact ⟨k, hk, h.symm⟩

theorem entire_apply_eq_of_periodic_of_compact {F : E → V} (hF : Differentiable ℂ F)
    {G K : Set E} (hK : IsCompact K) (hcov : ∀ x, ∃ k ∈ K, ∃ g ∈ G, x = k + g)
    (hper : ∀ x, ∀ g ∈ G, F (x + g) = F x) (z w : E) : F z = F w := by
  refine entire_apply_eq_of_values_on_compact hF hK (fun x => ?_) z w
  obtain ⟨k, hk, g, hg, rfl⟩ := hcov x
  exact ⟨k, hk, hper k g hg⟩

theorem entire_apply_eq_of_periodic_of_bounded [FiniteDimensional ℂ E] {F : E → V}
    (hF : Differentiable ℂ F) {G K : Set E} (hK : Bornology.IsBounded K)
    (hcov : ∀ x, ∃ k ∈ K, ∃ g ∈ G, x = k + g)
    (hper : ∀ x, ∀ g ∈ G, F (x + g) = F x) (z w : E) : F z = F w := by
  haveI : ProperSpace E := FiniteDimensional.proper ℂ E
  refine entire_apply_eq_of_periodic_of_compact hF hK.isCompact_closure (fun x => ?_) hper z w
  obtain ⟨k, hk, g, hg, h⟩ := hcov x
  exact ⟨k, subset_closure hk, g, hg, h⟩

theorem entire_const_of_addSubgroup_periodic [FiniteDimensional ℂ E] {F : E → V}
    (hF : Differentiable ℂ F) (G : AddSubgroup E) {K : Set E} (hK : Bornology.IsBounded K)
    (hcov : ∀ x, ∃ g ∈ G, ∃ k ∈ K, x = g + k)
    (hper : ∀ x, ∀ g ∈ G, F (x + g) = F x) : ∃ c, ∀ z, F z = c := by
  refine ⟨F 0, fun z => entire_apply_eq_of_periodic_of_bounded hF (G := G) hK (fun x => ?_)
    hper z 0⟩
  obtain ⟨g, hg, k, hk, h⟩ := hcov x
  exact ⟨k, hk, g, hg, h.trans (add_comm _ _)⟩

theorem entire_apply_eq_of_isZLattice_periodic [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → V} (hF : Differentiable ℂ F) (L : Submodule ℤ E) [DiscreteTopology L]
    [IsZLattice ℝ L] (hper : ∀ x, ∀ g ∈ L, F (x + g) = F x) (z w : E) : F z = F w :=
  hF.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L F hF.continuous hper).isBounded z w

omit [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V] in

theorem periodic_of_mem_span_int {F : E → V} {S : Set E}
    (hper : ∀ x, ∀ g ∈ S, F (x + g) = F x) :
    ∀ x, ∀ g ∈ Submodule.span ℤ S, F (x + g) = F x := by
  let P : AddSubgroup E :=
    { carrier := {g | ∀ x, F (x + g) = F x}
      zero_mem' := fun x => by simp
      add_mem' := fun {a b} ha hb x => by rw [← add_assoc, hb, ha]
      neg_mem' := fun {a} ha x => by rw [← ha (x + -a)]; simp }
  intro x g hg
  have : Submodule.span ℤ S ≤ AddSubgroup.toIntSubmodule P :=
    Submodule.span_le.2 fun s hs y => hper y s hs
  exact this hg x

theorem entire_apply_eq_of_periodic_of_span_real [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {F : E → V} (hF : Differentiable ℂ F) {S : Set E} (hS : Submodule.span ℝ S = ⊤)
    (hper : ∀ x, ∀ g ∈ S, F (x + g) = F x) (z w : E) : F z = F w := by
  obtain ⟨t, htS, hspan, hli⟩ := exists_linearIndependent ℝ S
  let b : Module.Basis t ℝ E := Module.Basis.mk hli (by simp [hspan, hS])
  haveI : Finite t := Module.Finite.finite_basis b
  refine entire_apply_eq_of_isZLattice_periodic hF (Submodule.span ℤ (range b))
    (periodic_of_mem_span_int ?_) z w
  rintro x _ ⟨i, rfl⟩
  exact hper x _ (by simpa [b] using htS i.2)

end Periodic

section Polynomial

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

theorem iteratedDeriv_zero_eq_zero_of_poly_bound {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) {n : ℕ} (hn : m < n) :
    iteratedDeriv n F 0 = 0 := by
  have hC : 0 ≤ C := by simpa using (norm_nonneg _).trans (hb 0)
  have key : ∀ R : ℝ, 1 ≤ R → ‖iteratedDeriv n F 0‖ ≤ (n ! * C * 2 ^ m) / R := by
    intro R hR
    have hR0 : 0 < R := by linarith
    have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (c := 0) (R := R)
      (C := C * (2 ^ m * R ^ m)) n hR0 hF.diffContOnCl (fun z hz => by
        have hz' : ‖z‖ = R := by simpa using hz
        refine (hb z).trans ?_
        rw [hz', ← mul_pow]
        gcongr
        linarith)
    refine h.trans ?_
    rw [div_le_div_iff₀ (by positivity) hR0]
    have : R ^ m * R ≤ R ^ n := by
      rw [← pow_succ]
      exact pow_le_pow_right₀ hR hn
    calc (n ! : ℝ) * (C * (2 ^ m * R ^ m)) * R = (n ! * C * 2 ^ m) * (R ^ m * R) := by ring
      _ ≤ _ := by gcongr
  have lim : Tendsto (fun R : ℝ => (n ! * C * 2 ^ m) / R) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  exact norm_le_zero_iff.1 (ge_of_tendsto lim ((eventually_ge_atTop 1).mono key))

theorem entire_eq_taylor_sum_of_poly_bound {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) (z : ℂ) :
    F z = ∑ k ∈ Finset.range (m + 1), z ^ k • ((k ! : ℂ)⁻¹ • iteratedDeriv k F 0) := by
  have h := Complex.hasSum_taylorSeries_of_entire hF 0 z
  have h2 := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (f := fun n : ℕ => (n ! : ℂ)⁻¹ • (z - 0) ^ n • iteratedDeriv n F 0)
    (s := Finset.range (m + 1)) (fun n hn => by
      have : m < n := by simpa using hn
      simp [iteratedDeriv_zero_eq_zero_of_poly_bound hF hb this])
  rw [h.unique h2]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sub_zero, smul_comm]

theorem entire_exists_coeff_of_poly_bound {F : ℂ → V} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ a : ℕ → V, ∀ z, F z = ∑ k ∈ Finset.range (m + 1), z ^ k • a k :=
  ⟨_, entire_eq_taylor_sum_of_poly_bound hF hb⟩

theorem entire_exists_polynomial_of_poly_bound {F : ℂ → ℂ} (hF : Differentiable ℂ F) {C : ℝ}
    {m : ℕ} (hb : ∀ z, ‖F z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ p : Polynomial ℂ, p.natDegree ≤ m ∧ ∀ z, F z = p.eval z := by
  obtain ⟨a, ha⟩ := entire_exists_coeff_of_poly_bound hF hb
  refine ⟨∑ k ∈ Finset.range (m + 1), Polynomial.monomial k (a k), ?_, fun z => ?_⟩
  · refine Polynomial.natDegree_sum_le_of_forall_le _ _ fun k hk => ?_
    exact (Polynomial.natDegree_monomial_le _).trans (by simpa [Nat.lt_succ_iff] using hk)
  · rw [ha z, Polynomial.eval_finset_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [mul_comm]

end Polynomial

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EqZeroOfEvalGridEqZeroOfTotalDegreeLe
section
namespace GlobalTheory

open MvPolynomial

section Vanishing

variable {σ R : Type*} [Finite σ] [CommRing R] [IsDomain R] [CharZero R]

theorem eq_zero_of_eval_box_eq_zero (d : σ → ℕ) (P : MvPolynomial σ R)
    (hdeg : ∀ i, P.degreeOf i ≤ d i)
    (hP : ∀ x : σ → ℕ, (∀ i, x i ≤ d i) → eval (fun i => (x i : R)) P = 0) : P = 0 := by
  classical
  refine eq_zero_of_eval_zero_at_prod_finset P
    (fun i => (Finset.range (d i + 1)).image (Nat.cast : ℕ → R)) (fun i => ?_) (fun x hx => ?_)
  · rw [Finset.card_image_of_injective _ Nat.cast_injective, Finset.card_range]
    exact Nat.lt_succ_of_le (hdeg i)
  · choose n hn hnx using fun i => Finset.mem_image.1 (hx i)
    have : x = fun i => (n i : R) := funext fun i => (hnx i).symm
    rw [this]
    exact hP n fun i => Nat.lt_succ_iff.1 (Finset.mem_range.1 (hn i))

theorem eq_zero_of_eval_grid_eq_zero (d : ℕ) (P : MvPolynomial σ R)
    (hdeg : ∀ i, P.degreeOf i ≤ d)
    (hP : ∀ x : σ → ℕ, (∀ i, x i ≤ d) → eval (fun i => (x i : R)) P = 0) : P = 0 :=
  eq_zero_of_eval_box_eq_zero (fun _ => d) P hdeg hP

end Vanishing

section Span

variable {σ A K V : Type*} [Finite σ] [Field K] [CharZero K] [CommSemiring A] [Algebra A K]
  [AddCommGroup V] [Module K V]

theorem mem_of_grid_mem (d : ℕ) (Φ : (σ → A) → V)
    (hΦ : ∀ l : Module.Dual K V, ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧
      ∀ x, l (Φ x) = eval (fun i => algebraMap A K (x i)) P)
    (U : Submodule K V)
    (hU : ∀ x : σ → ℕ, (∀ i, x i ≤ d) → Φ (fun i => (x i : A)) ∈ U) (y : σ → A) :
    Φ y ∈ U := by
  rw [← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff U]
  intro l hl
  obtain ⟨P, hdeg, hP⟩ := hΦ l
  have h0 : P = 0 := by
    refine eq_zero_of_eval_grid_eq_zero d P hdeg fun x hx => ?_
    have := (Submodule.mem_dualAnnihilator l).1 hl _ (hU x hx)
    rw [hP] at this
    simpa using this
  rw [hP, h0, map_zero]

theorem span_grid_eq_span_range (d : ℕ) (Φ : (σ → A) → V)
    (hΦ : ∀ l : Module.Dual K V, ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧
      ∀ x, l (Φ x) = eval (fun i => algebraMap A K (x i)) P) :
    Submodule.span K ((fun x : σ → ℕ => Φ fun i => (x i : A)) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range Φ) := by
  apply le_antisymm
  · apply Submodule.span_mono
    rintro _ ⟨x, -, rfl⟩
    exact ⟨_, rfl⟩
  · rw [Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    refine mem_of_grid_mem d Φ hΦ _ (fun x hx => ?_) y
    apply Submodule.subset_span
    exact ⟨x, hx, rfl⟩

omit [Finite σ] [CharZero K] in

theorem exists_poly_dual_sum_monomial_smul (d : ℕ) (s : Finset (σ →₀ ℕ)) (v : (σ →₀ ℕ) → V)
    (hs : ∀ a ∈ s, ∀ i, a i ≤ d) (l : Module.Dual K V) :
    ∃ P : MvPolynomial σ K, (∀ i, P.degreeOf i ≤ d) ∧ ∀ x : σ → A,
      l (∑ a ∈ s, (a.prod fun i n => algebraMap A K (x i) ^ n) • v a) =
        eval (fun i => algebraMap A K (x i)) P := by
  classical
  refine ⟨∑ a ∈ s, monomial a (l (v a)), fun i => ?_, fun x => ?_⟩
  · rw [degreeOf_le_iff]
    intro m hm
    obtain ⟨a, ha, hma⟩ := Finset.mem_biUnion.1 (support_sum hm)
    have := Finset.mem_singleton.1 (support_monomial_subset hma)
    rw [this]
    exact hs a ha i
  · simp only [map_sum, map_smul, eval_monomial, smul_eq_mul, mul_comm]

theorem span_grid_eq_span_range_of_eq_sum (d : ℕ) (Φ : (σ → A) → V)
    (s : Finset (σ →₀ ℕ)) (v : (σ →₀ ℕ) → V) (hs : ∀ a ∈ s, ∀ i, a i ≤ d)
    (hΦ : ∀ x, Φ x = ∑ a ∈ s, (a.prod fun i n => algebraMap A K (x i) ^ n) • v a) :
    Submodule.span K ((fun x : σ → ℕ => Φ fun i => (x i : A)) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range Φ) := by
  refine span_grid_eq_span_range d Φ fun l => ?_
  simp only [hΦ]
  exact exists_poly_dual_sum_monomial_smul d s v hs l

theorem span_grid_eval_eq_span_range {B : Type*} [CommRing B] [Algebra K B] (d : ℕ)
    (F : MvPolynomial σ B) (hF : ∀ i, F.degreeOf i ≤ d) :
    Submodule.span K ((fun x : σ → ℕ => eval (fun i => (x i : B)) F) '' {x | ∀ i, x i ≤ d}) =
      Submodule.span K (Set.range fun x : σ → A =>
        eval (fun i => algebraMap K B (algebraMap A K (x i))) F) := by
  have h := span_grid_eq_span_range_of_eq_sum (K := K) d
    (fun x : σ → A => eval (fun i => algebraMap K B (algebraMap A K (x i))) F)
    F.support (fun a => F.coeff a) (fun a ha i => (degreeOf_le_iff.1 (hF i)) a ha)
    (fun x => by
      rw [eval_eq]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Algebra.smul_def, Finsupp.prod, map_prod, mul_comm]
      simp only [map_pow])
  simpa only [map_natCast] using h

end Span

section Combination

variable {ι κ V : Type*} [Fintype ι] [AddCommGroup V] {W : ι → Type*}
  [∀ j, AddCommGroup (W j)]

theorem exists_nsmul_add_apply_ne_zero [∀ j, IsAddTorsionFree (W j)] (l : ∀ j, V →+ W j)
    (v w : V) :
    ∃ c : ℕ, c ≤ Fintype.card ι ∧ ∀ j, l j v ≠ 0 ∨ l j w ≠ 0 → l j (c • w + v) ≠ 0 := by
  classical
  by_contra h
  push Not at h
  choose f hf hf0 using h
  have hinj : Function.Injective fun a : Fin (Fintype.card ι + 1) =>
      f a (Nat.lt_succ_iff.1 a.2) := by
    intro a b hab
    have h1 := hf0 a (Nat.lt_succ_iff.1 a.2)
    have h2 := hf0 b (Nat.lt_succ_iff.1 b.2)
    have h3 := hf a (Nat.lt_succ_iff.1 a.2)
    simp only at hab
    rw [← hab] at h2
    generalize f a _ = j at h1 h2 h3
    rw [map_add, map_nsmul] at h1 h2
    have hw : l j w ≠ 0 := by
      intro hw
      rw [hw, nsmul_zero, zero_add] at h1
      exact h3.elim (· h1) (· hw)
    have h4 : (a : ℕ) • l j w = (b : ℕ) • l j w := add_right_cancel (h1.trans h2.symm)
    have h5 : ((a : ℤ) - (b : ℤ)) • l j w = 0 := by
      rw [sub_smul, natCast_zsmul, natCast_zsmul, h4, sub_self]
    have h6 := (smul_eq_zero.1 h5).resolve_right hw
    exact Fin.ext (by omega)
  have := Fintype.card_le_of_injective _ hinj
  simp at this

theorem exists_sum_nsmul_apply_ne_zero_finset [∀ j, IsAddTorsionFree (W j)]
    (l : ∀ j, V →+ W j) (s : κ → V) (t : Finset κ) :
    ∃ c : κ → ℕ, (∀ k, c k ≤ Fintype.card ι) ∧
      ∀ j, (∃ k ∈ t, l j (s k) ≠ 0) → l j (∑ k ∈ t, c k • s k) ≠ 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨0, fun _ => Nat.zero_le _, fun j ⟨k, hk, _⟩ => absurd hk (by simp)⟩
  | insert a t ha ih =>
    obtain ⟨c, hc, hl⟩ := ih
    obtain ⟨n, hn, hln⟩ := exists_nsmul_add_apply_ne_zero l (∑ k ∈ t, c k • s k) (s a)
    refine ⟨Function.update c a n, fun k => ?_, fun j ⟨k, hk, hjk⟩ => ?_⟩
    · by_cases hk : k = a
      · subst hk; simpa using hn
      · simpa [hk] using hc k
    · rw [Finset.sum_insert ha, Function.update_self,
        Finset.sum_congr rfl (g := fun k => c k • s k) fun k hk => by
          rw [Function.update_of_ne (ne_of_mem_of_not_mem hk ha)]]
      apply hln
      rcases Finset.mem_insert.1 hk with rfl | hk
      · exact Or.inr hjk
      · exact Or.inl (hl j ⟨k, hk, hjk⟩)

theorem exists_sum_nsmul_apply_ne_zero [∀ j, IsAddTorsionFree (W j)] [Fintype κ]
    (l : ∀ j, V →+ W j) (s : κ → V) (h : ∀ j, ∃ k, l j (s k) ≠ 0) :
    ∃ c : κ → ℕ, (∀ k, c k ≤ Fintype.card ι) ∧ ∀ j, l j (∑ k, c k • s k) ≠ 0 := by
  obtain ⟨c, hc, hl⟩ := exists_sum_nsmul_apply_ne_zero_finset l s Finset.univ
  exact ⟨c, hc, fun j => hl j ((h j).imp fun k hk => ⟨Finset.mem_univ k, hk⟩)⟩

variable {K : Type*} [Field K] [CharZero K] [Module K V] [∀ j, Module K (W j)]

theorem exists_sum_natCast_smul_apply_ne_zero [Fintype κ]
    (l : ∀ j, V →ₗ[K] W j) (s : κ → V) (h : ∀ j, ∃ k, l j (s k) ≠ 0) :
    ∃ c : κ → ℕ, (∀ k, c k ≤ Fintype.card ι) ∧ ∀ j, l j (∑ k, (c k : K) • s k) ≠ 0 := by
  have : ∀ j, IsAddTorsionFree (W j) := fun j => IsAddTorsionFree.of_isTorsionFree K (W j)
  simp only [Nat.cast_smul_eq_nsmul]
  exact exists_sum_nsmul_apply_ne_zero (fun j => (l j).toAddMonoidHom) s h

end Combination

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.OneLeDetOneAdd
section
open scoped ComplexOrder

namespace GlobalTheory.OneLeDetOneAdd

theorem one_le_det_one_add {𝕜 : Type*} {n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]
    {D : Matrix n n 𝕜} (hD : D.PosSemidef) : (1 : 𝕜) ≤ (1 + D).det := by
  have hA : (1 + D).IsHermitian := Matrix.isHermitian_one.add hD.1
  have hμ : ∀ i, 1 ≤ hA.eigenvalues i := by
    intro i
    have hv1 : RCLike.re (star ⇑(hA.eigenvectorBasis i) ⬝ᵥ ⇑(hA.eigenvectorBasis i)) = 1 := by
      rw [dotProduct_comm]
      simp only [← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
        hA.eigenvectorBasis.orthonormal.1 i, algebraMap.coe_one, one_pow, RCLike.one_re]
    have h := hA.eigenvalues_eq i
    rw [Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add, map_add, hv1] at h
    have h0 := hD.re_dotProduct_nonneg ⇑(hA.eigenvectorBasis i)
    linarith
  have hprod : (1 : ℝ) ≤ ∏ i, hA.eigenvalues i := by
    calc (1 : ℝ) = ∏ _i : n, (1 : ℝ) := by simp
      _ ≤ ∏ i, hA.eigenvalues i := Finset.prod_le_prod (fun _ _ => zero_le_one) (fun i _ => hμ i)
  rw [hA.det_eq_prod_eigenvalues, ← RCLike.ofReal_prod]
  calc (1 : 𝕜) = ((1 : ℝ) : 𝕜) := by simp
    _ ≤ _ := RCLike.ofReal_le_ofReal.mpr hprod

end GlobalTheory.OneLeDetOneAdd
end

