import Mathlib
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.EnormPowLeInvMeasureMulLintegralBall
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralLogNormLeHalfLogIntegralSq
section
open MeasureTheory Metric Set Filter Real
open scoped ENNReal Topology Pointwise

namespace GlobalTheory

section Rotation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [MeasurableSpace E] [BorelSpace E]

noncomputable def sphereRotation (θ : ℝ) (x : sphere (0 : E) 1) : sphere (0 : E) 1 :=
  ⟨circleMap 0 1 θ • (x : E), by simp [norm_smul]⟩

omit [MeasurableSpace E] [BorelSpace E] in
@[simp]
theorem coe_sphereRotation (θ : ℝ) (x : sphere (0 : E) 1) :
    (sphereRotation θ x : E) = circleMap 0 1 θ • (x : E) := rfl

omit [MeasurableSpace E] [BorelSpace E] in
theorem continuous_sphereRotation :
    Continuous (Function.uncurry (sphereRotation (E := E))) := by
  refine continuous_induced_rng.2 ?_
  have e : (Subtype.val ∘ Function.uncurry (sphereRotation (E := E))) =
      fun q : ℝ × sphere (0 : E) 1 => circleMap 0 1 q.1 • (q.2 : E) := by
    funext q
    exact coe_sphereRotation q.1 q.2
  rw [e]
  exact ((continuous_circleMap 0 1).comp continuous_fst).smul
    (continuous_subtype_val.comp continuous_snd)

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

theorem measurePreserving_sphereRotation [FiniteDimensional ℂ E] (μ : Measure E)
    [μ.IsAddHaarMeasure] (θ : ℝ) :
    MeasurePreserving (sphereRotation θ) μ.toSphere μ.toSphere := by
  set ζ : ℂ := circleMap 0 1 θ with hζ_def
  have hζ : ‖ζ‖ = 1 := by simp [ζ, norm_circleMap_zero]
  have hζ0 : ζ ≠ 0 := by
    rw [← norm_ne_zero_iff, hζ]; exact one_ne_zero
  have hm : Measurable (sphereRotation (E := E) θ) :=
    (continuous_sphereRotation.comp (continuous_const.prodMk continuous_id)).measurable
  refine ⟨hm, Measure.ext fun s hs => ?_⟩
  rw [Measure.map_apply hm hs, Measure.toSphere_apply' μ (hm hs), Measure.toSphere_apply' μ hs]
  congr 1
  have hset : Ioo (0 : ℝ) 1 • ((↑) '' (sphereRotation θ ⁻¹' s) : Set E) =
      (fun v : E => ζ • v) ⁻¹' (Ioo (0 : ℝ) 1 • ((↑) '' s)) := by
    ext v
    constructor
    · rintro ⟨t, ht, _, ⟨w, hw, rfl⟩, rfl⟩
      refine ⟨t, ht, _, ⟨sphereRotation θ w, hw, rfl⟩, ?_⟩
      show t • ((sphereRotation θ w : sphere (0 : E) 1) : E) = ζ • (t • (w : E))
      rw [coe_sphereRotation]
      exact smul_comm t ζ (w : E)
    · rintro ⟨t, ht, _, ⟨u, hu, rfl⟩, huv⟩
      have hwmem : ζ⁻¹ • (u : E) ∈ sphere (0 : E) 1 := by
        simp [norm_smul, hζ]
      set w : sphere (0 : E) 1 := ⟨ζ⁻¹ • (u : E), hwmem⟩ with hw_def
      have hw : sphereRotation θ w = u := by
        apply Subtype.ext
        rw [coe_sphereRotation]
        show ζ • ζ⁻¹ • (u : E) = u
        rw [smul_smul, mul_inv_cancel₀ hζ0, one_smul]
      refine ⟨t, ht, _, ⟨w, ?_, rfl⟩, ?_⟩
      · show sphereRotation θ w ∈ s
        rw [hw]; exact hu
      · have huv' : t • (u : E) = ζ • v := huv
        show t • (ζ⁻¹ • (u : E)) = v
        rw [smul_comm t ζ⁻¹, huv', smul_smul, inv_mul_cancel₀ hζ0, one_smul]
  rw [hset]
  exact (measurePreserving_smul_of_norm_eq_one μ hζ).measure_preimage_emb
    (MeasurableEquiv.smul₀ ζ hζ0).measurableEmbedding _

end Rotation

section Torus

variable {ι : Type*} [Fintype ι]

end Torus

section Concavity

variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V]

end Concavity

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NormDetMulProdSqLeOfEntryLe
section
open scoped TensorProduct Matrix
open Module Algebra

namespace GlobalTheory

section Pi

variable {E : Type*} [CommRing E] {ι : Type*} [Fintype ι]

theorem leftMulMatrix_pi_basisFun [DecidableEq ι] (x : ι → E) :
    leftMulMatrix (Pi.basisFun E ι) x = Matrix.diagonal x := by
  ext i j
  rw [leftMulMatrix_eq_repr_mul]
  by_cases h : i = j <;> simp [h, Matrix.diagonal_apply]

theorem algebraTrace_pi_apply (x : ι → E) : Algebra.trace E (ι → E) x = ∑ i, x i := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun E ι), leftMulMatrix_pi_basisFun,
    Matrix.trace_diagonal]

end Pi

section BaseChange

variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [CommRing E]
  [Algebra R E] [Module.Free R S] [Module.Finite R S]

theorem algebraTrace_one_tmul (x : S) :
    Algebra.trace E (E ⊗[R] S) (1 ⊗ₜ x) = algebraMap R E (Algebra.trace R S x) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul,
    LinearMap.trace_baseChange]

end BaseChange

section Split

variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field E]
  [Algebra R E] [IsFiniteSplit E (E ⊗[R] S)]

variable (R S) in

theorem exists_algEquiv_fin_points :
    ∃ (n : ℕ) (P : Fin n ≃ (S →ₐ[R] E)) (e : E ⊗[R] S ≃ₐ[E] (Fin n → E)),
      ∀ x j, e (1 ⊗ₜ x) j = P j x := by
  classical
  obtain ⟨n, ⟨e⟩⟩ := IsFiniteSplit.nonempty_algEquiv_fun E (E ⊗[R] S)
  let f : Fin n → (E ⊗[R] S →ₐ[E] E) := fun j ↦
    (Pi.evalAlgHom E (fun _ ↦ E) j).comp e.toAlgHom
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      by_contra h
      have := AlgHom.congr_fun hij (e.symm (Pi.single i 1))
      simp [f, Ne.symm h] at this
    · intro g
      obtain ⟨j, hj⟩ := AlgHom.eq_piEvalAlgHom (g.comp e.symm.toAlgHom)
      refine ⟨j, AlgHom.ext fun x ↦ ?_⟩
      simpa [f] using (AlgHom.congr_fun hj (e x)).symm
  exact ⟨n, (Equiv.ofBijective f hf).trans (AlgHom.liftEquiv R E S E).symm, e, fun x j ↦ rfl⟩

variable (R S) in
theorem finite_algHom_of_isFiniteSplit : Finite (S →ₐ[R] E) := by
  obtain ⟨n, P, -⟩ := exists_algEquiv_fin_points R S E
  exact Finite.of_equiv _ P

variable {E} in

theorem exists_algEquiv_points {ι : Type*} (P : ι ≃ (S →ₐ[R] E)) :
    ∃ e : E ⊗[R] S ≃ₐ[E] (ι → E), ∀ x j, e (1 ⊗ₜ x) j = P j x := by
  obtain ⟨n, Q, e, he⟩ := exists_algEquiv_fin_points R S E
  refine ⟨e.trans (AlgEquiv.piCongrLeft' E (fun _ ↦ E) (Q.trans P.symm)), fun x j ↦ ?_⟩
  simp [he]

variable [Module.Free R S]

variable (R S) in

theorem natCard_algHom_eq_finrank [Nontrivial R] : Nat.card (S →ₐ[R] E) = finrank R S := by
  obtain ⟨n, P, e, -⟩ := exists_algEquiv_fin_points R S E
  rw [← Nat.card_congr P, ← Module.finrank_baseChange (R := E), e.toLinearEquiv.finrank_eq]
  simp

variable {E} {ι : Type*} [Fintype ι]

theorem card_eq_finrank_of_points (P : ι ≃ (S →ₐ[R] E)) : Fintype.card ι = finrank R S := by
  have := (algebraMap R E).domain_nontrivial
  rw [← natCard_algHom_eq_finrank R S E, ← Nat.card_congr P, Nat.card_eq_fintype_card]

variable [Module.Finite R S]

theorem algebraMap_trace_eq_sum_points (P : ι ≃ (S →ₐ[R] E)) (x : S) :
    algebraMap R E (Algebra.trace R S x) = ∑ j, P j x := by
  obtain ⟨e, he⟩ := exists_algEquiv_points P
  rw [← algebraTrace_one_tmul, ← Algebra.trace_eq_of_algEquiv e, algebraTrace_pi_apply]
  simp [he]

variable [DecidableEq ι]

theorem det_points_sq_eq_discr (P : ι ≃ (S →ₐ[R] E)) (v : ι → S) :
    (Matrix.of fun i j ↦ P j (v i)).det ^ 2 = algebraMap R E (discr R v) := by
  have : (algebraMap R E).mapMatrix (traceMatrix R v) =
      (Matrix.of fun i j ↦ P j (v i)) * (Matrix.of fun i j ↦ P j (v i))ᵀ := by
    ext i j
    simp [Matrix.mul_apply, algebraMap_trace_eq_sum_points P]
  rw [discr_def, RingHom.map_det, this, Matrix.det_mul, Matrix.det_transpose, pow_two]

omit [Module.Free R S] [Module.Finite R S] in

theorem det_points_ne_zero_of_basis (P : ι ≃ (S →ₐ[R] E)) (b : Basis ι R S) :
    (Matrix.of fun i j ↦ P j (b i)).det ≠ 0 := by
  obtain ⟨e, he⟩ := exists_algEquiv_points P
  have h := (Pi.basisFun E ι).isUnit_det ((Algebra.TensorProduct.basis E b).map e.toLinearEquiv)
  rw [Basis.det_apply, ← Matrix.det_transpose] at h
  convert h.ne_zero using 2
  ext i j
  simp [Basis.toMatrix_apply, Algebra.TensorProduct.basis_apply, he]

end Split

section General

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

end General

section Hadamard

variable {𝕜 : Type*} [RCLike 𝕜] {ι : Type*} [Fintype ι] [DecidableEq ι]

end Hadamard

section Etale

variable (K A : Type*) [Field K] [CommRing A] [Algebra K A]

variable {K A} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem det_points_ne_zero_iff {E : Type*} [Field E] [Algebra K E] [Module.Finite K A]
    [IsFiniteSplit E (E ⊗[K] A)] (P : ι ≃ (A →ₐ[K] E)) (v : ι → A) :
    (Matrix.of fun i j ↦ P j (v i)).det ≠ 0 ↔ LinearIndependent K v := by
  constructor
  · intro h
    by_contra hli
    have := det_points_sq_eq_discr P v
    rw [discr_zero_of_not_linearIndependent K hli, map_zero] at this
    exact pow_ne_zero 2 h this
  · intro h
    simpa using det_points_ne_zero_of_basis P
      (basisOfLinearIndependentOfCardEqFinrank' v h (card_eq_finrank_of_points P))

theorem discr_ne_zero_iff_of_etale [Algebra.Etale K A] (h : Fintype.card ι = finrank K A)
    (v : ι → A) : discr K v ≠ 0 ↔ LinearIndependent K v := by
  have := FormallyUnramified.finite_of_free K A
  have := finite_algHom_of_isFiniteSplit K A (AlgebraicClosure K)
  obtain ⟨P⟩ : Nonempty (ι ≃ (A →ₐ[K] AlgebraicClosure K)) := by
    rw [← Finite.card_eq, natCard_algHom_eq_finrank, Nat.card_eq_fintype_card, h]
  rw [← det_points_ne_zero_iff P, ← pow_ne_zero_iff (a := Matrix.det _) two_ne_zero,
    det_points_sq_eq_discr]
  simp

end Etale

section DiscrBaseChange

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Module.Free R S]
  [Module.Finite R S] {ι : Type*} [Fintype ι] [DecidableEq ι]

end DiscrBaseChange

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CovolumeBounds.NormPderivIterLeOfAnalyticAt
section
open Filter Topology

namespace GlobalTheory

section Def

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

noncomputable def pderivList (l : List ι) (F : (ι → 𝕜) → V) : (ι → 𝕜) → V :=
  lineDerivList 𝕜 (l.map fun k => Pi.single k (1 : 𝕜)) F

noncomputable def pderivIter (α : ι →₀ ℕ) (F : (ι → 𝕜) → V) : (ι → 𝕜) → V :=
  pderivList α.toMultiset.toList F

noncomputable def polyDeriv (P : MvPolynomial ι 𝕜) (F : (ι → 𝕜) → V) (a : ι → 𝕜) : V :=
  ∑ α ∈ P.support, P.coeff α • pderivIter α F a

@[simp] theorem pderivList_nil (F : (ι → 𝕜) → V) : pderivList [] F = F := rfl

theorem pderivList_append (l₁ l₂ : List ι) (F : (ι → 𝕜) → V) :
    pderivList (l₁ ++ l₂) F = pderivList l₁ (pderivList l₂ F) := by
  simp only [pderivList, List.map_append, lineDerivList_append]

@[simp] theorem pderivIter_zero (F : (ι → 𝕜) → V) : pderivIter 0 F = F := by
  simp [pderivIter]

theorem update_eq_add_smul_single (z : ι → 𝕜) (k : ι) (t : 𝕜) :
    Function.update z k t = z + (t - z k) • (Pi.single k 1 : ι → 𝕜) := by
  funext j
  by_cases h : j = k
  · subst h; simp
  · simp [h]

theorem pderivList_replicate (k : ι) (n : ℕ) (F : (ι → 𝕜) → V) (z : ι → 𝕜) :
    pderivList (List.replicate n k) F z
      = iteratedDeriv n (fun t => F (Function.update z k t)) (z k) := by
  have h := lineDerivList_replicate n (Pi.single k (1 : 𝕜) : ι → 𝕜) F z (0 : 𝕜)
  rw [zero_smul, add_zero] at h
  rw [pderivList, List.map_replicate, h]
  simp only [update_eq_add_smul_single]
  rw [iteratedDeriv_comp_sub_const (f := fun s : 𝕜 => F (z + s • (Pi.single k 1 : ι → 𝕜)))]
  simp

theorem pderivIter_single (k : ι) (n : ℕ) (F : (ι → 𝕜) → V) (z : ι → 𝕜) :
    pderivIter (Finsupp.single k n) F z
      = iteratedDeriv n (fun t => F (Function.update z k t)) (z k) := by
  rw [← pderivList_replicate, pderivIter, Finsupp.toMultiset_single]
  congr 1
  rw [← List.perm_replicate, ← Multiset.coe_eq_coe, Multiset.coe_toList,
    Multiset.nsmul_singleton, Multiset.coe_replicate]

@[simp] theorem pderivIter_zero_fun (α : ι →₀ ℕ) :
    pderivIter α (fun _ : ι → 𝕜 => (0 : V)) = fun _ => 0 :=
  lineDerivList_zero _

theorem polyDeriv_eq_sum_of_subset (P : MvPolynomial ι 𝕜) {s : Finset (ι →₀ ℕ)}
    (hs : P.support ⊆ s) (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv P F a = ∑ α ∈ s, P.coeff α • pderivIter α F a := by
  refine Finset.sum_subset hs fun α _ hα => ?_
  rw [MvPolynomial.notMem_support_iff.1 hα, zero_smul]

noncomputable def polyDerivLinear (F : (ι → 𝕜) → V) (a : ι → 𝕜) : MvPolynomial ι 𝕜 →ₗ[𝕜] V where
  toFun P := polyDeriv P F a
  map_add' P Q := by
    classical
    rw [polyDeriv_eq_sum_of_subset (P + Q) (s := P.support ∪ Q.support) MvPolynomial.support_add,
      polyDeriv_eq_sum_of_subset P (s := P.support ∪ Q.support) Finset.subset_union_left,
      polyDeriv_eq_sum_of_subset Q (s := P.support ∪ Q.support) Finset.subset_union_right,
      ← Finset.sum_add_distrib]
    simp only [MvPolynomial.coeff_add, add_smul]
  map_smul' c P := by
    rw [polyDeriv_eq_sum_of_subset (c • P) (s := P.support) MvPolynomial.support_smul,
      polyDeriv, Finset.smul_sum]
    simp only [MvPolynomial.coeff_smul, smul_eq_mul, mul_smul, RingHom.id_apply]

@[simp] theorem polyDerivLinear_apply (F : (ι → 𝕜) → V) (a : ι → 𝕜) (P : MvPolynomial ι 𝕜) :
    polyDerivLinear F a P = polyDeriv P F a := rfl

@[simp] theorem polyDeriv_zero (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv (0 : MvPolynomial ι 𝕜) F a = 0 := (polyDerivLinear F a).map_zero

@[simp] theorem polyDeriv_monomial (α : ι →₀ ℕ) (c : 𝕜) (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv (MvPolynomial.monomial α c) F a = c • pderivIter α F a := by
  rw [polyDeriv_eq_sum_of_subset _ (s := {α}) MvPolynomial.support_monomial_subset]
  simp

@[simp] theorem polyDeriv_C (c : 𝕜) (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv (MvPolynomial.C c) F a = c • F a := by
  rw [← MvPolynomial.monomial_zero', polyDeriv_monomial, pderivIter_zero]

@[simp] theorem polyDeriv_one (F : (ι → 𝕜) → V) (a : ι → 𝕜) :
    polyDeriv (1 : MvPolynomial ι 𝕜) F a = F a := by
  rw [← MvPolynomial.C_1, polyDeriv_C, one_smul]

@[simp] theorem polyDeriv_zero_fun (P : MvPolynomial ι 𝕜) (a : ι → 𝕜) :
    polyDeriv P (fun _ => (0 : V)) a = 0 := by
  simp [polyDeriv]

end Def

section Analytic

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]

variable [CompleteSpace V]

theorem analyticAt_pderivIter {F : (ι → 𝕜) → V} {a : ι → 𝕜} (h : AnalyticAt 𝕜 F a)
    (α : ι →₀ ℕ) : AnalyticAt 𝕜 (pderivIter α F) a :=
  analyticAt_lineDerivList h _

theorem pderivList_perm {F : (ι → 𝕜) → V} {a : ι → 𝕜} (h : AnalyticAt 𝕜 F a) {l₁ l₂ : List ι}
    (hl : l₁.Perm l₂) : pderivList l₁ F a = pderivList l₂ F a :=
  lineDerivList_perm h (hl.map _)

theorem pderivIter_add_index {F : (ι → 𝕜) → V} {a : ι → 𝕜} (h : AnalyticAt 𝕜 F a)
    (α β : ι →₀ ℕ) : pderivIter (α + β) F a = pderivIter α (pderivIter β F) a := by
  rw [pderivIter, pderivIter, pderivIter, ← pderivList_append]
  refine pderivList_perm h ?_
  rw [← Multiset.coe_eq_coe, ← Multiset.coe_add]
  simp only [Multiset.coe_toList, map_add]

end Analytic

section Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {ι : Type*} [DecidableEq ι]

theorem hasDerivAt_eval_line (Q : MvPolynomial ι 𝕜) (z : ι → 𝕜) (k : ι) :
    HasDerivAt (fun t : 𝕜 => MvPolynomial.eval (z + t • (Pi.single k 1 : ι → 𝕜)) Q)
      (MvPolynomial.eval z (MvPolynomial.pderiv k Q)) 0 := by
  induction Q using MvPolynomial.induction_on with
  | C c => simpa using hasDerivAt_const (0 : 𝕜) c
  | add P Q hP hQ => simpa using hP.fun_add hQ
  | mul_X P j hP =>
    have hj : HasDerivAt (fun t : 𝕜 => z j + t * (Pi.single k 1 : ι → 𝕜) j)
        ((Pi.single k 1 : ι → 𝕜) j) 0 := by
      simpa using ((hasDerivAt_id (0 : 𝕜)).mul_const ((Pi.single k 1 : ι → 𝕜) j)).const_add (z j)
    have := hP.fun_mul hj
    have e : (fun t : 𝕜 => MvPolynomial.eval (z + t • (Pi.single k 1 : ι → 𝕜))
        (P * MvPolynomial.X j)) = fun t : 𝕜 =>
          MvPolynomial.eval (z + t • (Pi.single k 1 : ι → 𝕜)) P
            * (z j + t * (Pi.single k 1 : ι → 𝕜) j) := by
      funext t; simp
    rw [e]
    refine this.congr_deriv ?_
    by_cases h : j = k
    · subst h; simp [add_comm, mul_comm]
    · simp [h, mul_comm]

end Polynomial

section Cauchy

variable {ι : Type*} [DecidableEq ι] [Fintype ι]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]

private theorem cauchy_estimate_iterated_pderiv {F : (ι → ℂ) → V} {a : ι → ℂ} {r : ι → ℝ} {M : ℝ} (α : ι →₀ ℕ)
    (hr : ∀ k, 0 ≤ r k) (hα : ∀ k, α k ≠ 0 → 0 < r k)
    (hF : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ ≤ r k) → AnalyticAt ℂ F z)
    (hM : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ = r k) → ‖F z‖ ≤ M) (s : Finset ι) :
    ∀ z : ι → ℂ, (∀ k ∈ s, z k = a k) → (∀ k ∉ s, ‖z k - a k‖ = r k) →
      ‖pderivIter (∑ k ∈ s, Finsupp.single k (α k)) F z‖
        ≤ (∏ k ∈ s, ((α k).factorial : ℝ)) * M / ∏ k ∈ s, r k ^ α k := by
  induction s using Finset.induction_on with
  | empty => intro z _ hz; simpa using hM z fun k => hz k (by simp)
  | insert j s hj ih =>
    intro z hz hz'
    have hzj : z j = a j := hz j (Finset.mem_insert_self _ _)
    have hup : ∀ t : ℂ, ‖t - a j‖ ≤ r j → AnalyticAt ℂ F (Function.update z j t) := by
      intro t ht
      refine hF _ fun k => ?_
      by_cases hk : k = j
      · subst hk; simpa using ht
      · rw [Function.update_of_ne hk]
        by_cases hks : k ∈ s
        · simpa [hz k (Finset.mem_insert_of_mem hks)] using hr k
        · exact (hz' k (by simp [hk, hks])).le
    have hb : ∀ t : ℂ, ‖t - a j‖ = r j →
        ‖pderivIter (∑ k ∈ s, Finsupp.single k (α k)) F (Function.update z j t)‖
          ≤ (∏ k ∈ s, ((α k).factorial : ℝ)) * M / ∏ k ∈ s, r k ^ α k := by
      intro t ht
      refine ih _ (fun k hk => ?_) (fun k hk => ?_)
      · rw [Function.update_of_ne (ne_of_mem_of_not_mem hk hj)]
        exact hz k (Finset.mem_insert_of_mem hk)
      · by_cases hkj : k = j
        · subst hkj; simpa using ht
        · rw [Function.update_of_ne hkj]
          exact hz' k (by simp [hkj, hk])
    have hza : AnalyticAt ℂ F z := by
      have := hup (z j) (by simpa [hzj] using hr j)
      rwa [Function.update_eq_self] at this
    rw [Finset.sum_insert hj, pderivIter_add_index hza, pderivIter_single, Finset.prod_insert hj,
      Finset.prod_insert hj, hzj]
    rcases (hr j).eq_or_lt with h0 | hpos
    · have hαj : α j = 0 := by
        by_contra hne
        exact (hα j hne).ne h0
      simpa [hαj] using hb (a j) (by simpa using h0)
    · have hd : DiffContOnCl ℂ (fun t => pderivIter (∑ k ∈ s, Finsupp.single k (α k)) F
          (Function.update z j t)) (Metric.ball (a j) (r j)) := by
        refine DifferentiableOn.diffContOnCl fun t ht => ?_
        rw [closure_ball _ hpos.ne', mem_closedBall_iff_norm] at ht
        exact ((analyticAt_pderivIter (hup t ht) _).differentiableAt.comp t
          (hasDerivAt_update z j t).differentiableAt).differentiableWithinAt
      refine (Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le (α j) hpos hd
        fun t ht => hb t (mem_sphere_iff_norm.1 ht)).trans_eq ?_
      ring

theorem norm_pderivIter_le_of_analyticAt {F : (ι → ℂ) → V} {a : ι → ℂ} {r : ι → ℝ} {M : ℝ}
    (α : ι →₀ ℕ) (hr : ∀ k, 0 ≤ r k) (hα : ∀ k, α k ≠ 0 → 0 < r k)
    (hF : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ ≤ r k) → AnalyticAt ℂ F z)
    (hM : ∀ z : ι → ℂ, (∀ k, ‖z k - a k‖ = r k) → ‖F z‖ ≤ M) :
    ‖pderivIter α F a‖ ≤ (∏ k, ((α k).factorial : ℝ)) * M / ∏ k, r k ^ α k := by
  have h := cauchy_estimate_iterated_pderiv α hr hα hF hM Finset.univ a (fun _ _ => rfl) (by simp)
  rwa [Finsupp.univ_sum_single] at h

end Cauchy

end GlobalTheory
end

