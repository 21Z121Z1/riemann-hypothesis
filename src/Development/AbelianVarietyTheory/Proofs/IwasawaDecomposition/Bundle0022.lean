import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0016
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0004

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoordsEqPairingsRationalSymplecticBasisStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_eq_pairings_rational_symplectic_basis : ∀ (g r : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε φ : Fin g → Fin r → ℚ), r = 2 * g → Mqᵀ = -Mq → Mq.det ≠ 0 → (∀ i j, ε i ⬝ᵥ Mq *ᵥ ε j = 0) → (∀ i j, φ i ⬝ᵥ Mq *ᵥ φ j = 0) → (∀ i j, φ j ⬝ᵥ Mq *ᵥ ε i = if i = j then 1 else 0) → ∀ x : Fin r → ℚ, x = ∑ i, (-(x ⬝ᵥ Mq *ᵥ φ i)) • ε i + ∑ j, (x ⬝ᵥ Mq *ᵥ ε j) • φ j := by
  first | exact @GlobalTheory.coords_in_rational_symplectic_basis | exact GlobalTheory.coords_in_rational_symplectic_basis | (intros; apply GlobalTheory.coords_in_rational_symplectic_basis <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DescentJointEigenvectorsComplexReadingStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descent_joint_eigenvectors_complex_reading : ∀ {K V W ι κ : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module ℂ W] (f : K →+* ℂ) (e : V →ₛₗ[f] W) (G : Submodule K V), (∀ v ∈ G, e v = 0 → v = 0) → ∀ (T : κ → Module.End K V) (T' : κ → Module.End ℂ W) (I : Set κ), (∀ k ∈ I, ∀ v, e (T k v) = T' k (e v)) → ∀ (Part : ι → Submodule ℂ W) (s : Set ι) (lam : ι → κ → K), (∀ σ ∈ s, ∀ k ∈ I, ∀ w ∈ Part σ, T' k w = f (lam σ k) • w) → (∀ v, e v ∈ ⨆ σ ∈ s, Part σ → v ∈ G) → ∀ v, e v ∈ ⨆ σ ∈ s, Part σ → v ∈ ⨆ σ ∈ s, G ⊓ ⨅ k ∈ I, Module.End.eigenspace (T k) (lam σ k) := by
  first | exact @GlobalTheory.descent_joint_eigen | exact GlobalTheory.descent_joint_eigen | (intros; apply GlobalTheory.descent_joint_eigen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DifferentiableAtInvApply
section
open Matrix
open scoped ComplexOrder

namespace GlobalTheory.Mem.GaussPhase

variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem differentiableAt_det (M : ℝ → Matrix σ σ ℂ) (t : ℝ)
    (hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t) :
    DifferentiableAt ℝ (fun s => (M s).det) t := by
  first
  | exact @_root_.GlobalTheory.DifferentiableDet.differentiableAt_det
  | exact _root_.GlobalTheory.DifferentiableDet.differentiableAt_det
  | (apply _root_.GlobalTheory.DifferentiableDet.differentiableAt_det <;> assumption)
  | (intros; apply _root_.GlobalTheory.DifferentiableDet.differentiableAt_det <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DifferentiableDet.differentiableAt_det <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DifferentiableDet.differentiableAt_det ..)

theorem differentiableAt_inv_apply (M : ℝ → Matrix σ σ ℂ) (t : ℝ)
    (hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t) (hne : (M t).det ≠ 0) (i j : σ) :
    DifferentiableAt ℝ (fun s => (M s)⁻¹ i j) t := by
  have hadj : DifferentiableAt ℝ (fun s => (M s).adjugate i j) t := by
    have := differentiableAt_det (fun s => (M s).updateRow j (Pi.single i 1)) t (by
      intro a b
      by_cases h : a = j
      · simp only [updateRow_apply, h, if_true]
        exact differentiableAt_const _
      · simp only [updateRow_apply, h, if_false]
        exact hM a b)
    simpa only [adjugate_apply] using this
  have := ((differentiableAt_det M t hM).fun_inv hne).mul hadj
  refine this.congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  simp [Matrix.inv_def, Ring.inverse_eq_inv']

omit [DecidableEq σ] in
theorem hasDerivAt_dot (x : σ → ℂ) {w : ℝ → σ → ℂ} {w' : σ → ℂ} {t : ℝ} (h : HasDerivAt w w' t) :
    HasDerivAt (fun s => x ⬝ᵥ w s) (x ⬝ᵥ w') t := by
  simp only [dotProduct]
  exact HasDerivAt.fun_sum fun k _ => (hasDerivAt_pi.mp h k).const_mul _

omit [DecidableEq σ] in
theorem hasDerivAt_mulVec (S : Matrix σ σ ℂ) {w : ℝ → σ → ℂ} {w' : σ → ℂ} {t : ℝ}
    (h : HasDerivAt w w' t) : HasDerivAt (fun s => S *ᵥ w s) (S *ᵥ w') t :=
  hasDerivAt_pi.mpr fun i => hasDerivAt_dot (S i) h

omit [DecidableEq σ] in
theorem dot_symm {S : Matrix σ σ ℂ} (hS : Sᵀ = S) (a b : σ → ℂ) :
    (S *ᵥ a) ⬝ᵥ b = a ⬝ᵥ (S *ᵥ b) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hS]

theorem hasDerivAt_phase (σ : Type) [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ)
    (x y : σ → ℂ) (t : ℝ) (hS : Sᵀ = S) (hT : Tᵀ = T)
    (hu : IsUnit (1 - ((t : ℂ) ^ 2) • (T * S)).det) :
    let w : ℝ → σ → ℂ := fun s => (1 - ((s : ℂ) ^ 2) • (T * S))⁻¹ *ᵥ (y + (s : ℂ) • T *ᵥ x)
    let u : ℝ → σ → ℂ := fun s => x + (s : ℂ) • S *ᵥ w s
    HasDerivAt (fun s : ℝ => (s : ℂ) / 2 * (x ⬝ᵥ w s + y ⬝ᵥ u s)) (u t ⬝ᵥ w t) t := by
  intro w u
  have hof : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
  set M : ℝ → Matrix σ σ ℂ := fun s => 1 - ((s : ℂ) ^ 2) • (T * S) with hMdef
  have hM : ∀ i j, DifferentiableAt ℝ (fun s => M s i j) t := by
    intro i j
    simp only [hMdef, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    exact (differentiableAt_const _).fun_sub ((hof.differentiableAt.fun_pow 2).mul_const _)
  have hne : (M t).det ≠ 0 := hu.ne_zero
  have hev : ∀ᶠ s in nhds t, (M s).det ≠ 0 :=
    (differentiableAt_det M t hM).continuousAt.eventually_ne hne
  have hwd : DifferentiableAt ℝ w t := by
    refine differentiableAt_pi.mpr fun i => ?_
    change DifferentiableAt ℝ (fun s => ∑ k, (M s)⁻¹ i k * (y k + (s : ℂ) * (T *ᵥ x) k)) t
    exact DifferentiableAt.fun_sum fun k _ =>
      (differentiableAt_inv_apply M t hM hne i k).fun_mul
        ((differentiableAt_const _).fun_add (hof.differentiableAt.mul_const _))
  obtain ⟨w', hw⟩ : ∃ w', HasDerivAt w w' t := ⟨_, hwd.hasDerivAt⟩
  have hU : HasDerivAt u ((t : ℂ) • S *ᵥ w' + S *ᵥ w t) t := by
    have := (hof.fun_smul (hasDerivAt_mulVec S hw)).const_add x
    simpa only [one_smul] using this
  set u' := (t : ℂ) • S *ᵥ w' + S *ᵥ w t with hu'
  have hkey : ∀ s, (M s).det ≠ 0 → w s = y + (s : ℂ) • T *ᵥ u s := by
    intro s hs
    have h1 : M s *ᵥ w s = y + (s : ℂ) • T *ᵥ x := by
      change M s *ᵥ ((M s)⁻¹ *ᵥ _) = _
      rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hs), one_mulVec]
    simp only [hMdef, sub_mulVec, one_mulVec, smul_mulVec] at h1
    simp only [u, mulVec_add, mulVec_smul, mulVec_mulVec, smul_add, smul_smul]
    rw [← add_assoc, ← h1, pow_two, sub_add_cancel]
  have hw2 : HasDerivAt w ((t : ℂ) • T *ᵥ u' + T *ᵥ u t) t := by
    have := (hof.fun_smul (hasDerivAt_mulVec T hU)).const_add y
    simp only [one_smul] at this
    refine this.congr_of_eventuallyEq ?_
    filter_upwards [hev] with s hs using hkey s hs
  have hw' : w' = (t : ℂ) • T *ᵥ u' + T *ᵥ u t := hw.unique hw2
  have hx : x = u t - (t : ℂ) • S *ᵥ w t := by simp [u]
  have hy : y = w t - (t : ℂ) • T *ᵥ u t := by rw [eq_sub_iff_add_eq]; exact (hkey t hne).symm
  have hmain := (hof.div_const 2).fun_mul ((hasDerivAt_dot x hw).fun_add (hasDerivAt_dot y hU))
  refine hmain.congr_deriv ?_
  have e1 : x ⬝ᵥ w t = u t ⬝ᵥ w t - t * (w t ⬝ᵥ S *ᵥ w t) := by
    conv_lhs => rw [hx]
    rw [sub_dotProduct, smul_dotProduct, dot_symm hS, smul_eq_mul]
  have e2 : y ⬝ᵥ u t = u t ⬝ᵥ w t - t * (u t ⬝ᵥ T *ᵥ u t) := by
    conv_lhs => rw [hy]
    rw [sub_dotProduct, smul_dotProduct, dot_symm hT, smul_eq_mul, dotProduct_comm]
  have e3 : x ⬝ᵥ w' = u t ⬝ᵥ w' - t * (w t ⬝ᵥ S *ᵥ w') := by
    conv_lhs => rw [hx]
    rw [sub_dotProduct, smul_dotProduct, dot_symm hS, smul_eq_mul]
  have e4 : y ⬝ᵥ u' = w t ⬝ᵥ u' - t * (u t ⬝ᵥ T *ᵥ u') := by
    conv_lhs => rw [hy]
    rw [sub_dotProduct, smul_dotProduct, dot_symm hT, smul_eq_mul]
  have e5 : w t ⬝ᵥ u' = t * (w t ⬝ᵥ S *ᵥ w') + w t ⬝ᵥ S *ᵥ w t := by
    rw [hu', dotProduct_add, dotProduct_smul, smul_eq_mul]
  have e6 : u t ⬝ᵥ w' = t * (u t ⬝ᵥ T *ᵥ u') + u t ⬝ᵥ T *ᵥ u t := by
    conv_lhs => rw [hw']
    rw [dotProduct_add, dotProduct_smul, smul_eq_mul]
  rw [e1, e2, e3, e4, e5, e6]
  ring

end GlobalTheory.Mem.GaussPhase
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalTwSubK
section
noncomputable section

namespace GlobalTheory.IntegralityCompare

open MvPolynomial

def twSubK {E K ι : Type} [Field E] [Field K] [Fintype ι] {n : ℕ} (t : ι → E →+* K) (M : GL (Fin n) E) (s : ι → ℤ)
    (P : MvPolynomial (ι × Fin n × Fin n) K) : MvPolynomial (ι × Fin n × Fin n) K :=
  C (∏ τ, (t τ (M : Matrix (Fin n) (Fin n) E).det) ^ (s τ)) *
    bind₁ (fun k : ι × Fin n × Fin n => ∑ j : Fin n,
      C (t k.1 ((M : Matrix (Fin n) (Fin n) E) k.2.1 j)) * X (k.1, j, k.2.2)) P

open MvPolynomial in
theorem _root_.GlobalTheory.IntegralityCompare.map_twSubK {E K ι : Type} [Field E] [Field K] [Fintype ι] {n : ℕ}
    (t : ι → E →+* K) (M : GL (Fin n) E) (s : ι → ℤ) (P : MvPolynomial (ι × Fin n × Fin n) K)
    (φ : K →+* ℂ) :
    map φ (_root_.GlobalTheory.IntegralityCompare.twSubK t M s P) =
      _root_.GlobalTheory.IntegralityCompare.twSub (fun τ => φ.comp (t τ)) M s (map φ P) := by
  rw [_root_.GlobalTheory.IntegralityCompare.twSubK, _root_.GlobalTheory.IntegralityCompare.twSub, map_mul, map_C, map_bind₁]
  simp [map_prod, map_zpow₀]

open MvPolynomial in
private lemma eval_bind_eq_eval_comp {K σ τ : Type} [CommRing K] (f : σ → MvPolynomial τ K)
    (x : τ → K) (P : MvPolynomial σ K) :
    eval x (bind₁ f P) = eval (fun i => eval x (f i)) P := by
  rw [← aeval_eq_eval, ← aeval_eq_eval, aeval_bind₁]

open MvPolynomial in
theorem _root_.GlobalTheory.IntegralityCompare.eval_twSubK {E K ι : Type} [Field E] [Field K] [Fintype ι] {n : ℕ}
    (t : ι → E →+* K) (M : GL (Fin n) E) (s : ι → ℤ) (P : MvPolynomial (ι × Fin n × Fin n) K)
    (x : ι → Matrix (Fin n) (Fin n) K) :
    eval (fun k : ι × Fin n × Fin n => x k.1 k.2.1 k.2.2) (_root_.GlobalTheory.IntegralityCompare.twSubK t M s P) =
      (∏ τ, (t τ (M : Matrix (Fin n) (Fin n) E).det) ^ (s τ)) *
        eval (fun k : ι × Fin n × Fin n =>
          (((M : Matrix (Fin n) (Fin n) E).map (t k.1)) * x k.1) k.2.1 k.2.2) P := by
  rw [_root_.GlobalTheory.IntegralityCompare.twSubK, map_mul, eval_C, eval_bind_eq_eval_comp]
  congr 3
  funext k
  simp [Matrix.mul_apply, eval_sum]

end GlobalTheory.IntegralityCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAlgClosedTranscendentalSpecialisingEverywhStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algClosed_transcendental_specialising_everywhere : ∀ (K : Type) [Field K] [IsAlgClosed K], ∃ (L : Type) (_ : Field L) (_ : IsAlgClosed L) (ι : K →+* L) (s : L), (∀ P : Polynomial K, P.eval₂ ι s = 0 → P = 0) ∧ ∀ a : K, ∃ (V : ValuationSubring L) (ιV : K →+* V) (r : V →+* K) (sV : V), (algebraMap V L).comp ιV = ι ∧ r.comp ιV = RingHom.id K ∧ RingHom.ker r = IsLocalRing.maximalIdeal V ∧ algebraMap V L sV = s ∧ r sV = a := by
  first | exact @GlobalTheory.genval | exact GlobalTheory.genval | (intros; apply GlobalTheory.genval <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsApproxFinitePlacesNumberFieldStatement
section
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approx_finite_places_numberField : ∀ {F : Type} [Field F] [NumberField F] {ι : Type} [Fintype ι] (w : ι → HeightOneSpectrum (𝓞 F)), Function.Injective w → ∀ (y : ∀ i, (w i).adicCompletion F) (c : F), c ≠ 0 → ∃ a : F, ∀ i, Valued.v (algebraMap F ((w i).adicCompletion F) a - y i) ≤ Valued.v (algebraMap F ((w i).adicCompletion F) c) := by
  first | exact @GlobalTheory.exists_approx_finite_places | exact GlobalTheory.exists_approx_finite_places | (intros; apply GlobalTheory.exists_approx_finite_places <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisInFiniteDomainTraceMemStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_basis_of_integral_with_trace_in_base : ∀ (T C F K : Type) [CommRing T] [IsDomain T] [IsIntegrallyClosed T] [CommRing C] [IsDomain C] [Field F] [Field K] [Algebra T C] [Algebra T F] [IsFractionRing T F] [Algebra C K] [IsFractionRing C K] [Algebra T K] [Algebra F K] [IsScalarTower T C K] [IsScalarTower T F K] [Module.Finite T C], ∃ (n : ℕ) (b : Module.Basis (Fin n) F K), (∀ i, ∃ c : C, algebraMap C K c = b i) ∧ ∀ i j, ∃ t : T, algebraMap T F t = Algebra.trace F K (b i * b j) := by
  first | exact @GlobalTheory.exists_basis_in_finite_domain_trace_mem | exact GlobalTheory.exists_basis_in_finite_domain_trace_mem | (intros; apply GlobalTheory.exists_basis_in_finite_domain_trace_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonNonzeroOfPolynomialOnRealLinesStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_nonzero_of_polynomial_on_real_lines : ∀ (V : Type) [AddCommGroup V] [Module ℝ V] (ι : Type) [Finite ι] (f : ι → V → ℂ), (∀ i a b, ∃ p : Polynomial ℂ, ∀ s : ℝ, f i (a + s • b) = p.eval (s : ℂ)) → (∀ i, ∃ v, f i v ≠ 0) → ∃ v, ∀ i, f i v ≠ 0 := by
  first | exact @GlobalTheory.exists_common_nonzero_of_polynomial_on_lines | exact GlobalTheory.exists_common_nonzero_of_polynomial_on_lines | (intros; apply GlobalTheory.exists_common_nonzero_of_polynomial_on_lines <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonUnramifiedExtensionStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_common_unramified_extension : ∀ {k K L : Type} [Field k] [Field K] [Field L] (i : k →+* K) (j : k →+* L), i.Finite → i.FormallyUnramified → ∃ (M : Type) (_ : Field M) (u : K →+* M) (v : L →+* M), u.comp i = v.comp j ∧ v.Finite ∧ v.FormallyUnramified := by
  first | exact @GlobalTheory.compositum_finite_formallyUnramified | exact GlobalTheory.compositum_finite_formallyUnramified | (intros; apply GlobalTheory.compositum_finite_formallyUnramified <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConstSubstitutionOfHolomorphicFamiliesStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_substitution_of_holomorphic_families' : ∀ (L D : Type) [Countable D] (g : ℕ) (act : D → L → L) (U : Set ℂ) (s s' : ℂ → L → Fin g → ℂ), IsOpen U → IsPreconnected U → U.Nonempty → (∀ a, DifferentiableOn ℂ (fun w => s w a) U) → (∀ a, DifferentiableOn ℂ (fun w => s' w a) U) → (∀ w ∈ U, ∃ δ, ∀ a, s' w a = s w (act δ a)) → ∃ δ, ∀ w ∈ U, ∀ a, s' w a = s w (act δ a) := by
  first | exact @GlobalTheory.exists_const_substitution_of_holomorphic_families | exact GlobalTheory.exists_const_substitution_of_holomorphic_families | (intros; apply GlobalTheory.exists_const_substitution_of_holomorphic_families <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCyclotomicSplittingExtensionStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cyclotomic_splitting_extension : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CharZero A] (f : Polynomial (FractionRing A)), f ≠ 0 → ∀ q : ℕ, q ≠ 0 → ∃ (A' : Type) (_ : CommRing A') (_ : IsDomain A') (_ : Algebra A A') (σ : FractionRing A →+* FractionRing A'), Module.Finite A A' ∧ Function.Injective (algebraMap A A') ∧ IsIntegrallyClosed A' ∧ (∃ ζ : A', IsPrimitiveRoot ζ q) ∧ (f.map σ).Splits ∧ σ.comp (algebraMap A (FractionRing A)) = (algebraMap A' (FractionRing A')).comp (algebraMap A A') := by
  first | exact @GlobalTheory.splitExt_intClosure | exact GlobalTheory.splitExt_intClosure | (intros; apply GlobalTheory.splitExt_intClosure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDotProductMulVecEqOfLinearIndependentStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dotProduct_mulVec_eq_of_linearIndependent' : ∀ (r k : ℕ) (Mq : Matrix (Fin r) (Fin r) ℚ) (ε : Fin k → Fin r → ℚ), Mq.det ≠ 0 → LinearIndependent ℚ ε → ∀ t : Fin k → ℚ, ∃ x : Fin r → ℚ, ∀ i, x ⬝ᵥ Mq *ᵥ ε i = t i := by
  first | exact @GlobalTheory.exists_dotProduct_mulVec_eq_of_linearIndependent | exact GlobalTheory.exists_dotProduct_mulVec_eq_of_linearIndependent | (intros; apply GlobalTheory.exists_dotProduct_mulVec_eq_of_linearIndependent <;> assumption)
end

