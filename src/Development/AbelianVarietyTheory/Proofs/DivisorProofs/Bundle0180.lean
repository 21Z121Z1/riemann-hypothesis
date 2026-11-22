import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstPreorder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0092
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0094

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointedEtaleNeighbourhoodLocalRingIsDirected
section
open IsLocalRing GlobalTheory.Henselisation

open scoped TensorProduct

namespace GlobalTheory.Henselisation

theorem etNbhd_isDirected (R : Type) [CommRing R] [IsLocalRing R] :
    IsDirected (EtNbhd R) (· ≤ ·) := by
  refine ⟨fun i j => ?_⟩
  let C := i.A ⊗[R] j.A
  haveI : Algebra.Etale R C := Algebra.Etale.comp R i.A C
  obtain ⟨n, f, hf⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := R) (S := C)).1 inferInstance
  let e := Ideal.quotientKerAlgEquivOfSurjective hf
  let P : C →ₐ[R] ResidueField R := Algebra.TensorProduct.lift i.pt j.pt (fun _ _ => Commute.all _ _)
  let k : EtNbhd R :=
    { n := n, I := RingHom.ker f, etale := Algebra.Etale.of_equiv e.symm, pt := P.comp e.toAlgHom }
  refine ⟨k, ⟨(e.symm.toAlgHom).comp Algebra.TensorProduct.includeLeft, ?_⟩,
    ⟨(e.symm.toAlgHom).comp Algebra.TensorProduct.includeRight, ?_⟩⟩
  · apply AlgHom.ext; intro a
    show P (e (e.symm _)) = i.pt a
    rw [AlgEquiv.apply_symm_apply]
    change P (a ⊗ₜ[R] (1 : j.A)) = i.pt a
    rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]
  · apply AlgHom.ext; intro a
    show P (e (e.symm _)) = j.pt a
    rw [AlgEquiv.apply_symm_apply]
    change P ((1 : i.A) ⊗ₜ[R] a) = j.pt a
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]

end GlobalTheory.Henselisation
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointsOfSchemeOverArtinianFibreProductStatement
section
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.points_of_scheme_over_artinian_fibre_product : ∀ (P R₁ R₂ R₀ : CommRingCat.{0}) (f₁ : P ⟶ R₁) (f₂ : P ⟶ R₂) (g₁ : R₁ ⟶ R₀) (g₂ : R₂ ⟶ R₀), IsPullback f₁ f₂ g₁ g₂ → IsLocalRing P → IsArtinianRing P → Function.Surjective g₁ → Function.Surjective g₂ → ∀ (Y Y₁ Y₂ Y₀ : Scheme.{0}) (p : Y ⟶ Spec P) (p₁ : Y₁ ⟶ Spec R₁) (p₂ : Y₂ ⟶ Spec R₂) (p₀ : Y₀ ⟶ Spec R₀) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂), IsPullback j₁ p₁ p (Spec.map f₁) → IsPullback j₂ p₂ p (Spec.map f₂) → IsPullback i₁ p₀ p₁ (Spec.map g₁) → i₁ ≫ j₁ = i₂ ≫ j₂ → (∀ y : Y, (∃ y₁, j₁ y₁ = y) ∨ ∃ y₂, j₂ y₂ = y) ∧ ∀ (y₁ : Y₁) (y₂ : Y₂), j₁ y₁ = j₂ y₂ → ∃ y₀ : Y₀, i₁ y₀ = y₁ ∧ i₂ y₀ = y₂ := by
  first | exact @GlobalTheory.PinchPoints.points_of_pinch | exact GlobalTheory.PinchPoints.points_of_pinch | (intros; apply GlobalTheory.PinchPoints.points_of_pinch <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyGrowthSpreadOfIntegralMonodromyStatement
section
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polyGrowth_strip_of_integral_monodromy : ∀ (g m : ℕ) (lam : ℂ → Fin m → Fin g → ℂ) (C : ℝ) (k : ℕ) (P Q : Fin m → Fin m → ℤ), (∀ s : ℂ, s.re < 0 → ∀ j, lam (s + 2 * Real.pi * Complex.I) j = ∑ i, P j i • lam s i) → (∀ s : ℂ, s.re < 0 → ∀ j, lam s j = ∑ i, Q j i • lam (s + 2 * Real.pi * Complex.I) i) → (∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ Real.pi → ‖lam s‖ ≤ C * (1 + ‖s‖) ^ k) → ∀ R : ℝ, ∃ C' : ℝ, ∀ s : ℂ, s.re < 0 → ‖Complex.exp s‖ ≤ 1 / 2 → |s.im| ≤ R → ‖lam s‖ ≤ C' * (1 + ‖s‖) ^ k := by
  first | exact @GlobalTheory.polyGrowth_spread_of_integral_monodromy | exact GlobalTheory.polyGrowth_spread_of_integral_monodromy | (intros; apply GlobalTheory.polyGrowth_spread_of_integral_monodromy <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefExistsConjTransposeMulMulEqOneStatement
section
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posDef_exists_conjTranspose_mul_mul_eq_one' : ∀ (d : ℕ) (H : Matrix (Fin d) (Fin d) ℂ), H.PosDef → ∃ y₀ : GL (Fin d) ℂ, (y₀.1).conjTranspose * H * y₀.1 = 1 := by
  first | exact @GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one | exact GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one | (intros; apply GlobalTheory.posDef_exists_conjTranspose_mul_mul_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosDefRealGramPairHermitianFormsStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posDef_real_gram_pair_hermitian_forms : ∀ (g n : ℕ) (e : Module.Basis (Fin n) ℝ (Fin g → ℂ)) (H₁ H₂ : Matrix (Fin g) (Fin g) ℂ), H₁.IsHermitian → H₂.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₁.mulVec (star z)).re) →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ H₂.mulVec (star z)).re) →
    ∀ (γ : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)),
    (∀ z w, z ⬝ᵥ H₂.mulVec (star w) = z ⬝ᵥ H₁.mulVec (star (γ w))) →
    (Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re).PosDef ∧
    ((Matrix.of fun k l => (e k ⬝ᵥ H₁.mulVec (star (e l))).re) *
      LinearMap.toMatrix e e (γ.restrictScalars ℝ)).PosDef := by
  first | exact @GlobalTheory.HermGram.gram_posDef_pair | exact GlobalTheory.HermGram.gram_posDef_pair | (intros; apply GlobalTheory.HermGram.gram_posDef_pair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosOfPosMulInnerOnJointEigenvectorsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inner_pos_of_pos_on_joint_eigenvectors : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ι : V →ₗ[ℂ] H), Function.Injective ι → ∀ (W : Submodule ℂ V), FiniteDimensional ℂ W → ∀ (I : Type) (T : I → Module.End ℂ V), (∀ i, ∀ w ∈ W, T i w ∈ W) → (∀ i x y, inner ℂ (ι (T i x)) (ι y) = inner ℂ (ι x) (ι (T i y))) → (∀ i j, T i * T j = T j * T i) → ∀ (u : V →ₗ[ℂ] H), (∀ (m : I → ℝ), ∀ y ∈ W, (∀ i, T i y = (m i : ℂ) • y) → ∃ c : ℝ, 0 < c ∧ ∀ x ∈ W, inner ℂ (ι x) (u y) = (c : ℂ) * inner ℂ (ι x) (ι y)) → ∀ x ∈ W, x ≠ 0 → (inner ℂ (ι x) (u x)).im = 0 ∧ 0 < (inner ℂ (ι x) (u x)).re := by
  first | exact @GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors | exact GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors | (intros; apply GlobalTheory.pos_of_pos_mul_inner_on_joint_eigenvectors <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PosSemidefQuadraticAdjointPairBoundStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.posSemidef_quadratic_adjoint_pair_bound : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (h h' : X →+ X), ∃ C : ℕ, ∀ q : X → ℤ, (∀ y, 0 ≤ q y) → q 0 = 0 → (∀ y, q (-y) = q y) → (∀ x y z, q (x + y + z) + q x + q y + q z = q (x + y) + q (x + z) + q (y + z)) → (∀ y z, q (h y + z) + q y + q (h' z) = q (y + h' z) + q (h y) + q z) → ∀ y, q (h y) ≤ C * q y := by
  first | exact @GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound | exact GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound | (intros; apply GlobalTheory.PosFormAdjoint.pos_form_adjoint_bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMapsTorsionIntoSmulTopStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_apply_mem_smul_univ_of_torsion : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (M : Type) [AddCommGroup M] [Module R M] (I J : Ideal R) (f : M →ₗ[R] M) (m : ℕ), I.IsMaximal → J ≠ ⊥ → (∀ x, (f ^ m) x ∈ I • (⊤ : Submodule R M)) → ∃ j : ℕ, ∀ y : M, (∀ a ∈ I, a • y ∈ J • (⊤ : Submodule R M)) → (f ^ j) y ∈ J • (⊤ : Submodule R M) := by
  first | exact @GlobalTheory.pow_maps_torsion_into_smul_top | exact GlobalTheory.pow_maps_torsion_into_smul_top | (intros; apply GlobalTheory.pow_maps_torsion_into_smul_top <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMulNormGauLe
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder FourierTransform

namespace GlobalTheory.RealWeil

theorem pow_mul_norm_gau_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] (m : ℕ) (v : V) :
    ‖v‖ ^ m * ‖gau v‖ ≤ m.factorial * Real.exp 1 := by
  rw [norm_gau]
  have hx0 : 0 ≤ ‖v‖ := norm_nonneg v
  have h1 : ‖v‖ ^ m ≤ m.factorial * Real.exp ‖v‖ := by
    have := Real.pow_div_factorial_le_exp _ hx0 m
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < m.factorial)] at this
    linarith [mul_comm (Real.exp ‖v‖) (m.factorial : ℝ)]
  have h2 : ‖v‖ + (-(π / 2) * ‖v‖ ^ 2) ≤ 1 := by
    nlinarith [Real.pi_gt_three, sq_nonneg ‖v‖, sq_nonneg (‖v‖ - 1 / 3)]
  calc ‖v‖ ^ m * Real.exp (-(π / 2) * ‖v‖ ^ 2)
      ≤ (m.factorial * Real.exp ‖v‖) * Real.exp (-(π / 2) * ‖v‖ ^ 2) :=
        mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = m.factorial * Real.exp (‖v‖ + (-(π / 2) * ‖v‖ ^ 2)) := by rw [Real.exp_add]; ring
    _ ≤ m.factorial * Real.exp 1 := by gcongr

theorem gau_add {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (v t : V) :
    gau (v + t) = gau v * gau t * cexp (-(π : ℂ) * (⟪v, t⟫ : ℝ)) := by
  unfold gau
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have h' : ((‖v + t‖ : ℝ) : ℂ) ^ 2 = ((‖v‖ ^ 2 + 2 * ⟪v, t⟫ + ‖t‖ ^ 2 : ℝ) : ℂ) := by
    rw [← norm_add_sq_real v t]; push_cast; ring
  rw [h']
  push_cast
  ring

theorem contDiff_gau {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] :
    ContDiff ℝ ∞ (gau : V → ℂ) := by
  have e : (gau : V → ℂ) = fun u => cexp (-(π / 2 : ℂ) * ((‖u‖ ^ 2 : ℝ) : ℂ)) := by
    funext u
    simp only [gau]
    push_cast
    rfl
  rw [e]
  have hn : ContDiff ℝ ∞ (fun u : V => ‖u‖ ^ 2) := contDiff_norm_sq ℝ
  exact Complex.contDiff_exp.comp (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp hn))

theorem exists_shift_form {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (J : V ≃ₗᵢ[ℝ] V) (v : V) :
    ∃ l : V →L[ℝ] ℂ, ‖l‖ ≤ 2 * π * ‖v‖ ∧
      ∀ t, l t = -(π : ℂ) * (⟪v, t⟫ : ℝ) - π * I * (omJ J v t : ℂ) := by
  let l : V →L[ℝ] ℂ := (-(π : ℂ)) • (Complex.ofRealCLM.comp (innerSL ℝ v)) -
      ((π : ℂ) * I) • (Complex.ofRealCLM.comp ((innerSL ℝ v).comp (J : V →L[ℝ] V)))
  have hl : ∀ t, l t = -(π : ℂ) * (⟪v, t⟫ : ℝ) - π * I * (⟪v, J t⟫ : ℝ) := fun t => by
    simp [l]
  refine ⟨l, ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun t => ?_, fun t => by
    rw [hl t]; rfl⟩
  rw [hl t]
  calc ‖-(π : ℂ) * (⟪v, t⟫ : ℝ) - π * I * (⟪v, J t⟫ : ℝ)‖
      ≤ ‖-(π : ℂ) * (⟪v, t⟫ : ℝ)‖ + ‖(π : ℂ) * I * (⟪v, J t⟫ : ℝ)‖ := norm_sub_le _ _
    _ = π * |⟪v, t⟫| + π * |⟪v, J t⟫| := by
        simp [Complex.norm_real, abs_of_pos Real.pi_pos]
    _ ≤ π * (‖v‖ * ‖t‖) + π * (‖v‖ * ‖t‖) := by
        gcongr
        · exact abs_real_inner_le_norm _ _
        · exact (abs_real_inner_le_norm v (J t)).trans (by rw [J.norm_map])
    _ = 2 * π * ‖v‖ * ‖t‖ := by ring

theorem decay_gau_smul {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {B : Type} [NormedAddCommGroup B] [NormedSpace ℂ B] {J : V ≃ₗᵢ[ℝ] V} {ρ : V → B →L[ℂ] B}
    (h : IsHeis (omJ J) ρ) {f : B} (hf : Sm ρ f) (k n : ℕ) :
    ∃ C, ∀ v, ‖v‖ ^ k * ‖iteratedFDeriv ℝ n (fun u => gau u • ρ u f) v‖ ≤ C := by
  set F : V → B := fun u => gau u • ρ u f with hF
  have hFs : ContDiff ℝ ∞ F := contDiff_gau.smul hf
  have hE : ContDiff ℝ ∞ (fun z : ℂ => cexp z) := Complex.contDiff_exp
  have hN : ((n : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π) ^ i) *
      ‖iteratedFDeriv ℝ (n - i) F 0‖ * ((k + i).factorial * Real.exp 1), fun v => ?_⟩
  obtain ⟨l, hl, hlt⟩ := exists_shift_form J v
  have hshift : (fun t => F (t + v)) = fun t => (gau v • ρ v) (cexp (l t) • F t) := by
    funext t
    simp only [hF, _root_.smul_apply, map_smul, smul_smul]
    rw [add_comm t v, h.2.1 v t f, smul_smul]
    congr 1
    have key : cexp (-(π : ℂ) * (⟪v, t⟫ : ℝ)) = cexp (l t) * cexp (π * I * (omJ J v t : ℂ)) := by
      rw [hlt t, ← Complex.exp_add]; congr 1; ring
    rw [gau_add, key]
    ring
  have hG : ContDiff ℝ ∞ (fun t => cexp (l t)) := hE.comp l.contDiff
  have hρ1 : ‖ρ v‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => by rw [h.2.2.1, one_mul]
  have hL : ‖(gau v • ρ v).restrictScalars ℝ‖ ≤ ‖gau v‖ := by
    rw [ContinuousLinearMap.norm_restrictScalars]
    calc ‖gau v • ρ v‖ ≤ ‖gau v‖ * ‖ρ v‖ := norm_smul_le _ _
      _ ≤ ‖gau v‖ * 1 := by gcongr
      _ = ‖gau v‖ := mul_one _
  have hexp : ∀ i : ℕ, ‖iteratedFDeriv ℝ i (fun t => cexp (l t)) 0‖ ≤
      ‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π * ‖v‖) ^ i := by
    intro i
    have e1 : (fun t => cexp (l t)) = (fun z : ℂ => cexp z) ∘ (l : V → ℂ) := rfl
    rw [e1, l.iteratedFDeriv_comp_right hE 0 (by exact_mod_cast le_top), map_zero]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    gcongr
  have hD : ‖iteratedFDeriv ℝ n F v‖ ≤ ‖gau v‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
      (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π * ‖v‖) ^ i) *
      ‖iteratedFDeriv ℝ (n - i) F 0‖ := by
    have e0 : iteratedFDeriv ℝ n F v = iteratedFDeriv ℝ n (fun t => F (t + v)) 0 := by
      rw [iteratedFDeriv_comp_add_right, zero_add]
    have e2 : (fun t => (gau v • ρ v) (cexp (l t) • F t)) =
        ((gau v • ρ v).restrictScalars ℝ) ∘ (fun t => cexp (l t) • F t) := rfl
    rw [e0, hshift, e2]
    refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ (hG.smul hFs).contDiffAt hN).trans ?_
    refine mul_le_mul hL ?_ (norm_nonneg _) (norm_nonneg _)
    refine (norm_iteratedFDeriv_smul_le hG hFs 0 hN).trans (Finset.sum_le_sum fun i _ => ?_)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hexp i) (by positivity))
      (norm_nonneg _)
  calc ‖v‖ ^ k * ‖iteratedFDeriv ℝ n F v‖
      ≤ ‖v‖ ^ k * (‖gau v‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π * ‖v‖) ^ i) *
        ‖iteratedFDeriv ℝ (n - i) F 0‖) := mul_le_mul_of_nonneg_left hD (by positivity)
    _ = ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        (‖iteratedFDeriv ℝ i (fun z : ℂ => cexp z) 0‖ * (2 * π) ^ i) *
        ‖iteratedFDeriv ℝ (n - i) F 0‖ * (‖v‖ ^ (k + i) * ‖gau v‖) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [mul_pow, pow_add]
        ring
    _ ≤ _ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (pow_mul_norm_gau_le _ _) (by positivity)

theorem Sm.good : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B]
    (J : V ≃ₗᵢ[ℝ] V) (ρ : V → B →L[ℂ] B), (∀ x, J (J x) = -x) → ∀ h : IsHeis (omJ J) ρ, ∀ f : B,
    Sm ρ f → Good h f := by
  intro V _ _ _ _ _ B _ _ _ J ρ hJ h f hf
  let ψ : SchwartzMap V B := ⟨fun u => gau u • ρ u f, contDiff_gau.smul hf, fun k n => decay_gau_smul h hf k n⟩
  have hψ : ((𝓕 ψ : SchwartzMap V B) : V → B) = 𝓕 (fun u => gau u • ρ u f) := SchwartzMap.fourier_coe ψ
  intro n
  have hint := (𝓕 ψ).integrable_pow_mul volume n
  refine (J.measurePreserving.integrable_comp_of_integrable hint).congr (Filter.Eventually.of_forall fun w => ?_)
  simp only [Function.comp_apply, LinearIsometryEquiv.norm_map, proj_translate hJ h f w, h.2.2.1, hψ]

end GlobalTheory.RealWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Pr13Snd
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et

noncomputable section

namespace GlobalTheory.Et.CovChar.Trip

variable {X Y : Scheme.{0}} (f : Y ⟶ X)

abbrev Tr : Scheme.{0} := pullback (pullback.snd f f) (pullback.fst f f)

def pr13 : Tr f ⟶ pullback f f :=
  pullback.lift (pullback.fst _ _ ≫ pullback.fst f f) (pullback.snd _ _ ≫ pullback.snd f f) (by
    simp only [Category.assoc]
    rw [pullback.condition (f := f) (g := f), pullback.condition_assoc, pullback.condition (f := f) (g := f)])

@[reassoc (attr := simp)] theorem pr13_fst : pr13 f ≫ pullback.fst f f = pullback.fst _ _ ≫ pullback.fst f f :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)] theorem pr13_snd : pr13 f ≫ pullback.snd f f = pullback.snd _ _ ≫ pullback.snd f f :=
  pullback.lift_snd _ _ _

variable (R : Type) [CommRing R]

def d1 : (freeOn R).obj (pullback f f) ⟶ (freeOn R).obj Y :=
  (freeOn R).map (pullback.snd f f) - (freeOn R).map (pullback.fst f f)

def d2 : (freeOn R).obj (Tr f) ⟶ (freeOn R).obj (pullback f f) :=
  (freeOn R).map (pullback.snd _ _) - (freeOn R).map (pr13 f) + (freeOn R).map (pullback.fst _ _)

theorem d2_comp : d2 f R ≫ d1 f R = 0 := by
  simp only [d1, d2, Preadditive.sub_comp, Preadditive.add_comp, Preadditive.comp_sub, ← Functor.map_comp,
    pr13_fst, pr13_snd, pullback.condition]
  abel

end GlobalTheory.Et.CovChar.Trip
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreEig
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity

noncomputable section
namespace GlobalTheory.HermitianPreEigenvalues
variable {O : Type} [CommRing O] {S : Type} [Fintype S] [DecidableEq S]

def mulR (a : S → O) (N : ℕ) (r : RS a) : (Fin N → RS a) →ₗ[O] (Fin N → RS a) :=
  (LinearMap.lsmul (RS a) (Fin N → RS a) r).restrictScalars O

def preEig (a : S → O) {N : ℕ} (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) :
    Submodule O (Fin N → RS a) :=
  (Fil.restrictScalars O).comap (mulR a N (lin a τ))

def filKer (a : S → O) {N : ℕ} (Fil : Submodule (RS a) (Fin N → RS a)) (τ : S) :
    Submodule O (Fin N → RS a) :=
  Fil.restrictScalars O ⊓ LinearMap.ker (mulR a N (cofac a τ))

end GlobalTheory.HermitianPreEigenvalues
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleSpaceFibreHypersurfaceSpectrumIffStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preirreducibleSpace_fibreHypersurface_spectrum_iff : ∀ (A : Type) [CommRing A] (σ : Type) (f g : MvPolynomial σ A) (k : Type) [Field k] [Algebra A k], PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away (Ideal.Quotient.mk (Ideal.span {f}) g))) ↔ IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map (algebraMap A k) g}) := by
  first | exact @GlobalTheory.FibreHyp.spectrum_fibre_preirreducible_iff | exact GlobalTheory.FibreHyp.spectrum_fibre_preirreducible_iff | (intros; apply GlobalTheory.FibreHyp.spectrum_fibre_preirreducible_iff <;> assumption)
end

