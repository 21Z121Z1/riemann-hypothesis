import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0006
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousBicharacterWeilSetup
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0007
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayLSeriesEulerProduct
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0010
import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsOrthogonalBasisDotProductApplyEq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0008
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CayleyTransformUnitarySkewInvolutive
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.CayleyInv

variable {R : Type} [CommRing R] {n : ℕ}

theorem map_mul_map_inv (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) (h : IsUnit M.det) :
    M.map σ * (M⁻¹).map σ = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ h, Matrix.map_one σ (map_zero σ) (map_one σ)]

theorem map_one_add (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) :
    (1 + M).map σ = 1 + M.map σ := by
  rw [Matrix.map_add σ (map_add σ), Matrix.map_one σ (map_zero σ) (map_one σ)]

theorem map_one_sub (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R) :
    (1 - M).map σ = 1 - M.map σ := by
  rw [Matrix.map_sub σ (map_sub σ), Matrix.map_one σ (map_zero σ) (map_one σ)]

theorem one_add_cayley (g : Matrix (Fin n) (Fin n) R) (h : IsUnit (1 + g).det) :
    1 + (1 - g) * (1 + g)⁻¹ = (2 : R) • (1 + g)⁻¹ := by
  have h1 : (1 + g) * (1 + g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have h2 : (1 + g) + (1 - g) = (2 : R) • (1 : Matrix (Fin n) (Fin n) R) := by
    rw [two_smul]; abel
  calc 1 + (1 - g) * (1 + g)⁻¹ = (1 + g) * (1 + g)⁻¹ + (1 - g) * (1 + g)⁻¹ := by rw [h1]
    _ = ((1 + g) + (1 - g)) * (1 + g)⁻¹ := (Matrix.add_mul _ _ _).symm
    _ = (2 : R) • (1 + g)⁻¹ := by rw [h2, Matrix.smul_mul, Matrix.one_mul]

theorem one_sub_cayley (g : Matrix (Fin n) (Fin n) R) (h : IsUnit (1 + g).det) :
    1 - (1 - g) * (1 + g)⁻¹ = (2 : R) • (g * (1 + g)⁻¹) := by
  have h1 : (1 + g) * (1 + g)⁻¹ = 1 := Matrix.mul_nonsing_inv _ h
  have h2 : (1 + g) - (1 - g) = (2 : R) • g := by
    rw [two_smul]; abel
  calc 1 - (1 - g) * (1 + g)⁻¹ = (1 + g) * (1 + g)⁻¹ - (1 - g) * (1 + g)⁻¹ := by rw [h1]
    _ = ((1 + g) - (1 - g)) * (1 + g)⁻¹ := (Matrix.sub_mul _ _ _).symm
    _ = (2 : R) • (g * (1 + g)⁻¹) := by rw [h2, Matrix.smul_mul]

theorem one_add_cayley_mul (g : Matrix (Fin n) (Fin n) R) (h : IsUnit (1 + g).det) (c : R)
    (hc : 2 * c = 1) : (1 + (1 - g) * (1 + g)⁻¹) * (c • (1 + g)) = 1 := by
  rw [one_add_cayley g h, smul_mul_smul_comm, hc, one_smul, Matrix.nonsing_inv_mul _ h]

private theorem eq_zero_of_mul_mul_eq_zero_of_isUnit_det (A B X : Matrix (Fin n) (Fin n) R)
    (hA : IsUnit A.det) (hB : IsUnit B.det) (h : A * X * B = 0) : X = 0 := by
  calc X = (A⁻¹ * A) * X * (B * B⁻¹) := by
        rw [Matrix.nonsing_inv_mul _ hA, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul,
          Matrix.mul_one]
    _ = A⁻¹ * (A * X * B) * B⁻¹ := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h, Matrix.mul_zero, Matrix.zero_mul]

private theorem isUnit_det_map_of_isUnit_det (σ : R →+* R) (M : Matrix (Fin n) (Fin n) R)
    (h : IsUnit M.det) : IsUnit (M.map σ).det := by
  simpa [RingHom.map_det, RingHom.mapMatrix_apply] using h.map σ

theorem cayley_transform : ∀ (R : Type) [CommRing R] (σ : R →+* R) (n : ℕ) (G : Matrix (Fin n) (Fin n) R), (∀ x, σ (σ x) = x) → (G.map σ)ᵀ = G → IsUnit G.det → IsUnit (2 : R) → (∀ g : Matrix (Fin n) (Fin n) R, gᵀ * G * g.map σ = G → IsUnit (1 + g).det → ((1 - g) * (1 + g)⁻¹)ᵀ * G + G * ((1 - g) * (1 + g)⁻¹).map σ = 0 ∧ IsUnit (1 + (1 - g) * (1 + g)⁻¹ : Matrix (Fin n) (Fin n) R).det) ∧ (∀ g : Matrix (Fin n) (Fin n) R, IsUnit (1 + g).det → (1 - (1 - g) * (1 + g)⁻¹) * (1 + (1 - g) * (1 + g)⁻¹)⁻¹ = g) ∧ (∀ S : Matrix (Fin n) (Fin n) R, Sᵀ * G + G * S.map σ = 0 → IsUnit (1 + S).det → ((1 - S) * (1 + S)⁻¹)ᵀ * G * ((1 - S) * (1 + S)⁻¹).map σ = G) ∧ ∀ A : Matrix (Fin n) (Fin n) R, (A - (G * A.map σ * G⁻¹)ᵀ)ᵀ * G + G * (A - (G * A.map σ * G⁻¹)ᵀ).map σ = 0 := by
  intro R _ σ n G hσ hG hGu h2
  obtain ⟨c, hc⟩ := h2.exists_right_inv
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g hg hP
    have hSP : (1 - g) * (1 + g)⁻¹ * (1 + g) = 1 - g := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
    refine ⟨?_, ?_⟩
    · apply eq_zero_of_mul_mul_eq_zero_of_isUnit_det ((1 + g)ᵀ) ((1 + g).map σ) _
        (by rwa [Matrix.det_transpose]) (isUnit_det_map_of_isUnit_det σ _ hP)
      have e1 : (1 + g)ᵀ * ((1 - g) * (1 + g)⁻¹)ᵀ = (1 - g)ᵀ := by
        rw [← Matrix.transpose_mul, hSP]
      have e2 : ((1 - g) * (1 + g)⁻¹).map σ * (1 + g).map σ = (1 - g).map σ := by
        rw [← Matrix.map_mul, hSP]
      have e3 : (1 - gᵀ) * G * (1 + g.map σ) + (1 + gᵀ) * G * (1 - g.map σ)
          = (G - gᵀ * G * g.map σ) + (G - gᵀ * G * g.map σ) := by noncomm_ring
      calc (1 + g)ᵀ * (((1 - g) * (1 + g)⁻¹)ᵀ * G + G * ((1 - g) * (1 + g)⁻¹).map σ)
            * (1 + g).map σ
          = ((1 + g)ᵀ * ((1 - g) * (1 + g)⁻¹)ᵀ) * G * (1 + g).map σ
            + (1 + g)ᵀ * G * (((1 - g) * (1 + g)⁻¹).map σ * (1 + g).map σ) := by
            simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _ = (1 - g)ᵀ * G * (1 + g).map σ + (1 + g)ᵀ * G * (1 - g).map σ := by rw [e1, e2]
        _ = 0 := by
            rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one,
              map_one_add, map_one_sub, e3, hg, sub_self, add_zero]
    · rw [one_add_cayley g hP, Matrix.det_smul]
      exact (h2.pow _).mul (Matrix.isUnit_nonsing_inv_det _ hP)
  · intro g hP
    have hinv : (1 + (1 - g) * (1 + g)⁻¹)⁻¹ = c • (1 + g) :=
      Matrix.inv_eq_right_inv (one_add_cayley_mul g hP c hc)
    rw [hinv, one_sub_cayley g hP, smul_mul_smul_comm, hc, one_smul, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
  · intro S hS hP
    have hgP : (1 - S) * (1 + S)⁻¹ * (1 + S) = 1 - S := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hP, Matrix.mul_one]
    rw [← sub_eq_zero]
    apply eq_zero_of_mul_mul_eq_zero_of_isUnit_det ((1 + S)ᵀ) ((1 + S).map σ) _
      (by rwa [Matrix.det_transpose]) (isUnit_det_map_of_isUnit_det σ _ hP)
    have e1 : (1 + S)ᵀ * ((1 - S) * (1 + S)⁻¹)ᵀ = (1 - S)ᵀ := by
      rw [← Matrix.transpose_mul, hgP]
    have e2 : ((1 - S) * (1 + S)⁻¹).map σ * (1 + S).map σ = (1 - S).map σ := by
      rw [← Matrix.map_mul, hgP]
    have e3 : (1 - Sᵀ) * G * (1 - S.map σ) - (1 + Sᵀ) * G * (1 + S.map σ)
        = -((Sᵀ * G + G * S.map σ) + (Sᵀ * G + G * S.map σ)) := by noncomm_ring
    calc (1 + S)ᵀ * (((1 - S) * (1 + S)⁻¹)ᵀ * G * ((1 - S) * (1 + S)⁻¹).map σ - G)
          * (1 + S).map σ
        = ((1 + S)ᵀ * ((1 - S) * (1 + S)⁻¹)ᵀ) * G
            * (((1 - S) * (1 + S)⁻¹).map σ * (1 + S).map σ)
          - (1 + S)ᵀ * G * (1 + S).map σ := by
          simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc]
      _ = (1 - S)ᵀ * G * (1 - S).map σ - (1 + S)ᵀ * G * (1 + S).map σ := by rw [e1, e2]
      _ = 0 := by
          rw [Matrix.transpose_sub, Matrix.transpose_add, Matrix.transpose_one,
            map_one_add, map_one_sub, e3, hS, add_zero, neg_zero]
  · intro A
    have hGinvG : G⁻¹ * G = 1 := Matrix.nonsing_inv_mul _ hGu
    have hKG : ((G⁻¹).map σ)ᵀ * G = 1 := by
      calc ((G⁻¹).map σ)ᵀ * G = ((G⁻¹).map σ)ᵀ * (G.map σ)ᵀ := by rw [hG]
        _ = (G.map σ * (G⁻¹).map σ)ᵀ := (Matrix.transpose_mul _ _).symm
        _ = 1 := by rw [map_mul_map_inv σ G hGu, Matrix.transpose_one]
    have hGK : G * ((G⁻¹).map σ)ᵀ = 1 := by
      rw [← Matrix.inv_eq_left_inv hKG]
      exact Matrix.mul_nonsing_inv _ hGu
    have hAA : (A.map σ).map σ = A := by
      ext i j
      simp [hσ]
    have hT : (A - (G * A.map σ * G⁻¹)ᵀ)ᵀ = Aᵀ - G * A.map σ * G⁻¹ := by
      rw [Matrix.transpose_sub, Matrix.transpose_transpose]
    have hTs : (A - (G * A.map σ * G⁻¹)ᵀ).map σ
        = A.map σ - ((G⁻¹).map σ)ᵀ * (Aᵀ * G) := by
      rw [Matrix.map_sub σ (map_sub σ), Matrix.transpose_map, Matrix.map_mul, Matrix.map_mul,
        hAA, Matrix.transpose_mul, Matrix.transpose_mul, hG]
    rw [hT, hTs]
    calc (Aᵀ - G * A.map σ * G⁻¹) * G + G * (A.map σ - ((G⁻¹).map σ)ᵀ * (Aᵀ * G))
        = Aᵀ * G - G * A.map σ * (G⁻¹ * G)
          + (G * A.map σ - (G * ((G⁻¹).map σ)ᵀ) * (Aᵀ * G)) := by
          simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
      _ = 0 := by
          rw [hGinvG, hGK, Matrix.mul_one, Matrix.one_mul]
          abel

end GlobalTheory.CayleyInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CompletelyReducibleToMatrixIffIsSemisimpleRepresStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.completelyReducible_toMatrix_iff_isSemisimpleRepresentation : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Type) [Group G] (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (b : Module.Basis ι ℂ V), SS (Set.range fun g => LinearMap.toMatrix b b (ρ g)) ↔ ρ.IsSemisimpleRepresentation := by
  first | exact @GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation | exact GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation | (intros; apply GlobalTheory.ClassFin.ss_range_toMatrix_iff_isSemisimpleRepresentation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousBicharacterWeilSetupStatement
section
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_bicharacter_weil_setup : ∀ (G V : Type) [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (p : G →+ V) (ι : V →+ G) (β : G → G → ℂ) (om : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (J : V →ₗ[ℝ] V) (Γ U₀ U : AddSubgroup G) (χ : G → ℂ), Continuous p → Continuous ι → (∀ v, p (ι v) = v) → (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y z, β x (y + z) = β x y * β x z) → (∀ x, β x x = 1) → (∀ x y, ‖β x y‖ = 1) → Continuous (fun q : G × G => β q.1 q.2) → (∀ x v, β x (ι v) = Complex.exp (-(Real.pi * Complex.I) * (om (p x) v : ℝ))) → (∀ v, om v v = 0) → (∀ v, J (J v) = -v) → (∀ x y, om x (J y) = om y (J x)) → (∀ v, v ≠ 0 → 0 < om v (J v)) → (∀ g ∈ Γ, ∀ g' ∈ Γ, β g g' = 1) → (∀ g ∈ Γ, p g = 0 → g = 0) → (∀ v, ι v ∈ U₀) → (∀ R : ℝ, {g : G | g ∈ Γ ∧ g ∈ U₀ ∧ ‖p g‖ ≤ R}.Finite) → (∀ x, x ∉ U₀ → χ x = 0) → (∀ x, ‖χ x‖ ≤ 1) → χ 0 = 1 → (∀ x v, χ (x + ι v) = χ x) → IsOpen (U : Set G) → (∀ u ∈ U, ∀ x, β x (u - ι (p u)) * χ (x + (u - ι (p u))) = χ x) → ∃ f : G → ℂ, f ≠ 0 ∧ Continuous f ∧ (∀ g ∈ Γ, ∀ w, β g w * f (g + w) = f w) ∧ (∀ u, p u = 0 → (∀ x, β x u * χ (x + u) = χ x) → ∀ w, β w u * f (w + u) = f w) ∧ (∀ w, ContDiff ℝ ∞ fun v : V => f (w + ι v)) ∧ ∀ w z, deriv (fun t : ℝ => β w (ι (t • z)) * f (w + ι (t • z))) 0 + Complex.I * deriv (fun t : ℝ => β w (ι (t • J z)) * f (w + ι (t • J z))) 0 = 0 := by
  first | exact @GlobalTheory.HeisenbergGaussianSeries.exists_theta | exact GlobalTheory.HeisenbergGaussianSeries.exists_theta | (intros; apply GlobalTheory.HeisenbergGaussianSeries.exists_theta <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CoordsLeftMulMatrixConstBaseChangeStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_leftMulMatrix_const_baseChange : ∀ (F β : Type) [Field F] [Algebra ℚ F] [Fintype β] [DecidableEq β] (ω : Module.Basis β ℚ F) (R A : Type) [CommRing R] [CommRing A] [Algebra ℚ R] [Algebra R A] [Algebra F A] (b : Module.Basis β R A), (∀ i, b i = algebraMap F A (ω i)) → ∀ x : F, (∀ k, b.repr (algebraMap F A x) k = algebraMap ℚ R (ω.repr x k)) ∧ Algebra.leftMulMatrix b (algebraMap F A x) = (Algebra.leftMulMatrix ω x).map (algebraMap ℚ R) := by
  first | exact @GlobalTheory.ClassFin.coords_const_baseChange | exact GlobalTheory.ClassFin.coords_const_baseChange | (intros; apply GlobalTheory.ClassFin.coords_const_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.CountableIdealSummableAbsNormRpow
section
open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical
open scoped ContDiff nonZeroDivisors

namespace GlobalTheory

open NumberField IsDedekindDomain NumberField.mixedEmbedding MeasureTheory Complex Classical in
open scoped ContDiff nonZeroDivisors in

theorem _root_.GlobalTheory.countable_ideal_and_summable_absNorm_rpow :
    ∀ (K : Type) [Field K] [NumberField K], Countable (Ideal (𝓞 K)) ∧ ∀ σ : ℝ, 1 < σ → (Summable fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ)) ∧ Summable fun P : HeightOneSpectrum (𝓞 K) => (Ideal.absNorm P.asIdeal : ℝ) ^ (-σ) := by
  intro K _ _
  refine ⟨?_, fun σ hσ => ?_⟩
  · have hU : (Set.univ : Set (Ideal (𝓞 K))) = ⋃ n : ℕ, {I | Ideal.absNorm I = n} := by
      ext I; simp
    have hc : (Set.univ : Set (Ideal (𝓞 K))).Countable := by
      rw [hU]
      exact Set.countable_iUnion fun n => (Ideal.finite_setOfPred_absNorm_eq n).countable
    exact Set.countable_univ_iff.mp hc
  · have hsum : Summable fun I : Ideal (𝓞 K) => (Ideal.absNorm I : ℝ) ^ (-σ) := by
      have h := _root_.GlobalTheory.Mem.summable_norm_absNorm_cpow K (s := (σ : ℂ)) (by simpa using hσ)
      refine h.congr fun I => ?_
      rw [Complex.norm_natCast_cpow_of_re_ne_zero _ (by simp; linarith)]
      simp
    refine ⟨hsum, ?_⟩
    have hinj : Function.Injective fun P : HeightOneSpectrum (𝓞 K) => P.asIdeal :=
      fun P Q h => HeightOneSpectrum.ext h
    exact hsum.comp_injective hinj

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.DetLeadingMinorGramIwasawaStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_leading_minor_gram_iwasawa : ∀ (N : ℕ) (k : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) (n : Matrix (Fin N) (Fin N) ℝ), kᵀ * k = 1 → (∀ i, n i i = 1) → (∀ i j, j < i → n i j = 0) → ∀ (j : ℕ) (h : j ≤ N), (((k * diagonal a * n)ᵀ * (k * diagonal a * n)).submatrix (Fin.castLE h) (Fin.castLE h)).det = ∏ i : Fin j, a (Fin.castLE h i) ^ 2 := by
  first | exact @GlobalTheory.ClassFin.det_leading_gram_iwasawa | exact GlobalTheory.ClassFin.det_leading_gram_iwasawa | (intros; apply GlobalTheory.ClassFin.det_leading_gram_iwasawa <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EntriesBoundedOfConjSpanningBoundedStatement
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.entries_bounded_of_conj_spanning_bounded' : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (σ : Type) [Fintype σ] (g : σ → Matrix ι ι ℂ), Submodule.span ℂ (Set.range g) = ⊤ → ∀ C : ℝ, ∃ C' : ℝ, ∀ P : Matrix ι ι ℂ, P.det = 1 → (∀ s i j, ‖(P * g s * P⁻¹) i j‖ ≤ C) → ∀ i j, ‖P i j‖ ≤ C' := by
  first | exact @GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded | exact GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded | (intros; apply GlobalTheory.ClassFin.entries_bounded_of_conj_spanning_bounded <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.EvenOrderNormsOneAddFourMulOfNoRootStatement
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.evenOrderNorms_one_add_four_mul_of_no_root : ∀ (K : Type) [Field K] (w : Valuation K ℤᵐ⁰) (ρ : K), (2 : K) ≠ 0 → w ρ ≤ 1 → (∀ x : K, w x ≤ 1 → w (x ^ 2 + x - ρ) = 1) → EvenNorms w (1 + 4 * ρ) := by
  first | exact @GlobalTheory.QNorm.evenNorms_one_add_four_mul | exact GlobalTheory.QNorm.evenNorms_one_add_four_mul | (intros; apply GlobalTheory.QNorm.evenNorms_one_add_four_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAdmissiblePlacesContainingPrimeSupersetMon
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem exists_admissiblePlaces_superset_and_mono : ∀ (p : ℕ) (F : Type) [Field F] [NumberField F], 0 < p →
    (∀ S₀ : Finset (HeightOneSpectrum (𝓞 F)), ∃ S, S₀ ⊆ S ∧ AdmP p F S) ∧
      ∀ S T : Finset (HeightOneSpectrum (𝓞 F)), S ⊆ T → AdmP p F S → AdmP p F T := by
  intro p F _ _ hp
  refine ⟨fun S₀ => ?_, fun S T hST h => ⟨h.1.mono hST, fun v hv => h.2 v fun a => hv (hST a)⟩⟩
  have hp0 : (p : F) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  obtain ⟨S₁, h01, h1⟩ := exists_superset_mem_sUnits F {Units.mk0 (p : F) hp0} S₀
  obtain ⟨S, h1S, hS⟩ := exists_admissible_superset_finite_places F S₁
  refine ⟨S, h01.trans h1S, hS, ?_⟩
  exact (mem_sUnits F S _).1 (h1 S h1S _ (Finset.mem_singleton_self _))

end GlobalTheory.CNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsAnisotropicOrthogonalBasisHermitian
section
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep

theorem exists_anisotropic_orthogonal_basis :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
      (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), IsHermForm c G →
      ∃ x : Fin n → Fin n → E, (∀ i, hermE c G (x i) (x i) ≠ 0) ∧
        (∀ i j, i ≠ j → hermE c G (x i) (x j) = 0) ∧ Submodule.span E (Set.range x) = ⊤ := by
  intro F E _ _ _ _ _ c n G ⟨hc, _, hG, hdet⟩
  let σ : E →+* E := (c : E →+* E)
  have he : ∀ x y : Fin n → E, hermE c G x y = x ⬝ᵥ G *ᵥ (σ ∘ y) := fun x y =>
    (GlobalTheory.HermDiag.dotProduct_mulVec_comp_eq_sum σ G x y).symm
  obtain ⟨v, hv⟩ := GlobalTheory.HermDiag.exists_orthogonal_basis_dotProduct (c := σ) two_ne_zero hc hG
  have hd := GlobalTheory.HermDiag.congr_diagonal_of_orthogonal σ v hv
  refine ⟨v, fun i => ?_, fun i j hij => ?_, v.span_eq⟩
  · rw [he]
    exact GlobalTheory.HermDiag.ne_zero_of_congr_diagonal (GlobalTheory.HermDiag.det_of_basis_ne_zero v) hd hdet i
  · rw [he]
    exact hv i j hij

end GlobalTheory.UnRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsApproxModLocalSquaresStatement
section
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_approx_mod_local_squares : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F) (z : (F →+* ℝ) → ℝ), (∀ v, y v ≠ 0) → (∀ σ, z σ ≠ 0) → ∃ x : F, x ≠ 0 ∧ (∀ v ∈ S, IsSquare (algebraMap F (v.adicCompletion F) x * y v)) ∧ ∀ σ : F →+* ℝ, 0 < σ x * z σ := by
  first | exact @GlobalTheory.QNorm.exists_approx_mod_squares | exact GlobalTheory.QNorm.exists_approx_mod_squares | (intros; apply GlobalTheory.QNorm.exists_approx_mod_squares <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsApproxModPowers
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.QNorm GlobalTheory.CNorm
open scoped WithZero TensorProduct

namespace GlobalTheory.CNorm

theorem mul_pow_mem_nhds {K : Type*} [NontriviallyNormedField K] [CompleteSpace K] [CharZero K]
    {p : ℕ} (hp : 0 < p) {y : K} (hy : y ≠ 0) :
    {a : K | a ≠ 0 ∧ ∃ r : K, a = y * r ^ p} ∈ nhds y := by
  have hd : HasStrictDerivAt (fun r : K => y * r ^ p) (y * ((p : K) * 1 ^ (p - 1))) 1 :=
    (hasStrictDerivAt_pow p (1 : K)).const_mul y
  have hne : y * ((p : K) * 1 ^ (p - 1)) ≠ 0 := by
    have : (p : K) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
    simp [hy, this]
  have h := hd.map_nhds_eq hne
  simp only [one_pow, mul_one] at h
  refine Filter.inter_mem (isOpen_ne.mem_nhds hy) ?_
  rw [← h]
  exact Filter.mem_map.2 (Filter.Eventually.of_forall fun r => ⟨r, rfl⟩)

theorem exists_approx_mod_powers :
    ∀ (p : ℕ) (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (y : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F), 0 < p → (∀ v, y v ≠ 0) → ∃ x : F, x ≠ 0 ∧ ∀ v ∈ S, ∃ r : v.adicCompletion F, algebraMap F (v.adicCompletion F) x = y v * r ^ p := by
  intro p F _ _ S y hp hy
  let U : Set (((v : S) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ)) :=
    ⋂ v : S, {q | q.1 v ≠ 0 ∧ ∃ r : v.1.adicCompletion F, q.1 v = y v.1 * r ^ p}
  have hU : U ∈ nhds ((fun v : S => y v.1), (0 : (F →+* ℝ) → ℝ)) := by
    refine Filter.iInter_mem.2 fun v => ?_
    have hc : Continuous fun q : ((v : S) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ) => q.1 v :=
      (continuous_apply v).comp continuous_fst
    have : CharZero (v.1.adicCompletion F) :=
      charZero_of_injective_algebraMap (algebraMap F (v.1.adicCompletion F)).injective
    letI : NontriviallyNormedField (v.1.adicCompletion F) :=
      Valued.toNontriviallyNormedField (v.1.adicCompletion F) ℤᵐ⁰
    exact hc.continuousAt.preimage_mem_nhds
      (mul_pow_mem_nhds (K := v.1.adicCompletion F) hp (hy v.1))
  obtain ⟨x, hx⟩ := (GlobalTheory.LocalQuad.denseRange_finite_real F S).mem_nhds hU
  have h1 : ∀ v : S, algebraMap F (v.1.adicCompletion F) x ≠ 0 ∧
      ∃ r : v.1.adicCompletion F, algebraMap F (v.1.adicCompletion F) x = y v.1 * r ^ p :=
    fun v => Set.mem_iInter.1 hx v
  by_cases hx0 : x = 0
  · subst hx0
    exact ⟨1, one_ne_zero, fun v hv => absurd (map_zero _) (h1 ⟨v, hv⟩).1⟩
  · exact ⟨x, hx0, fun v hv => (h1 ⟨v, hv⟩).2⟩

end GlobalTheory.CNorm
end

