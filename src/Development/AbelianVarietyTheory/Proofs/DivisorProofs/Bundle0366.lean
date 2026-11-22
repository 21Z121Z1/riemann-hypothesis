import Mathlib
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0294
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0304
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0311
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedLeastSquaresBound
section
open scoped ComplexOrder Matrix

namespace GlobalTheory.WeightedLS

open Matrix

variable {M g : ℕ}

theorem det_pos (L : Matrix (Fin M) (Fin g) ℝ) (hL : L.rank = g) (D : Fin M → ℝ)
    (hD : ∀ k, 0 < D k) : 0 < (L.transpose * Matrix.diagonal D * L).det := by
  have hinj : Function.Injective L.mulVec := by
    have h := LinearMap.finrank_range_add_finrank_ker L.mulVecLin
    have h2 : Module.finrank ℝ (LinearMap.range L.mulVecLin) = g := hL
    rw [h2, Module.finrank_fin_fun] at h
    have h3 : Module.finrank ℝ (LinearMap.ker L.mulVecLin) = 0 := by omega
    have h4 : LinearMap.ker L.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h3
    exact LinearMap.ker_eq_bot.mp h4
  have hP : (Matrix.diagonal D).PosDef := Matrix.posDef_diagonal_iff.mpr hD
  have h := hP.conjTranspose_mul_mul_same hinj
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h.det_pos

theorem det_eq_sum (L X : Matrix (Fin M) (Fin g) ℝ) (D : Fin M → ℝ) :
    (L.transpose * Matrix.diagonal D * X).det = ∑ S : {S : Finset (Fin M) // S.card = g},
      (∏ j, D (S.1.orderEmbOfFin S.2 j)) * ((L.submatrix (S.1.orderEmbOfFin S.2) id).det *
        (X.submatrix (S.1.orderEmbOfFin S.2) id).det) := by
  rw [ReciprocityTheory.ChartRestriction.DS.S7.det_mul_eq_sum_submatrix]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h : (L.transpose * Matrix.diagonal D).submatrix id (S.1.orderEmbOfFin S.2) =
      (L.submatrix (S.1.orderEmbOfFin S.2) id).transpose *
        Matrix.diagonal (fun j => D (S.1.orderEmbOfFin S.2 j)) := by
    ext i j
    simp [Matrix.mul_diagonal]
  rw [h, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

theorem block_bound (A : Matrix (Fin g) (Fin g) ℝ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (c : Fin g → ℝ) (k : Fin g),
      |A.det * (A.updateCol k c).det| ≤ K * ‖c‖ * (A.det * A.det) := by
  by_cases hA : A.det = 0
  · exact ⟨0, le_rfl, fun c k => by simp [hA]⟩
  · let f : (Fin g → ℝ) →L[ℝ] (Fin g → ℝ) := LinearMap.toContinuousLinearMap (Matrix.cramer A)
    have hp : 0 < |A.det| := abs_pos.mpr hA
    refine ⟨‖f‖ / |A.det|, by positivity, fun c k => ?_⟩
    have h1 : |(A.updateCol k c).det| ≤ ‖f‖ * ‖c‖ := by
      have h2 : (A.updateCol k c).det = f c k := by
        simp [f, Matrix.cramer_apply]
      rw [h2]
      exact (norm_le_pi_norm (f c) k).trans (f.le_opNorm c)
    rw [abs_mul, ← abs_mul_abs_self A.det]
    calc |A.det| * |(A.updateCol k c).det| ≤ |A.det| * (‖f‖ * ‖c‖) :=
          mul_le_mul_of_nonneg_left h1 hp.le
      _ = _ := by field_simp

theorem weighted_least_squares_bound : ∀ (M g : ℕ) (L : Matrix (Fin M) (Fin g) ℝ), L.rank = g →
    ∃ K : ℝ, ∀ (D : Fin M → ℝ) (b : Fin M → ℝ), (∀ k, 0 < D k) →
      ‖((L.transpose * Matrix.diagonal D * L)⁻¹ * L.transpose * Matrix.diagonal D).mulVec b‖ ≤
        K * ‖b‖ := by
  intro M g L hL
  choose K hK0 hK using fun S : {S : Finset (Fin M) // S.card = g} =>
    block_bound (L.submatrix (S.1.orderEmbOfFin S.2) id)
  refine ⟨∑ S, K S, fun D b hD => ?_⟩
  have hKs : 0 ≤ ∑ S, K S := Finset.sum_nonneg fun S _ => hK0 S
  have hdet := det_pos L hL D hD
  set A := L.transpose * Matrix.diagonal D * L with hA
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
  have hx : A.det * (A⁻¹ * L.transpose * Matrix.diagonal D).mulVec b k =
      (L.transpose * Matrix.diagonal D * L.updateCol k b).det := by
    have h1 := Matrix.det_smul_inv_mulVec_eq_cramer A ((L.transpose * Matrix.diagonal D).mulVec b)
      (isUnit_iff_ne_zero.mpr hdet.ne')
    have h2 := congrFun h1 k
    rw [Matrix.cramer_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc] at h2
    rw [← smul_eq_mul, ← Pi.smul_apply, h2]
    congr 1
    ext i j
    by_cases hj : j = k
    · subst hj
      simp [Matrix.mul_apply (M := L.transpose * Matrix.diagonal D), Matrix.mulVec, dotProduct]
    · simp [hA, Matrix.mul_apply (M := L.transpose * Matrix.diagonal D), Matrix.updateCol_ne hj]
  have hb : |(L.transpose * Matrix.diagonal D * L.updateCol k b).det| ≤
      (∑ S, K S) * ‖b‖ * A.det := by
    rw [hA, det_eq_sum, det_eq_sum, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S _ => ?_)
    set e := S.1.orderEmbOfFin S.2 with he
    have hp : 0 ≤ ∏ j, D (e j) := Finset.prod_nonneg fun j _ => (hD _).le
    have hu : (L.updateCol k b).submatrix e id = (L.submatrix e id).updateCol k (b ∘ e) := by
      ext i j
      by_cases hj : j = k
      · subst hj; simp
      · simp [Matrix.updateCol_ne hj]
    have hn : ‖b ∘ e‖ ≤ ‖b‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => norm_le_pi_norm b (e i)
    have hKS : K S ≤ ∑ S, K S :=
      Finset.single_le_sum (f := K) (fun S _ => hK0 S) (Finset.mem_univ S)
    rw [abs_mul, abs_of_nonneg hp, hu, mul_left_comm]
    refine mul_le_mul_of_nonneg_left ((hK S (b ∘ e) k).trans ?_) hp
    exact mul_le_mul_of_nonneg_right (mul_le_mul hKS hn (norm_nonneg _) hKs) (mul_self_nonneg _)
  rw [← hx, abs_mul, abs_of_pos hdet, mul_comm] at hb
  exact le_of_mul_le_mul_right hb hdet

end GlobalTheory.WeightedLS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRepReductionStructure
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

namespace GlobalTheory.DetInv

theorem special_fibre_generators : ∀ (p : ℕ) [Fact p.Prime] (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Free ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] (k : Type) [Field k] [IsAlgClosed k] [CharP k p] (h d N : ℕ) (b : Module.Basis (Fin d) ℤ_[p] Λ) (s : ℤ_[p] →+* WittVector p k) (ρ : Λ →+* Matrix (Fin h) (Fin h) (WittVector p k)), (∀ c : ℤ_[p], ρ (algebraMap ℤ_[p] Λ c) = s c • (1 : Matrix (Fin h) (Fin h) (WittVector p k))) → (∀ a : Λ, (ρ a).charpoly = ((LinearMap.mulLeft ℤ_[p] a).charpoly ^ N).map s) → ∃ x : Fin N → Fin h → k, Submodule.span k (Set.range fun ij : Fin N × Fin d => (ρ (b ij.2)).map WittVector.constantCoeff *ᵥ x ij.1) = ⊤ := by
  intro p _ Λ _ _ _ _ _ _ k _ _ _ h d N b s ρ hρ hch
  obtain ⟨e, π, a, u, h0, he, hp, hmon, hmem, -, hψ⟩ := GlobalTheory.T.exists_uniformizer_separable_reduction p Λ
  let c : WittVector p k →+* k := WittVector.constantCoeff
  let ψ : ℤ_[p] →+* k := c.comp s
  let Φ : Λ →+* Matrix (Fin h) (Fin h) k := c.mapMatrix.comp ρ
  have hΦ : ∀ l, Φ l = (ρ l).map c := fun l => rfl
  obtain ⟨hsep, hcp⟩ := hψ k ψ
  have hsurj : Function.Surjective c := fun r =>
    ⟨WittVector.teichmuller p r, by
      simp only [c, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]⟩
  have hker : ∀ w, c w = 0 → (p : WittVector p k) ∣ w := fun w hw =>
    Ideal.mem_span_singleton.1 ((WittVector.mem_span_p_iff_coeff_zero_eq_zero w).2 hw)
  have hcp0 : c p = 0 := by rw [map_natCast, CharP.cast_eq_zero]
  obtain ⟨ht0, htk⟩ := GlobalTheory.T.reduction_uniformizer_nilpotent p (WittVector p k) k Λ h e c ρ π u
    (WittVector.p_nonzero p k) hsurj hker hcp0 he hp
  have hscal : Φ.comp (algebraMap ℤ_[p] Λ) = (algebraMap k (Matrix (Fin h) (Fin h) k)).comp ψ := by
    refine RingHom.ext fun z => ?_
    change Φ (algebraMap ℤ_[p] Λ z) = algebraMap k (Matrix (Fin h) (Fin h) k) (ψ z)
    rw [hΦ, hρ, Algebra.algebraMap_eq_smul_one]
    ext i j
    by_cases hij : i = j <;> simp [ψ, hij, Matrix.one_apply]
  have hscal' : ∀ z (l : Λ), Φ (z • l) = ψ z • Φ l := by
    intro z l
    have : Φ (algebraMap ℤ_[p] Λ z) = algebraMap k (Matrix (Fin h) (Fin h) k) (ψ z) :=
      RingHom.congr_fun hscal z
    rw [Algebra.smul_def, map_mul, this, ← Algebra.smul_def]
  have haev : Polynomial.aeval (Φ a) (h0.map ψ) = Φ (Polynomial.aeval a h0) := by
    rw [Polynomial.aeval_def, Polynomial.aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map,
      hscal]
  obtain ⟨m, hm⟩ := Ideal.mem_span_singleton.1 hmem
  have hT : (Φ a).charpoly = (h0.map ψ) ^ (e * N) := by
    rw [hΦ, Matrix.charpoly_map, hch, Polynomial.map_map, Polynomial.map_pow, pow_mul, ← hcp]
  obtain ⟨x, hx⟩ := GlobalTheory.T.cyclic_generators_invariant_top k h e N (Φ π) (Φ a) (h0.map ψ) he (hmon.map ψ) hsep
    (by rw [← map_mul, ← map_mul, mul_comm]) ht0 htk
    (fun x => ⟨Φ m *ᵥ x, by rw [haev, hm, map_mul, Matrix.mulVec_mulVec]⟩) hT
  refine ⟨x, ?_⟩
  set U := Submodule.span k (Set.range fun ij : Fin N × Fin d =>
    (ρ (b ij.2)).map WittVector.constantCoeff *ᵥ x ij.1) with hU
  have key : ∀ (l : Λ) i, Φ l *ᵥ x i ∈ U := by
    intro l i
    rw [← b.sum_repr l, map_sum, Matrix.sum_mulVec]
    refine U.sum_mem fun j _ => ?_
    rw [hscal', Matrix.smul_mulVec]
    exact U.smul_mem _ (Submodule.subset_span ⟨(i, j), rfl⟩)
  have stab : ∀ (l : Λ), ∀ z ∈ U, Φ l *ᵥ z ∈ U := by
    intro l z hz
    have : U ≤ U.comap (Φ l).mulVecLin := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨i, j⟩, rfl⟩
      change Φ l *ᵥ (Φ (b j) *ᵥ x i) ∈ U
      rw [Matrix.mulVec_mulVec, ← map_mul]
      exact key _ _
    exact this hz
  refine hx U (fun i => ?_) (stab π) (stab a)
  simpa using key 1 i

end GlobalTheory.DetInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZmodTorsorExistsPointFiniteSeparableStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zmodTorsor_exists_point_finite_separable : ∀ (B K : Type) [CommRing B] [Field K] (f : B →+* K) (D : Type) [CommRing D] [Algebra B D]
    (q : ℕ), 0 < q → ∀ (act : Multiplicative (ZMod q) →* (D ≃ₐ[B] D)),
    GlobalTheory.KeyOriginCut.IsZTorsor B D q act →
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (_ : Algebra.IsSeparable K L)
      (σ : D →+* L), σ.comp (algebraMap B D) = (algebraMap K L).comp f := by
  first | (exact @GlobalTheory.TorsorFieldPoint.exists_point_finite_separable) | (exact GlobalTheory.TorsorFieldPoint.exists_point_finite_separable) | (intros; apply GlobalTheory.TorsorFieldPoint.exists_point_finite_separable  <;> assumption)
end

