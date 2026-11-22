import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0224
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0218
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002
import Development.AbelianVarietyTheory.Definitions.Divisors.OrthSubrepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0221
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0002
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0180
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0222
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaussianPairingUnitaryGroupTwoThree
section
open MeasureTheory Complex Matrix GlobalTheory.RealWeil
open scoped RealInnerProductSpace ContDiff Real ComplexOrder

namespace GlobalTheory.RealWeil.GaussPairing

section Coord

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {ι : Type} [Fintype ι]

theorem norm_sq_eq_dot (e : V ≃L[ℝ] (ι → ℂ)) (he : ∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) (v : V) :
    (‖v‖ : ℂ) ^ 2 = star (e v) ⬝ᵥ e v := by
  have h : ((‖v‖ ^ 2 : ℝ) : ℂ) = ((∑ i, ‖e v i‖ ^ 2 : ℝ) : ℂ) := by rw [he v]
  push_cast at h
  rw [h, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact (Complex.conj_mul' _).symm

theorem inner_eq_dot (e : V ≃L[ℝ] (ι → ℂ)) (he : ∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) (x y : V) :
    ((⟪x, y⟫ : ℝ) : ℂ) = (1 / 2 : ℂ) * (star (e x) ⬝ᵥ e y + star (e y) ⬝ᵥ e x) := by
  have h : ((‖x + y‖ ^ 2 : ℝ) : ℂ) = ((‖x‖ ^ 2 + 2 * ⟪x, y⟫ + ‖y‖ ^ 2 : ℝ) : ℂ) := by
    rw [norm_add_sq_real]
  push_cast at h
  rw [norm_sq_eq_dot e he (x + y), norm_sq_eq_dot e he x, norm_sq_eq_dot e he y, map_add, star_add,
    add_dotProduct, dotProduct_add, dotProduct_add] at h
  linear_combination (-1 / 2 : ℂ) * h

theorem star_mulVec_dot (g : Matrix ι ι ℂ) (z w : ι → ℂ) :
    star (g *ᵥ z) ⬝ᵥ w = star z ⬝ᵥ gᴴ *ᵥ w := by
  rw [star_mulVec, dotProduct_mulVec]

end Coord

theorem posDef_one_add {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] (g : Matrix κ ι ℂ) :
    (1 + gᴴ * g).PosDef :=
  PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self g)

theorem integral_sum_elim {ι : Type} [Fintype ι] (F : (ι ⊕ ι → ℂ) → ℂ) (hF : Integrable F) :
    ∫ z : ι → ℂ, ∫ w : ι → ℂ, F (Sum.elim z w) = ∫ x, F x := by
  have hmp := volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : ι ⊕ ι => ℂ)
  have hF' : Integrable (fun p => F ((MeasurableEquiv.sumPiEquivProdPi fun _ : ι ⊕ ι => ℂ).symm p))
      ((volume : Measure (ι → ℂ)).prod volume) :=
    (hmp.integrable_comp_emb (MeasurableEquiv.measurableEmbedding _)).2 hF
  rw [← hmp.integral_comp' F, Measure.volume_eq_prod, integral_prod _ hF']
  rfl

private lemma half_smul_add_conjTranspose_eq_of_hermitian {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι ℂ) (hX : Xᴴ = X) :
    (1 / 2 : ℂ) • X + ((1 / 2 : ℂ) • X)ᴴ = X := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [Complex.star_def, map_div₀, map_one, map_ofNat]
  rw [conjTranspose_smul, hX, h2, ← smul_add, GlobalTheory.RealWeil.PosDet.half_add_self]

private lemma half_cross_add_conjTranspose_eq_mul {ι : Type} [Fintype ι] [DecidableEq ι] (s a b : Matrix ι ι ℂ) (hs : sᴴ = s) :
    (1 / 2 : ℂ) • (aᴴ * (1 + s) * b) + ((1 / 2 : ℂ) • (bᴴ * (1 - s) * a))ᴴ = 0 + aᴴ * b := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [Complex.star_def, map_div₀, map_one, map_ofNat]
  rw [conjTranspose_smul, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_sub, conjTranspose_one, hs, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, zero_add]
  module

private lemma half_cross_add_conjTranspose_eq_mul_swap {ι : Type} [Fintype ι] [DecidableEq ι] (s a b : Matrix ι ι ℂ) (hs : sᴴ = s) :
    (1 / 2 : ℂ) • (bᴴ * (1 - s) * a) + ((1 / 2 : ℂ) • (aᴴ * (1 + s) * b))ᴴ = 0 + bᴴ * a := by
  have h2 : star (1 / 2 : ℂ) = 1 / 2 := by
    rw [Complex.star_def, map_div₀, map_one, map_ofNat]
  rw [conjTranspose_smul, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_add, conjTranspose_one, hs, h2]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
    Matrix.one_mul, Matrix.mul_assoc, zero_add]
  module

theorem lam_mu_eq : ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (ι : Type) [Fintype ι] [DecidableEq ι] (e : V ≃L[ℝ] (ι → ℂ)), (∀ v, ‖v‖ ^ 2 = ∑ i, ‖e v i‖ ^ 2) → ∀ (s : Matrix ι ι ℂ), sᴴ = s → s * s = 1 → ∀ J : V ≃ₗᵢ[ℝ] V, (∀ v, e (J v) = I • s *ᵥ e v) → (∀ (g : Matrix ι ι ℂ) (k : V → V), gᴴ * s * g = s → (∀ v, e (k v) = g *ᵥ e v) → dP s g ≠ 0 ∧ dP s g⁻¹ = star (dP s g) ∧ lam k = (dP s g * dP s g⁻¹)⁻¹) ∧ ∀ (g₁ g₂ : Matrix ι ι ℂ) (k₁ k₂ : V → V), g₁ᴴ * s * g₁ = s → g₂ᴴ * s * g₂ = s → (∀ v, e (k₁ v) = g₁ *ᵥ e v) → (∀ v, e (k₂ v) = g₂ *ᵥ e v) → mu J k₁ k₂ = (dP s g₁⁻¹ * dP s g₂ * dP s (g₂⁻¹ * g₁))⁻¹ := by
  intro V _ _ _ _ _ ι _ _ e he s hs hss J hJ
  have hmp := GlobalTheory.measurePreserving_of_norm_sq_eq_sum_complex_coords V ι e he
  have hme : MeasurableEmbedding e := e.toHomeomorph.measurableEmbedding
  obtain ⟨hd1, hd2⟩ := GlobalTheory.RealWeil.PosDet.detPlus_identities ι s hs hss
  have hHerm : ∀ g : Matrix ι ι ℂ, (1 + gᴴ * g)ᴴ = 1 + gᴴ * g := fun g => by
    rw [conjTranspose_add, conjTranspose_one, conjTranspose_mul, conjTranspose_conjTranspose]
  refine ⟨fun g k hg hk => ?_, fun g₁ g₂ k₁ k₂ hg₁ hg₂ hk₁ hk₂ => ?_⟩
  · obtain ⟨A, hA⟩ : ∃ A : Matrix ι ι ℂ, A = (1 / 2 : ℂ) • (1 + gᴴ * g) := ⟨_, rfl⟩
    have hAA : A + Aᴴ = 1 + gᴴ * g := by rw [hA]; exact half_smul_add_conjTranspose_eq_of_hermitian _ (hHerm g)
    obtain ⟨hA0, -, hAint⟩ := GlobalTheory.T.integral_complexGaussian_posDef_hermitian_part ι A (by rw [hAA]; exact posDef_one_add g)
    obtain ⟨hstar, hdet⟩ := hd1 g hg
    rw [← hA] at hdet
    have hpt : ∀ u, gau u * gau (k u) = cexp (-(π : ℂ) * (star (e u) ⬝ᵥ A *ᵥ e u)) := by
      intro u
      simp only [gau, ← Complex.exp_add]
      congr 1
      rw [norm_sq_eq_dot e he u, norm_sq_eq_dot e he (k u), hk u, star_mulVec_dot, hA, smul_mulVec,
        dotProduct_smul, add_mulVec, one_mulVec, ← mulVec_mulVec, dotProduct_add, smul_eq_mul]
      ring
    have hlam : lam k = A.det⁻¹ :=
      calc lam k = ∫ u, cexp (-(π : ℂ) * (star (e u) ⬝ᵥ A *ᵥ e u)) := by
            unfold lam
            congr 1
            funext u
            exact hpt u
        _ = ∫ z, cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)) :=
            hmp.integral_comp hme (fun z => cexp (-(π : ℂ) * (star z ⬝ᵥ A *ᵥ z)))
        _ = A.det⁻¹ := hAint
    refine ⟨fun h0 => hA0 (by rw [hdet, h0, zero_mul]), hstar, ?_⟩
    rw [hlam, hdet]
  · obtain ⟨M, hM⟩ : ∃ M : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ, M =
        fromBlocks ((1 / 2 : ℂ) • (1 + g₁ᴴ * g₁)) ((1 / 2 : ℂ) • (g₁ᴴ * (1 + s) * g₂))
          ((1 / 2 : ℂ) • (g₂ᴴ * (1 - s) * g₁)) ((1 / 2 : ℂ) • (1 + g₂ᴴ * g₂)) := ⟨_, rfl⟩
    have hdet2 := hd2 g₁ g₂ hg₁ hg₂
    rw [← hM] at hdet2
    have hMM : M + Mᴴ = 1 + (fromCols g₁ g₂)ᴴ * fromCols g₁ g₂ := by
      rw [hM, conjTranspose_fromCols_eq_fromRows_conjTranspose, fromRows_mul_fromCols,
        fromBlocks_conjTranspose, fromBlocks_add, ← fromBlocks_one, fromBlocks_add,
        half_smul_add_conjTranspose_eq_of_hermitian _ (hHerm g₁), half_smul_add_conjTranspose_eq_of_hermitian _ (hHerm g₂), half_cross_add_conjTranspose_eq_mul s g₁ g₂ hs,
        half_cross_add_conjTranspose_eq_mul_swap s g₁ g₂ hs]
    obtain ⟨-, hMi, hMint⟩ := GlobalTheory.T.integral_complexGaussian_posDef_hermitian_part (ι ⊕ ι) M (by rw [hMM]; exact posDef_one_add _)
    have hpt : ∀ u v, gau u * gau v * (cexp (π * I * (omJ J (k₁ u) (k₂ v) : ℂ)) * gau (k₁ u + k₂ v)) =
        cexp (-(π : ℂ) * (star (Sum.elim (e u) (e v)) ⬝ᵥ M *ᵥ Sum.elim (e u) (e v))) := by
      intro u v
      simp only [gau, ← Complex.exp_add]
      congr 1
      have hsum : star (Sum.elim (e u) (e v)) = Sum.elim (star (e u)) (star (e v)) := by
        funext i
        cases i <;> rfl
      have hA1 : ∀ (g : Matrix ι ι ℂ) (z : ι → ℂ),
          star z ⬝ᵥ ((1 / 2 : ℂ) • (1 + gᴴ * g)) *ᵥ z = 1 / 2 * (star z ⬝ᵥ z + star (g *ᵥ z) ⬝ᵥ g *ᵥ z) := by
        intro g z
        rw [smul_mulVec, dotProduct_smul, add_mulVec, one_mulVec, ← mulVec_mulVec, dotProduct_add,
          ← star_mulVec_dot, smul_eq_mul]
      have hB1 : star (e u) ⬝ᵥ ((1 / 2 : ℂ) • (g₁ᴴ * (1 + s) * g₂)) *ᵥ e v =
          1 / 2 * (star (g₁ *ᵥ e u) ⬝ᵥ g₂ *ᵥ e v + star (g₁ *ᵥ e u) ⬝ᵥ s *ᵥ (g₂ *ᵥ e v)) := by
        rw [smul_mulVec, dotProduct_smul, ← mulVec_mulVec, ← mulVec_mulVec, ← star_mulVec_dot,
          add_mulVec, one_mulVec, dotProduct_add, smul_eq_mul]
      have hC1 : star (e v) ⬝ᵥ ((1 / 2 : ℂ) • (g₂ᴴ * (1 - s) * g₁)) *ᵥ e u =
          1 / 2 * (star (g₂ *ᵥ e v) ⬝ᵥ g₁ *ᵥ e u - star (g₂ *ᵥ e v) ⬝ᵥ s *ᵥ (g₁ *ᵥ e u)) := by
        rw [smul_mulVec, dotProduct_smul, ← mulVec_mulVec, ← mulVec_mulVec, ← star_mulVec_dot,
          sub_mulVec, one_mulVec, dotProduct_sub, smul_eq_mul]
      have hJ1 : star (g₁ *ᵥ e u) ⬝ᵥ I • s *ᵥ (g₂ *ᵥ e v) = I * (star (g₁ *ᵥ e u) ⬝ᵥ s *ᵥ (g₂ *ᵥ e v)) := by
        rw [dotProduct_smul, smul_eq_mul]
      have hJ2 : star (I • s *ᵥ (g₂ *ᵥ e v)) ⬝ᵥ g₁ *ᵥ e u =
          -I * (star (g₂ *ᵥ e v) ⬝ᵥ s *ᵥ (g₁ *ᵥ e u)) := by
        rw [star_smul, smul_dotProduct, star_mulVec_dot, hs, smul_eq_mul, Complex.star_def, Complex.conj_I]
      have hN : star (g₁ *ᵥ e u + g₂ *ᵥ e v) ⬝ᵥ (g₁ *ᵥ e u + g₂ *ᵥ e v) =
          star (g₁ *ᵥ e u) ⬝ᵥ g₁ *ᵥ e u + star (g₁ *ᵥ e u) ⬝ᵥ g₂ *ᵥ e v +
            (star (g₂ *ᵥ e v) ⬝ᵥ g₁ *ᵥ e u + star (g₂ *ᵥ e v) ⬝ᵥ g₂ *ᵥ e v) := by
        rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add]
      unfold omJ
      rw [inner_eq_dot e he, hJ, norm_sq_eq_dot e he u, norm_sq_eq_dot e he v,
        norm_sq_eq_dot e he (k₁ u + k₂ v), map_add, hk₁, hk₂, hJ1, hJ2, hN, hM, hsum, fromBlocks_mulVec,
        sumElim_dotProduct_sumElim]
      simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, dotProduct_add]
      rw [hA1, hA1, hB1, hC1]
      linear_combination ((π : ℂ) / 2 * (star (g₁ *ᵥ e u) ⬝ᵥ s *ᵥ (g₂ *ᵥ e v) -
        star (g₂ *ᵥ e v) ⬝ᵥ s *ᵥ (g₁ *ᵥ e u))) * Complex.I_sq
    calc mu J k₁ k₂ = ∫ u, ∫ v, cexp (-(π : ℂ) * (star (Sum.elim (e u) (e v)) ⬝ᵥ M *ᵥ Sum.elim (e u) (e v))) := by
          unfold mu
          congr 1
          funext u
          congr 1
          funext v
          exact hpt u v
      _ = ∫ u, ∫ w, cexp (-(π : ℂ) * (star (Sum.elim (e u) w) ⬝ᵥ M *ᵥ Sum.elim (e u) w)) := by
          congr 1
          funext u
          exact hmp.integral_comp hme (fun w => cexp (-(π : ℂ) * (star (Sum.elim (e u) w) ⬝ᵥ M *ᵥ Sum.elim (e u) w)))
      _ = ∫ z, ∫ w, cexp (-(π : ℂ) * (star (Sum.elim z w) ⬝ᵥ M *ᵥ Sum.elim z w)) :=
          hmp.integral_comp hme (fun z => ∫ w, cexp (-(π : ℂ) * (star (Sum.elim z w) ⬝ᵥ M *ᵥ Sum.elim z w)))
      _ = ∫ x, cexp (-(π : ℂ) * (star x ⬝ᵥ M *ᵥ x)) := integral_sum_elim _ hMi
      _ = M.det⁻¹ := hMint
      _ = (dP s g₁⁻¹ * dP s g₂ * dP s (g₂⁻¹ * g₁))⁻¹ := by rw [hdet2]

end GlobalTheory.RealWeil.GaussPairing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreLocalizationDirectedUnionKernelStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibreLocalization_directedUnion_kernel : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T) (hA : Monotone 𝒜), (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra T E] (Q : Ideal E) [Q.IsPrime]
      (Ek : ι → Type) [∀ k, CommRing (Ek k)] [∀ k, Algebra (𝒜 k) (Ek k)]
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k (a : 𝒜 k), e k (algebraMap (𝒜 k) (Ek k) a) = algebraMap T E a) →
      (∀ k l (hkl : k ≤ l) (a : 𝒜 k), h k l hkl (algebraMap (𝒜 k) (Ek k) a) =
          algebraMap (𝒜 l) (Ek l) (Subring.inclusion (hA hkl) a)) →
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) →
      (∀ k, Function.Injective (e k)) →
      (∀ x : E, ∃ k y, e k y = x) →
    ∀ (g : ∀ k, GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
      (∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y))) →
    ∀ (f : ∀ k l, k ≤ l → GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib (𝒜 l) (Localization.AtPrime (Q.comap (e l)))),
      (∀ k l (hkl : k ≤ l) (y : Ek k), f k l hkl (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime (Q.comap (e l)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 l) (Localization.AtPrime (Q.comap (e l))))
          (algebraMap (Ek l) (Localization.AtPrime (Q.comap (e l))) (h k l hkl y))) →
    ∀ k (x : GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k)))), g k x = 0 →
      ∃ l, ∃ hkl : k ≤ l, f k l hkl x = 0 := by
  first | (exact @GlobalTheory.genFib_colim_ker) | (exact GlobalTheory.genFib_colim_ker) | (intros; apply GlobalTheory.genFib_colim_ker  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericFibreLocalizationDirectedUnionSurjectiveStatement
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericFibreLocalization_directedUnion_surjective : ∀ (T : Type) [CommRing T] [IsDomain T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra T E] (Q : Ideal E) [Q.IsPrime]
      (Ek : ι → Type) [∀ k, CommRing (Ek k)] [∀ k, Algebra (𝒜 k) (Ek k)]
      (e : ∀ k, Ek k →+* E) (h : ∀ k l, k ≤ l → Ek k →+* Ek l),
      (∀ k (a : 𝒜 k), e k (algebraMap (𝒜 k) (Ek k) a) = algebraMap T E a) →
      (∀ k l (hkl : k ≤ l) (y : Ek k), e l (h k l hkl y) = e k y) →
      (∀ x : E, ∃ k y, e k y = x) →
    ∀ (g : ∀ k, GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))) →+*
        GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q)),
      (∀ k (y : Ek k), g k (algebraMap (Localization.AtPrime (Q.comap (e k)))
          (GlobalTheory.LocAcyc.GenFib (𝒜 k) (Localization.AtPrime (Q.comap (e k))))
          (algebraMap (Ek k) (Localization.AtPrime (Q.comap (e k))) y)) =
        algebraMap (Localization.AtPrime Q) (GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q))
          (algebraMap E (Localization.AtPrime Q) (e k y))) →
    ∀ b : GlobalTheory.LocAcyc.GenFib T (Localization.AtPrime Q), ∃ k x, g k x = b := by
  first | (exact @GlobalTheory.genFib_colim_surj) | (exact GlobalTheory.genFib_colim_surj) | (intros; apply GlobalTheory.genFib_colim_surj  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomRegFibOfIsRegularRingTensorEssFiniteTypeStatement
section
open IsLocalRing TensorProduct ReciprocityTheory.AnForm.R
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geomRegFib_of_isRegularRing_tensor_essFiniteType : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B], (∀ (K : Type) [Field K] [Algebra R K] [Algebra.EssFiniteType R K], IsRegularRing (B ⊗[R] K)) → FinalTheorems.GeomRegFib R B := by
  first | exact @GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType | exact GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType | (intros; apply GlobalTheory.geomRegFib_of_isRegularRing_essFiniteType <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLCommStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
private lemma hc_conj_invariant {F : Type} [Field F] (a b n : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (x p : GL (Fin n) F) :
    hc a b α β n (p * x * p⁻¹) = hc a b α β n x := by
  unfold hc hcTw
  simp only [GlobalTheory.HCCommF.gal_id]
  congr 1
  rw [← finsum_comp_equiv (Equiv.mulLeft p)]
  congr 1
  funext y
  simp only [Equiv.coe_mulLeft, mul_inv_rev, mul_assoc, inv_mul_cancel_left]

private lemma inPar_swap_eq_inPar_aflipG {F : Type} [Field F] (a b : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β) (z : GL (Fin (a + b)) F) :
    (if InPar b z then β (tlG b z) * α (brG b a z) else 0) =
      (if InPar a (GlobalTheory.HCCommF.aflipG z) then
        α (tlG a (GlobalTheory.HCCommF.aflipG z)) * β (brG a b (GlobalTheory.HCCommF.aflipG z)) else 0) := by
  obtain ⟨w, rfl⟩ : ∃ w, z = GlobalTheory.HCCommF.aflipG w :=
    ⟨GlobalTheory.HCCommF.aflipG z, (GlobalTheory.HCCommF.aflipG_aflipG z).symm⟩
  rw [GlobalTheory.HCCommF.aflipG_aflipG, GlobalTheory.HCCommF.inPar_aflip]
  unfold tlG brG
  rw [GlobalTheory.HCCommF.aflipG_coe, GlobalTheory.HCCommF.tl_aflip, GlobalTheory.HCCommF.br_aflip,
    GlobalTheory.HCCommF.class_aflip hβ, GlobalTheory.HCCommF.class_aflip hα, mul_comm (β _)]

private lemma hc_swap_eq_hc_aflipG {F : Type} [Field F] (a b : ℕ) (α : GL (Fin a) F → ℂ)
    (β : GL (Fin b) F → ℂ) (hα : IsCl α) (hβ : IsCl β) (x : GL (Fin (a + b)) F) :
    hc b a β α (a + b) x = hc a b α β (a + b) (GlobalTheory.HCCommF.aflipG x) := by
  unfold hc hcTw
  simp only [GlobalTheory.HCCommF.gal_id]
  have hcard : Nat.card {p : GL (Fin (a + b)) F // InPar b p} =
      Nat.card {p : GL (Fin (a + b)) F // InPar a p} :=
    Nat.card_congr (Equiv.subtypeEquiv (GlobalTheory.HCCommF.aflipE (F := F) (a + b)) (fun p => by
      show InPar b p ↔ InPar a (GlobalTheory.HCCommF.aflipG p)
      conv_lhs => rw [← GlobalTheory.HCCommF.aflipG_aflipG p]
      exact GlobalTheory.HCCommF.inPar_aflip _))
  rw [hcard]
  congr 1
  conv_rhs => rw [← finsum_comp_equiv ((GlobalTheory.HCCommF.aflipE (F := F) (a + b)).trans (Equiv.inv _))]
  congr 1
  funext y
  rw [inPar_swap_eq_inPar_aflipG a b α β hα hβ]
  have h : GlobalTheory.HCCommF.aflipG (y⁻¹ * x * y) =
      ((GlobalTheory.HCCommF.aflipG y)⁻¹)⁻¹ * GlobalTheory.HCCommF.aflipG x * (GlobalTheory.HCCommF.aflipG y)⁻¹ := by
    rw [inv_inv, GlobalTheory.HCCommF.aflipG_mul, GlobalTheory.HCCommF.aflipG_mul, GlobalTheory.HCCommF.aflipG_inv, mul_assoc]
  rw [h]
  rfl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_comm : ∀ (F : Type) [Field F] [Finite F], ∀ (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ), IsCl α → IsCl β → n = a + b → hc a b α β n = hc b a β α n := by
  intro F _ _ a b n α β hα hβ hn
  subst hn
  funext x
  rw [hc_swap_eq_hc_aflipG a b α β hα hβ x]
  obtain ⟨p, hp⟩ := GlobalTheory.HCCommF.aflipG_conj x
  rw [hp, hc_conj_invariant]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLFieldAutomorphismStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_fieldAutomorphism : ∀ (F : Type) [Field F] [Finite F], ∀ (t : F ≃+* F) (a b n : ℕ) (α : GL (Fin a) F → ℂ) (β : GL (Fin b) F → ℂ) (x : GL (Fin n) F), hc a b α β n (gal (t : F →+* F) n x) = hc a b (fun y => α (gal (t : F →+* F) a y)) (fun y => β (gal (t : F →+* F) b y)) n x := by
  first | (exact @GlobalTheory.Shin.HcGal.hc_gal) | (exact GlobalTheory.Shin.HcGal.hc_gal) | (intros; apply GlobalTheory.Shin.HcGal.hc_gal  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarishChandraInductionGLOneLeftRightUnitStatement
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harishChandraInductionGL_one_left_right_unit : ∀ (F : Type) [Field F] [Finite F], ∀ (a : ℕ) (α : GL (Fin a) F → ℂ), IsCl α → hc 0 a (fun _ => 1) α a = α ∧ hc a 0 α (fun _ => 1) a = α := by
  first | (exact @GlobalTheory.Shin.HcUnit.main) | (exact GlobalTheory.Shin.HcUnit.main) | (intros; apply GlobalTheory.Shin.HcUnit.main  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasFderivAtSchwartzOperatorFirst
section
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp

noncomputable section

open Filter Topology Asymptotics

namespace GlobalTheory.SchwartzFstOp

variable {V W V' E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem sliceCLM_add_eq (x' v : V') (f : 𝓢(V × V', ℂ)) :
    sliceCLM (x' + v) f = sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f) := by
  ext x
  simp [SchwartzMap.compSubConstCLM_apply]

theorem remainder_bound (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (x' : V') :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : V', ‖v‖ ≤ 1 → ∀ z : W,
      ‖T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f)) z‖
        ≤ K * ‖v‖ ^ 2 := by
  let q : Seminorm ℂ 𝓢(V × V', ℂ) :=
    (SchwartzMap.seminorm ℂ 0 0).comp (T.comp (sliceCLM x')).toLinearMap
  have hq : Continuous q :=
    ((schwartz_withSeminorms ℂ W E).continuous_seminorm (0, 0)).comp (T.comp (sliceCLM x')).continuous
  obtain ⟨s, C, -, hC⟩ := Seminorm.bound_of_continuous (schwartz_withSeminorms ℂ (V × V') ℂ) q hq
  choose D hD using fun i : ℕ × ℕ => GlobalTheory.T.schwartz_translate_taylor_second_order f i.1 i.2
  refine ⟨(C : ℝ) * ∑ i ∈ s, |D i|, by positivity, fun v hv z => ?_⟩
  set g := SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f with hg
  have ha : ‖((0 : V), v)‖ = ‖v‖ := by simp [Prod.norm_def]
  have h1 : ‖T (sliceCLM x' g) z‖ ≤ q g := SchwartzMap.norm_le_seminorm ℂ _ _
  have h2 : q g ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) g := by
    have := hC g
    simpa [Seminorm.smul_apply, NNReal.smul_def] using this
  have h3 : (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) g ≤ (∑ i ∈ s, |D i|) * ‖v‖ ^ 2 := by
    apply Seminorm.finset_sup_apply_le (by positivity)
    intro i hi
    have hDi := hD i ((0 : V), v) (by rw [ha]; exact hv)
    rw [ha] at hDi
    calc schwartzSeminormFamily ℂ (V × V') ℂ i g ≤ D i * ‖v‖ ^ 2 := hDi
      _ ≤ |D i| * ‖v‖ ^ 2 := by gcongr; exact le_abs_self _
      _ ≤ (∑ j ∈ s, |D j|) * ‖v‖ ^ 2 := by
          gcongr; exact Finset.single_le_sum (fun j _ => abs_nonneg (D j)) hi
  calc ‖T (sliceCLM x' g) z‖ ≤ q g := h1
    _ ≤ (C : ℝ) * (s.sup (schwartzSeminormFamily ℂ (V × V') ℂ)) g := h2
    _ ≤ (C : ℝ) * ((∑ i ∈ s, |D i|) * ‖v‖ ^ 2) := by gcongr
    _ = (C : ℝ) * (∑ i ∈ s, |D i|) * ‖v‖ ^ 2 := by ring

theorem opFst_add_decomp (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ)) (y w : W) (x' v : V') :
    opFst T f (y + w, x' + v) =
      T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f)) (y + w)
        + T (sliceCLM x' f) (y + w) + T (sliceCLM x' (lineSnd v f)) (y + w) := by
  rw [opFst_apply, sliceCLM_add_eq]
  conv_lhs => rw [show SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f
      = (SchwartzMap.compSubConstCLM ℂ (-((0 : V), v)) f - f - lineSnd v f) + f + lineSnd v f by abel]
  simp only [map_add, SchwartzMap.add_apply]

theorem hasFDerivAt_opFst [FiniteDimensional ℝ V'] (T : 𝓢(V, ℂ) →L[ℂ] 𝓢(W, E)) (f : 𝓢(V × V', ℂ))
    (y : W) (x' : V') :
    HasFDerivAt (opFst T f) ((fderiv ℝ (T (sliceCLM x' f)) y).comp (ContinuousLinearMap.fst ℝ W V')
      + (dSndCLM T f (y, x')).comp (ContinuousLinearMap.snd ℝ W V')) (y, x') := by
  have hA : HasFDerivAt (fun q : W × V' => T (sliceCLM x' f) q.1)
      ((fderiv ℝ (T (sliceCLM x' f)) y).comp (ContinuousLinearMap.fst ℝ W V')) (y, x') :=
    ((T (sliceCLM x' f)).differentiableAt.hasFDerivAt).comp (y, x') hasFDerivAt_fst
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hA ⊢
  have hcont : Continuous fun z : W => dSndCLM T f (z, x') := by
    rw [continuous_clm_apply]
    intro v
    exact (T (sliceCLM x' (lineSnd v f))).continuous
  have hB : (fun p : W × V' => dSndCLM T f (y + p.1, x') p.2 - dSndCLM T f (y, x') p.2)
      =o[𝓝 0] fun p => p := by
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have ht : Tendsto (fun p : W × V' => dSndCLM T f (y + p.1, x')) (𝓝 0) (𝓝 (dSndCLM T f (y, x'))) := by
      have : Tendsto (fun p : W × V' => y + p.1) (𝓝 0) (𝓝 y) := by
        have := (tendsto_const_nhds (x := y)).add ((continuous_fst.tendsto (0 : W × V')))
        simpa using this
      exact (hcont.tendsto y).comp this
    filter_upwards [(Metric.tendsto_nhds.mp ht) c hc] with p hp
    rw [← ContinuousLinearMap.sub_apply]
    calc _ ≤ ‖dSndCLM T f (y + p.1, x') - dSndCLM T f (y, x')‖ * ‖p.2‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ c * ‖p‖ := by
          gcongr
          · rw [← dist_eq_norm]; exact hp.le
          · exact norm_snd_le p
  obtain ⟨K, hK0, hK⟩ := remainder_bound T f x'
  have hC : (fun p : W × V' =>
      T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), p.2)) f - f - lineSnd p.2 f)) (y + p.1))
      =o[𝓝 0] fun p => p := by
    have h1 : (fun p : W × V' =>
        T (sliceCLM x' (SchwartzMap.compSubConstCLM ℂ (-((0 : V), p.2)) f - f - lineSnd p.2 f)) (y + p.1))
        =O[𝓝 0] fun p : W × V' => ‖p‖ ^ 2 := by
      rw [Asymptotics.isBigO_iff]
      refine ⟨K, ?_⟩
      filter_upwards [Metric.closedBall_mem_nhds (0 : W × V') one_pos] with p hp
      rw [Metric.mem_closedBall, dist_zero_right] at hp
      calc _ ≤ K * ‖p.2‖ ^ 2 := hK p.2 ((norm_snd_le p).trans hp) _
        _ ≤ K * ‖p‖ ^ 2 := by gcongr; exact norm_snd_le p
        _ = K * ‖‖p‖ ^ 2‖ := by rw [norm_pow, norm_norm]
    exact h1.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine ((hA.add hB).add hC).congr_left (fun p => ?_)
  obtain ⟨w, v⟩ := p
  simp only [Prod.mk_add_mk]
  rw [opFst_add_decomp]
  simp only [opFst_apply, dSndCLM_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  abel

end GlobalTheory.SchwartzFstOp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasLatticeRelativeLengthMapIffStatement
section
open GlobalTheory.IndefiniteRowSideFullHecke.MultiplicationKernelIdentity GlobalTheory.HermitianPreEigenvalues Polynomial Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasLatticeRelativeLength_map_iff : ∀ (C : Type) [Field C] (v : AddValuation C (WithTop ℝ)) (M M' : Type) [AddCommGroup M] [Module (Int0 v) M] [AddCommGroup M'] [Module (Int0 v) M'], (∀ (c : Int0 v) (x : M), c ≠ 0 → c • x = 0 → x = 0) → (∀ (c : Int0 v) (x : M'), c ≠ 0 → c • x = 0 → x = 0) → ∀ (f : M →ₗ[Int0 v] M') (X' X : Submodule (Int0 v) M), X' ≤ X → X ⊓ LinearMap.ker f ≤ X' → Module.Finite (Int0 v) X → Module.Finite (Int0 v) X' → ∀ r : ℝ, (RelLen v X' X r ↔ RelLen v (X'.map f) (X.map f) r) := by
  first | exact @GlobalTheory.LenMap.relLen_map_iff | exact GlobalTheory.LenMap.relLen_map_iff | (intros; apply GlobalTheory.LenMap.relLen_map_iff <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQMdifferentiableAndIsBoundedAtImInftyStatement
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mdifferentiable_and_isBoundedAtImInfty_of_hasQ : ∀ (N : ℕ) (f : ℍ → ℂ) (a : ℕ → ℂ), 0 < N → HasQ N f a → MDifferentiable 𝓘(ℂ) 𝓘(ℂ) f ∧ UpperHalfPlane.IsBoundedAtImInfty f := by
  first | exact @GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty | exact GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty | (intros; apply GlobalTheory.QFam.hasQ_mdifferentiable_and_isBoundedAtImInfty <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumAbsNormCpowUnitClassesPartialZetaStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_abs_norm_cpow_unitClasses_partialZeta : ∀ (F : Type) [Field F] [NumberField F] (𝔟 : GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) (Zb : ℂ → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.IsPartialZeta (ClassGroup.mk F 𝔟)⁻¹ Zb → ∀ s : ℂ, 1 < s.re → HasSum (fun c : Quotient (GlobalTheory.HeckeTwo.unitRel (𝔟 : FractionalIdeal (NumberField.RingOfIntegers F)⁰ F)) => ((|((Algebra.norm ℚ c.out.1 : ℚ) : ℝ)| : ℝ) : ℂ) ^ (-s)) (((GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.nrm 𝔟 : ℝ) : ℂ) ^ (-s) * Zb s) := by
  first | exact @GlobalTheory.PartialZetaSum.hasSum_norm_cpow | exact GlobalTheory.PartialZetaSum.hasSum_norm_cpow | (intros; apply GlobalTheory.PartialZetaSum.hasSum_norm_cpow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSumLambertDoubleSeriesDivisorsStatement
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasSum_lambert_double_series_divisors : ∀ (e : ℕ) (Q : ℂ) (c : ℕ → ℕ → ℂ), ‖Q‖ < 1 → (∀ d m, ‖c d m‖ ≤ 1) → HasSum (fun k : ℕ => (∑ m ∈ k.divisors, (m : ℂ) ^ e * c (k / m) m) * Q ^ k) (∑' d : ℕ+, ∑' m : ℕ+, ((m : ℕ) : ℂ) ^ e * c d m * Q ^ ((d : ℕ) * (m : ℕ))) := by
  first | exact @GlobalTheory.WpFam.hasSum_lambert | exact GlobalTheory.WpFam.hasSum_lambert | (intros; apply GlobalTheory.WpFam.hasSum_lambert <;> assumption)
end

