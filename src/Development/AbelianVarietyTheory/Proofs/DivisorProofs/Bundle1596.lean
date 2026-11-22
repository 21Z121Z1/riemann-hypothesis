import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1583
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0003
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0107
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0059
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0031
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0123
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelNormConstantSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1569
import Development.AbelianVarietyTheory.Definitions.Divisors.MapSmulOfIsHausdorff

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChgFromBlocksEqOne
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder

namespace GlobalTheory.HermFrame

open Matrix

section Exists

variable {m l n : Type} [Fintype m] [Fintype l] [Fintype n] [DecidableEq m] [DecidableEq l]
  [DecidableEq n]

open scoped MatrixOrder in

theorem exists_chg_eq_one {H : Matrix n n ℂ} (hH : H.PosDef) :
    ∃ R : Matrix n n ℂ, IsUnit R.det ∧ chg R H = 1 := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hH.transpose.posSemidef.nonneg
  have hd : Hᵀ.det ≠ 0 := hH.transpose.det_pos.ne'
  have hu : IsUnit B.det := by
    rw [hB, det_mul] at hd
    exact (right_ne_zero_of_mul hd).isUnit
  refine ⟨B⁻¹, isUnit_nonsing_inv_det _ hu, ?_⟩
  apply transpose_injective
  have e : (chg B⁻¹ H)ᵀ = (B⁻¹)ᴴ * Hᵀ * B⁻¹ := by
    simp only [chg, transpose_mul, transpose_transpose, Matrix.mul_assoc]
  rw [e, hB, star_eq_conjTranspose, conjTranspose_nonsing_inv, Matrix.mul_assoc, Matrix.mul_assoc,
    mul_nonsing_inv _ hu, Matrix.mul_one,
    nonsing_inv_mul _ (by rw [det_conjTranspose]; exact hu.star), transpose_one]

theorem exists_chg_fromBlocks_eq_one {H : Matrix (m ⊕ l) (m ⊕ l) ℂ} (hH : H.PosDef)
    {R : Matrix l l ℂ} (hR : chg R (quotGram H) = 1) :
    ∃ (A : Matrix m m ℂ) (B : Matrix m l ℂ), IsUnit A.det ∧ chg (fromBlocks A B 0 R) H = 1 := by
  obtain ⟨A, hA, hA1⟩ := exists_chg_eq_one (posDef_subGram hH)
  have hs : IsUnit H.toBlocks₁₁.det := (posDef_subGram hH).det_pos.ne'.isUnit
  set B : Matrix m l ℂ := -(orthCoeff H * R) with hBdef
  have hBt : Bᵀ = -(Rᵀ * (H.toBlocks₂₁ * H.toBlocks₁₁⁻¹)) := by
    simp [hBdef, orthCoeff, transpose_mul, transpose_nonsing_inv]
  have hW : Bᵀ * H.toBlocks₁₁ + Rᵀ * H.toBlocks₂₁ = 0 := by
    rw [hBt, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc, nonsing_inv_mul _ hs,
      Matrix.mul_one, neg_add_cancel]
  have hZ : Bᵀ * H.toBlocks₁₂ + Rᵀ * H.toBlocks₂₂ = Rᵀ * quotGram H := by
    rw [hBt, quotGram, Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_assoc, Matrix.mul_assoc]
    abel
  have hherm : (chg (fromBlocks A B 0 R) H).IsHermitian := by
    have := isHermitian_mul_mul_conjTranspose (fromBlocks A B 0 R)ᵀ hH.isHermitian
    rwa [show (fromBlocks A B 0 R)ᵀᴴ = (fromBlocks A B 0 R)ᴴᵀ from rfl] at this
  have e21 : (chg (fromBlocks A B 0 R) H).toBlocks₂₁ = 0 := by
    rw [chg_fromBlocks, toBlocks_fromBlocks₂₁, hW, Matrix.zero_mul]
  have e12 : (chg (fromBlocks A B 0 R) H).toBlocks₁₂ = 0 := by
    have := conjTranspose_toBlocks₁₂ hherm
    rw [e21] at this
    simpa using congrArg conjTranspose this
  have e11 : (chg (fromBlocks A B 0 R) H).toBlocks₁₁ = 1 := by
    rw [chg_fromBlocks, toBlocks_fromBlocks₁₁]; exact hA1
  have e22 : (chg (fromBlocks A B 0 R) H).toBlocks₂₂ = 1 := by
    rw [chg_fromBlocks, toBlocks_fromBlocks₂₂, hW, hZ, Matrix.zero_mul, zero_add]; exact hR
  refine ⟨A, B, hA, ?_⟩
  rw [← fromBlocks_toBlocks (chg (fromBlocks A B 0 R) H), e11, e12, e21, e22, fromBlocks_one]

theorem exists_triangular_chg_eq_one {H : Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ} (hH : H.PosDef) :
    ∃ (A₁ : Matrix m m ℂ) (B : Matrix m (l ⊕ n) ℂ) (A₂ : Matrix l l ℂ) (C : Matrix l n ℂ)
      (A₃ : Matrix n n ℂ), IsUnit A₁.det ∧ IsUnit A₂.det ∧ IsUnit A₃.det ∧
        chg (fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)) H = 1 := by
  have hQ := posDef_quotGram hH
  obtain ⟨A₃, h₃, e₃⟩ := exists_chg_eq_one (posDef_quotGram hQ)
  obtain ⟨A₂, C, h₂, e₂⟩ := exists_chg_fromBlocks_eq_one hQ e₃
  obtain ⟨A₁, B, h₁, e₁⟩ := exists_chg_fromBlocks_eq_one hH e₂
  exact ⟨A₁, B, A₂, C, A₃, h₁, h₂, h₃, e₁⟩

theorem chg_submatrix_first (A₁ : Matrix m m ℂ) (B : Matrix m (l ⊕ n) ℂ) (A₂ : Matrix l l ℂ)
    (C : Matrix l n ℂ) (A₃ : Matrix n n ℂ) (H : Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ) :
    (chg (fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)) H).submatrix (Sum.map id Sum.inl)
        (Sum.map id Sum.inl) =
      chg (fromBlocks A₁ (B.submatrix id Sum.inl) 0 A₂)
        (H.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) := by
  set J : Matrix (m ⊕ (l ⊕ n)) (m ⊕ l) ℂ :=
    (1 : Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ).submatrix id (Sum.map id Sum.inl) with hJ
  have h0 : ∀ T : Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ,
      chg (T.submatrix id (Sum.map id Sum.inl)) H =
        (chg T H).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl) := fun T => by
    have := chg_submatrix T H (Equiv.refl _) (Sum.map id Sum.inl : m ⊕ l → m ⊕ (l ⊕ n))
    simpa using this
  have h1 : H.submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl) = chg J H := by
    rw [hJ, h0, chg_one]
  have h2 : (fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)).submatrix id (Sum.map id Sum.inl)
      = J * fromBlocks A₁ (B.submatrix id Sum.inl) 0 A₂ := by
    ext (a | a | a) (b | b) <;>
      simp [hJ, mul_apply, Fintype.sum_sum_type, one_apply]
  rw [h1, chg_chg, ← h2, h0]

end Exists

section Forms

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
  [IsScalarTower ℝ ℂ E] {m l n : Type} [Fintype m] [Fintype l] [Fintype n] [DecidableEq m]
  [DecidableEq l] [DecidableEq n]

theorem extTrace_eq_sum_of_eq_one {K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
    (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (h1 : K z = 1) (ξ η : E) :
    extTrace K z ξ η = kappa * ∑ a : m, ∑ b : l,
      mdel K z ξ (Sum.inl a) (Sum.inr b) * star (mdel K z η (Sum.inl a) (Sum.inr b)) := by
  have hs : subGram (1 : Matrix (m ⊕ l) (m ⊕ l) ℂ) = 1 := by
    ext a b; simp [subGram, toBlocks₁₁, one_apply]
  have hq : quotGram (1 : Matrix (m ⊕ l) (m ⊕ l) ℂ) = 1 := by
    have e1 : (1 : Matrix (m ⊕ l) (m ⊕ l) ℂ).toBlocks₂₁ = 0 := by
      ext a b; simp [toBlocks₂₁, one_apply]
    have e2 : (1 : Matrix (m ⊕ l) (m ⊕ l) ℂ).toBlocks₂₂ = 1 := by
      ext a b; simp [toBlocks₂₂, one_apply]
    rw [quotGram, e1, e2]; simp
  have hb : ∀ ξ, secondForm K z ξ = (mdel K z ξ).toBlocks₁₂ᵀ := fun ξ => by
    rw [secondForm_eq, conn, h1, transpose_one, inv_one, Matrix.one_mul]; rfl
  rw [extTrace_eq h hp, secondFormAdj, h1, hs, hq, hb, hb, adj]
  simp only [transpose_one, inv_one, Matrix.one_mul, Matrix.mul_one, trace, diag_apply, mul_apply,
    transpose_apply, conjTranspose_apply, toBlocks₁₂, of_apply]
  rw [Finset.sum_comm]

theorem mdel_quotGram_of_eq_one {K : E → Matrix (m ⊕ l) (m ⊕ l) ℂ} {z : E}
    (h : MContDiffAt 1 K z) (h1 : K z = 1) (ξ : E) :
    mdel (fun x => quotGram (K x)) z ξ = (mdel K z ξ).toBlocks₂₂ := by
  have hu : IsUnit (subGram (K z)).det := by
    have : subGram (K z) = 1 := by rw [h1]; ext a b; simp [subGram, toBlocks₁₁, one_apply]
    rw [this]; simp
  have e12 : (K z).toBlocks₁₂ = 0 := by rw [h1]; ext a b; simp [toBlocks₁₂, one_apply]
  have e21 : (K z).toBlocks₂₁ = 0 := by rw [h1]; ext a b; simp [toBlocks₂₁, one_apply]
  have h21 : MContDiffAt 1 (fun x => (K x).toBlocks₂₁) z := h.submatrix Sum.inr Sum.inl
  have h12 : MContDiffAt 1 (fun x => (K x).toBlocks₁₂) z := h.submatrix Sum.inl Sum.inr
  have h22 : MContDiffAt 1 (fun x => (K x).toBlocks₂₂) z := h.submatrix Sum.inr Sum.inr
  have h11 : MContDiffAt 1 (fun x => (K x).toBlocks₁₁⁻¹) z := h.subGram.inv hu
  have hP := h21.mul h11
  have e : (fun x => quotGram (K x)) =
      fun x => (K x).toBlocks₂₂ + -((K x).toBlocks₂₁ * (K x).toBlocks₁₁⁻¹ * (K x).toBlocks₁₂) := by
    funext x; rw [quotGram, sub_eq_add_neg]
  rw [e, mdel_add h22 (hP.mul h12).neg, mdel_neg, mdel_mul hP h12, e12, e21]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, neg_zero]
  rfl

theorem extTrace_add_of_eq_one {K : E → Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ} {z : E}
    (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef) (h1 : K z = 1) (ξ η : E) :
    extTrace (fun x => (K x).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) z ξ η +
        extTrace (fun x => (K x).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) z ξ η =
      extTrace K z ξ η + extTrace (fun x => quotGram (K x)) z ξ η := by
  have hf : Function.Injective (Sum.map id Sum.inl : m ⊕ l → m ⊕ (l ⊕ n)) :=
    Function.injective_id.sumMap Sum.inl_injective
  have he := (Equiv.sumAssoc m l n).injective
  have hsub : subGram (K z) = 1 := by rw [h1]; ext a b; simp [subGram, toBlocks₁₁, one_apply]
  have hu : IsUnit (subGram (K z)).det := by rw [hsub]; simp
  have hq : quotGram (K z) = 1 := by
    have e1 : (K z).toBlocks₂₁ = 0 := by rw [h1]; ext a b; simp [toBlocks₂₁, one_apply]
    have e2 : (K z).toBlocks₂₂ = 1 := by rw [h1]; ext a b; simp [toBlocks₂₂, one_apply]
    rw [quotGram, e1, e2]; simp
  rw [extTrace_eq_sum_of_eq_one (h.submatrix _ _) (hp.mono fun x hx => hx.submatrix hf)
      (by rw [h1]; exact submatrix_one _ hf),
    extTrace_eq_sum_of_eq_one (h.submatrix _ _) (hp.mono fun x hx => hx.submatrix he)
      (by rw [h1]; exact submatrix_one _ he),
    extTrace_eq_sum_of_eq_one h hp h1,
    extTrace_eq_sum_of_eq_one (h.quotGram hu) (hp.mono fun x hx => posDef_quotGram hx) hq,
    mdel_quotGram_of_eq_one h h1, mdel_quotGram_of_eq_one h h1]
  simp only [Fintype.sum_sum_type, Finset.sum_add_distrib, mdel_apply, submatrix_apply,
    Sum.map_inl, Sum.map_inr, id, Equiv.sumAssoc_apply_inl_inl, Equiv.sumAssoc_apply_inl_inr,
    Equiv.sumAssoc_apply_inr, toBlocks₂₂, of_apply]
  ring

variable {K : E → Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ} {z : E}

theorem extTrace_add_chg (h : MContDiffAt 1 K z) (hp : ∀ᶠ x in 𝓝 z, (K x).PosDef)
    {A₁ : Matrix m m ℂ} (B : Matrix m (l ⊕ n) ℂ) {A₂ : Matrix l l ℂ} (C : Matrix l n ℂ)
    {A₃ : Matrix n n ℂ} (h₁ : IsUnit A₁.det) (h₂ : IsUnit A₂.det) (h₃ : IsUnit A₃.det) :
    let A := fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)
    extTrace (fun x => (chg A (K x)).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) z =
        extTrace (fun x => (K x).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) z ∧
      extTrace (fun x => (chg A (K x)).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) z =
        extTrace (fun x => (K x).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) z ∧
      extTrace (fun x => chg A (K x)) z = extTrace K z ∧
      extTrace (fun x => quotGram (chg A (K x))) z = extTrace (fun x => quotGram (K x)) z := by
  intro A
  have hf : Function.Injective (Sum.map id Sum.inl : m ⊕ l → m ⊕ (l ⊕ n)) :=
    Function.injective_id.sumMap Sum.inl_injective
  have he := (Equiv.sumAssoc m l n).injective
  have hA₂ : IsUnit (fromBlocks A₂ C 0 A₃).det := by
    rw [det_fromBlocks_zero₂₁]; exact h₂.mul h₃
  have hA : IsUnit A.det := by
    simp only [A]; rw [det_fromBlocks_zero₂₁]; exact h₁.mul hA₂
  have hs : IsUnit (subGram (K z)).det := (posDef_subGram hp.self_of_nhds).det_pos.ne'.isUnit
  refine ⟨?_, ?_, ?_, ?_⟩
  · have e : (fun x => (chg A (K x)).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) =
        fun x => chg (fromBlocks A₁ (B.submatrix id Sum.inl) 0 A₂)
          ((K x).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) :=
      funext fun x => chg_submatrix_first A₁ B A₂ C A₃ (K x)
    rw [e]
    refine extTrace_chg (A := fun _ => fromBlocks A₁ (B.submatrix id Sum.inl) 0 A₂)
      (h.submatrix _ _) (hp.mono fun x hx => hx.submatrix hf) (mContDiffAt_const _)
      (by rw [det_fromBlocks_zero₂₁]; exact h₁.mul h₂) (fun η => mdbar_const _ _ _)
      (.of_forall fun _ => toBlocks_fromBlocks₂₁ _ _ _ _)
  · have e : (fun x => (chg A (K x)).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) =
        fun x => chg (A.submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n))
          ((K x).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) :=
      funext fun x => (chg_submatrix A (K x) (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)).symm
    rw [e]
    refine extTrace_chg (A := fun _ => A.submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n))
      (h.submatrix _ _) (hp.mono fun x hx => hx.submatrix he) (mContDiffAt_const _)
      (by rw [det_submatrix_equiv_self]; exact hA) (fun η => mdbar_const _ _ _)
      (.of_forall fun _ => ?_)
    ext a (b | b) <;> simp [A, toBlocks₂₁]
  · exact extTrace_chg (A := fun _ => A) h hp (mContDiffAt_const _) hA
      (fun η => mdbar_const _ _ _) (.of_forall fun _ => toBlocks_fromBlocks₂₁ _ _ _ _)
  · rw [extTrace_congr (K' := fun x => chg (fromBlocks A₂ C 0 A₃) (quotGram (K x)))
      (hp.mono fun x hx => quotGram_chg B _ h₁ (posDef_subGram hx).det_pos.ne'.isUnit)]
    exact extTrace_chg (A := fun _ => fromBlocks A₂ C 0 A₃) (h.quotGram hs)
      (hp.mono fun x hx => posDef_quotGram hx) (mContDiffAt_const _) hA₂
      (fun η => mdbar_const _ _ _) (.of_forall fun _ => toBlocks_fromBlocks₂₁ _ _ _ _)

end Forms

theorem extTrace_add_extTrace :
    ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]
      (m l n : Type) [Fintype m] [Fintype l] [Fintype n] [DecidableEq m] [DecidableEq l]
      [DecidableEq n] (K : E → Matrix (m ⊕ (l ⊕ n)) (m ⊕ (l ⊕ n)) ℂ) (z ξ η : E),
      MContDiffAt 1 K z → (∀ᶠ x in 𝓝 z, (K x).PosDef) →
      extTrace (fun x => (K x).submatrix (Sum.map id Sum.inl) (Sum.map id Sum.inl)) z ξ η +
          extTrace (fun x => (K x).submatrix (Equiv.sumAssoc m l n) (Equiv.sumAssoc m l n)) z ξ η =
        extTrace K z ξ η + extTrace (fun x => quotGram (K x)) z ξ η := by
  intro E _ _ _ _ m l n _ _ _ _ _ _ K z ξ η h hp
  obtain ⟨A₁, B, A₂, C, A₃, h₁, h₂, h₃, e⟩ := exists_triangular_chg_eq_one hp.self_of_nhds
  obtain ⟨t₁, t₂, t₃, t₄⟩ := extTrace_add_chg h hp B C h₁ h₂ h₃
  have hA : IsUnit (fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)).det := by
    rw [det_fromBlocks_zero₂₁, det_fromBlocks_zero₂₁]; exact h₁.mul (h₂.mul h₃)
  have := extTrace_add_of_eq_one (K := fun x => chg (fromBlocks A₁ B 0 (fromBlocks A₂ C 0 A₃)) (K x))
    (((mContDiffAt_const _).mul h).mul (mContDiffAt_const _))
    (hp.mono fun x hx => posDef_chg ((isUnit_iff_isUnit_det _).2 hA) hx) e ξ η
  rwa [t₁, t₂, t₃, t₄] at this

end GlobalTheory.HermFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmEllipticCurveGaloisTorsionSections
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PureLift
open scoped CategoryTheory.Obj

namespace GlobalTheory.TorsionModel

theorem exists_galois (B : Type) [CommRing B] [Module.Finite ℤ B] :
    ∃ (N : IntermediateField ℚ ℂ) (_ : NumberField N) (_ : IsGalois ℚ N), ∀ χ : B →+* ℂ,
      ∃ χ' : B →+* 𝓞 N, ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)).comp χ' = χ := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := B)
  have hi : ∀ b : B, IsIntegral ℤ b := fun b => IsIntegral.of_finite ℤ b
  choose p hp hp' using hi
  let q : Polynomial ℚ := (∏ b ∈ s, p b).map (algebraMap ℤ ℚ)
  have hq : q.Monic := (Polynomial.monic_prod_of_monic _ _ fun b _ => hp b).map _
  let N : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (q.rootSet ℂ)
  have hN : Polynomial.IsSplittingField ℚ N q :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have : FiniteDimensional ℚ N := Polynomial.IsSplittingField.finiteDimensional N q
  have : Normal ℚ N := Normal.of_isSplittingField q
  have : NumberField N := ⟨⟩
  refine ⟨N, inferInstance, ⟨⟩, fun χ => ?_⟩
  have hm : ∀ b, χ b ∈ N := fun b => by
    have hb : b ∈ Submodule.span ℤ (s : Set B) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem c hc =>
      refine IntermediateField.subset_adjoin ℚ _ (Polynomial.mem_rootSet.2 ⟨hq.ne_zero, ?_⟩)
      rw [Polynomial.aeval_map_algebraMap, map_prod]
      refine Finset.prod_eq_zero hc ?_
      have h := congrArg χ (hp' c)
      rw [Polynomial.hom_eval₂, map_zero] at h
      rw [Polynomial.aeval_def, ← h]
      congr 1
      exact RingHom.ext_int _ _
    | zero => rw [map_zero]; exact zero_mem _
    | add _ _ _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul r c _ hc => rw [map_zsmul]; exact zsmul_mem hc r
  let χ₁ : B →+* N := χ.codRestrict N hm
  exact ⟨χ₁.codRestrict (integralClosure ℤ N) fun b => (IsIntegral.of_finite ℤ b).map χ₁.toIntAlgHom, rfl⟩

theorem exists_finite_ring {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) [IsFinite q] :
    ∃ (B : Type) (_ : CommRing B) (g : R →+* B) (e : Sp B ≅ Z), g.Finite ∧ e.hom ≫ q = spMap g := by
  have : IsAffine Z := isAffine_of_isAffineHom q
  obtain ⟨g, hg⟩ := Spec.map_surjective (Z.isoSpec.inv ≫ q)
  refine ⟨Γ(Z, ⊤), inferInstance, g.hom, Z.isoSpec.symm, ?_, hg.symm⟩
  have : IsFinite (Spec.map g) := by rw [hg]; infer_instance
  exact (IsFinite.SpecMap_iff g).1 this

theorem exists_integral_points (hM : Out.MulNSt) {R : Type} [CommRing R] [Module.Finite ℤ R] (P : Out.PolAV (Sp R))
    (σ : R →+* ℂ) {n : ℕ} (hn : 1 ≤ n) :
    ∃ (N : IntermediateField ℚ ℂ) (_ : NumberField N) (_ : IsGalois ℚ N) (f : R →+* 𝓞 N),
      ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)).comp f = σ ∧ ∀ x : Over.mk (spMap σ) ⟶ P.A, x ^ n = 1 →
        ∃ y : Over.mk (spMap f) ⟶ P.A, y ^ n = 1 ∧
          spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left = x.left := by
  have : IsNoetherianRing R := IsNoetherianRing.of_finite ℤ R
  have := (hM _ P n hn).1
  let η₀ : Sp R ⟶ P.A.left := (η[P.A]).left
  have hη : η₀ ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  have hw : (Out.mulA P.A n).left ≫ P.A.hom = P.A.hom := Over.w _
  have key : ∀ {T : Over (Sp R)} (x : T ⟶ P.A), x ^ n = 1 ↔ x.left ≫ (Out.mulA P.A n).left = T.hom ≫ η₀ := by
    intro T x
    have e₁ : x ≫ Out.mulA P.A n = x ^ n := by rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
    have e₂ : (1 : T ⟶ P.A).left = T.hom ≫ η₀ := by rw [Hom.one_def]; simp [η₀]
    rw [← Over.comp_left, e₁, ← e₂]
    exact ⟨fun h => by rw [h], Over.OverMorphism.ext⟩
  obtain ⟨B, _, g, e, hg, he⟩ := exists_finite_ring (pullback.snd (Out.mulA P.A n).left η₀)
  have : Module.Finite ℤ B := by
    have h := RingHom.Finite.comp hg (RingHom.finite_algebraMap.2 (inferInstance : Module.Finite ℤ R))
    rw [RingHom.ext_int (g.comp _) (algebraMap ℤ B)] at h
    exact RingHom.finite_algebraMap.1 h
  obtain ⟨N, _, _, hN⟩ := exists_galois B
  have main : ∀ x : Over.mk (spMap σ) ⟶ P.A, x ^ n = 1 → ∃ χ' : B →+* 𝓞 N,
      (∀ r, ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) (χ' (g r)) = σ r) ∧
      spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ spMap χ' ≫ e.hom ≫ pullback.fst _ _ = x.left := by
    intro x hx
    obtain ⟨χ, hχ⟩ := Spec.map_surjective (pullback.lift x.left (spMap σ) ((key x).1 hx) ≫ e.inv)
    obtain ⟨χ', h⟩ := hN χ.hom
    have e₁ : spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ spMap χ' = Spec.map χ :=
      Ex.UnifModel.spMap_comp fun r => congr($h r)
    refine ⟨χ', fun r => ?_, by rw [reassoc_of% e₁, hχ, Category.assoc, e.inv_hom_id_assoc, pullback.lift_fst]⟩
    have e₂ : Spec.map χ ≫ spMap g = spMap σ := by
      rw [← he, hχ, Category.assoc, e.inv_hom_id_assoc, pullback.lift_snd]
    rw [← Spec.map_comp] at e₂
    exact (congr($h (g r))).trans (congrArg (fun f => f.hom r) (Spec.map_injective e₂))
  obtain ⟨χ₀, h₀, -⟩ := main 1 (one_pow n)
  refine ⟨N, inferInstance, inferInstance, χ₀.comp g, RingHom.ext h₀, fun x hx => ?_⟩
  obtain ⟨χ', h₁, h₂⟩ := main x hx
  have e₁ : spMap χ' ≫ spMap g = spMap (χ₀.comp g) := Ex.UnifModel.spMap_comp fun r =>
    RingOfIntegers.coe_injective ((algebraMap N ℂ).injective ((h₁ r).trans (h₀ r).symm))
  have e₂ : (spMap χ' ≫ e.hom ≫ pullback.fst _ _) ≫ (Out.mulA P.A n).left = spMap (χ₀.comp g) ≫ η₀ := by
    rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% he, reassoc_of% e₁]
  exact ⟨Over.homMk (spMap χ' ≫ e.hom ≫ pullback.fst _ _) (by
    rw [← hw, ← Category.assoc, e₂, Category.assoc, hη]; exact Category.comp_id _), (key _).2 e₂, h₂⟩

theorem exists_ell_fibre {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    ∃ (M : IntermediateField ℚ ℂ) (_ : NumberField M) (ω : 𝓞 M) (C : GlobalTheory.CM.Ell H (𝓞 M) ω) (C₀ : GlobalTheory.CompRat.Curve H)
      (ψ : C₀.P.A.left ⟶ C.P.A.left), (2 * ω - 1) ^ 2 = -(H.d : 𝓞 M) ∧
      IsGrpPullback C₀.P.A C.P.A (spMap ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M))) ψ := by
  have : NeZero H.d := ⟨H.d_prime.ne_zero⟩
  obtain ⟨χ, hχ⟩ := exists_isKroneckerChar (d := H.d) H.d_prime.ne_zero (Or.inr (by have := H.d_mod; omega))
  obtain ⟨M, _, ω, C, -, hω, hC, -⟩ := CM.EllExists.exists_ell cmCurve_closed thetaUnifAV_all firstFiveLaws.1
    (CM.homExtDvr_of_card_torsion GlobalTheory.UU.TorsionCount.card_torsion_points_unconditional) E H χ hχ H.rt0 H.sqrt_neg_disc_sq
  obtain ⟨Q, ψ, hψ⟩ := exists_isPolFibre firstFiveLaws.1.polBaseChange
    ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) C.P
  obtain ⟨u, hu⟩ := PureType.exists_isThetaUnif thetaUnifAV_all Q
  obtain ⟨c, hc, hΛ⟩ := hC Q ψ hψ u
  refine ⟨M, inferInstance, ω, C, ⟨Q, hψ.1.trans C.dim, u, hu, c, hc, hΛ⟩, ψ, ?_, hψ.2.1⟩
  refine RingOfIntegers.coe_injective ((algebraMap M ℂ).injective ?_)
  rw [← RingHom.comp_apply, ← RingHom.comp_apply]
  rw [map_pow, map_sub, map_mul, map_one, map_ofNat, map_neg, map_natCast, ← H.sqrt_neg_disc_sq, ← hω]
  rfl

theorem exists_ell_torsion_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (n : ℕ), 0 < n → ∃ (N : IntermediateField ℚ ℂ) (_ : NumberField N) (_ : IsGalois ℚ N) (ω : 𝓞 N) (C : GlobalTheory.CM.Ell H (𝓞 N) ω) (C₀ : GlobalTheory.CompRat.Curve H) (ψ : C₀.P.A.left ⟶ C.P.A.left), (2 * ω - 1) ^ 2 = -(H.d : 𝓞 N) ∧ IsGrpPullback C₀.P.A C.P.A (spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ψ ∧ ∀ a : ℤ × ℤ, ∃ y : Over.mk (𝟙 (Sp (𝓞 N))) ⟶ C.P.A, y ^ n = 1 ∧ C₀.pt (GlobalTheory.CompRat.wC H a / n) ≫ ψ = spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ y.left := by
  intro E _ _ _ H n hn
  obtain ⟨M, _, ω, C, C₀, ψ, hω, hψ⟩ := exists_ell_fibre H
  obtain ⟨N, _, _, f, hf, hN⟩ := exists_integral_points firstFiveLaws.1.mulN C.P
    ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) hn
  obtain ⟨C', φ, -, ⟨-, hφ, -⟩, -⟩ := CM.exists_ellMap firstFiveLaws.1.polBaseChange E H _ ω C _ f
  have e : spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N)) ≫ spMap f =
      spMap ((algebraMap M ℂ).comp (algebraMap (𝓞 M) M)) := Ex.UnifModel.spMap_comp fun r => congr($hf r)
  have w : ψ ≫ C.P.A.hom = (C₀.P.A.hom ≫ spMap ((algebraMap N ℂ).comp (algebraMap (𝓞 N) N))) ≫ spMap f := by
    rw [Category.assoc, e, hψ.1.w]
  refine ⟨N, inferInstance, inferInstance, f ω, C', C₀, hφ.1.lift _ _ w, by simpa [map_ofNat] using congrArg f hω,
    hφ.cancel (hψ.congr e.symm (hφ.1.lift_fst _ _ w).symm) (hφ.1.lift_snd _ _ w), fun a => ?_⟩
  obtain ⟨ε, hε⟩ := exists_mulEquiv_of_isGrpPullback hψ (𝟙 (Sp ℂ)) _ (Category.id_comp _).symm
  obtain ⟨ε', hε'⟩ := exists_mulEquiv_of_isGrpPullback hφ (𝟙 (Sp (𝓞 N))) _ (Category.id_comp _).symm
  obtain ⟨y, hy, hy'⟩ := hN (ε (C₀.u.ex fun _ => C₀.c * (CompRat.wC H a / n))) (by
    rw [← map_pow]
    exact (congrArg ε (CurveField.ex_pow_eq_one C₀ hn a)).trans (map_one ε))
  obtain ⟨z, rfl⟩ := ε'.surjective y
  rw [hε, hε'] at hy'
  refine ⟨z, ε'.injective (by rw [map_pow, hy, map_one]), ?_⟩
  have ho : C₀.pt (CompRat.wC H a / n) ≫ C₀.P.A.hom = 𝟙 _ := Over.w (C₀.u.ex fun _ => C₀.c * (CompRat.wC H a / n))
  have hz : z.left ≫ C'.P.A.hom = 𝟙 (Sp (𝓞 N)) := Over.w z
  refine hφ.1.hom_ext ?_ ?_
  · rw [Category.assoc, hφ.1.lift_fst, Category.assoc]
    exact hy'.symm
  · rw [Category.assoc, hφ.1.lift_snd, Category.assoc, hz, reassoc_of% ho]
    exact (Category.comp_id _).symm

end GlobalTheory.TorsionModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteIndexSubgroupAutExtendSepClosure
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SepExt

open Polynomial

theorem mem_fieldRange (K L Ω Ω' : Type) [Field K] [Field L] [Field Ω] [Field Ω'] [Algebra K L]
    [Algebra K Ω] [IsSepClosed Ω] [Algebra L Ω'] [Algebra K Ω'] [IsScalarTower K L Ω']
    (j : Ω →ₐ[K] Ω') (a : L) (ha : IsSeparable K a) :
    IsScalarTower.toAlgHom K L Ω' a ∈ j.fieldRange := by
  set p := minpoly K a
  have hp0 : p ≠ 0 := minpoly.ne_zero ha.isIntegral
  have hsplit : (p.map (algebraMap K Ω)).Splits := IsSepClosed.splits_codomain p ha
  have hne : p.map (algebraMap K Ω') ≠ 0 := (Polynomial.map_ne_zero_iff (algebraMap K Ω').injective).2 hp0
  have himg := Splits.image_rootSet_of_map_ne_zero hsplit j hne
  have hroot : IsScalarTower.toAlgHom K L Ω' a ∈ p.rootSet Ω' := by
    rw [mem_rootSet_of_ne hp0, aeval_algHom_apply, minpoly.aeval, map_zero]
  rw [← himg] at hroot
  obtain ⟨w, -, hw⟩ := hroot
  exact (AlgHom.mem_fieldRange).2 ⟨w, hw⟩

end GlobalTheory.SepExt

namespace GlobalTheory.SepExt

open Polynomial

theorem exists_finiteIndex_extend : ∀ (K L Ω Ω' : Type) [Field K] [Field L] [Field Ω] [Field Ω'] [Algebra K L] [FiniteDimensional K L] [Algebra K Ω] [IsSepClosure K Ω] [Algebra L Ω'] [IsSepClosure L Ω'] [Algebra K Ω'] [IsScalarTower K L Ω'] (j : Ω →ₐ[K] Ω'), ∃ H : Subgroup (Ω ≃ₐ[K] Ω), H.FiniteIndex ∧ ∀ σ ∈ H, ∃ σ' : Ω' ≃ₐ[L] Ω', ∀ x, σ' (j x) = j (σ x) := by
  intro K L Ω Ω' _ _ _ _ _ _ _ _ _ _ _ _ j
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  let Ls : IntermediateField K L := separableClosure K L
  let ψ : Ls →ₐ[K] Ω' := (IsScalarTower.toAlgHom K L Ω').comp Ls.val
  have hmem : ∀ a : Ls, ψ a ∈ j.fieldRange := fun a =>
    mem_fieldRange K L Ω Ω' j a ((mem_separableClosure_iff).1 a.2)
  let e : Ω ≃ₐ[K] j.fieldRange := AlgEquiv.ofInjectiveField j
  let φ : Ls →ₐ[K] Ω := e.symm.toAlgHom.comp (ψ.codRestrict j.fieldRange.toSubalgebra hmem)
  have hφ : ∀ a : Ls, j (φ a) = ψ a := by
    intro a
    have h := congrArg Subtype.val (e.apply_symm_apply ⟨ψ a, hmem a⟩)
    exact h
  let E : IntermediateField K Ω := φ.fieldRange
  have : FiniteDimensional K E :=
    (AlgEquiv.ofInjectiveField φ).toLinearEquiv.finiteDimensional
  have : Finite ((Ω ≃ₐ[K] Ω) ⧸ E.fixingSubgroup) :=
    Subgroup.quotient_finite_of_isOpen _ E.fixingSubgroup_isOpen
  refine ⟨E.fixingSubgroup, Subgroup.finiteIndex_of_finite_quotient, fun σ hσ => ?_⟩
  let A := AlgebraicClosure Ω'
  letI : Algebra Ω A := ((algebraMap Ω' A).comp j.toRingHom).toAlgebra
  haveI : IsScalarTower K Ω A := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap K A x = algebraMap Ω' A (j (algebraMap K Ω x))
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.IsAlgebraic K Ω' := Algebra.IsAlgebraic.trans K L Ω'
  haveI : IsAlgClosure K A := IsAlgClosure.ofAlgebraic K Ω' A
  haveI : Normal K A := IsAlgClosure.normal K A
  let τ : A ≃ₐ[K] A := σ.liftNormal A
  have hτ : ∀ x : Ω, τ (algebraMap Ω' A (j x)) = algebraMap Ω' A (j (σ x)) := fun x =>
    AlgEquiv.liftNormal_commutes σ A x
  have hfixL : ∀ a : L, τ (algebraMap L A a) = algebraMap L A a := by
    have hinj := IsPurelyInseparable.injective_comp_algebraMap Ls L A
    have heq : (τ.toRingEquiv.toRingHom.comp (algebraMap L A)).comp (algebraMap Ls L) =
        (algebraMap L A).comp (algebraMap Ls L) := by
      ext a
      have h1 : algebraMap L A (algebraMap Ls L a) = algebraMap Ω' A (j (φ a)) := by
        rw [hφ]; exact IsScalarTower.algebraMap_apply L Ω' A _
      have h2 : σ (φ a) = φ a :=
        (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ _ ⟨a, rfl⟩
      simp only [RingHom.comp_apply]
      rw [h1]
      change τ (algebraMap Ω' A (j (φ a))) = _
      rw [hτ, h2]
    exact fun a => congrArg (fun f : L →+* A => f a) (hinj heq)
  let τL : A ≃ₐ[L] A := { τ.toRingEquiv with commutes' := hfixL }
  refine ⟨τL.restrictNormal Ω', fun x => ?_⟩
  apply (algebraMap Ω' A).injective
  rw [AlgEquiv.restrictNormal_commutes]
  exact hτ x

end GlobalTheory.SepExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthonormalBasisDefiniteHermitianSpaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField Matrix MvPolynomial
open scoped TensorProduct nonZeroDivisors
open GlobalTheory.SignedHC GlobalTheory.ChiGrid Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.FunObj
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthonormalBasis_definite_hermitianSpace : ∀ (D : D7) (V : HSp D), V.SigOK → (∀ τ, V.sig τ = (V.rank, 0)) →
    ∃ fr : GL (Fin V.rank) D.host.E, Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) fr.1 * V.gram * fr.1 = 1 := by
  first | exact @GlobalTheory.DefiniteFrame.exists_unitary_frame | exact GlobalTheory.DefiniteFrame.exists_unitary_frame | (intros; apply GlobalTheory.DefiniteFrame.exists_unitary_frame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateModuleLevelComponentEqOfCardTorsionStatement
section
open GlobalTheory.HTLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tateModule_levelComponent_eq_of_card_torsion : ∀ (M : Type) [CommGroup M] (l : ℕ) [Fact l.Prime] (c : ℕ), (∀ k : ℕ, Nat.card {x : M // x ^ (l ^ k) = 1} = l ^ (c * k)) → ∀ (N : ℕ) (x : M), x ^ (l ^ N) = 1 → ∃ t : Tate l M, t.lev N = x := by
  first | exact @GlobalTheory.exists_tate_lev_eq_of_card_torsion | exact GlobalTheory.exists_tate_lev_eq_of_card_torsion | (intros; apply GlobalTheory.exists_tate_lev_eq_of_card_torsion <;> assumption)
end

