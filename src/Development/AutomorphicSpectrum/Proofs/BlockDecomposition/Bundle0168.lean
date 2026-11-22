import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0163
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0141
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0156
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0157
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0154
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TorusJacobianDet
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.Cone

theorem dlog_ratio_det {K R : Type} [Field K] [CommRing R] [Algebra K R] (n : ℕ) (t : Fin (n + 1) → Rˣ)
    (D : Fin (n + 1) → Derivation K R R) (hD : ∀ k j, D k (t j) = if k = j then 1 else 0) :
    let g : Fin (n + 1) → R := fun k => if h : (k : ℕ) = 0 then ((t 0)⁻¹ : Rˣ) else
      (t ⟨k - 1, by omega⟩ : R) * ((t k)⁻¹ : Rˣ)
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = (((∏ k, t k)⁻¹ : Rˣ) : R) ∨
    Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det = -(((∏ k, t k)⁻¹ : Rˣ) : R) := by
  intro g
  set u : Fin (n + 1) → R := fun j => (((t j)⁻¹ : Rˣ) : R) with hu
  have htu : ∀ j, (t j : R) * u j = 1 := fun j => by simp [hu]
  have hDu : ∀ k j, D k (u j) = if k = j then -(u j * u j) else 0 := by
    intro k j
    have h2 := (D k).leibniz_of_mul_eq_one (a := u j) (b := (t j : R)) (by rw [mul_comm]; exact htu j)
    rw [h2, hD k j]
    split_ifs <;> simp [pow_two]
  have hg0 : g 0 = u 0 := by simp [g, hu]
  have hgs : ∀ (l : Fin (n + 1)) (h : (l : ℕ) ≠ 0), g l = (t ⟨l - 1, by omega⟩ : R) * u l := by
    intro l h
    exact dif_neg h
  have hgu : ∀ l, IsUnit (g l) := by
    intro l
    by_cases h : (l : ℕ) = 0
    · simp only [g, h, dite_true]; exact Units.isUnit _
    · simp only [g, h, dite_false]; exact (Units.isUnit _).mul (Units.isUnit _)
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    Matrix.of fun k l => if k = l then -1 else if (k : ℕ) + 1 = l then 1 else 0
  have hM : (Matrix.of fun k l => D k (g l)) = Matrix.diagonal u * B * Matrix.diagonal g := by
    ext k l
    rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
    simp only [Matrix.of_apply, B]
    by_cases h : (l : ℕ) = 0
    · have hl : l = 0 := Fin.ext h
      subst hl
      have hk : ¬ ((k : ℕ) + 1 = ((0 : Fin (n + 1)) : ℕ)) := by simp
      rw [hg0, hDu k 0]
      by_cases hk0 : k = 0
      · subst hk0; simp
      · simp [hk0]
    · rw [hgs l h, Derivation.leibniz, hDu k l, hD k _]
      simp only [smul_eq_mul]
      by_cases hkl : k = l
      · subst hkl
        have hne : k ≠ ⟨(k : ℕ) - 1, by omega⟩ := by
          intro e
          have := congrArg Fin.val e
          simp at this
          omega
        simp only [if_true, hne, if_false]
        ring
      · by_cases hs : (k : ℕ) + 1 = l
        · have hp : k = ⟨(l : ℕ) - 1, by omega⟩ := Fin.ext (by simp; omega)
          rw [if_neg hkl, if_pos hp, if_neg hkl, if_pos hs, ← hp]
          have := htu k
          linear_combination (-(u l)) * this
        · have hp : k ≠ ⟨(l : ℕ) - 1, by omega⟩ := by
            intro e
            have := congrArg Fin.val e
            simp at this
            omega
          rw [if_neg hkl, if_neg hp, if_neg hkl, if_neg hs]
          simp
  have hB : B.det = (-1) ^ (n + 1) := by
    rw [Matrix.det_of_upperTriangular]
    · simp [B]
    · intro i j hij
      have : (j : ℕ) < i := hij
      have h1 : i ≠ j := fun h => by simp [h] at this
      have h2 : ¬ ((i : ℕ) + 1 = j) := by omega
      simp [B, h1, h2]
  have hprod : ∏ k, u k = (((∏ k, t k)⁻¹ : Rˣ) : R) := by
    simp only [hu, ← Units.coe_prod, Finset.prod_inv_distrib]
  have hU : IsUnit (∏ k, g k) := by
    obtain ⟨v, hv⟩ := IsUnit.prod_univ_iff.2 hgu
    exact hv ▸ v.isUnit
  have hcan : Ring.inverse (∏ k, g k) * (∏ k, g k) = 1 := Ring.inverse_mul_cancel _ hU
  have key : Ring.inverse (∏ k, g k) * (Matrix.of fun k l => D k (g l)).det =
      (-1) ^ (n + 1) * (((∏ k, t k)⁻¹ : Rˣ) : R) := by
    rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal, hB, hprod]
    linear_combination ((-1) ^ (n + 1) * (((∏ k, t k)⁻¹ : Rˣ) : R)) * hcan
  rcases neg_one_pow_eq_or R (n + 1) with h | h
  · left; rw [key, h, one_mul]
  · right; rw [key, h, neg_one_mul]

end GlobalTheory.CompanionTheory.Cone
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitClassNeZeroOfNonemptyStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_class_ne_zero_of_nonempty : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)), Nonempty X →
    oneK q ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero | exact GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero | (intros; apply GlobalTheory.CompanionTheory.ConeOne.oneK_ne_zero <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WedgeTSurjective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge

namespace GlobalTheory.CompanionTheory.WedgeOf

theorem wedgeT_surjective (R V : Type) [CommRing R] [AddCommGroup V] [Module R V] :
    Function.Surjective (wedgeT (R := R) V) := by
  rw [← LinearMap.range_eq_top, eq_top_iff, ← exteriorPower.ιMulti_span (R := R) (n := 2) (M := V),
    Submodule.span_le]
  rintro _ ⟨v, rfl⟩
  refine ⟨v 0 ⊗ₜ v 1, ?_⟩
  rw [wedgeT_tmul]
  congr 1
  funext i; fin_cases i <;> rfl

theorem wedgeOf_of_low : LowSt → WedgeOfSt := by
  intro hL R _ P _ _ F g hH hV hBC hV2 hspan
  have : Finite Pᵒᵖ := Finite.of_injective unop unop_injective
  have hV' := hV
  obtain ⟨hf, hp, -⟩ := hV'
  have hκ : Function.Surjective (TensorProduct.lift (cup F)) := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hspan, Submodule.span_le]
    rintro _ ⟨x, rfl⟩
    exact ⟨x.1 ⊗ₜ x.2, rfl⟩
  have hinj : Function.Injective (TensorProduct.map (iotaQ F) (iotaQ F)) := by
    have e : TensorProduct.map (iotaQ F) (iotaQ F) =
        ((iotaQ F).lTensor (QC F)) ∘ₗ ((iotaQ F).rTensor (H1 F)) := by
      rw [LinearMap.lTensor_comp_rTensor]
    rw [e, LinearMap.coe_comp]
    exact (GlobalTheory.T.first_cohomology_inclusion_tensor_injective R _ F hBC (QC F)).comp
      (Module.Flat.rTensor_preserves_injective_linearMap _ (iotaQ_injective F))
  have hker : LinearMap.ker (TensorProduct.lift (cup F)) ≤ LinearMap.ker (wedgeT (R := R) (H1 F)) := by
    intro t ht
    have h1 := GlobalTheory.T.cup_vanishing_antisymmetric_cross hL R _ F hH t ht
    have h2 := GlobalTheory.T.cross_product_kernel_quotient_vanishing R _ F _ h1
    have h3 := hinj (h2.trans (map_zero _).symm)
    exact GlobalTheory.T.wedge_of_symmetric_tensor_zero R _ t h3
  let s : H2 F →ₗ[R] ⋀[R]^2 (H1 F) :=
    (LinearMap.ker (TensorProduct.lift (cup F))).liftQ (wedgeT (R := R) (H1 F)) hker ∘ₗ
      (LinearMap.quotKerEquivOfSurjective _ hκ).symm.toLinearMap
  have hs : ∀ t, s (TensorProduct.lift (cup F) t) = wedgeT (R := R) (H1 F) t := by
    intro t
    have : (LinearMap.quotKerEquivOfSurjective _ hκ).symm (TensorProduct.lift (cup F) t) =
        Submodule.Quotient.mk t := by
      rw [LinearEquiv.symm_apply_eq]; rfl
    simp only [s, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  have hsurj : Function.Surjective s := fun y ↦ by
    obtain ⟨t, rfl⟩ := wedgeT_surjective R (H1 F) y
    exact ⟨_, hs t⟩
  have hb := GlobalTheory.T.bijective_of_surjective_same_rank R _ _ _ hV2 (GlobalTheory.T.exterior_square_vector_bundle_rank R _ g hV) s hsurj
  refine ⟨(LinearEquiv.ofBijective s hb).symm, fun a b ↦ ?_⟩
  rw [LinearEquiv.symm_apply_eq, LinearEquiv.ofBijective_apply]
  have := hs (a ⊗ₜ b)
  rw [wedgeT_tmul] at this
  exact this.symm

end GlobalTheory.CompanionTheory.WedgeOf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ZKApply
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.BasisBase

def zK {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (Q : ObjectProperty (Thick (smFun X q))) (t u : ℤ) (ht : t ≤ 0) (j : ℕ) : HdR q j →ₗ[K] HQ Q t u j :=
  ((toSq (sFil Q t) (sFil Q u) fun T => by
    change T.obj.pdPow t.toNat = ⊤
    rw [Int.toNat_of_nonpos ht, Thick.pdPow_zero]).pull j).comp (resK q Q j)

theorem zK_apply {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (Q : ObjectProperty (Thick (smFun X q))) (t u : ℤ) (ht : t ≤ 0) (j : ℕ) (x : HdR q j) :
    zK q Q t u ht j x = (toSq (sFil Q t) (sFil Q u) fun T => by
      change T.obj.pdPow t.toNat = ⊤
      rw [Int.toNat_of_nonpos ht, Thick.pdPow_zero]).pull j (resK q Q j x) := rfl

end GlobalTheory.CompanionTheory.BasisBase
end
end

