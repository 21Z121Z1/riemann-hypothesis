import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0728
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0751
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0755
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0770
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0750
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0818
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0819
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0775
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0348
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0384
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsColumnInputAssembled
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.IsLinked
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumOfPin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0749
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0756
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0699
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0729
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0758
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0721
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0717

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityBoundedDomainModelEqMulOrigin
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

noncomputable section
namespace GlobalTheory.PointChernScale

open Matrix
open scoped ComplexOrder

theorem curv_tau {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w ξ η : ReciprocityTheory.L2DbarEstimates.V n)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) w ξ η =
      -(Z ξ * (1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹) := GlobalTheory.T.chernCurvature_modelGram_conjMulTranspose_inv Z w ξ η hw

theorem curv_tauBar {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w ξ η : ReciprocityTheory.L2DbarEstimates.V n)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) :
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w ξ η =
      -((1 - (Z w)ᴴ * Z w)⁻¹ * (Z η)ᴴ * (1 - Z w * (Z w)ᴴ)⁻¹ * Z ξ)ᵀ := GlobalTheory.T.chernCurvature_modelGram_conjugateEmbedding Z w ξ η hw

theorem exists_factor {p : ℕ} (P : Matrix (Fin p) (Fin p) ℂ) (hP : P.PosDef) :
    ∃ A : Matrix (Fin p) (Fin p) ℂ, IsUnit A.det ∧ Aᴴ * A = P := GlobalTheory.T.exists_isUnit_det_conjTranspose_mul_eq_of_posDef P hP

theorem posDef_swap {p q : ℕ} (z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - zᴴ * z).PosDef) :
    (1 - z * zᴴ).PosDef := GlobalTheory.T.posDef_one_sub_mul_conjTranspose_of_posDef_swap z h

theorem chernPoly_conj {n r : ℕ} (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin r) (Fin r) ℂ) (v v' : ReciprocityTheory.L2DbarEstimates.V n)
    (J : Matrix (Fin n) (Fin n) ℂ) (S : Matrix (Fin r) (Fin r) ℂ) (hS : IsUnit S.det)
    (h : ∀ a b, curv F v (coordVec a) (coordVec b) =
      S⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) • curv F v' (coordVec c) (coordVec d)) * S) (k : ℕ) :
    chernPoly F v k = aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b))
      (chernPoly F v' k) := GlobalTheory.T.chernPoly_conj_linearSubst_curvature F v v' J S hS h k

theorem chernPoly_reindex {n a b : ℕ} (e : Fin a ≃ Fin b) (F : ReciprocityTheory.L2DbarEstimates.V n → Matrix (Fin a) (Fin a) ℂ)
    (v : ReciprocityTheory.L2DbarEstimates.V n) (k : ℕ) : chernPoly (fun u => reindex e e (F u)) v k = chernPoly F v k := GlobalTheory.T.chernFormPolyCoeff_reindex_frame e F v k

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def zLin {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (σ : GlobalTheory.AllWt.Psi H) : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin Dw.p) (Fin Dw.q) ℂ where
  toFun u := coordOf ix u σ
  map_add' u v := by ext i j; simp [coordOf]
  map_smul' c u := by ext i j; simp [coordOf]

theorem zLin_apply {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (σ : GlobalTheory.AllWt.Psi H) (u : ReciprocityTheory.L2DbarEstimates.V n) : zLin ix σ u = coordOf ix u σ := rfl

def jMat {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (A : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.p) ℂ) (B : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.q) (Fin Dw.q) ℂ) :
    Matrix (Fin n) (Fin n) ℂ := fun c a =>
  (A (ix c).1 * coordOf ix (coordVec a) (ix c).1 * B (ix c).1) (ix c).2.1 (ix c).2.2

theorem zLin_jMat {H : Host E} {Dw : Datum H} {n : ℕ} (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q)
    (A : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.p) (Fin Dw.p) ℂ) (B : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.q) (Fin Dw.q) ℂ)
    (σ : GlobalTheory.AllWt.Psi H) (a : Fin n) :
    zLin ix σ (∑ c, jMat ix A B c a • coordVec c) = A σ * zLin ix σ (coordVec a) * B σ := by
  ext i j
  change (∑ c, jMat ix A B c a • coordVec c) (ix.symm (σ, i, j)) = _
  simp [WithLp.ofLp_sum, Finset.sum_apply, EuclideanSpace.single_apply, jMat, zLin_apply, Pi.single_apply]

theorem conj_tau {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w : ReciprocityTheory.L2DbarEstimates.V n)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (J : Matrix (Fin n) (Fin n) ℂ)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) (hA : IsUnit A.det) (hAA : Aᴴ * A = (1 - Z w * (Z w)ᴴ)⁻¹)
    (hB : B * Bᴴ = (1 - (Z w)ᴴ * Z w)⁻¹) (hJ : ∀ a, Z (∑ c, J c a • coordVec c) = A * Z (coordVec a) * B)
    (a b : Fin n) :
    curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) w (coordVec a) (coordVec b) =
      A⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
        curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) 0 (coordVec c) (coordVec d)) * A := by
  have h0 : (1 - (Z 0)ᴴ * Z 0).PosDef := by simpa using (PosDef.one : (1 : Matrix (Fin q) (Fin q) ℂ).PosDef)
  have hsum : (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
      curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) 0 (coordVec c) (coordVec d)) =
      -(Z (∑ c, J c a • coordVec c) * (Z (∑ d, J d b • coordVec d))ᴴ) := by
    have hc : ∀ ξ η, curv (fun u => (1 - (Z u).map (starRingEnd ℂ) * (Z u)ᵀ)⁻¹) 0 ξ η = -(Z ξ * (Z η)ᴴ) := by
      intro ξ η
      rw [curv_tau Z 0 ξ η h0]
      simp
    simp only [hc, map_sum, map_smul, conjTranspose_sum, conjTranspose_smul, Matrix.sum_mul,
      Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_neg, Finset.sum_neg_distrib, neg_inj]
    simp only [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by rw [mul_comm]; rfl
  rw [hsum, hJ, hJ, curv_tau Z w _ _ hw, ← hAA, ← hB]
  simp only [conjTranspose_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc,
    nonsing_inv_mul_cancel_left _ _ hA]

theorem conj_tauBar {n p q : ℕ} (Z : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] Matrix (Fin p) (Fin q) ℂ) (w : ReciprocityTheory.L2DbarEstimates.V n)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) (J : Matrix (Fin n) (Fin n) ℂ)
    (hw : (1 - (Z w)ᴴ * Z w).PosDef) (hB0 : IsUnit B.det) (hAA : Aᴴ * A = (1 - Z w * (Z w)ᴴ)⁻¹)
    (hB : B * Bᴴ = (1 - (Z w)ᴴ * Z w)⁻¹) (hJ : ∀ a, Z (∑ c, J c a • coordVec c) = A * Z (coordVec a) * B)
    (a b : Fin n) :
    curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) w (coordVec a) (coordVec b) =
      (Bᵀ)⁻¹ * (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
        curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) 0 (coordVec c) (coordVec d)) * Bᵀ := by
  have h0 : (1 - (Z 0)ᴴ * Z 0).PosDef := by simpa using (PosDef.one : (1 : Matrix (Fin q) (Fin q) ℂ).PosDef)
  have hsum : (∑ c, ∑ d, (J c a * starRingEnd ℂ (J d b)) •
      curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) 0 (coordVec c) (coordVec d)) =
      -((Z (∑ d, J d b • coordVec d))ᴴ * Z (∑ c, J c a • coordVec c))ᵀ := by
    have hc : ∀ ξ η, curv (fun u => (1 - (Z u)ᴴ * Z u)⁻¹) 0 ξ η = -((Z η)ᴴ * Z ξ)ᵀ := by
      intro ξ η
      rw [curv_tauBar Z 0 ξ η h0]
      simp
    simp only [hc, map_sum, map_smul, conjTranspose_sum, conjTranspose_smul,
      Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul, smul_neg,
      Finset.sum_neg_distrib, neg_inj, transpose_sum, transpose_smul]
    simp only [Finset.smul_sum, smul_smul]
    rfl
  rw [hsum, hJ, hJ, curv_tauBar Z w _ _ hw, ← hAA, ← hB, ← transpose_nonsing_inv, Matrix.mul_neg,
    Matrix.neg_mul, neg_inj, ← transpose_mul, ← transpose_mul]
  congr 1
  simp only [conjTranspose_mul, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hB0]

theorem chernPoly_model_eq_subst {H : Host E} (Dw : Datum H) {n : ℕ}
    (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n) (hw : InDom (coordOf ix w)) :
    ∃ J : Matrix (Fin n) (Fin n) ℂ, ∀ (τ : E →+* ℂ) (k : ℕ),
      chernPoly (fun u => modelGram H Dw (coordOf ix u) τ) w k =
        aeval (fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b))
          (chernPoly (fun u => modelGram H Dw (coordOf ix u) τ) 0 k) := by
  have hP : ∀ σ, (1 - coordOf ix w σ * (coordOf ix w σ)ᴴ)⁻¹.PosDef := fun σ => (posDef_swap _ (hw σ)).inv
  have hQ : ∀ σ, (1 - (coordOf ix w σ)ᴴ * coordOf ix w σ)⁻¹.PosDef := fun σ => (hw σ).inv
  choose A hA hAA using fun σ => exists_factor _ (hP σ)
  choose A' hA' hAA' using fun σ => exists_factor _ (hQ σ)
  let B : GlobalTheory.AllWt.Psi H → Matrix (Fin Dw.q) (Fin Dw.q) ℂ := fun σ => (A' σ)ᴴ
  have hB : ∀ σ, B σ * (B σ)ᴴ = (1 - (coordOf ix w σ)ᴴ * coordOf ix w σ)⁻¹ := fun σ => by
    simp only [B, conjTranspose_conjTranspose]; exact hAA' σ
  have hB0 : ∀ σ, IsUnit (B σ).det := fun σ => by
    simp only [B, det_conjTranspose]; exact (hA' σ).star
  refine ⟨jMat ix A B, fun τ k => ?_⟩
  by_cases h : τ (H.rt : E) = H.rt0
  · have e : (fun u => modelGram H Dw (coordOf ix u) τ) = fun u =>
        reindex (finCongr (mult_of_mem Dw h).symm) (finCongr (mult_of_mem Dw h).symm)
          ((1 - (zLin ix ⟨τ, h⟩ u).map (starRingEnd ℂ) * (zLin ix ⟨τ, h⟩ u)ᵀ)⁻¹) := by
      funext u; simp only [modelGram, dif_pos h]; rfl
    rw [e, chernPoly_reindex, chernPoly_reindex]
    exact chernPoly_conj _ w 0 _ (A ⟨τ, h⟩) (hA _)
      (conj_tau (zLin ix ⟨τ, h⟩) w (A _) (B _) _ (hw _) (hA _) (hAA _) (hB _) (zLin_jMat ix A B _)) k
  · by_cases h' : conjEmb τ (H.rt : E) = H.rt0
    · have e : (fun u => modelGram H Dw (coordOf ix u) τ) = fun u =>
          reindex (finCongr (mult_of_not_mem Dw h).symm) (finCongr (mult_of_not_mem Dw h).symm)
            ((1 - (zLin ix ⟨conjEmb τ, h'⟩ u)ᴴ * zLin ix ⟨conjEmb τ, h'⟩ u)⁻¹) := by
        funext u; simp only [modelGram, dif_neg h, dif_pos h']; rfl
      rw [e, chernPoly_reindex, chernPoly_reindex]
      exact chernPoly_conj _ w 0 _ (B _)ᵀ (by rw [det_transpose]; exact hB0 _)
        (conj_tauBar (zLin ix ⟨conjEmb τ, h'⟩) w (A _) (B _) _ (hw _) (hB0 _) (hAA _) (hB _)
          (zLin_jMat ix A B _)) k
    · have e : (fun u => modelGram H Dw (coordOf ix u) τ) = fun _ => 1 := by
        funext u; simp only [modelGram, dif_neg h, dif_neg h']
      have hc : ∀ v, chernPoly (fun _ : ReciprocityTheory.L2DbarEstimates.V n => (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)) v k =
          (1 : Polynomial (MvPolynomial (Fin n × Fin n) ℂ)).coeff k := by
        intro v
        have h0 : curvPoly (fun _ : ReciprocityTheory.L2DbarEstimates.V n => (1 : Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) ℂ)) v = 0 := by
          ext i j; simp [curvPoly]
        simp [chernPoly, h0, Matrix.charpolyRev]
      rw [e, hc, hc, Polynomial.coeff_one]
      split_ifs <;> simp

end GlobalTheory.PointChernScale

open GlobalTheory.PointChernScale in

theorem GlobalTheory.PointChern.chernTop_model_eq_mul : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) {n : ℕ}
    (ix : Fin n ≃ GlobalTheory.AllWt.Psi H × Fin Dw.p × Fin Dw.q) (w : ReciprocityTheory.L2DbarEstimates.V n), InDom (coordOf ix w) →
    ∃ κ : ℝ, ∀ R : MvPolynomial ((E →+* ℂ) × ℕ) ℝ,
      chernTop R (fun u => modelGram H Dw (coordOf ix u)) w = κ * chernTop R (fun u => modelGram H Dw (coordOf ix u)) 0 := by
  intro E _ _ _ H Dw n ix w hw
  obtain ⟨J, hJ⟩ := chernPoly_model_eq_subst Dw ix w hw
  refine ⟨Complex.normSq J.det, fun R => ?_⟩
  let φ : MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
    aeval fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)
  have hR : aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) w x.2) R =
      φ (aeval (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) 0 x.2) R) := by
    have := congrArg (fun f => f R) (MvPolynomial.comp_aeval (R := ℝ)
      (fun x : (E →+* ℂ) × ℕ => chernPoly (fun u => modelGram H Dw (coordOf ix u) x.1) 0 x.2) (φ.restrictScalars ℝ))
    simp only [AlgHom.comp_apply, AlgHom.restrictScalars_apply] at this
    rw [this]
    exact congrArg (fun f => (aeval f R : MvPolynomial (Fin n × Fin n) ℂ)) (funext fun x => hJ x.1 x.2)
  simp only [chernTop]
  rw [hR, GlobalTheory.GoodMetric.topCoeff_subst_conj, Complex.mul_conj, Complex.re_ofReal_mul]
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChoiceOfLocalAdmissible
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.StandardLattice Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie GlobalTheory.ExportSeries NumberField IsDedekindDomain
open Formalism.MainNotions.IntegralHeckeForms (TwOK HkIdx)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.HeightCounting.FirstFacts

theorem pair_of_over (D : D7) {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host}
    (hPq : ∀ v, NG.OverPl (Pq v) v) (P P' : PlE D.host) (hc : IsConjPl D.host P P') (hne : P ≠ P') :
    P ∈ Set.range Pq ↔ P' ∉ Set.range Pq := by
  have e := (GlobalTheory.PlacePair.comap_eq_iff D P P').2 (Or.inr hc)
  constructor
  · rintro ⟨v, rfl⟩ ⟨v', rfl⟩
    obtain rfl : v = v' := HeightOneSpectrum.ext ((hPq v).symm.trans (e.trans (hPq v')))
    exact hne rfl
  · intro h
    let v : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) := P.under _
    have hv : NG.OverPl P v := rfl
    rcases (GlobalTheory.PlacePair.comap_eq_iff D P (Pq v)).1 (hv.trans (hPq v).symm) with e1 | e1
    · exact ⟨v, e1.symm⟩
    · exact absurd ⟨v, GlobalTheory.GalChar.isConjPl_unique e1 hc⟩ h

theorem vstd_of_over {K : GlobalTheory.Mem.Top.Ctx} (X : GlobalTheory.Mem.Stages) (hX : K.Over X.B.toPre) (i : Fin X.toD7.R.m) :
    FWT.VStd X.toD7 i := by
  obtain ⟨-, -, -, -, -, hVf, -⟩ := GlobalTheory.Mem.HostFrames.frames_of_over K X hX
  obtain ⟨h1, h2⟩ := hVf i
  rw [GlobalTheory.StdFrameCounterexample.vstd_iff]
  refine ⟨Matrix.ext fun a b => ?_, fun x => ?_⟩
  · rw [HSpace.gram, h1, Matrix.one_apply]
  · rw [h2, Module.Basis.mem_span_iff_repr_mem, Module.Basis.repr_sum_self]
    refine forall_congr' fun a => ?_
    constructor
    · rintro ⟨y, hy⟩
      rw [← hy]; exact y.2
    · intro h
      exact ⟨⟨x a, h⟩, rfl⟩

theorem mem_range_of_mem_QE {X : Col.Fields} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {Q : HeightOneSpectrum (𝓞 X.E)} : ∀ {ξ}, Q ∈ Col.QE sel ξ → Q ∈ Set.range sel := by
  classical
  intro ξ h
  unfold Col.QE at h
  split_ifs at h
  · obtain ⟨v, -, e⟩ := Finset.mem_image.1 h
    exact ⟨v, e⟩
  · exact absurd h (Finset.notMem_empty _)

theorem facts : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {K : GlobalTheory.Mem.Top.Ctx} {B : GlobalTheory.Mem.Base} {f : GlobalTheory.Mem.Top.Fr B.toPre} {T : GlobalTheory.Mem.Top.TwDat B} {w : GlobalTheory.Mem.Top.Bl.ColW B f T}, K.Over B.toPre → GlobalTheory.Mem.Top.Bl.Start K B f T w → ∀ {P : GlobalTheory.Mem.R3.Rw.Pre2 K w} (x : GlobalTheory.Mem.R3.Rw.St P) (l : GlobalTheory.HeightCounting.Up.LA hL x), IsChoice (D := GlobalTheory.HeightCounting.Up.Dof x) (Set.range l.Pq) ∧ (∀ t, ∀ Q ∈ x.m.z.R.Q t, Q ∈ Set.range l.Pq) ∧ (∀ j, FWT.VStd (GlobalTheory.HeightCounting.Up.Dof x) j) ∧ x.m.z.R.C = GlobalTheory.HeightCounting.Up.cfOf x ∧ ∀ (k : Fin 2) (z : ℂ), z ^ ((GlobalTheory.HeightCounting.Up.Dof x).host.g k * ((GlobalTheory.HeightCounting.Up.Dof x).host.g k - 1)) = 1 → z ∈ (embLL0 (GlobalTheory.HeightCounting.Up.Dof x)).fieldRange := by
  intro hL K B f T w hK hS P x l
  obtain ⟨⟨c⟩, -⟩ := hS
  refine ⟨⟨pair_of_over _ l.Pq_over, ?_⟩, ?_, vstd_of_over (w.st x.o.Z) hK, x.m.z.lev.C, fun k z hz => ?_⟩
  · rw [l.sel]
    rintro _ ⟨v, rfl⟩ _ ⟨v', rfl⟩ ⟨p, hp, h1, h2⟩
    have key : ∀ u : HeightOneSpectrum (𝓞 B.host.F), (p : 𝓞 B.host.E) ∈ (w.I.sel u).asIdeal → (p : 𝓞 B.host.F) ∈ u.asIdeal := by
      intro u hu
      have e : (w.I.sel u).asIdeal.under (𝓞 B.host.F) = u.asIdeal := w.ok.sel_ok u
      rw [← e, Ideal.mem_comap, map_natCast]
      exact hu
    exact congrArg HeightOneSpectrum.asIdeal (c.half v v' p hp (key v h1) (key v' h2))
  · intro t Q hQ
    rw [x.m.z.lev.Q] at hQ
    rw [l.sel]
    exact mem_range_of_mem_QE hQ
  · have h0 : B.host.g k * (B.host.g k - 1) ≠ 0 :=
      mul_ne_zero (B.host.g_prime k).ne_zero (by have := (B.host.g_prime k).two_le; omega)
    obtain ⟨y, hy, e⟩ := B.roots_Ks (B.host.g k * (B.host.g k - 1)) (by fin_cases k <;> simp)
    obtain ⟨u, hu⟩ := GlobalTheory.Mem.Col2.InEx.root_mem (embLL0 (GlobalTheory.HeightCounting.Up.Dof x)) h0 ⟨⟨y, B.Ks_le hy⟩, e⟩ hz
    exact ⟨u, hu⟩

end GlobalTheory.HeightCounting.FirstFacts

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisibilityBundle
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop

namespace GlobalTheory.ClassSumPinLink

open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem classSumPin_of_read (p : PtAt ex Csz) (Yr : R3.Read (A3 := p.P.A3) p.R.toRealDat p.F.lv2 ex.p0)
    (hjW : ∀ (i : Fin D.R.m) (v : Fin ((p.P.A3.indefDown p.P.S0).dW i) → D.what₂.LL)
      (y : Fin (Module.finrank D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)) → D.what₂.LL), HEq v y →
      Yr.mj.eW i (p.P.I.jW i v) = (p.R.FW i).j (sg0 D p.P.A3.A) (jDL p.R p.F.lv2 i y))
    (hth : GlobalTheory.HeightCounting.EMtTheta Yr p.nexp ex.nch)
    (hD : DivRows3 D p.P.A3 p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.Zs p.P.S0 p.P.S1 ex.p0 p.P.C p.P.NuC p.P.I) :
    GlobalTheory.ExportPin.ClassSumPin p := by
  intro w i h1 h2 t ht hw c x hx hxT y hy n a f hsum
  subst hx
  apply hth w i hw _ hxT n a f
  rw [hsum, GlobalTheory.ExportPin.Model.theta_cast _ _ _ ht, hD.thTheta, hjW i _ y hy]

end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink

open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX

section Pack

variable {D : D7} {O : Obj D}

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

def ReadAt {R : Formalism.L2.RecT O.ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR R} (k : RPk R S) : Prop :=
  ∃ Yr : R3.Read (A3 := k.P.A3) k.B.Q.Rl.toRealDat
      (⟨k.P.P0, k.P.ψ0, k.P.Ps, k.P.ψs, k.Dc, k.Sp, k.Zsc⟩ : Face3 D k.P.A3).lv2 O.ex.p0,
    (∀ (i : Fin D.R.m) (v : Fin ((k.P.A3.indefDown k.P.S0).dW i) → D.what₂.LL)
      (y : Fin (Module.finrank D.what₂.LL (k.B.Q.Rl.toRealDat.WL
        (⟨k.P.P0, k.P.ψ0, k.P.Ps, k.P.ψs, k.Dc, k.Sp, k.Zsc⟩ : Face3 D k.P.A3).lv2 false i)) → D.what₂.LL),
      HEq v y → Yr.mj.eW i (k.P.I.jW i v) = (k.B.Q.Rl.FW i).j (sg0 D k.P.A3.A)
        (jDL k.B.Q.Rl (⟨k.P.P0, k.P.ψ0, k.P.Ps, k.P.ψs, k.Dc, k.Sp, k.Zsc⟩ : Face3 D k.P.A3).lv2 i y)) ∧
    GlobalTheory.HeightCounting.EMtTheta Yr k.B.Q.nexp O.ex.nch

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem readAt_rpkX {R : Formalism.L2.RecT O.ex} {S : Formalism.L2.SG.SpectralTiesReal.STiesR R} {x : R3.TwIn O.ex} (y : R3.RealIn x R S)
    (h : GlobalTheory.HeightCounting.EMtTheta x.Y y.nexp O.ex.nch) : ReadAt (rpkX y) := by
  refine ⟨x.Y, ?_, h⟩
  intro i v z hvz
  obtain rfl := eq_of_heq hvz
  exact x.Z.jW_read i v

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem classSumPin_of_readAt {c : ℝ} (b : Bundle D O c) (t : b.Comparison₂) (h : ReadAt (rpkB b)) (hD : Ind.PDiv D O c (b.part t)) :
    GlobalTheory.ExportPin.ClassSumPin (b.part t).pt := by
  obtain ⟨Yr, h1, h2⟩ := h
  exact classSumPin_of_read (b.part t).pt Yr h1 h2 hD

end Pack

end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink

open Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem eMtTheta_of_pack {D : D7} {nch : NChoice D} {X0 : BaseLevelRowSide D} {G G' : Type} {g : Group G} {g' : Group G'} {fi : Fintype G}
    {fi' : Fintype G'} {Pl0 I0 T Pl0' I0' T' : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {A3' : FamIn3 D.what₂.LL G' Pl0' I0' (List ℕ) T' D.R.m}
    {C C' : CoreJ D} {al : Algebra C.Q.c.F D.what₂.LL} {al' : Algebra C'.Q.c.F D.what₂.LL} {R : RealDat3 D A3 C.Q.c.F}
    {R' : RealDat3 D A3' C'.Q.c.F} {F : Face3 D A3} {F' : Face3 D A3'} {kap : ℝ} {lam : type_of% R'.lam3} {err : type_of% R'.err0}
    {Dc : ∀ Zs : DefSub A3'.fam3.amb3, DefCols (A3'.side3 F'.P1 F'.ψ1 Zs)} {Sp : ∀ Zs, SPer (Dc Zs)}
    {Zsc : DefSub A3'.fam3.amb3 → IndefScale A3'.fam3.base3}
    {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {cG' : G0 R'.Pg D.R.r ≃* G0g D.nd}
    {cG'' : G0 ((R'.updS kap lam).withErr err).Pg D.R.r ≃* G0g D.nd}
    (pack : (⟨G, g, fi, Pl0, I0, T, A3, C, al, R, F, cG⟩ :
      Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : CoreJ D)
        (_ : Algebra C.Q.c.F D.what₂.LL) (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3),
        G0 R.Pg D.R.r ≃* G0g D.nd) =
      ⟨G', g', fi', Pl0', I0', T', A3', C', al', (R'.updS kap lam).withErr err, R3.reFace F' Dc Sp Zsc, cG''⟩)
    (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (Y' : R3.Read (A3 := A3') R'.toRealDat F'.lv2 X0)
    (hW : HEq Y.mj.eW Y'.mj.eW) {S S' : RatDat D.ntw} (hS : S = S')
    (E : NExpRealS R cG S) (E' : NExpRealS R' cG' S') (hF : HEq E.eF E'.eF) (hi : HEq E.fi E'.fi)
    (h : GlobalTheory.HeightCounting.EMtTheta Y' E' nch) : GlobalTheory.HeightCounting.EMtTheta Y E nch := by
  cases pack
  cases hS
  intro w i hw x hx n a f hs
  have e1 : E.eF = E'.eF := eq_of_heq hF
  have e2 : E.fi = E'.fi := eq_of_heq hi
  have e3 : Y.mj.eW = Y'.mj.eW := eq_of_heq hW
  rw [e2, e3] at hs
  rw [e1]
  exact h w i hw x hx n a f hs

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem eMtTheta_of_args {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T}
    {Z : w.Lt} {Wt : Set B.places.Pl} {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L}
    {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC}
    {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX} (t : RowsT K w Z Wt ex.p0) (n : NchT w Z Wt ex.nch) (c : NCore hL t n)
    (a : R3.TwArgs ex t) (x : R3.TwIn ex) (ax : HEq a.x x) {Sx : RatDat (w.st Z).toD7.ntw} (E : NExpRealS x.R x.cG Sx)
    (hS : HEq Sx (ratDatR (D := (w.st Z).toD7) t.r.z.R t.r.z.cG c.row.kKs c.row.hk))
    (hF : HEq E.eF c.row.nexp.eF) (hi : HEq E.fi c.row.nexp.fi)
    (h : GlobalTheory.HeightCounting.EMtTheta (D := (w.st Z).toD7) t.r.Y c.row.nexp ex.nch) : GlobalTheory.HeightCounting.EMtTheta x.Y E ex.nch := by
  cases ax
  exact eMtTheta_of_pack a.pack a.x.Y t.r.Y a.eW (eq_of_heq hS) E c.row.nexp hF hi h

end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink

set_option maxHeartbeats 4000000 in

theorem pIota_classSumPin : ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (N : NExt hL) (S : SExt) (Γ : GeoP), (∀ K B f T w Z Wt p0 t nch n xd c, N K B f T w Z Wt p0 t nch n xd c → Nonempty (GlobalTheory.HeightCounting.Up.NEb hL K B f T w Z Wt p0 t nch n xd c)) → ∀ (K : Ctx) (q : WPt (prmR N S Γ).s K) (c : ℝ) (b : Bundle (q.w.D q.Z) q.O c) (_ : BWit (p := prmR N S Γ) q b) (t : b.Comparison₂), Ind.PIota _ _ c (b.part t) ∧ (Ind.PDiv _ _ c (b.part t) → GlobalTheory.ExportPin.ClassSumPin (b.part t).pt) := by
  intro hL N S Γ hN K q c b hb t
  refine ⟨?_, fun hD => ?_⟩
  · obtain ⟨sP, sS, -, -, hS⟩ := hb.s
    have key : ∀ S' : Formalism.L2.SG.SpectralTiesReal.STiesR b.R, S' = sS.toSTiesR b.R → ∀ x : S'.X.B.I.E, HEq (S'.X.ιE x) x := by
      rintro S' rfl
      exact sP.pin
    exact key b.S hS
  · have hth : GlobalTheory.HeightCounting.EMtTheta hb.x.Y hb.y.y.nexp q.O.ex.nch := by
      obtain ⟨m⟩ := hN _ _ _ _ _ _ _ _ _ _ _ _ _ q.x.nx.2
      exact eMtTheta_of_args q.x.what₂ q.x.n (WPt.core (p := prmR N S Γ) q) hb.a hb.x hb.ax hb.y.y.nexp hb.sx hb.eF hb.fi m.1.th
    have hR : ReadAt (rpkB b) := by
      rw [hb.y.eq]
      exact readAt_rpkX hb.y.y hth
    exact classSumPin_of_readAt b t hR hD

end GlobalTheory.ClassSumPinLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompAtBaseCharacterMulUnramifiedEqTypeCharacterStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compAt_baseCharacter_mul_unramified_eq_typeCharacter : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ)
    (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0)
    (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf Rw low Pq S hL eig θ), ValLL0 D cf →
    ∀ τ : ℕ → ∀ kv : (Σ k : Fin 2, D.nd.PlG k), (ZMod (D.host.g kv.1))ˣ →* (↥D.LL0)ˣ,
    (∀ i j b kv x, 1 ≤ j → j ≤ D.R.m → ((Bs.exp.tauG i j b kv x : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) =
      GlobalTheory.SeriesTie.sideEmb D.ntw i b ((τ j kv x : (↥D.LL0)ˣ) : ↥D.LL0)) →
    ∀ (j : Fin D.R.m) (kv : Σ k : Fin 2, D.nd.PlG k) (s : SplitPlace D.host.E), s.w = NX.pG D kv →
    ∀ χ : HChar D.host.E, χ.UnrAt s.w →
    ∀ red : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E) →+* ZMod (D.host.g kv.1),
    ∃ ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ, NG.IsCompAt (cf.mu0 j * χ) s ξ ∧
      ∀ (y : s.v.adicCompletionIntegers (maximalRealSubfield D.host.E)) (hy : IsUnit (red y))
        (uu : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ), (uu : s.v.adicCompletion (maximalRealSubfield D.host.E)) = y →
          ((ξ uu : ℂˣ) : ℂ) = embLL0 D ((τ (j.1 + 1) kv hy.unit : (↥D.LL0)ˣ) : ↥D.LL0) := by
  first | exact @GlobalTheory.TypeCharRead.compAt_baseCharacter_mul_unramified_eq_typeCharacter_alt | exact GlobalTheory.TypeCharRead.compAt_baseCharacter_mul_unramified_eq_typeCharacter_alt | (intros; apply GlobalTheory.TypeCharRead.compAt_baseCharacter_mul_unramified_eq_typeCharacter_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeMatchRaysAfterDroppingZeroCoordsStatement
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolFan.OrbMark
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_match_rays_after_dropping_zero_coords : ∀ {X : Type} [AddCommGroup X] {m₀ : ℕ} (p : Fin m₀ → LinearMap.BilinForm ℤ X) (t : Fin m₀ → ℝ), (∀ i, 0 ≤ t i) →
  LinearIndependent ℤ (fun i : {i // 0 < t i} => p i) →
  ∀ β : LinearMap.BilinForm ℤ X, toReal β = ∑ i, t i • toReal (p i) →
  ∀ (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X), LinearIndependent ℤ δ →
  ∀ c : Fin m → ℝ, (∀ j, 0 ≤ c j) → toReal β = ∑ j, c j • toReal (δ j) →
  (∀ i, 0 < t i → InRCone δ (p i)) →
  (∀ j, 0 < c j → ∃ a : Fin m₀ → ℝ, (∀ i, 0 ≤ a i) ∧ (∀ i, t i = 0 → a i = 0) ∧ toReal (δ j) = ∑ i, a i • toReal (p i)) →
  (∀ i, 0 < t i → ∃ j, 0 < c j ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j)) ∧
    (∀ j, 0 < c j → ∃ i, 0 < t i ∧ ∃ d : ℝ, 0 < d ∧ toReal (p i) = d • toReal (δ j) ∧ c j = t i * d) := by
  first | exact @GlobalTheory.PolFan.cone_match_rays_of_nonneg | exact GlobalTheory.PolFan.cone_match_rays_of_nonneg | (intros; apply GlobalTheory.PolFan.cone_match_rays_of_nonneg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EnlargedBaseLb2ExtensionStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.enlarged_base_lb2_extension : PrN → SerN → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) {K : Ctx} {B' : Base} {f' : Top.Fr B'.toPre} {T' : TwDat B'} {w' : ColW B' f' T'}, KPx B' f' → Forced K B' T' → Start K B' f' T' w' → ∀ (B : Base) (f : Top.Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl B B' → HEq f' f → Start K B f T w → HEq w'.px w.px → HEq w'.I.sel w.I.sel → HEq w'.I.J w.I.J → HEq w'.δ w.δ → ∀ (P : Pre2 K w) (x : St P) (lb : StrictHenselianAcyclic hL x) (P' : Pre2 K w'), Ext P.z P'.z → ∀ (x' : St P') (l' : LI hL x'), SameGal (Dof x) (Dof x') → ∀ (N : TwNew (Dof x')) (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0), CopyN (Dof x) N ι e → ∀ (x'' : St P') (l'' : LI hL x''), x''.o = oTw x' N → HEq x''.m.z.R.toRealDat.toLevCh (GlobalTheory.Mem.R3.Tr.levCh (a := x'.o.Z) (oTw x' N).Z x'.m.z.R.toRealDat.toLevCh) → HEq l''.a.A.row (N.row l'.a.A.row) → HEq l''.Pq l'.Pq → HEq l''.rat.S (N.rat l'.rat.S) → HEq l''.rat.In.Sb l'.rat.In.Sb → HEq l''.rat.In.hL l'.rat.In.hL → HEq l''.rat.In.eig l'.rat.In.eig → HEq l''.rat.In.θ l'.rat.In.θ → ∀ cDep : ℝ, ListSt cDep x → ListSt cDep x'' := by
  first | exact @GlobalTheory.HeightCounting.Up.ListCarry.listSt_carry | exact GlobalTheory.HeightCounting.Up.ListCarry.listSt_carry | (intros; apply GlobalTheory.HeightCounting.Up.ListCarry.listSt_carry <;> assumption)
end

