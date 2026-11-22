import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0264
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0167
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0219
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeHankelTransformABHasDerivAtY
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0265
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0251
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0266
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueBaseChangeEqOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0225
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0246
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0222
import ReciprocityTheory.Chebotarev.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IrreducibleXSqAddOne
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0278
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0161
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0177

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZero
section
open MeasureTheory Matrix

namespace GlobalTheory.DetFactor

variable {k : Type} [Field k] {m : ℕ}

noncomputable def diagGL (n : ℕ) : (Fin n → kˣ) →* GL (Fin n) k :=
  (Units.map (diagonalRingHom (Fin n) k).toMonoidHom).comp MulEquiv.piUnits.symm.toMonoidHom

theorem diagGL_val {n : ℕ} (d : Fin n → kˣ) : ((diagGL n d : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = diagonal (fun i => (d i : k)) := rfl

noncomputable def toGL {n : ℕ} (M : Matrix (Fin n) (Fin n) k) (h : M.det ≠ 0) : GL (Fin n) k :=
  nonsingInvUnit M (isUnit_iff_ne_zero.mpr h)

@[simp] theorem toGL_val {n : ℕ} (M : Matrix (Fin n) (Fin n) k) (h : M.det ≠ 0) :
    ((toGL M h : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = M := rfl

theorem conj_transvection {n : ℕ} {i j : Fin n} (hij : i ≠ j) (t : k) :
    diagonal (fun l => if l = i then (2 : k) else 1) * transvection i j t
      = transvection i j (2 * t) * diagonal (fun l => if l = i then (2 : k) else 1) := by
  ext a b
  simp only [transvection, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, diagonal_mul, mul_diagonal]
  by_cases ha : a = i <;> by_cases hb : b = j <;> by_cases hbi : b = i <;> by_cases hab : a = b <;>
    simp_all [single, one_apply, eq_comm] <;> ring

theorem det_diag2_ne {n : ℕ} (h2 : (2 : k) ≠ 0) (i : Fin n) :
    (diagonal (fun l => if l = i then (2 : k) else 1)).det ≠ 0 := by
  rw [det_diagonal, Finset.prod_ne_zero_iff]
  intro l _
  split_ifs <;> simp [h2]

theorem det_transvection_ne {n : ℕ} {i j : Fin n} (hij : i ≠ j) (t : k) :
    (transvection i j t).det ≠ 0 := by
  rw [det_transvection_of_ne _ _ hij]; exact one_ne_zero

theorem map_transvection_eq_one (h2 : (2 : k) ≠ 0) {n : ℕ} (c : GL (Fin n) k →* ℂˣ) {i j : Fin n}
    (hij : i ≠ j) (t : k) : c (toGL (transvection i j t) (det_transvection_ne hij t)) = 1 := by
  set D := toGL _ (det_diag2_ne h2 i)
  have h1 : D * toGL (transvection i j t) (det_transvection_ne hij t)
      = toGL (transvection i j (2 * t)) (det_transvection_ne hij _) * D := by
    apply Units.ext; simp only [Units.val_mul, toGL_val, D]; exact conj_transvection hij t
  have h3 : toGL (transvection i j t) (det_transvection_ne hij t) * toGL (transvection i j t) (det_transvection_ne hij t)
      = toGL (transvection i j (2 * t)) (det_transvection_ne hij _) := by
    apply Units.ext; simp only [Units.val_mul, toGL_val]; rw [transvection_mul_transvection_same (h := hij), two_mul]
  have e1 := congrArg c h1
  have e3 := congrArg c h3
  rw [map_mul, map_mul, mul_comm (c D)] at e1
  have e1' := mul_right_cancel e1
  rw [map_mul, ← e1'] at e3
  exact (mul_eq_left.mp e3)

theorem det_perm_ne {n : ℕ} (σ : Equiv.Perm (Fin n)) : (σ.toPEquiv.toMatrix : Matrix (Fin n) (Fin n) k).det ≠ 0 := by
  have := det_permutation (R := k) σ
  simp only [Equiv.Perm.permMatrix] at this
  rw [this]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem map_diagGL_perm {n : ℕ} (c : GL (Fin n) k →* ℂˣ) (σ : Equiv.Perm (Fin n)) (d : Fin n → kˣ) :
    c (diagGL n (d ∘ σ)) = c (diagGL n d) := by
  set P := toGL _ (det_perm_ne (k := k) σ)
  have h1 : P * diagGL n d = diagGL n (d ∘ σ) * P := by
    apply Units.ext
    simp only [Units.val_mul, toGL_val, P, diagGL_val]
    rw [PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv]
    ext a b
    simp [diagonal_apply, Equiv.eq_symm_apply]
  have e := congrArg c h1
  rw [map_mul, map_mul, mul_comm (c P)] at e
  exact (mul_right_cancel e).symm

theorem map_diagGL_eq (c : GL (Fin (m + 1)) k →* ℂˣ) (d : Fin (m + 1) → kˣ) :
    c (diagGL (m + 1) d) = (c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0) (∏ i, d i) := by
  have hs : ∀ i (x : kˣ), c (diagGL (m + 1) (Pi.mulSingle i x)) = c (diagGL (m + 1) (Pi.mulSingle 0 x)) := by
    intro i x
    rw [← map_diagGL_perm c (Equiv.swap 0 i) (Pi.mulSingle i x)]
    congr 2
    funext a
    simp only [Function.comp_apply, Pi.mulSingle_apply, Equiv.swap_apply_eq_iff, Equiv.swap_apply_right]
  have e : c (diagGL (m + 1) d) = (c.comp (diagGL (m + 1))) (∏ i, Pi.mulSingle i (d i)) := by
    rw [Finset.univ_prod_mulSingle]; rfl
  rw [e, map_prod, map_prod]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MonoidHom.mulSingle_apply]
  exact Finset.prod_congr rfl (fun i _ => hs i (d i))

theorem factors_through_det (h2 : (2 : k) ≠ 0) {n : ℕ} (c : GL (Fin n) k →* ℂˣ) :
    ∃ χ : kˣ →* ℂˣ, ∀ g, c g = χ (Matrix.GeneralLinearGroup.det g) := by
  cases n with
  | zero =>
    refine ⟨1, fun g => ?_⟩
    have : g = 1 := Units.ext (Matrix.ext fun i _ => i.elim0)
    simp [this]
  | succ m =>
    refine ⟨(c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0), fun g => ?_⟩
    set χ := (c.comp (diagGL (m + 1))).comp (MonoidHom.mulSingle (fun _ => kˣ) 0)
    let P : Matrix (Fin (m + 1)) (Fin (m + 1)) k → Prop := fun M =>
      ∀ u : GL (Fin (m + 1)) k, (u : Matrix _ _ k) = M → c u = χ (Matrix.GeneralLinearGroup.det u)
    have hg : Matrix.det (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) ≠ 0 := (Matrix.isUnits_det_units g).ne_zero
    refine diagonal_transvection_induction_of_det_ne_zero P (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) hg ?_ ?_ ?_ g rfl
    · intro D hD u hu
      have hD' : ∀ i, D i ≠ 0 := by
        intro i; rw [det_diagonal] at hD; exact Finset.prod_ne_zero_iff.mp hD i (Finset.mem_univ i)
      have hu' : u = diagGL (m + 1) (fun i => Units.mk0 (D i) (hD' i)) := by
        apply Units.ext; rw [hu, diagGL_val]; rfl
      have hdet : Matrix.GeneralLinearGroup.det u = ∏ i, Units.mk0 (D i) (hD' i) := by
        apply Units.ext; simp [hu, det_diagonal]
      rw [hdet, hu', map_diagGL_eq]
    · intro t u hu
      have hu' : u = toGL (transvection t.i t.j t.c) (det_transvection_ne t.hij t.c) := Units.ext hu
      have hdet : Matrix.GeneralLinearGroup.det u = 1 := by
        apply Units.ext; simp [hu, TransvectionStruct.toMatrix, det_transvection_of_ne _ _ t.hij]
      rw [hdet, map_one, hu']
      exact map_transvection_eq_one h2 c t.hij t.c
    · intro A B hA hB PA PB u hu
      have hu' : u = toGL A hA * toGL B hB := Units.ext (by simp [hu])
      rw [hu', map_mul, map_mul, PA _ rfl, PB _ rfl, ← map_mul]

end GlobalTheory.DetFactor

theorem GlobalTheory.ghom_factors_through_det : ∀ {k : Type} [Field k], (2 : k) ≠ 0 → ∀ {n : ℕ} (c : GL (Fin n) k →* ℂˣ),
    ∃ χ : kˣ →* ℂˣ, ∀ g, c g = χ (Matrix.GeneralLinearGroup.det g) :=
  by intro k _ h2 n c; exact GlobalTheory.DetFactor.factors_through_det h2 c
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeHankelTransformABDifferentiableOnSigmaStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeHankelTransformAB_differentiableOn_sigma : ∀ (a b : ℕ) (ν y : ℝ), 2 ≤ a + b → y ≠ 0 → DifferentiableOn ℂ (fun σ => hTransAB a b σ ν y) halfPlane := by
  first | exact @GlobalTheory.HeckeTwo.hTransAB_differentiableOn | exact GlobalTheory.HeckeTwo.hTransAB_differentiableOn | (intros; apply GlobalTheory.HeckeTwo.hTransAB_differentiableOn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeHankelTransformABHasDerivAtYStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeHankelTransformAB_hasDerivAt_y : ∀ (a b : ℕ) (σ : ℂ) (ν y : ℝ), 2 ≤ a + b → σ ∈ halfPlane → y ≠ 0 →
    HasDerivAt (fun y' : ℝ => hTransAB a b σ ν y')
      (I * (-(a : ℂ) - σ) * hTransAB (a + 1) b σ ν y + I * ((b : ℂ) + σ) * hTransAB a (b + 1) σ ν y) y := by
  first | exact @GlobalTheory.HeckeTwo.hTransAB_hasDerivAt | exact GlobalTheory.HeckeTwo.hTransAB_hasDerivAt | (intros; apply GlobalTheory.HeckeTwo.hTransAB_hasDerivAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckePhiFourierTransformSigmaZeroEqStatement
section
open Complex GlobalTheory.HeckeTwo
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckePhiFourierTransform_sigma_zero_eq : ∀ (ν y : ℝ), 0 < y → GlobalTheory.HeckeTwo.hTrans 0 ν y = if 0 < ν then -4 * (Real.pi : ℂ) ^ 2 * (ν : ℂ) * ((Real.exp (-(2 * Real.pi * ν * y)) : ℝ) : ℂ) else 0 := by
  first | exact @GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq | exact GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq | (intros; apply GlobalTheory.HeckeTwo.hTrans_sigma_zero_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoIsGoodOfTsumStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeWeightTwo_isGood_of_tsum : ∀ (F : Type) [Field F] [NumberField F] (ι : Type) (g : ι → ℂ → (Emb F → ℂ) → ℂ) (P : ℂ → (Emb F → ℂ) → ℂ),
  (∀ i, ∀ σ ∈ halfPlane, ContDiffOn ℝ ∞ (g i σ) (upperHalf F)) →
  (∀ i, ∀ w : List (Emb F × Bool), ∀ z ∈ upperHalf F, DifferentiableOn ℂ (fun σ => wirtWord w (g i σ) z) halfPlane) →
  (∀ K : Set ℂ, IsCompact K → K ⊆ halfPlane → ∀ L : Set (Emb F → ℂ), IsCompact L → L ⊆ upperHalf F → ∀ n : ℕ,
    ∃ u : ι → ℝ, Summable u ∧ ∀ i, ∀ σ ∈ K, ∀ z ∈ L, ‖iteratedFDeriv ℝ n (g i σ) z‖ ≤ u i) →
  (∀ σ ∈ halfPlane, ∀ z ∈ upperHalf F, P σ z = ∑' i, g i σ z) →
  IsGood P := by
  first | exact @GlobalTheory.HeckeTwo.isGood_of_tsum | exact GlobalTheory.HeckeTwo.isGood_of_tsum | (intros; apply GlobalTheory.HeckeTwo.isGood_of_tsum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeYDerivativeTermHasFDerivUpperHalfPlaneStatement
section
open NumberField Complex
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeYDerivativeTerm_hasFDeriv_upperHalfPlane : ∀ (F : Type) [Field F] [NumberField F] (b ν : F), b ≠ 0 → (∀ (n : ℝ) (k : ℕ) (y : ℝ), y ≠ 0 →
    (∀ σ ∈ halfPlane, HasDerivAt (iteratedDeriv k (hTrans σ n)) (iteratedDeriv (k + 1) (hTrans σ n) y) y) ∧
    DifferentiableOn ℂ (fun σ => iteratedDeriv k (hTrans σ n) y) halfPlane) →
    ∀ σ ∈ halfPlane, ∀ (q : Emb F → ℕ), ∀ z ∈ upperHalf F, ∀ τ₀ : Emb F,
    DifferentiableAt ℝ (termQ σ b ν q) z ∧
    fderiv ℝ (termQ σ b ν q) z (Pi.single τ₀ 1) = 2 * (Real.pi : ℂ) * I * ((τ₀ ν * τ₀ b : ℝ) : ℂ) * termQ σ b ν q z ∧
    fderiv ℝ (termQ σ b ν q) z (Pi.single τ₀ I) = ((τ₀ b : ℝ) : ℂ) * termQ σ b ν (q + Pi.single τ₀ 1) z := by
  first | exact @GlobalTheory.HeckeTwo.termQ_fderiv | exact GlobalTheory.HeckeTwo.termQ_fderiv | (intros; apply GlobalTheory.HeckeTwo.termQ_fderiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightOnePrimeOverConstantIdeal
section
open IsLocalRing Polynomial
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_one_prime_over_constant_ideal : ∀ (A : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A]
    (E : Type) [CommRing E] [Algebra A[X] E] [Algebra A E] [IsScalarTower A A[X] E]
    [Algebra.Etale A[X] E] (Q : Ideal E) [Q.IsPrime] (P : Ideal (Localization.AtPrime Q)) [P.IsPrime]
    (p : Ideal A) [p.IsPrime], p.height = 1 →
    P.comap (algebraMap A[X] (Localization.AtPrime Q)) = p.map (Polynomial.C : A →+* A[X]) →
    (∃ _ : IsDomain (Localization.AtPrime P), IsDiscreteValuationRing (Localization.AtPrime P)) ∧
      ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime p) π) →
        Irreducible (algebraMap A (Localization.AtPrime P) π) := by
  first | (exact @GlobalTheory.EtalePolyDvr.isDiscreteValuationRing_atPrime_of_etale_polynomial) | (exact GlobalTheory.EtalePolyDvr.isDiscreteValuationRing_atPrime_of_etale_polynomial) | (intros; apply GlobalTheory.EtalePolyDvr.isDiscreteValuationRing_atPrime_of_etale_polynomial  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.Hilbert90LocalOfCocycleTensorStatement
section
open TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbert90_of_cocycle_faithfullyFlat_tensor : ∀ (R S : Type) [CommRing R] [CommRing S] [Algebra R S] [IsNoetherianRing R] [Module.Finite R S]
    [Module.FaithfullyFlat R S] (c : (S ⊗[R] S)ˣ),
    Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S ⊗[R] S) (B := S) (c : S ⊗[R] S) *
        Algebra.TensorProduct.map (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)) (AlgHom.id R S) (c : S ⊗[R] S) =
      Algebra.TensorProduct.map (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := S) (B := S)) (AlgHom.id R S) (c : S ⊗[R] S) →
    ∀ p : Ideal R, p.IsPrime → ∃ r ∉ p, ∃ m s : S, ∃ n : ℕ,
      (m ⊗ₜ[R] (1 : S)) * (c : S ⊗[R] S) = (1 : S) ⊗ₜ[R] m ∧ m * s = algebraMap R S r ^ n := by
  first | exact @GlobalTheory.FlatDescent.hilbert90_local_of_cocycle | exact GlobalTheory.FlatDescent.hilbert90_local_of_cocycle | (intros; apply GlobalTheory.FlatDescent.hilbert90_local_of_cocycle <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertCoordinateMapBijectiveOfLeAffine
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

namespace GlobalTheory.HilbAff

theorem coord_bijective_of_le_affine : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ) (e : Module.Basis (Fin N) A B) (σ : Fin r ↪ Fin N) (Z : Scheme.{0}) (y : (GlobalTheory.HilbAff.functor A B r).obj (op Z)) (W W' : Z.affineOpens), (W' : Z.Opens) ≤ W → Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y W) → Function.Bijective (GlobalTheory.HilbAff.coord A B e σ y W') := by
  intro A B _ _ _ N r e σ Z y W W' hle hW
  have hbas : ∀ f : Γ(Z, W), Function.Bijective (coord A B e σ y (Z.basicOpen f)) := by
    intro f
    rw [GlobalTheory.T.affineHilbertCoordinateMap_basicOpen_bijective A B N r e σ Z y W f]
    exact ⟨LocalizedModule.map_injective _ _ hW.1, LocalizedModule.map_surjective _ _ hW.2⟩
  let s : Set Γ(Z, W') := {g | Function.Bijective (coord A B e σ y (Z.basicOpen g))}
  have hspan : Ideal.span s = ⊤ := by
    rw [← W'.2.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨f, g, hfg, hxf⟩ := exists_basicOpen_le_affine_inter W.2 W'.2 x ⟨hle hx, hx⟩
    refine TopologicalSpace.Opens.mem_iSup.2 ⟨⟨g, ?_⟩, ?_⟩
    · show Function.Bijective _
      rw [← hfg]; exact hbas f
    · show x ∈ Z.basicOpen g
      rw [← hfg]; exact hxf
  exact bijective_of_localized_span s hspan _ fun g => (GlobalTheory.T.affineHilbertCoordinateMap_basicOpen_bijective A B N r e σ Z y W' g.1).1 g.2

end GlobalTheory.HilbAff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertEisensteinLatticeSummandWeightTwoBoundStatement
section
open NumberField Complex Polynomial
open scoped nonZeroDivisors ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization GlobalTheory.HeckeTwo

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hilbertEisensteinLatticeSummand_weightTwo_bound : ∀ (F : Type) [Field F] [NumberField F] (σ : ℂ), 0 < σ.re → ∀ z ∈ GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.upperHalf F, ∃ C : ℝ, ∀ p : F × F, p ≠ 0 → ‖GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.eisTerm 2 σ z p‖ ≤ C * (∏ τ : F →+* ℝ, ((τ p.1) ^ 2 + (τ p.2) ^ 2)) ^ (-(1 + σ.re)) := by
  first | exact @GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound.bound | exact GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound.bound | (intros; apply GlobalTheory.Proof.hilbertEisensteinLatticeSummand_weightTwo_bound.bound <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCurvatureDualMetricPointwiseBound
section
open Matrix Complex Filter Topology
open scoped ComplexOrder ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram GlobalTheory.HermFrame

noncomputable section

namespace GlobalTheory.HodgeCurvPoint

variable {g : ℕ}

theorem re_form_map (M : Matrix (Fin g) (Fin g) ℝ) (v : Fin g → ℂ) :
    (form (M.map ofReal) v v).re = (fun j => (v j).re) ⬝ᵥ M *ᵥ (fun j => (v j).re) +
      (fun j => (v j).im) ⬝ᵥ M *ᵥ (fun j => (v j).im) := by
  simp only [form_eq_sum, dotProduct, mulVec, Finset.mul_sum, re_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  simp [Matrix.map_apply, mul_re, mul_im, conj_re, conj_im]; ring

theorem isHermitian_map {M : Matrix (Fin g) (Fin g) ℝ} (hM : M.IsSymm) :
    (M.map ofReal).IsHermitian := by
  ext i j; simp [conjTranspose_apply, hM.apply]

theorem form_map_self {M : Matrix (Fin g) (Fin g) ℝ} (hM : M.IsSymm) (v : Fin g → ℂ) :
    form (M.map ofReal) v v = (((fun j => (v j).re) ⬝ᵥ M *ᵥ (fun j => (v j).re) +
      (fun j => (v j).im) ⬝ᵥ M *ᵥ (fun j => (v j).im) : ℝ) : ℂ) := by
  apply Complex.ext
  · rw [re_form_map, ofReal_re]
  · rw [ofReal_im]
    exact Complex.conj_eq_iff_im.mp (conj_form (isHermitian_map hM) v v)

theorem posSemidef_map {M : Matrix (Fin g) (Fin g) ℝ} (hM : M.IsSymm)
    (h : ∀ x, 0 ≤ x ⬝ᵥ M *ᵥ x) : (M.map ofReal).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_map hM, fun x => ?_⟩
  have e : star x ⬝ᵥ (M.map ofReal) *ᵥ x = form (M.map ofReal) (star x) (star x) := by
    simp [form]
  rw [e, form_map_self hM]
  exact_mod_cast add_nonneg (h _) (h _)

theorem sum_norm_sq (v : Fin g → ℂ) : ∑ j, ‖v j‖ ^ 2 =
    (fun j => (v j).re) ⬝ᵥ (fun j => (v j).re) + (fun j => (v j).im) ⬝ᵥ (fun j => (v j).im) := by
  simp only [dotProduct, ← Finset.sum_add_distrib, Complex.sq_norm, Complex.normSq_apply]

theorem gnorm_map_star (M : Matrix (Fin g) (Fin g) ℝ) (u : Fin g → ℂ) :
    gnorm (M.map ofReal) (star u) = gnorm (M.map ofReal) u := by
  have e1 : (fun j => (star u j).re) = fun j => (u j).re := by ext j; simp
  have e2 : (fun j => (star u j).im) = -fun j => (u j).im := by ext j; simp
  rw [gnorm, gnorm, re_form_map, re_form_map, e1, e2, mulVec_neg, neg_dotProduct, dotProduct_neg,
    neg_neg]

theorem dotProduct_mulVec_eq_form {M : Matrix (Fin g) (Fin g) ℂ} (hM : M.IsSymm)
    (u v : Fin g → ℂ) : u ⬝ᵥ M *ᵥ v = form M v (star u) := by
  rw [form, star_star, dotProduct_mulVec, ← mulVec_transpose, hM.eq, dotProduct_comm]

theorem dotProduct_finsetSum {a : ℕ} (u : Fin g → ℂ) (w : Fin a → Fin g → ℂ) :
    u ⬝ᵥ ∑ i, w i = ∑ i, u ⬝ᵥ w i := by
  simp only [dotProduct, Finset.sum_apply, Finset.mul_sum]
  exact Finset.sum_comm

theorem dual_bound : ∀ (g a : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (Bs : Fin a → Matrix (Fin g) (Fin g) ℝ)
    (Dm : Matrix (Fin g) (Fin g) ℂ) (s : Fin a → ℂ) (t : Fin a → ℝ) (c K : ℝ), 0 < c → 0 ≤ K →
    Y.IsSymm → (∀ x, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ i, (Bs i).PosSemidef) → (∀ i, 0 < t i) →
    (∀ i x, t i * (x ⬝ᵥ Bs i *ᵥ x) ≤ x ⬝ᵥ Y *ᵥ x) → (∀ j k, ‖Dm j k‖ ≤ K) →
    (Y.map Complex.ofReal).PosDef ∧ ∀ v, ‖form (Y.map Complex.ofReal)⁻¹
      ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v)
      ((Dm + ∑ i, s i • (Bs i).map Complex.ofReal) *ᵥ v)‖ ≤
      (g * K / c + ∑ i, ‖s i‖ / t i) ^ 2 * gnorm (Y.map Complex.ofReal) v ^ 2 := by
  intro g a Y Bs Dm s t c K hc hK hY hcY hB ht hBt hD
  have hBs : ∀ i, (Bs i).IsSymm := fun i =>
    IsSymm.ext fun j k => by simpa using (hB i).isHermitian.apply j k
  have hYpos : ∀ v : Fin g → ℂ, c * ∑ j, ‖v j‖ ^ 2 ≤ (form (Y.map ofReal) v v).re := fun v => by
    rw [re_form_map, sum_norm_sq, mul_add]; exact add_le_add (hcY _) (hcY _)
  have hPD : (Y.map ofReal).PosDef := by
    refine posDef_iff.2 ⟨isHermitian_map hY, fun v hv => ?_⟩
    obtain ⟨j, hj⟩ := Function.ne_iff.1 hv
    have hS : 0 < ∑ j, ‖v j‖ ^ 2 :=
      Finset.sum_pos' (fun _ _ => sq_nonneg _) ⟨j, Finset.mem_univ _, pow_pos (norm_pos_iff.2 hj) 2⟩
    have h1 := hYpos v
    rw [form_map_self hY] at h1 ⊢
    rw [ofReal_re] at h1
    rw [Complex.zero_lt_real]
    linarith [mul_pos hc hS]
  have hYpsd := hPD.posSemidef
  have hBpsd : ∀ i, ((Bs i).map ofReal).PosSemidef := fun i =>
    posSemidef_map (hBs i) fun x => by simpa using (hB i).dotProduct_mulVec_nonneg x
  have hgB : ∀ i w, t i * gnorm ((Bs i).map ofReal) w ^ 2 ≤ gnorm (Y.map ofReal) w ^ 2 :=
    fun i w => by
      rw [gnorm_sq (hBpsd i), gnorm_sq hYpsd, re_form_map, re_form_map, mul_add]
      exact add_le_add (hBt i _) (hBt i _)
  have hgY : ∀ w : Fin g → ℂ, c * ∑ j, ‖w j‖ ^ 2 ≤ gnorm (Y.map ofReal) w ^ 2 := fun w => by
    rw [gnorm_sq hYpsd]; exact hYpos w
  have hgc : 0 ≤ (g : ℝ) / c := div_nonneg (Nat.cast_nonneg _) hc.le

  have hDb : ∀ u v : Fin g → ℂ, ‖u ⬝ᵥ Dm *ᵥ v‖ ≤
      g * K / c * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v := by
    intro u v
    have h1 : ‖u ⬝ᵥ Dm *ᵥ v‖ ≤ K * ((∑ j, ‖u j‖) * ∑ k, ‖v k‖) := by
      simp only [dotProduct, mulVec]
      calc _ ≤ ∑ j, ‖u j * ∑ k, Dm j k * v k‖ := norm_sum_le _ _
        _ ≤ ∑ j, ‖u j‖ * ∑ k, K * ‖v k‖ := by
          refine Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul]
          refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans
            (Finset.sum_le_sum fun k _ => ?_)) (norm_nonneg _)
          rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hD j k) (norm_nonneg _)
        _ = _ := by rw [← Finset.mul_sum, ← Finset.sum_mul]; ring
    have hs : ∀ w : Fin g → ℂ, (∑ j, ‖w j‖) ^ 2 ≤ g / c * gnorm (Y.map ofReal) w ^ 2 :=
      fun w => by
        refine sq_sum_le_card_mul_sum_sq.trans ?_
        rw [Finset.card_univ, Fintype.card_fin, div_mul_eq_mul_div, le_div_iff₀ hc]
        nlinarith [hgY w, (Nat.cast_nonneg g : (0 : ℝ) ≤ g)]
    have hab : (∑ j, ‖u j‖) * (∑ k, ‖v k‖) ≤
        g / c * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v := by
      rw [← pow_le_pow_iff_left₀ (by positivity)
        (mul_nonneg (mul_nonneg hgc (gnorm_nonneg _ _)) (gnorm_nonneg _ _)) two_ne_zero]
      calc ((∑ j, ‖u j‖) * (∑ k, ‖v k‖)) ^ 2 = (∑ j, ‖u j‖) ^ 2 * (∑ k, ‖v k‖) ^ 2 := mul_pow _ _ _
        _ ≤ (g / c * gnorm (Y.map ofReal) u ^ 2) * (g / c * gnorm (Y.map ofReal) v ^ 2) :=
          mul_le_mul (hs u) (hs v) (sq_nonneg _) (mul_nonneg hgc (sq_nonneg _))
        _ = _ := by ring
    calc _ ≤ K * ((∑ j, ‖u j‖) * ∑ k, ‖v k‖) := h1
      _ ≤ K * (g / c * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v) :=
        mul_le_mul_of_nonneg_left hab hK
      _ = _ := by ring

  have hBb : ∀ i (u v : Fin g → ℂ), ‖u ⬝ᵥ (Bs i).map ofReal *ᵥ v‖ ≤
      gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v / t i := by
    intro i u v
    rw [dotProduct_mulVec_eq_form ((hBs i).map _)]
    refine (norm_form_le (hBpsd i) _ _).trans ?_
    rw [gnorm_map_star]
    rw [← pow_le_pow_iff_left₀ (mul_nonneg (gnorm_nonneg _ _) (gnorm_nonneg _ _))
      (div_nonneg (mul_nonneg (gnorm_nonneg _ _) (gnorm_nonneg _ _)) (ht i).le) two_ne_zero]
    have a1 : ∀ w, gnorm ((Bs i).map ofReal) w ^ 2 ≤ gnorm (Y.map ofReal) w ^ 2 / t i := fun w => by
      rw [le_div_iff₀ (ht i), mul_comm]; exact hgB i w
    calc (gnorm ((Bs i).map ofReal) v * gnorm ((Bs i).map ofReal) u) ^ 2 =
          gnorm ((Bs i).map ofReal) v ^ 2 * gnorm ((Bs i).map ofReal) u ^ 2 := mul_pow _ _ _
      _ ≤ (gnorm (Y.map ofReal) v ^ 2 / t i) * (gnorm (Y.map ofReal) u ^ 2 / t i) :=
          mul_le_mul (a1 v) (a1 u) (sq_nonneg _) (div_nonneg (sq_nonneg _) (ht i).le)
      _ = _ := by ring

  have hPb : ∀ u v : Fin g → ℂ, ‖u ⬝ᵥ (Dm + ∑ i, s i • (Bs i).map ofReal) *ᵥ v‖ ≤
      (g * K / c + ∑ i, ‖s i‖ / t i) * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v := by
    intro u v
    rw [add_mulVec, sum_mulVec, dotProduct_add, dotProduct_finsetSum]
    refine (norm_add_le _ _).trans ?_
    have h2 : ‖∑ i, u ⬝ᵥ (s i • (Bs i).map ofReal) *ᵥ v‖ ≤
        ∑ i, ‖s i‖ / t i * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [smul_mulVec, dotProduct_smul, smul_eq_mul, norm_mul]
      calc _ ≤ ‖s i‖ * (gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v / t i) :=
            mul_le_mul_of_nonneg_left (hBb i u v) (norm_nonneg _)
        _ = _ := by ring
    calc _ ≤ g * K / c * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v +
          ∑ i, ‖s i‖ / t i * gnorm (Y.map ofReal) u * gnorm (Y.map ofReal) v :=
          add_le_add (hDb u v) h2
      _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]; ring

  refine ⟨hPD, fun v => ?_⟩
  have hdet : IsUnit (Y.map ofReal).det := (isUnit_iff_isUnit_det _).1 hPD.isUnit
  set x := (Dm + ∑ i, s i • (Bs i).map ofReal) *ᵥ v with hx
  set q := (Y.map ofReal)⁻¹ *ᵥ star x with hq
  have hF : form (Y.map ofReal)⁻¹ x x = q ⬝ᵥ (Dm + ∑ i, s i • (Bs i).map ofReal) *ᵥ v := by
    rw [form]; exact dotProduct_comm _ _
  have hsq : star q = (Y.map ofReal)⁻¹ *ᵥ x := by
    rw [hq, star_mulVec, star_star, (isHermitian_map hY).inv.eq, ← mulVec_transpose,
      transpose_nonsing_inv, (hY.map _).eq]
  have hq2 : gnorm (Y.map ofReal) q ^ 2 = (form (Y.map ofReal)⁻¹ x x).re := by
    rw [gnorm_sq hYpsd]
    simp only [form]
    rw [hsq, mulVec_mulVec, mul_nonsing_inv _ hdet, one_mulVec, dotProduct_comm]
  have hb := hPb q v
  rw [← hF] at hb
  have hre : gnorm (Y.map ofReal) q ^ 2 ≤ ‖form (Y.map ofReal)⁻¹ x x‖ := hq2 ▸ re_le_norm _
  have h2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
  rcases (norm_nonneg (form (Y.map ofReal)⁻¹ x x)).eq_or_lt with h0 | h0
  · rw [← h0]; positivity
  · refine le_of_mul_le_mul_right ?_ h0
    calc ‖form (Y.map ofReal)⁻¹ x x‖ * ‖form (Y.map ofReal)⁻¹ x x‖ =
          ‖form (Y.map ofReal)⁻¹ x x‖ ^ 2 := by ring
      _ ≤ _ := h2
      _ = (g * K / c + ∑ i, ‖s i‖ / t i) ^ 2 * gnorm (Y.map ofReal) v ^ 2 *
          gnorm (Y.map ofReal) q ^ 2 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hre (by positivity)

end GlobalTheory.HodgeCurvPoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypersurfacePartGeometricIrreducibleSpreads
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

theorem hypersurface_part_preirreducible_spreads : ∀ (A : Type) [CommRing A] (σ : Type) [Finite σ] (f g : MvPolynomial σ A) (i : σ), (∀ (k : Type) [Field k] (ψ : A →+* k), MvPolynomial.map ψ f ≠ 0) → (∀ (k : Type) [Field k] (ψ : A →+* k) (Q : σ → k), MvPolynomial.eval Q (MvPolynomial.map ψ f) = 0 → MvPolynomial.eval Q (MvPolynomial.map ψ g) ≠ 0 → MvPolynomial.eval Q (MvPolynomial.pderiv i (MvPolynomial.map ψ f)) ≠ 0) → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map φ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map φ g}) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → IsPreirreducible (PrimeSpectrum.zeroLocus {MvPolynomial.map ψ f} \ PrimeSpectrum.zeroLocus {MvPolynomial.map ψ g}) := by
  intro A _ σ _ f g i h0 hd Ω _ _ φ hirr
  have h3 := GlobalTheory.T.no_splitting_factorisation_of_pderiv_ne_zero Ω σ (MvPolynomial.map φ f) (MvPolynomial.map φ g) i f.totalDegree
    (hd Ω φ) hirr
  obtain ⟨a, I, ha, hI, h⟩ := GlobalTheory.T.splitting_absence_spreads_alt A σ f g f.totalDegree Ω φ h3
  refine ⟨a, I, ha, hI, fun k _ _ ψ hψa hψI => ?_⟩
  refine GlobalTheory.T.hypersurface_diff_isPreirreducible_of_no_splitting k σ (MvPolynomial.map ψ f) (MvPolynomial.map ψ g) f.totalDegree
    (h0 k ψ) ?_ (h k ψ hψa hψI)
  exact Finset.sup_mono (MvPolynomial.support_map_subset ψ f)

end GlobalTheory
end

