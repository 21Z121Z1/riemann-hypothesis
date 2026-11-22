import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0015
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0014
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocallyPrincipalOfConormalRankOne
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0013

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartierAtOfLocallyPrincipalStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartier_at_of_locally_principal : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData) (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)), LocPrincipal (Z.ideal U) q.asIdeal → CartAt Z (U.2.fromSpec q) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_locPrincipal | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_locPrincipal | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_locPrincipal <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.CartierAtOfNotMemSupportStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartier_at_of_not_mem_support : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) (x : X), x ∉ J.support → CartAt J x := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.cartAt_of_notMem_support <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConormalFiniteProjectiveOfSmoothStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conormal_finite_projective_of_smooth : ∀ {k A : Type} [Field k] [CommRing A] (φ : k →+* A) (I : Ideal A), φ.Smooth → ((Ideal.Quotient.mk I).comp φ).Smooth → Module.Finite (A ⧸ I) I.Cotangent ∧ Module.Projective (A ⧸ I) I.Cotangent := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent | exact GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Conormal.finite_projective_cotangent <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ConormalRankOneOfLocallyPrincipalStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conormal_rank_one_of_locally_principal : ∀ {A : Type} [CommRing A] [IsDomain A] (I : Ideal A) [Module.Finite (A ⧸ I) I.Cotangent] [Module.Projective (A ⧸ I) I.Cotangent] (P : PrimeSpectrum (A ⧸ I)), LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I)) → Module.rankAtStalk I.Cotangent P = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.rankAtStalk_cotangent_eq_one | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.rankAtStalk_cotangent_eq_one | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.rankAtStalk_cotangent_eq_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsSmoothAffinePresentationPairStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_affine_presentation_pair : ∀ {k : Type} [Field k] {X : Scheme.{0}} (g : X ⟶ Sp k) (Z : X.IdealSheafData) (U : X.affineOpens), Smooth g → Smooth (Z.subschemeι ≫ g) → ∃ φ : k →+* Γ(X, U.1), φ.Smooth ∧ ((Ideal.Quotient.mk (Z.ideal U)).comp φ).Smooth := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart | exact GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Charts.smooth_affine_chart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocallyPrincipalOfCartierAtStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_principal_of_cartier_at : ∀ {X : Scheme.{0}} [IsIntegral X] (Z : X.IdealSheafData) (U : X.affineOpens) (q : PrimeSpectrum Γ(X, U.1)), CartAt Z (U.2.fromSpec q) → LocPrincipal (Z.ideal U) q.asIdeal := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_cartAt | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_cartAt | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_cartAt <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LocallyPrincipalOfConormalRankOneStatement
section
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.locally_principal_of_conormal_rank_one : ∀ {A : Type} [CommRing A] [IsDomain A] [IsNoetherianRing A] (I : Ideal A) [Module.Finite (A ⧸ I) I.Cotangent] [Module.Projective (A ⧸ I) I.Cotangent] (P : PrimeSpectrum (A ⧸ I)), Module.rankAtStalk I.Cotangent P = 1 → LocPrincipal I (P.asIdeal.comap (Ideal.Quotient.mk I)) := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one | exact GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.CentreOver.locPrincipal_of_rankAtStalk_eq_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.MeasureUniformizerMultipleMatrices
section
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QL.Vol

noncomputable def scalarInvGL {F : Type} [Field F] (m : ℕ) (x : F) (hx : x ≠ 0) : GL (Fin m) F :=
  Units.map (Matrix.scalar (Fin m) : F →+* Matrix (Fin m) (Fin m) F).toMonoidHom (Units.mk0 x⁻¹ (inv_ne_zero hx))

theorem coe_scalarInvGL {F : Type} [Field F] (m : ℕ) (x : F) (hx : x ≠ 0) :
    ((scalarInvGL m x hx : GL (Fin m) F) : Matrix (Fin m) (Fin m) F) = Matrix.diagonal (fun _ => x⁻¹) := by
  simp [scalarInvGL, Matrix.scalar_apply]

theorem preimage_intMat_eq {F : Type} [Field F] (O : Subring F) {ϖ : F} (hϖ : ϖ ≠ 0) (n m : ℕ) :
    (fun x : Matrix (Fin n) (Fin m) F => x * ((scalarInvGL m ϖ hϖ : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) ⁻¹'
      intMat O n m = (IIset O ϖ : Set (Matrix (Fin n) (Fin m) F)) := by
  ext x
  simp only [Set.mem_preimage, intMat, Set.mem_setOf_eq, IIset, coe_scalarInvGL, Matrix.mul_diagonal]
  constructor
  · intro h i j
    exact ⟨x i j * ϖ⁻¹, h i j, by field_simp⟩
  · intro h i j
    obtain ⟨o, ho, e⟩ := h i j
    have : x i j * ϖ⁻¹ = o := by rw [e]; field_simp
    rw [this]; exact ho

theorem vol_IIset : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] {O : Subring F} {ϖ : F} {nrm : AbsoluteValue F ℝ} {q : ℕ}, LF O ϖ nrm q → ∀ n m : ℕ, ∀ (dx : Measure (Matrix (Fin n) (Fin m) F)), dx.IsAddLeftInvariant → dx (intMat O n m) = 1 → dx (IIset O ϖ : Set (Matrix (Fin n) (Fin m) F)) = ENNReal.ofReal ((q : ℝ) ^ (-((n * m : ℕ) : ℤ))) := by
  intro F _ _ _ _ _ _ O ϖ nrm q hL n m dx hinv hone
  obtain ⟨hB, hOpen, -, -, -, -⟩ := GlobalTheory.T.matrix_additive_haar_normalized hL n m
  have hscale := (GlobalTheory.T.matrix_haar_right_translate hL n m dx hinv hone).1 (scalarInvGL m ϖ hL.ne)
  have hcont : Continuous (fun x : Matrix (Fin n) (Fin m) F =>
      x * ((scalarInvGL m ϖ hL.ne : GL (Fin m) F) : Matrix (Fin m) (Fin m) F)) :=
    continuous_id.matrix_mul continuous_const
  have hmap := congrArg (fun μ : Measure (Matrix (Fin n) (Fin m) F) => μ (intMat O n m)) hscale
  rw [Measure.map_apply hcont.measurable hOpen.measurableSet, preimage_intMat_eq O hL.ne n m] at hmap
  rw [hmap, Measure.smul_apply, hone, smul_eq_mul, mul_one]
  congr 1
  rw [coe_scalarInvGL, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    map_pow, map_inv₀, hL.nrm_pi, inv_inv, ← inv_pow, ← pow_mul, _root_.zpow_neg, zpow_natCast, inv_pow, mul_comm m n]

end GlobalTheory.CompanionTheory.QL.Vol
end

