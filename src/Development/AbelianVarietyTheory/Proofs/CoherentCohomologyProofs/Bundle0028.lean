import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0027
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubeTotalComplexAcyclicOfSlicesInductionOnCard
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0025
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0016

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsHomogeneousFormEqHighPowerSectionStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_homogeneousForm_eq_highPowerSection : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB Y) (m : ℕ) (s : Fin (m + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∃ t₀ : ℕ, ∀ t : ℕ, t₀ ≤ t → ∀ σ : LB.Sec (pw H t), ∃ F : MvPolynomial (Fin (m + 1)) R, F.IsHomogeneous t ∧ ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) F := by
  first | exact @GlobalTheory.AbLaw.exists_form_eq_sec_pw | exact GlobalTheory.AbLaw.exists_form_eq_sec_pw | (intros; apply GlobalTheory.AbLaw.exists_form_eq_sec_pw <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FiniteCechLineBundleHomology
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

namespace GlobalTheory.AbLaw

theorem finite_cechLB_homology (R : Type) [CommRing R] (Y : Scheme.{0})
    (f : Y ⟶ Spec (CommRingCat.of R)) [IsNoetherianRing R] (H : LB Y) (m : ℕ)
    (s : Fin (m + 1) → LB.Sec H) (M : LB Y) (hH : H.IsLB) (hM : M.IsLB) (hv : VeryAmpleBy f H s)
    (p : ℕ) : Module.Finite R ((cechLB f M (fun i => nonzeroLocus (s i))).homology p) := by
  obtain ⟨N, _, _, _, _, 𝒩, _, _, hN, hφ⟩ :=
    exists_finite_graded_module_secCube R Y f H m s M hH hM hv
  obtain ⟨φ, hφ⟩ := hφ 0
  have := finite_grCech_homology (Fin (m + 1)) R N 𝒩 hN 0 p
  have : IsIso (cechComplexMap φ) := isIso_cechComplexMap φ hφ
  let e : cechComplex (grCube (Fin (m + 1)) 𝒩 0) ≅ cechLB f M (fun i => nonzeroLocus (s i)) :=
    asIso (cechComplexMap φ) ≪≫ (cechLBTwZero f _ hM hH).symm
  exact Module.Finite.equiv (HomologicalComplex.homologyMapIso e p).toLinearEquiv

end GlobalTheory.AbLaw
end

