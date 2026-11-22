import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0093
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0091
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0094
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0095
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveCharZeroTensorRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0027
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0096
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleSpaceTensorOfPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preirreducibleSpace_tensor_of_pullback' : ∀ (X S : Scheme.{0}) (f : X ⟶ S) (V : S.Opens) (W : X.Opens) (h : W ≤ f ⁻¹ᵁ V) (hV : IsAffineOpen V) (hW : IsAffineOpen W) (k : Type) [Field k] [Algebra Γ(S, V) k] [Algebra Γ(S, V) Γ(X, W)], algebraMap Γ(S, V) Γ(X, W) = (f.appLE V W h).hom → PreirreducibleSpace ↥(pullback (W.ι ≫ f) (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) k)) ≫ hV.fromSpec)) → PreirreducibleSpace (PrimeSpectrum (k ⊗[Γ(S, V)] Γ(X, W))) := by
  first | exact @GlobalTheory.preirreducibleSpace_tensor_of_pullback | exact GlobalTheory.preirreducibleSpace_tensor_of_pullback | (intros; apply GlobalTheory.preirreducibleSpace_tensor_of_pullback <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreirreducibleTensorLocalizationAwayStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preirreducible_tensor_localization_away : ∀ (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (b : B) (k : Type) [Field k] [Algebra A k], PreirreducibleSpace (PrimeSpectrum (k ⊗[A] B)) → PreirreducibleSpace (PrimeSpectrum (k ⊗[A] Localization.Away b)) := by
  first | exact @GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway | exact GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway | (intros; apply GlobalTheory.preirreducibleSpace_primeSpectrum_tensor_localizationAway <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimaryTorsionDivisibleAndTorsionEqIdealTorsionStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primaryTorsion_divisible_and_torsion_eq_ideal_torsion : ∀ (E : Type) [Field E] [NumberField E] (M : Type) [AddCommGroup M] [Module (𝓞 E) M] (g : ℕ) (I : Ideal (𝓞 E)), g.Prime → Ideal.absNorm I = g → (g : 𝓞 E) ∉ I ^ 2 → (∀ x : M, ∃ y : M, g • y = x) → (∀ (j : ℕ) (x : M), (∀ a ∈ I ^ j, a • x = 0) → ∃ y : M, g • y = x ∧ ∀ a ∈ I ^ (j + 1), a • y = 0) ∧ (∀ (j : ℕ) (x : M), (∀ a ∈ I ^ j, a • x = 0) → g • x = 0 → ∀ a ∈ I, a • x = 0) := by
  first | exact @GlobalTheory.primaryTorsion_divisible_and_gTorsion | exact GlobalTheory.primaryTorsion_divisible_and_gTorsion | (intros; apply GlobalTheory.primaryTorsion_divisible_and_gTorsion <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdArgRealUnitEqOneStatement
section
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_arg_real_unit_eq_one' : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (q : ℕ), q.Prime → 2 < q →
    ∀ u : (𝓞 E)ˣ, (u : 𝓞 E) - 1 ∈ Ideal.span {((q : ℕ) : 𝓞 E)} →
    (∀ φ : E →+* ℂ, starRingEnd ℂ (φ ((u : 𝓞 E) : E)) = φ ((u : 𝓞 E) : E)) →
    ∏ w : InfinitePlace E, (w.embedding ((u : 𝓞 E) : E) / ((‖w.embedding ((u : 𝓞 E) : E)‖ : ℝ) : ℂ)) = 1 := by
  first | exact @GlobalTheory.prod_arg_real_unit_eq_one | exact GlobalTheory.prod_arg_real_unit_eq_one | (intros; apply GlobalTheory.prod_arg_real_unit_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdClassGroupMk0EqOfLinearEquivPiStatement
section
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_classGroup_mk0_eq_of_linearEquiv_pi : ∀ (R : Type) [CommRing R] [IsDedekindDomain R] (ι : Type) [Fintype ι] (I J : ι → (Ideal R)⁰), Nonempty (((i : ι) → (I i : Ideal R)) ≃ₗ[R] ((i : ι) → (J i : Ideal R))) → ∏ i, ClassGroup.mk0 (I i) = ∏ i, ClassGroup.mk0 (J i) := by
  first | exact @GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv | exact GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv | (intros; apply GlobalTheory.prod_classGroup_mk0_eq_of_pi_linearEquiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdFourMapsEqOneStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_four_maps_lam_pow_eq_one : ∀ (U : Type) [CommGroup U] {r : ℕ} (W A : Matrix (Fin r) (Fin r) ℤ) (lam : Fin r → Fin r → U), (∀ k l, lam k l = lam l k) → W = (W + W.transpose) * A → ∏ a : Fin 4, ∏ i, ∏ j, (∏ k, ∏ l, lam k l ^ ((![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a i k * (![1 + A, 1, A, 0] : Fin 4 → Matrix (Fin r) (Fin r) ℤ) a j l)) ^ ((![1, -2, -1, 2] : Fin 4 → ℤ) a * W i j) = 1 := by
  first | exact @GlobalTheory.SymmProd.prod_four_maps_eq_one | exact GlobalTheory.SymmProd.prod_four_maps_eq_one | (intros; apply GlobalTheory.SymmProd.prod_four_maps_eq_one <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdRpowDecayIsBigOCocompactStatement
section
open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prod_rpow_decay_isBigO_cocompact' : ∀ (ι : Type) [Fintype ι] (g : ι → ℝ → ℂ) (b : ℝ), 0 ≤ b → (∀ i, ∃ C : ℝ, ∀ t : ℝ, ‖g i t‖ ≤ C * (1 + |t|) ^ (-b)) → (fun v : EuclideanSpace ℝ ι => ∏ i, g i (v i)) =O[Filter.cocompact (EuclideanSpace ℝ ι)] (fun v => ‖v‖ ^ (-b)) := by
  first | exact @GlobalTheory.prod_rpow_decay_isBigO_cocompact | exact GlobalTheory.prod_rpow_decay_isBigO_cocompact | (intros; apply GlobalTheory.prod_rpow_decay_isBigO_cocompact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveBaseChangeOfPresentationMatrixSplitStatement
section
open CategoryTheory Limits TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_baseChange_of_presentation_matrix_split : ∀ (R B M : Type) [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M]
    [Module R M] (n m : ℕ) (π : (Fin n → R) →ₗ[R] M), Function.Surjective π →
    ∀ (r : Fin m → Fin n → R), Submodule.span R (Set.range r) = LinearMap.ker π →
    ∀ (v : Fin n → Fin n → B) (w : Fin n → Fin m → B),
    (∀ b l, ∑ a, algebraMap R B (r b a) * v a l = 0) →
    (∀ a l, v a l = (if a = l then 1 else 0) + ∑ b, w a b * algebraMap R B (r b l)) →
    Module.Projective B (B ⊗[R] M) := by
  first | (exact @GlobalTheory.projective_baseChange_of_presentation_split) | (exact GlobalTheory.projective_baseChange_of_presentation_split) | (intros; apply GlobalTheory.projective_baseChange_of_presentation_split <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjectiveCharZeroTensorRingOfIntegersStatement
section
open NumberField
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_charZero_tensor_ringOfIntegers' : ∀ (F : Type) [Field F] [NumberField F] (k : Type) [Field k] [CharZero k] (M : Type 1) [AddCommGroup M] [Module (k ⊗[ℤ] 𝓞 F) M], Module.Projective (k ⊗[ℤ] 𝓞 F) M := by
  first | exact @GlobalTheory.projective_charZero_tensor_ringOfIntegers | exact GlobalTheory.projective_charZero_tensor_ringOfIntegers | (intros; apply GlobalTheory.projective_charZero_tensor_ringOfIntegers <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSquareSectionsGlueOfBasis
section
open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option autoImplicit false

namespace GlobalTheory.PinchLift

theorem app_res {X Y : Scheme.{0}} (f : Y ⟶ X) {W W' : X.Opens} (h : W' ≤ W) (s : Γ(X, W)) :
    (f.app W').hom ((X.presheaf.map (homOfLE h).op).hom s) =
      (Y.presheaf.map ((Opens.map f.base).map (homOfLE h)).op).hom ((f.app W).hom s) := by
  rw [← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, Scheme.Hom.naturality]
  rfl

theorem compat_res {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z)
    {W W' : X.Opens} (h : W' ≤ W) (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W))
    (hab : (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
      (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b) :
    (i'.appLE (p ⁻¹ᵁ W') (i' ⁻¹ᵁ (p ⁻¹ᵁ W') ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W')) inf_le_left).hom
        ((X'.presheaf.map ((Opens.map p.base).map (homOfLE h)).op).hom a) =
      (p'.appLE (i ⁻¹ᵁ W') (i' ⁻¹ᵁ (p ⁻¹ᵁ W') ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W')) inf_le_right).hom
        ((Z.presheaf.map ((Opens.map i.base).map (homOfLE h)).op).hom b) := by
  have hV : i' ⁻¹ᵁ (p ⁻¹ᵁ W') ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W') ≤ i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W) :=
    fun x hx => ⟨h hx.1, h hx.2⟩
  have := congrArg (Z'.presheaf.map (homOfLE hV).op).hom hab
  simp only [← ConcreteCategory.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE] at this ⊢
  exact this

theorem unique_of_basis {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z)
    (B : Set X.Opens) (hbasis : ∀ (W : X.Opens) (x : X), x ∈ W → ∃ W' ∈ B, x ∈ W' ∧ W' ≤ W)
    (hB : ∀ W ∈ B, ∀ (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W)),
      (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
        (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b →
      ∃! s : Γ(X, W), (p.app W).hom s = a ∧ (i.app W).hom s = b)
    (W : X.Opens) (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W))
    (hab : (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
      (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b)
    (s s' : Γ(X, W)) (hs : (p.app W).hom s = a ∧ (i.app W).hom s = b)
    (hs' : (p.app W).hom s' = a ∧ (i.app W).hom s' = b) : s = s' := by
  have hcover : W ≤ ⨆ j : {W' : X.Opens // W' ∈ B ∧ W' ≤ W}, j.1 := by
    intro x hx
    obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W x hx
    exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
  refine X.sheaf.eq_of_locally_eq' (fun j : {W' : X.Opens // W' ∈ B ∧ W' ≤ W} => j.1) W
    (fun j => homOfLE j.2.2) hcover s s' fun j => ?_
  have hc := compat_res p i i' p' j.2.2 a b hab
  refine (hB j.1 j.2.1 _ _ hc).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
  · exact (app_res p j.2.2 s).trans (congrArg _ hs.1)
  · exact (app_res i j.2.2 s).trans (congrArg _ hs.2)
  · exact (app_res p j.2.2 s').trans (congrArg _ hs'.1)
  · exact (app_res i j.2.2 s').trans (congrArg _ hs'.2)

theorem glues_of_basis : ∀ {X X' Z Z' : Scheme.{0}} (p : X' ⟶ X) (i : Z ⟶ X) (i' : Z' ⟶ X') (p' : Z' ⟶ Z)
    (B : Set X.Opens), (∀ (W : X.Opens) (x : X), x ∈ W → ∃ W' ∈ B, x ∈ W' ∧ W' ≤ W) →
    (∀ W ∈ B, ∀ (a : Γ(X', p ⁻¹ᵁ W)) (b : Γ(Z, i ⁻¹ᵁ W)),
      (i'.appLE (p ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_left).hom a =
        (p'.appLE (i ⁻¹ᵁ W) (i' ⁻¹ᵁ (p ⁻¹ᵁ W) ⊓ p' ⁻¹ᵁ (i ⁻¹ᵁ W)) inf_le_right).hom b →
      ∃! s : Γ(X, W), (p.app W).hom s = a ∧ (i.app W).hom s = b) → GlobalTheory.PinchLift.Glues p i i' p' := by
  intro X X' Z Z' p i i' p' B hbasis hB W a b hab
  let I := {W' : X.Opens // W' ∈ B ∧ W' ≤ W}
  have hcover : W ≤ ⨆ j : I, j.1 := by
    intro x hx
    obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W x hx
    exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
  choose t ht using fun j : I => (hB j.1 j.2.1 _ _ (compat_res p i i' p' j.2.2 a b hab)).exists
  have hcompat : TopCat.Presheaf.IsCompatible X.sheaf.1 (fun j : I => j.1) t := by
    intro j k
    have hjk : j.1 ⊓ k.1 ≤ W := inf_le_left.trans j.2.2
    refine unique_of_basis p i i' p' B hbasis hB (j.1 ⊓ k.1) _ _ (compat_res p i i' p' hjk a b hab) _ _
      ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · refine (app_res p inf_le_left (t j)).trans ?_
      rw [(ht j).1, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    · refine (app_res i inf_le_left (t j)).trans ?_
      rw [(ht j).2, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    · refine (app_res p inf_le_right (t k)).trans ?_
      rw [(ht k).1, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
    · refine (app_res i inf_le_right (t k)).trans ?_
      rw [(ht k).2, ← ConcreteCategory.comp_apply, ← Functor.map_comp]; rfl
  obtain ⟨s, hs, -⟩ := X.sheaf.existsUnique_gluing' (fun j : I => j.1) W (fun j => homOfLE j.2.2)
    hcover t hcompat
  have key : (p.app W).hom s = a ∧ (i.app W).hom s = b := by
    constructor
    · have hcov' : p ⁻¹ᵁ W ≤ ⨆ j : I, p ⁻¹ᵁ j.1 := by
        intro x hx
        obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W (p.base x) hx
        exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
      refine X'.sheaf.eq_of_locally_eq' (fun j : I => p ⁻¹ᵁ j.1) (p ⁻¹ᵁ W)
        (fun j => (Opens.map p.base).map (homOfLE j.2.2)) hcov' _ _ fun j => ?_
      refine (app_res p j.2.2 s).symm.trans ?_
      rw [show (X.presheaf.map (homOfLE j.2.2).op).hom s = t j from hs j]
      exact (ht j).1
    · have hcov' : i ⁻¹ᵁ W ≤ ⨆ j : I, i ⁻¹ᵁ j.1 := by
        intro x hx
        obtain ⟨W', hW'B, hxW', hle⟩ := hbasis W (i.base x) hx
        exact Opens.mem_iSup.2 ⟨⟨W', hW'B, hle⟩, hxW'⟩
      refine Z.sheaf.eq_of_locally_eq' (fun j : I => i ⁻¹ᵁ j.1) (i ⁻¹ᵁ W)
        (fun j => (Opens.map i.base).map (homOfLE j.2.2)) hcov' _ _ fun j => ?_
      refine (app_res i j.2.2 s).symm.trans ?_
      rw [show (X.presheaf.map (homOfLE j.2.2).op).hom s = t j from hs j]
      exact (ht j).2
  exact ⟨s, key, fun s' hs' => unique_of_basis p i i' p' B hbasis hB W a b hab s' s hs' key⟩

end GlobalTheory.PinchLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PushoutResidueLinearIndependentStatement
section
open IsLocalRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pushout_residue_linearIndependent' : ∀ (T D A B : Type) [CommRing T] [CommRing D] [CommRing A] [CommRing B] [IsLocalRing T] [IsLocalRing D] [Algebra T D] [Algebra T A] [Algebra D B] [Algebra A B] [Algebra T B] [IsScalarTower T D B] [IsScalarTower T A B] [Algebra.IsPushout T D A B], (maximalIdeal T).map (algebraMap T D) = maximalIdeal D → ∀ (n : ℕ) (x : Fin n → A), (∀ c : Fin n → T, ∑ i, c i • x i ∈ (maximalIdeal T).map (algebraMap T A) → ∀ i, c i ∈ maximalIdeal T) → ∀ d : Fin n → D, ∑ i, d i • algebraMap A B (x i) ∈ (maximalIdeal D).map (algebraMap D B) → ∀ i, d i ∈ maximalIdeal D := by
  first | exact @GlobalTheory.pushout_residue_linearIndependent | exact GlobalTheory.pushout_residue_linearIndependent | (intros; apply GlobalTheory.pushout_residue_linearIndependent <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosed
section
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam

namespace GlobalTheory.QFam.QAllSubring

variable {R : Subring ℂ} {N : ℕ}

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.const {c : ℂ} (hc : c ∈ R) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun _ => c := by
  refine ⟨fun n => if n = 0 then c else 0, ?_, fun n => ?_⟩
  · rw [_root_.GlobalTheory.QFam.hasQ_iff]
    intro τ
    have h := hasSum_single (f := fun n : ℕ =>
      (if n = 0 then c else 0) * Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N) ^ n) 0
      (fun m hm => by simp [hm])
    simpa using h
  · show (if n = 0 then c else 0) ∈ R
    split_ifs
    · exact hc
    · exact R.zero_mem

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.add {f g : ℍ → ℂ} (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f)
    (hg : _root_.GlobalTheory.QFam.QAll (· ∈ R) N g) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ + g τ := by
  obtain ⟨a, ha, haR⟩ := hf
  obtain ⟨b, hb, hbR⟩ := hg
  refine ⟨fun n => a n + b n, ?_, fun n => R.add_mem (haR n) (hbR n)⟩
  rw [_root_.GlobalTheory.QFam.hasQ_iff] at ha hb ⊢
  intro τ
  simpa [add_mul] using (ha τ).add (hb τ)

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.sub {f g : ℍ → ℂ} (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f)
    (hg : _root_.GlobalTheory.QFam.QAll (· ∈ R) N g) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ - g τ := by
  obtain ⟨a, ha, haR⟩ := hf
  obtain ⟨b, hb, hbR⟩ := hg
  refine ⟨fun n => a n - b n, ?_, fun n => R.sub_mem (haR n) (hbR n)⟩
  rw [_root_.GlobalTheory.QFam.hasQ_iff] at ha hb ⊢
  intro τ
  simpa [sub_mul] using (ha τ).sub (hb τ)

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.mul {f g : ℍ → ℂ} (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f)
    (hg : _root_.GlobalTheory.QFam.QAll (· ∈ R) N g) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ * g τ := by
  obtain ⟨a, ha, haR⟩ := hf
  obtain ⟨b, hb, hbR⟩ := hg
  refine ⟨fun n => ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2, ?_,
    fun n => R.sum_mem fun kl _ => R.mul_mem (haR kl.1) (hbR kl.2)⟩
  rw [_root_.GlobalTheory.QFam.hasQ_iff] at ha hb ⊢
  intro τ
  set q := Complex.exp (2 * ↑Real.pi * Complex.I * ↑τ / ↑N)
  have hsa : Summable fun n => ‖a n * q ^ n‖ := summable_norm_iff.mpr (ha τ).summable
  have hsb : Summable fun n => ‖b n * q ^ n‖ := summable_norm_iff.mpr (hb τ).summable
  have hterm : ∀ n, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n,
      a kl.1 * q ^ kl.1 * (b kl.2 * q ^ kl.2) =
      (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal n, a kl.1 * b kl.2) * q ^ n := by
    intro n
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun kl hkl => ?_
    rw [← Finset.HasAntidiagonal.mem_antidiagonal.mp hkl, pow_add]
    ring
  have hs := summable_norm_sum_mul_antidiagonal_of_summable_norm hsa hsb
  have heq := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsa hsb
  rw [(ha τ).tsum_eq, (hb τ).tsum_eq] at heq
  rw [heq]
  simp only [hterm] at hs ⊢
  exact (summable_norm_iff.mp hs).hasSum

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.pow {f : ℍ → ℂ} (k : ℕ)
    (hf : _root_.GlobalTheory.QFam.QAll (· ∈ R) N f) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ ^ k := by
  induction k with
  | zero => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.one_mem
  | succ k ih => simpa [pow_succ] using _root_.GlobalTheory.QFam.QAllSubring.mul ih hf

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.sum {κ : Type} (s : Finset κ) {f : κ → ℍ → ℂ}
    (hf : ∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.zero_mem
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact _root_.GlobalTheory.QFam.QAllSubring.add (hf i (Finset.mem_insert_self i s))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in
theorem _root_.GlobalTheory.QFam.QAllSubring.prod {κ : Type} (s : Finset κ) {f : κ → ℍ → ℂ}
    (hf : ∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) :
    _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using _root_.GlobalTheory.QFam.QAllSubring.const (N := N) R.one_mem
  | insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact _root_.GlobalTheory.QFam.QAllSubring.mul (hf i (Finset.mem_insert_self i s))
      (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators in
variable {R : Subring ℂ} {N : ℕ} in

theorem _root_.GlobalTheory.QFam.QAllSubring.ring_closed : ∀ (R : Subring ℂ) (N : ℕ), 0 < N →
    (∀ c ∈ R, _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun _ => c) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ + g τ) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ - g τ) ∧
    (∀ f g, _root_.GlobalTheory.QFam.QAll (· ∈ R) N f → _root_.GlobalTheory.QFam.QAll (· ∈ R) N g →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ * g τ) ∧
    (∀ f (k : ℕ), _root_.GlobalTheory.QFam.QAll (· ∈ R) N f →
      _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => f τ ^ k) ∧
    (∀ (κ : Type) (s : Finset κ) (f : κ → ℍ → ℂ),
      (∀ k ∈ s, _root_.GlobalTheory.QFam.QAll (· ∈ R) N (f k)) →
      (_root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∑ k ∈ s, f k τ) ∧
        _root_.GlobalTheory.QFam.QAll (· ∈ R) N fun τ => ∏ k ∈ s, f k τ) := by
  intro R N _
  exact ⟨fun c hc => _root_.GlobalTheory.QFam.QAllSubring.const hc,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.add hf hg,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.sub hf hg,
    fun f g hf hg => _root_.GlobalTheory.QFam.QAllSubring.mul hf hg,
    fun f k hf => _root_.GlobalTheory.QFam.QAllSubring.pow k hf,
    fun κ s f hf => ⟨_root_.GlobalTheory.QFam.QAllSubring.sum s hf,
      _root_.GlobalTheory.QFam.QAllSubring.prod s hf⟩⟩

end GlobalTheory.QFam.QAllSubring
end

