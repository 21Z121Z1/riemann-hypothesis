import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2202
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0101
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0609
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2200
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2182
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueHomExtensionOfIsOpenImmersion
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SemiAbExtDomain

variable {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]

theorem existsUnique_hom_extension_generic (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : Over (Sp R)) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (f : (Over.pullback (spMap (algebraMap R K))).obj G ⟶ (Over.pullback (spMap (algebraMap R K))).obj H)
    [IsMonHom f] :
    ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback (spMap (algebraMap R K))).map F = f :=
  GlobalTheory.semiAbelianHomExtension_holds.fractionField R K G H hG hH f

theorem existsUnique_iso_extension_generic (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
    (G H : Over (Sp R)) [GrpObj G] [GrpObj H] (hG : IsSemiAbelian G) (hH : IsSemiAbelian H)
    (e : (Over.pullback (spMap (algebraMap R K))).obj G ≅ (Over.pullback (spMap (algebraMap R K))).obj H)
    [IsMonHom e.hom] :
    ∃! E : G ≅ H, IsMonHom E.hom ∧ (Over.pullback (spMap (algebraMap R K))).map E.hom = e.hom :=
  GlobalTheory.semiAbelianHomExtension_holds.generic_existsUnique_iso (GlobalTheory.IsNormalScheme.pred _)
    (.fractionField R K) hG hH e

end GlobalTheory.SemiAbExtDomain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitMinorApproximation
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

namespace GlobalTheory.MinorBound

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

theorem norm_det_le_one {m : ℕ} (B : Matrix (Fin m) (Fin m) K) (hB : ∀ i j, ‖B i j‖ ≤ 1) :
    ‖B.det‖ ≤ 1 := by
  rw [Matrix.det_apply]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun σ _ => ?_
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp only [h, one_smul, Units.neg_smul, norm_neg] <;>
  · rw [norm_prod]; exact Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hB _ _

theorem norm_prod_sub_prod_le {Idx : Type*} (s : Finset Idx) (x y : Idx → K) {ε : ℝ} (hε : 0 ≤ ε)
    (hx : ∀ i, ‖x i‖ ≤ 1) (hy : ∀ i, ‖y i‖ ≤ 1) (hxy : ∀ i, ‖x i - y i‖ ≤ ε) :
    ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ ≤ ε := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hε
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have : x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i
        = x a * (∏ i ∈ s, x i - ∏ i ∈ s, y i) + (x a - y a) * ∏ i ∈ s, y i := by ring
    rw [this]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]; nlinarith [hx a, ih, norm_nonneg (x a), norm_nonneg (∏ i ∈ s, x i - ∏ i ∈ s, y i)]
    · rw [norm_mul, norm_prod]
      have h1 : ∏ i ∈ s, ‖y i‖ ≤ 1 := Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hy i
      nlinarith [hxy a, norm_nonneg (x a - y a), Finset.prod_nonneg fun i (_ : i ∈ s) => norm_nonneg (y i)]

theorem norm_det_sub_det_le {m : ℕ} (B C : Matrix (Fin m) (Fin m) K) {ε : ℝ} (hε : 0 ≤ ε)
    (hB : ∀ i j, ‖B i j‖ ≤ 1) (hC : ∀ i j, ‖C i j‖ ≤ 1) (hBC : ∀ i j, ‖B i j - C i j‖ ≤ ε) :
    ‖B.det - C.det‖ ≤ ε := by
  rw [Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hε fun σ _ => ?_
  rw [← smul_sub]
  have := norm_prod_sub_prod_le Finset.univ (fun i => B (σ i) i) (fun i => C (σ i) i) hε
    (fun i => hB _ _) (fun i => hC _ _) (fun i => hBC _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp only [h, one_smul, Units.neg_smul, norm_neg] <;>
    exact this

theorem det_mul_expand {m g : ℕ} (M : Matrix (Fin m) (Fin g) K) (A : Matrix (Fin g) (Fin m) K) :
    (M * A).det = ∑ κ : Fin m → Fin g, (∏ i, M i (κ i)) * (Matrix.of fun k j => A (κ k) j).det := by
  classical
  have h1 : (M * A) = fun i => ∑ k, M i k • A k := by
    ext i j; simp [Matrix.mul_apply, Finset.sum_apply]
  have h2 := (Matrix.detRowAlternating : (Fin m → K) [⋀^Fin m]→ₗ[K] K).toMultilinearMap.map_sum
    (fun i k => M i k • A k)
  simp only [AlternatingMap.coe_multilinearMap] at h2
  rw [Matrix.det, h1, h2]
  refine Finset.sum_congr rfl fun f _ => ?_
  have h3 := (Matrix.detRowAlternating : (Fin m → K) [⋀^Fin m]→ₗ[K] K).toMultilinearMap.map_smul_univ
    (fun i => M i (f i)) (fun i => A (f i))
  simp only [AlternatingMap.coe_multilinearMap] at h3
  rw [h3, smul_eq_mul]
  rfl

theorem exists_minor_ge (p : ℕ) [hp : Fact p.Prime] (n m g : ℕ) (d : ℂ_[p]) (A Cc : Fin g → Fin m → ℂ_[p])
    (G : Matrix (Fin m) (Fin m) ℂ_[p]) (M : Fin m → Fin g → ℂ_[p]) (hd : d ≠ 0)
    (hCc : ∀ k j, ‖Cc k j‖ ≤ 1) (hCA : ∀ k j, ‖Cc k j - A k j‖ ≤ (p : ℝ)⁻¹ ^ n)
    (hM : ∀ i k, ‖M i k‖ ≤ 1) (hG : ‖G.det‖ = 1) (hrel : ∀ i j, d * G i j = ∑ k, M i k * A k j) :
    ∃ K : Fin m → Fin g, ‖d‖ ^ m ≤ ‖(Matrix.of fun k j => A (K k) j).det‖ ∧
      ‖(Matrix.of fun k j => A (K k) j).det‖ ≤ 1 ∧
      ‖(Matrix.of fun k j => Cc (K k) j).det - (Matrix.of fun k j => A (K k) j).det‖ ≤ (p : ℝ)⁻¹ ^ n := by
  have hε : 0 ≤ (p : ℝ)⁻¹ ^ n := by positivity
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hε1 : (p : ℝ)⁻¹ ^ n ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ hp1)
  have hA : ∀ k j, ‖A k j‖ ≤ 1 := fun k j => by
    have h : A k j = Cc k j + -(Cc k j - A k j) := by ring
    rw [h]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hCc k j) ?_)
    rw [norm_neg]; exact (hCA k j).trans hε1
  have hdet : d ^ m * G.det = (Matrix.of M * Matrix.of A).det := by
    have h : d • G = Matrix.of M * Matrix.of A := by
      ext i j; simp [Matrix.mul_apply, hrel]
    rw [← h, Matrix.det_smul, Fintype.card_fin]
  rw [det_mul_expand] at hdet
  have hGne : G.det ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hG; exact zero_ne_one hG
  by_cases hne : Nonempty (Fin m → Fin g)
  · obtain ⟨K0, hK0⟩ := Finite.exists_max (fun κ : Fin m → Fin g => ‖(Matrix.of fun k j => A (κ k) j).det‖)
    refine ⟨K0, ?_, norm_det_le_one _ fun i j => hA _ _,
      norm_det_sub_det_le _ _ hε (fun i j => hCc _ _) (fun i j => hA _ _) (fun i j => hCA _ _)⟩
    have h1 : ‖d‖ ^ m = ‖d ^ m * G.det‖ := by rw [norm_mul, norm_pow, hG, _root_.mul_one]
    rw [h1, hdet]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun κ _ => ?_
    rw [norm_mul, norm_prod]
    have hP : ∏ i, ‖Matrix.of M i (κ i)‖ ≤ 1 :=
      Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => hM _ _
    calc (∏ i, ‖Matrix.of M i (κ i)‖) * ‖(Matrix.of fun k j => Matrix.of A (κ k) j).det‖
        ≤ 1 * ‖(Matrix.of fun k j => A (κ k) j).det‖ :=
          mul_le_mul_of_nonneg_right hP (norm_nonneg _)
      _ ≤ _ := by rw [_root_.one_mul]; exact hK0 κ
  · exfalso
    haveI : IsEmpty (Fin m → Fin g) := not_nonempty_iff.mp hne
    rw [Finset.univ_eq_empty, Finset.sum_empty] at hdet
    exact mul_ne_zero (pow_ne_zero _ hd) hGne hdet

end GlobalTheory.MinorBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitOfCocycleRightActionCharZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

namespace GlobalTheory

theorem exists_unit_of_cocycle_rightAction_charZero :
    ∀ (K : Type) [Field K] [CharZero K] (Γ : Type) [Group Γ] [Finite Γ] (σ : Γ → K →+* K),
    (∀ γ δ a, σ (γ * δ) a = σ δ (σ γ a)) → ∀ (c : Γ → Kˣ),
    (∀ γ δ, (c (γ * δ) : K) = σ δ (c γ) * c δ) → (∀ γ, (∀ a, σ γ a = a) → c γ = 1) →
    ∃ f : Kˣ, ∀ γ, σ γ f = c γ * f := by
  intro K _ _ Γ _ _ σ hσ c hc htriv
  classical
  haveI := Fintype.ofFinite Γ
  have h1 : ∀ a, σ 1 a = a := by
    intro a
    have e := hσ 1 1 a
    rw [mul_one] at e
    exact (σ 1).injective e.symm
  have key : ∀ γ δ, (σ δ (c γ : K))⁻¹ = (c δ : K) * ((c (γ * δ) : K))⁻¹ := by
    intro γ δ
    rw [hc γ δ, mul_inv, mul_left_comm, mul_inv_cancel₀ (Units.ne_zero _), mul_one]
  let F : K → K := fun b => ∑ γ, ((c γ : K))⁻¹ * σ γ b
  have hF : ∀ b δ, σ δ (F b) = c δ * F b := by
    intro b δ
    simp only [F, map_sum, map_mul, map_inv₀, Finset.mul_sum]
    apply Fintype.sum_equiv (Equiv.mulRight δ)
    intro γ
    simp only [Equiv.coe_mulRight]
    rw [key γ δ, hσ]
    ring
  have hex : ∃ b, F b ≠ 0 := by
    by_contra hno
    push_neg at hno
    let φ : Γ → (K →* K) := fun γ => (σ γ : K →* K)
    let s : Finset (K →* K) := Finset.univ.image φ
    let g : (K →* K) → K := fun ψ => ∑ γ ∈ Finset.univ.filter (fun γ => φ γ = ψ), ((c γ : K))⁻¹
    have hli := linearIndependent_monoidHom K K
    have hsum : ∑ ψ ∈ s, g ψ • (ψ : K → K) = 0 := by
      funext b
      rw [Finset.sum_apply, Pi.zero_apply, ← hno b]
      simp only [Pi.smul_apply, smul_eq_mul, g, Finset.sum_mul]
      have hterm : ∀ ψ ∈ s, ∑ i ∈ Finset.univ.filter (fun γ => φ γ = ψ), ((c i : K))⁻¹ * ψ b
          = ∑ i ∈ Finset.univ.filter (fun γ => φ γ = ψ), ((c i : K))⁻¹ * σ i b := fun ψ _ =>
        Finset.sum_congr rfl fun γ hγ => by rw [← (Finset.mem_filter.mp hγ).2]; rfl
      rw [Finset.sum_congr rfl hterm, Finset.sum_fiberwise_of_maps_to
        (fun γ _ => Finset.mem_image_of_mem φ (Finset.mem_univ γ))]
    have hz := linearIndependent_iff'.mp hli s g hsum (φ 1)
      (Finset.mem_image_of_mem φ (Finset.mem_univ 1))
    have hterm : ∀ γ ∈ Finset.univ.filter (fun γ => φ γ = φ 1), ((c γ : K))⁻¹ = 1 := by
      intro γ hγ
      rw [Finset.mem_filter] at hγ
      have hid : ∀ a, σ γ a = a := fun a => (DFunLike.congr_fun hγ.2 a).trans (h1 a)
      rw [htriv γ hid]
      simp
    have hcard : g (φ 1) = ((Finset.univ.filter (fun γ => φ γ = φ 1)).card : K) := by
      simp only [g]
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, mul_one]
    rw [hcard, Nat.cast_eq_zero, Finset.card_eq_zero] at hz
    have hmem : (1 : Γ) ∈ Finset.univ.filter (fun γ => φ γ = φ 1) := by simp
    rw [hz] at hmem
    simp at hmem
  obtain ⟨b, hb⟩ := hex
  refine ⟨Units.mk0 (F b) hb, fun γ => ?_⟩
  simp only [Units.val_mk0]
  exact hF b γ

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsValuationExtensionField
section
open CategoryTheory Limits AlgebraicGeometry NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CompHt GlobalTheory.AllWt

namespace GlobalTheory.PlaceExt

theorem valuation_lt_one_iff_inv {L : Type*} [Field L] (V : ValuationSubring L) (y : L) :
    V.valuation y < 1 ↔ y = 0 ∨ y⁻¹ ∉ V := by
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · have hpos : 0 < V.valuation y := zero_lt_iff.2 ((map_ne_zero _).2 hy)
    rw [← V.valuation_le_one_iff, map_inv₀, not_le, one_lt_inv₀ hpos]
    simp [hy]

theorem exists_lift {L M C : Type*} [Field L] [Field M] [Algebra L M] [Algebra.IsAlgebraic L M] [Field C]
    [IsAlgClosed C] (f : L →+* C) : ∃ h : M →+* C, ∀ x, h (algebraMap L M x) = f x := by
  letI := f.toAlgebra
  exact ⟨(IsAlgClosed.lift : M →ₐ[L] C), fun x => (IsAlgClosed.lift : M →ₐ[L] C).commutes x⟩

theorem exists_extend_compatible : ∀ (F F' : IntermediateField ℚ ℂ) (hle : F ≤ F'), FiniteDimensional ℚ F' →
    ∀ (W : ValuationSubring ℂ) (K : Type) [Field K] [IsAlgClosed K] (O : ValuationSubring K) (g : F →+* K),
    (∀ x : F, (x : ℂ) ∈ W ↔ g x ∈ O) → ∃ g' : F' →+* K, (∀ x : F, g' (IntermediateField.inclusion hle x) = g x) ∧
      ∀ x : F', (x : ℂ) ∈ W → g' x ∈ O := by
  intro F F' hle hfin W K _ _ O g hg
  haveI : FiniteDimensional ℚ F :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion hle).injective
  haveI : NumberField F := ⟨⟩
  letI : Algebra F F' := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ F F' := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : Algebra.IsAlgebraic F F' := Algebra.IsAlgebraic.tower_top (K := ℚ) F
  let Ω := AlgebraicClosure F'
  haveI : Algebra.IsAlgebraic F Ω := Algebra.IsAlgebraic.trans F F' Ω
  haveI : IsAlgClosure F Ω := ⟨inferInstance, inferInstance⟩
  obtain ⟨g₀, hg₀⟩ := exists_lift (M := F') g
  obtain ⟨ι₂, hι₂⟩ := exists_lift (M := Ω) g₀
  obtain ⟨ι₁, hι₁⟩ := exists_lift (M := Ω) (algebraMap F' ℂ)
  have k₁ : ∀ y : F, ι₁ (algebraMap F Ω y) = (y : ℂ) := fun y => by
    rw [IsScalarTower.algebraMap_apply F F' Ω, hι₁]; rfl
  have k₂ : ∀ y : F, ι₂ (algebraMap F Ω y) = g y := fun y => by
    rw [IsScalarTower.algebraMap_apply F F' Ω, hι₂, hg₀]
  let A := W.comap ι₁
  let A' := O.comap ι₂
  have h : ∀ x : 𝓞 F, A.valuation (algebraMap F Ω x) < 1 ↔ A'.valuation (algebraMap F Ω x) < 1 := by
    intro x
    generalize (x : F) = y
    rw [valuation_lt_one_iff_inv, valuation_lt_one_iff_inv, ValuationSubring.mem_comap,
      ValuationSubring.mem_comap, ← map_inv₀, k₁, k₂, hg]
  obtain ⟨σ, hσ⟩ := GlobalTheory.InertiaLift.exists_smul_eq (F := F) (Ω := Ω) h
  refine ⟨ι₂.comp (σ.toRingEquiv.toRingHom.comp (algebraMap F' Ω)), fun x => ?_, fun x hx => ?_⟩
  · change ι₂ (σ (algebraMap F' Ω (algebraMap F F' x))) = g x
    rw [← IsScalarTower.algebraMap_apply, σ.commutes, k₂]
  · change ι₂ (σ (algebraMap F' Ω x)) ∈ O
    by_contra hn
    have h1 : A'.valuation (σ (algebraMap F' Ω x)⁻¹) < 1 := by
      rw [valuation_lt_one_iff_inv, map_inv₀, inv_inv]
      exact Or.inr hn
    rcases (valuation_lt_one_iff_inv _ _).1 ((hσ _).1 h1) with h2 | h2
    · have : x = 0 := by simpa using h2
      subst this
      exact hn (by simp)
    · apply h2
      rw [inv_inv, ValuationSubring.mem_comap, hι₁]
      exact hx

end GlobalTheory.PlaceExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorFieldImageOpenImmersion
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LogKS Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.LogKS.FieldImage

variable {Z Z' : Scheme.{0}} (φ : Z' ⟶ Z) [IsOpenImmersion φ]

def appEquiv (O : Z.Opens) (h : O ≤ φ.opensRange) : Γ(Z, O) ≃+* Γ(Z', φ ⁻¹ᵁ O) :=
  haveI := Scheme.Hom.isIso_app φ O h
  (asIso (φ.app O)).commRingCatIsoToRingEquiv

theorem appEquiv_apply (O : Z.Opens) (h : O ≤ φ.opensRange) (f : Γ(Z, O)) :
    appEquiv φ O h f = (φ.app O).hom f := rfl

theorem app_res {W W' : Z.Opens} (h : W' ≤ W) (f : Γ(Z, W)) :
    (φ.app W').hom (resG Z h f) = resG Z' (Scheme.Hom.preimage_mono φ h) ((φ.app W).hom f) := by
  have := congrArg (fun g => g.hom f) (Scheme.Hom.naturality φ (homOfLE h).op)
  simpa [resG] using this

open Classical in

def push (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)) (O : Z.Opens) (f : Γ(Z, O)) : Γ(Z, O) :=
  if h : O ≤ φ.opensRange then (appEquiv φ O h).symm (d (φ ⁻¹ᵁ O) ((φ.app O).hom f)) else 0

theorem app_push (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)) (O : Z.Opens) (h : O ≤ φ.opensRange)
    (f : Γ(Z, O)) : (φ.app O).hom (push φ d O f) = d (φ ⁻¹ᵁ O) ((φ.app O).hom f) := by
  rw [push, dif_pos h, ← appEquiv_apply φ O h, RingEquiv.apply_symm_apply]

theorem le_range {W₀ : Z'.Opens} {O : Z.Opens} (hO : O ≤ φ ''ᵁ W₀) : O ≤ φ.opensRange :=
  hO.trans (Scheme.Hom.image_le_opensRange φ W₀)

theorem preimage_le {W₀ : Z'.Opens} {O : Z.Opens} (hO : O ≤ φ ''ᵁ W₀) : φ ⁻¹ᵁ O ≤ W₀ := by
  have := Scheme.Hom.preimage_mono φ hO
  rwa [Scheme.Hom.preimage_image_eq] at this

theorem inj_app {O : Z.Opens} (h : O ≤ φ.opensRange) : Function.Injective (φ.app O).hom :=
  (appEquiv φ O h).injective

theorem isField_push (W₀ : Z'.Opens) (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)) (hd : IsField W₀ d) :
    IsField (φ ''ᵁ W₀) (push φ d) := by
  obtain ⟨hadd, hmul, hres⟩ := hd
  refine ⟨fun W hW f f' => ?_, fun W hW f f' => ?_, fun W W' h hW f => ?_⟩
  · apply inj_app φ (le_range φ hW)
    rw [map_add, app_push φ d W (le_range φ hW), app_push φ d W (le_range φ hW),
      app_push φ d W (le_range φ hW), map_add, hadd _ (preimage_le φ hW)]
  · apply inj_app φ (le_range φ hW)
    rw [map_add, map_mul, map_mul, app_push φ d W (le_range φ hW), app_push φ d W (le_range φ hW),
      app_push φ d W (le_range φ hW), map_mul, hmul _ (preimage_le φ hW)]
  · have hW' : W' ≤ φ ''ᵁ W₀ := h.trans hW
    apply inj_app φ (le_range φ hW')
    rw [app_push φ d W' (le_range φ hW'), app_res, app_res, app_push φ d W (le_range φ hW),
      hres _ _ _ (preimage_le φ hW)]

end GlobalTheory.LogKS.FieldImage

theorem GlobalTheory.LogKS.isField_image : ∀ (Z Z' : Scheme.{0}) (φ : Z' ⟶ Z) [IsOpenImmersion φ] (W₀ : Z'.Opens) (d : ∀ O : Z'.Opens, Γ(Z', O) → Γ(Z', O)), IsField W₀ d → ∃ d₂ : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O), IsField (φ ''ᵁ W₀) d₂ ∧ ∀ (O : Z.Opens), O ≤ φ ''ᵁ W₀ → ∀ f : Γ(Z, O), (φ.app O).hom (d₂ O f) = d (φ ⁻¹ᵁ O) ((φ.app O).hom f) := by
  intro Z Z' φ _ W₀ d hd
  exact ⟨FieldImage.push φ d, FieldImage.isField_push φ W₀ d hd,
    fun O hO f => FieldImage.app_push φ d O (FieldImage.le_range φ hO) f⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsVectorGroupDeterminantsNeZero
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenericGroupDet

theorem det_delta_ne_zero (S : Type) [Group S] [Fintype S] [DecidableEq S] (f : S → ℂ)
    (hf : ∀ h, f h = if h = 1 then 1 else 0) :
    (Matrix.of fun h g : S => f (h * g)).det ≠ 0 := by
  have : (Matrix.of fun h g : S => f (h * g)) = (Equiv.inv S).permMatrix ℂ := by
    ext h g
    simp [Equiv.Perm.permMatrix, PEquiv.toMatrix_apply, hf, mul_eq_one_iff_inv_eq]
  rw [this, Matrix.det_permutation]
  simp

theorem exists_combination_delta (F V S J : Type) [Field F] [Algebra F ℂ] [AddCommGroup V] [Module F V]
    [Group S] [Fintype S] [DecidableEq S] [Fintype J]
    (ev : V →ₗ[F] (S → ℂ)) (r : J → S) (W : Submodule F V) (h1 : ∃ j, r j = 1)
    (h2 : ∀ v ∈ W, ∀ h, h ∉ Set.range r → ev v h = 0)
    (h3 : ∀ a : J → ℂ, (∀ v ∈ W, ∑ j, a j * ev v (r j) = 0) → a = 0) :
    ∃ (n : ℕ) (c : Fin n → ℂ) (w : Fin n → V), (∀ k, w k ∈ W) ∧
      ∀ h, ∑ k, c k * ev (w k) h = if h = 1 then 1 else 0 := by
  classical
  set s : Set (J → ℂ) := (fun v => fun j => ev v (r j)) '' (W : Set V) with hs
  have htop : Submodule.span ℂ s = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    have hφ : ∀ x : J → ℂ, φ x = ∑ j, x j * φ (fun j' => if j = j' then 1 else 0) := fun x => by
      rw [LinearMap.pi_apply_eq_sum_univ φ x]
      simp [smul_eq_mul]
    have ha := h3 (fun j => φ (fun j' => if j = j' then 1 else 0)) fun v hv => by
      have := hle (Submodule.subset_span ⟨v, hv, rfl⟩)
      rw [LinearMap.mem_ker, hφ] at this
      simpa [mul_comm] using this
    apply hφ0
    refine LinearMap.ext fun x => ?_
    rw [hφ x, LinearMap.zero_apply]
    exact Finset.sum_eq_zero fun j _ => by rw [congrFun ha j]; simp
  let b : J → ℂ := fun j => if r j = 1 then 1 else 0
  have hb : b ∈ Submodule.span ℂ s := htop ▸ Submodule.mem_top
  obtain ⟨n, c, g, hg⟩ := Submodule.mem_span_set'.1 hb
  choose w hw hwg using fun k => (g k).2
  refine ⟨n, c, w, hw, fun h => ?_⟩
  by_cases hr : h ∈ Set.range r
  · obtain ⟨j, rfl⟩ := hr
    have := congrFun hg j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, b] at this
    rw [← this]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← hwg k]
  · have h1' : h ≠ 1 := by
      rintro rfl
      obtain ⟨j, hj⟩ := h1
      exact hr ⟨j, hj⟩
    rw [if_neg h1']
    exact Finset.sum_eq_zero fun k _ => by rw [h2 _ (hw k) h hr, mul_zero]

theorem exists_vec_det_ne_zero (F : Type) [Field F] [CharZero F] [Algebra F ℂ] (V : Type) [AddCommGroup V] [Module F V]
    (S : Type) [Group S] [Fintype S] [DecidableEq S] (ι : Type) [Finite ι] (ev : ι → V →ₗ[F] (S → ℂ))
    (J : ι → Type) [∀ i, Fintype (J i)] (r : ∀ i, J i → S) (W : ι → Submodule F V)
    (h1 : ∀ i, ∃ j, r i j = 1) (h2 : ∀ i, ∀ v ∈ W i, ∀ h, h ∉ Set.range (r i) → ev i v h = 0)
    (h3 : ∀ i (a : J i → ℂ), (∀ v ∈ W i, ∑ j, a j * ev i v (r i j) = 0) → a = 0) :
    ∃ v : V, ∀ i, (Matrix.of fun h g : S => ev i v (h * g)).det ≠ 0 := by
  classical
  have := Fintype.ofFinite ι
  choose n c w hw hcw using fun i => exists_combination_delta F V S (J i) (ev i) (r i) (W i) (h1 i) (h2 i) (h3 i)
  let vec : (Σ i, Fin (n i)) → V := fun p => w p.1 p.2
  let P : ι → MvPolynomial (Σ i, Fin (n i)) ℂ := fun i =>
    Matrix.det (Matrix.of fun h g : S => ∑ p, MvPolynomial.X p * MvPolynomial.C (ev i (vec p) (h * g)))
  have hP : ∀ i (x : (Σ i, Fin (n i)) → ℂ), MvPolynomial.eval x (P i) =
      (Matrix.of fun h g : S => ∑ p, x p * ev i (vec p) (h * g)).det := by
    intro i x
    rw [RingHom.map_det]
    congr 1
    ext h g
    simp [RingHom.mapMatrix_apply]
  have hPi : ∀ i, P i ≠ 0 := by
    intro i hz
    let x : (Σ i, Fin (n i)) → ℂ := fun p => if p.1 = i then c p.1 p.2 else 0
    have hx : ∀ h, ∑ p, x p * ev i (vec p) h = if h = 1 then 1 else 0 := by
      intro h
      rw [← hcw i h, Fintype.sum_sigma, Finset.sum_eq_single i]
      · simp [x, vec]
      · intro b _ hb
        exact Finset.sum_eq_zero fun k _ => by simp [x, hb]
      · simp
    have := det_delta_ne_zero S _ hx
    rw [← hP, hz, map_zero] at this
    exact this rfl
  have hQ : (∏ i, P i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hPi i
  obtain ⟨x, hx, hQx⟩ : ∃ x ∈ Set.pi Set.univ (fun _ : (Σ i, Fin (n i)) => Set.range (algebraMap F ℂ)),
      MvPolynomial.eval x (∏ i, P i) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hQ (MvPolynomial.funext_set (fun _ => Set.range (algebraMap F ℂ))
      (fun _ => Set.infinite_range_of_injective (algebraMap F ℂ).injective)
      fun x hx => by rw [hcon x hx, map_zero])
  choose t ht using fun p => hx p (Set.mem_univ p)
  refine ⟨∑ p, t p • vec p, fun i => ?_⟩
  have hne : MvPolynomial.eval x (P i) ≠ 0 := by
    rw [map_prod] at hQx
    exact Finset.prod_ne_zero_iff.1 hQx i (Finset.mem_univ _)
  rw [hP] at hne
  convert hne using 2
  ext h g
  simp [map_sum, Finset.sum_apply, Algebra.smul_def, ht]

end GlobalTheory.GenericGroupDet
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendsVanishingOfSimplePoleMulExtendsStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.extends_vanishing_of_simplePole_mul_extends : ∀ {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} [IsReduced Y] {O : Y.Opens}, Dense (O : Set Y) → ∀ {P B N : LB Y} (C : ProdChart P B N) (ω : H0 p P O), GlobalTheory.LogCanonicalReflexive.SimplePoleAlong O C ω → ∀ (G : H0 p N ⊤) (f : H0 p B O), H0.restr le_top G = C.mul ω f → ∃ g : H0 p B ⊤, (∀ y, y ∉ O → ∀ i hi, H0.germ i y (memTop y) hi g ∈ IsLocalRing.maximalIdeal (Y.presheaf.stalk y)) ∧ H0.restr le_top g = f := by
  first | exact @GlobalTheory.LogCanonicalReflexive.extends_vanishing_of_mul | exact GlobalTheory.LogCanonicalReflexive.extends_vanishing_of_mul | (intros; apply GlobalTheory.LogCanonicalReflexive.extends_vanishing_of_mul <;> assumption)
end

