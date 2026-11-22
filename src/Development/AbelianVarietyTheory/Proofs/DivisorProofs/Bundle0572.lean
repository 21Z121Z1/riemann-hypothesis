import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0539
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0552
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0555
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0010
import ReciprocityTheory.AnalyticForms.RegularLocalRings.ExistsMulMemOfAlgebraMapLocRingEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0392
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0549
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0553
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0356
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0559
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeCongruenceSubgroups
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.UCls.KGrp
open scoped ENNReal TensorProduct

theorem GlobalTheory.UCls.exists_special_reduction : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r M m : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ L : Submodule (𝓞 E) (Fin r → E)) (g : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (g0 : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)) (S : Finset (Fin m)) (Γ : Fin m → Subgroup (GL (Fin r) E)) (Λi : Fin m → Submodule (𝓞 E) (Fin r → E)), 1 ≤ M → SelfDualLat G Λ → IsUA (IsCMField.complexConj E) G g0 → (L : Set (Fin r → E)) = latOf (maximalRealSubfield E) g0 (Λ : Set (Fin r → E)) → (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) = g0.mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) → (∀ i, IsUA (IsCMField.complexConj E) G (g i)) → (∀ i ∈ S, TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M g0.det (g i).det) → (∀ i ∈ S, (Λi i : Set (Fin r → E)) = latOf (maximalRealSubfield E) (g i) (Λ : Set (Fin r → E)) ∧ ∀ γ, γ ∈ Γ i ↔ IsUStab G (Λi i) γ ∧ ∀ x ∈ Λi i, ∃ y ∈ Λi i, (γ : Matrix (Fin r) (Fin r) E) *ᵥ x - x = M • y) → ∃ (γ : Fin m → GL (Fin r) E) (s : Fin m → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), (∀ i ∈ S, (∀ u v, herm G ((γ i : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ i : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) ∧ IsSA G (s i) ∧ ∀ δ : GL (Fin r) E, (δ : Matrix (Fin r) (Fin r) E).det = 1 → (∀ u v, herm G ((δ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((δ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm G u v) → (δ ∈ (Γ i).map (MulAut.conj (γ i)⁻¹).toMonoidHom ↔ IsKM (IsCMField.complexConj E) G (L : Set (Fin r → E)) M ((s i)⁻¹ * ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) * s i))) ∧ ∀ i ∈ S, ∀ j ∈ S, SEquiv G (L : Set (Fin r → E)) M (s i) (s j) → UEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M (g i) (g j) := by
  intro E _ _ _ r M m G Λ L g g0 S Γ Λi hM hΛ hg0 hL hLhat hg hT hΓ
  have hU : ∀ {γ : GL (Fin r) E}, (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) → ∀ x y,
      herm G (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x)
        (((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y := by
    intro γ hγ x y
    rw [← hγ, mulVec_mulVec, mulVec_mulVec, Units.mul_inv, one_mulVec, one_mulVec]
  have hRA : ∀ γ : GL (Fin r) E, (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x)
      ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) →
      IsUA (IsCMField.complexConj E) G (ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E)) :=
    fun γ hγ => GlobalTheory.T.isInvertibleUnitaryAdelicMatrix_of_rational_unitary E r G _ (Matrix.isUnits_det_units γ).ne_zero hγ
  have hR1 : ∀ γ : GL (Fin r) E, ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E) *
      ratM (maximalRealSubfield E) ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = 1 := fun γ => by
    rw [← ratM_mul, Units.mul_inv, ratM_one]
  have hR2 : ∀ γ : GL (Fin r) E, ratM (maximalRealSubfield E) ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *
      ratM (maximalRealSubfield E) (γ : Matrix (Fin r) (Fin r) E) = 1 := fun γ => by
    rw [← ratM_mul, Units.inv_mul, ratM_one]
  have hdet : ∀ γ : Matrix (Fin r) (Fin r) E, (ratM (maximalRealSubfield E) γ).det =
      (1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ γ.det := fun γ =>
    (RingHom.map_det (Algebra.TensorProduct.includeRight : E →ₐ[maximalRealSubfield E]
      RA (maximalRealSubfield E) E).toRingHom γ).symm
  have hex : ∀ i, ∃ (γ : GL (Fin r) E) (k : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), i ∈ S →
      (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) ∧
      IsKM (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M k ∧
      IsSA G (ratM (maximalRealSubfield E) ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i * k⁻¹ * g0⁻¹) := by
    intro i
    by_cases hi : i ∈ S
    swap
    · exact ⟨1, 1, fun h => absurd h hi⟩
    obtain ⟨u, hu, k, hk, hdg⟩ := hT i hi
    obtain ⟨γ, hγ, hγdet⟩ : ∃ γ : GL (Fin r) E, (∀ x y, herm G ((γ : Matrix (Fin r) (Fin r) E) *ᵥ x)
        ((γ : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y) ∧ (0 < r → (γ : Matrix (Fin r) (Fin r) E).det = u) := by
      rcases Nat.eq_zero_or_pos r with hr | hr
      · exact ⟨1, fun x y => by simp, fun h => absurd h (by omega)⟩
      · obtain ⟨γ, h1, h2⟩ := GlobalTheory.T.exists_unitary_with_determinant E r G u hr hΛ.1 hΛ.2.1 hu
        exact ⟨γ, h1, fun _ => h2⟩
    refine ⟨γ, k, fun _ => ⟨hγ, hk, ?_, ?_⟩⟩
    · exact isUA_mul _ G (isUA_mul _ G (isUA_mul _ G (hRA _ (hU hγ)) (hg i)) (isUA_inv _ G hk.1))
        (isUA_inv _ G hg0)
    · rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; simp
      · have hγ1 : ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).det * u = 1 := by
          rw [← hγdet hr, ← det_mul, Units.inv_mul, det_one]
        have e1 : ((1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ
            ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).det : RA (maximalRealSubfield E) E) *
            ((1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ u) = 1 := by
          rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, hγ1, Algebra.TensorProduct.one_def]
        have e2 := Ring.mul_inverse_cancel _ hg0.1
        have e3 := Ring.mul_inverse_cancel _ hk.1.1
        rw [det_mul, det_mul, det_mul, det_nonsing_inv, det_nonsing_inv, hdet, hdg]
        calc _ = (((1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ
            ((γ⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).det : RA (maximalRealSubfield E) E) *
            ((1 : FiniteAdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ⊗ₜ u)) *
            (g0.det * Ring.inverse g0.det) * (k.det * Ring.inverse k.det) := by ring
          _ = 1 := by rw [e1, e2, e3, one_mul, one_mul]
  choose γ k hγk using hex

  refine ⟨γ, fun i => ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
    (k i)⁻¹ * g0⁻¹, ?_, ?_⟩
  · intro i hi
    obtain ⟨hγU, hk, hsSA⟩ := hγk i hi
    refine ⟨hγU, hsSA, fun δ hδdet hδU => ?_⟩
    have hmap : δ ∈ (Γ i).map (MulAut.conj (γ i)⁻¹).toMonoidHom ↔ γ i * δ * (γ i)⁻¹ ∈ Γ i := by
      rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply, inv_inv]
    obtain ⟨hΛi, hΓi⟩ := hΓ i hi
    have hgU : IsUnit (g i) := (Matrix.isUnit_iff_isUnit_det _).2 (hg i).1
    obtain ⟨Λ', hΛ'1, -, -, hΛ'hat⟩ := exists_lattice_latOf (maximalRealSubfield E) E r Λ hgU.unit
      hΛ.2.2.1 hΛ.2.2.2.1
    rw [IsUnit.unit_spec] at hΛ'1 hΛ'hat
    have hhat : (hat (maximalRealSubfield E) (Λi i : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) =
        (g i).mulVec '' (hat (maximalRealSubfield E) (Λ : Set (Fin r → E)) : Set _) := by
      rw [hΛi, ← hΛ'1, hΛ'hat]
    have hrat : ∀ v, fv (maximalRealSubfield E) v ∈ hat (maximalRealSubfield E) (Λi i : Set (Fin r → E)) ↔
        v ∈ Λi i := fun v => by
      rw [← SetLike.mem_coe, hhat, ← SetLike.mem_coe (x := v), hΛi]; rfl
    have hβU : ∀ x y, herm G (((γ i * δ * (γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ x)
        (((γ i * δ * (γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) *ᵥ y) = herm G x y := by
      intro x y
      simp only [Units.val_mul, ← mulVec_mulVec, hγU, hδU, hU hγU]
    have e0 : g0 * g0⁻¹ = 1 := mul_nonsing_inv g0 hg0.1
    have e0' : g0⁻¹ * g0 = 1 := nonsing_inv_mul g0 hg0.1
    have ek : k i * (k i)⁻¹ = 1 := mul_nonsing_inv _ hk.1.1
    have ek' : (k i)⁻¹ * k i = 1 := nonsing_inv_mul _ hk.1.1
    have eg : g i * (g i)⁻¹ = 1 := mul_nonsing_inv _ (hg i).1
    have eg' : (g i)⁻¹ * g i = 1 := nonsing_inv_mul _ (hg i).1
    have c0 : ∀ P, P * g0 * g0⁻¹ = P := fun P => by rw [Matrix.mul_assoc, e0, Matrix.mul_one]
    have c0' : ∀ P, P * g0⁻¹ * g0 = P := fun P => by rw [Matrix.mul_assoc, e0', Matrix.mul_one]
    have ck : ∀ P, P * k i * (k i)⁻¹ = P := fun P => by rw [Matrix.mul_assoc, ek, Matrix.mul_one]
    have ck' : ∀ P, P * (k i)⁻¹ * k i = P := fun P => by rw [Matrix.mul_assoc, ek', Matrix.mul_one]
    have cg : ∀ P, P * g i * (g i)⁻¹ = P := fun P => by rw [Matrix.mul_assoc, eg, Matrix.mul_one]
    have cg' : ∀ P, P * (g i)⁻¹ * g i = P := fun P => by rw [Matrix.mul_assoc, eg', Matrix.mul_one]
    have cR : ∀ P, P * ratM (maximalRealSubfield E) (γ i : Matrix (Fin r) (Fin r) E) *
        ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) = P := fun P => by
      rw [Matrix.mul_assoc, hR1, Matrix.mul_one]
    have hXY : (hat (maximalRealSubfield E) (Λi i : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) =
        (g i * (k i)⁻¹ * g0⁻¹).mulVec '' (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E)) := by
      rw [hhat, ← isKM_image _ G _ M (isKM_inv _ G _ M hk), Set.image_image, hLhat, Set.image_image]
      simp only [mulVec_mulVec, c0']
    have hsinv : (ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
        (k i)⁻¹ * g0⁻¹)⁻¹ = g0 * k i * (g i)⁻¹ * ratM (maximalRealSubfield E) (γ i : Matrix (Fin r) (Fin r) E) := by
      refine Matrix.inv_eq_left_inv ?_
      simp only [← Matrix.mul_assoc, cR, cg', ck, e0]
    have hconj := hatKM_conj (X := (hat (maximalRealSubfield E) (Λi i : Set (Fin r → E)) : Set _))
      (Y := (hat (maximalRealSubfield E) (L : Set (Fin r → E)) : Set (Fin r → RA (maximalRealSubfield E) E))) M
      (A := g i * (k i)⁻¹ * g0⁻¹) (A' := g0 * k i * (g i)⁻¹)
      (P := ratM (maximalRealSubfield E) ((γ i * δ * (γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E))
      (by simp only [← Matrix.mul_assoc, c0', ck', eg]) (by simp only [← Matrix.mul_assoc, cg', ck, e0]) hXY
    have hPeq : g0 * k i * (g i)⁻¹ * ratM (maximalRealSubfield E)
        ((γ i * δ * (γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * (g i * (k i)⁻¹ * g0⁻¹) =
        (ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
        (k i)⁻¹ * g0⁻¹)⁻¹ * ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) *
        (ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
        (k i)⁻¹ * g0⁻¹) := by
      rw [hsinv, Units.val_mul, Units.val_mul, ratM_mul, ratM_mul]
      simp only [Matrix.mul_assoc]
    rw [hPeq] at hconj
    have hsUA := hsSA.1
    have hKUA : IsUA (IsCMField.complexConj E) G ((ratM (maximalRealSubfield E)
        (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i * (k i)⁻¹ * g0⁻¹)⁻¹ *
        ratM (maximalRealSubfield E) (δ : Matrix (Fin r) (Fin r) E) *
        (ratM (maximalRealSubfield E) (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g i *
        (k i)⁻¹ * g0⁻¹)) :=
      isUA_mul _ G (isUA_mul _ G (isUA_inv _ G hsUA) (hRA δ hδU)) hsUA
    have hL5 := GlobalTheory.T.lattice_congruence_iff_completion (maximalRealSubfield E) E r (Λi i) M (γ i * δ * (γ i)⁻¹) hM hrat
    rw [hmap, hΓi]
    constructor
    · rintro ⟨⟨-, h1⟩, h2⟩
      exact ⟨hKUA, hconj.1 (hL5.1 ⟨h1, h2⟩)⟩
    · intro hK
      obtain ⟨h1, h2⟩ := hL5.2 (hconj.2 hK.2)
      exact ⟨⟨hβU, h1⟩, h2⟩

  · intro i hi j hj hSE
    obtain ⟨δ, hδ, κ, hκ, -, hsj⟩ := hSE
    simp only at hsj
    obtain ⟨hγiU, hki, -⟩ := hγk i hi
    obtain ⟨hγjU, hkj, -⟩ := hγk j hj
    have e0' : g0⁻¹ * g0 = 1 := nonsing_inv_mul g0 hg0.1
    have ekj : k j * (k j)⁻¹ = 1 := mul_nonsing_inv _ hkj.1.1
    have egj : g j * (g j)⁻¹ = 1 := mul_nonsing_inv _ (hg j).1
    refine ⟨(γ j : Matrix (Fin r) (Fin r) E) * δ * (((γ i)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E), ?_,
      (k i)⁻¹ * (g0⁻¹ * κ * g0) * k j, ?_, ?_⟩
    · rw [ratM_mul, ratM_mul]
      exact isUA_mul _ G (isUA_mul _ G (hRA _ hγjU) hδ.1) (hRA _ (hU hγiU))
    · exact isKM_mul _ G _ M (isKM_mul _ G _ M (isKM_inv _ G _ M hki) (isKM_conj _ G _ _ M hg0 hLhat hκ)) hkj
    · have hdj : g j = ratM (maximalRealSubfield E) (γ j : Matrix (Fin r) (Fin r) E) *
          (ratM (maximalRealSubfield E) (((γ j)⁻¹ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E) * g j *
            (k j)⁻¹ * g0⁻¹) * g0 * k j := by
        simp only [← Matrix.mul_assoc, hR1 (γ j), Matrix.one_mul]
        rw [Matrix.mul_assoc (g j * (k j)⁻¹), e0', Matrix.mul_one, Matrix.mul_assoc, nonsing_inv_mul _ hkj.1.1,
          Matrix.mul_one]
      rw [hdj, hsj, ratM_mul, ratM_mul]
      simp only [Matrix.mul_assoc]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SncAtOfStalkIdEqSpanProd
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.AnForm.R

namespace GlobalTheory

theorem sncAt_of_stalkId_eq_span_prod : ∀ (Y : Scheme.{0}) [IsLocallyNoetherian Y] (I : Y.IdealSheafData) (y : Y),
    IsRegularLocalRing (Y.presheaf.stalk y) → ∀ (n : ℕ) (r : Fin n → Y.presheaf.stalk y) (T : Finset (Fin n)),
    FinalTheorems.Rsp (Y.presheaf.stalk y) n r → FinalTheorems.stalkId I y = Ideal.span {∏ i ∈ T, r i} → FinalTheorems.SncAt I y := by
  intro Y _ I y hreg n r T hR hI
  refine ⟨hreg, ?_⟩
  choose O hO t ht using fun i => TopCat.Presheaf.exists_germ_eq Y.presheaf (r i)
  have hSo : IsOpen (⋂ i, (O i : Set Y)) := isOpen_iInter_of_finite fun i => (O i).2
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVS⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_iInter.2 hO) hSo
  have hle : ∀ i, V ≤ O i := fun i z hz => Set.mem_iInter.1 (hVS hz) i
  let f : Fin n → Γ(Y, V) := fun i => Y.presheaf.map (homOfLE (hle i)).op (t i)
  have hgf : ∀ i, Y.presheaf.germ V y hyV (f i) = r i := fun i => by
    simp only [f]; rw [TopCat.Presheaf.germ_res_apply]; exact ht i
  let a : Γ(Y, V) := ∏ i ∈ T, f i
  have hga : Y.presheaf.germ V y hyV a = ∏ i ∈ T, r i := by
    simp only [a, map_prod, hgf]
  let V' : Y.affineOpens := ⟨V, hV⟩
  haveI : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian V'
  have hmap := WMult.stalkId_eq_map_germ I y V' hyV
  rw [hI] at hmap

  obtain ⟨h₂, hu₂, hm₂⟩ := IrreducibleComponentPreimages.exists_unit_mul_mem_of_germ_mem hV y hyV (I.ideal V') (t := a)
    (by show _ ∈ Ideal.map (Y.presheaf.germ V y hyV).hom (I.ideal V')
        rw [← hmap, hga]; exact Ideal.mem_span_singleton_self _)

  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (I.ideal V') : (I.ideal V').FG)
  have hgen : ∀ g : s, ∃ d : Γ(Y, V), IsUnit (Y.presheaf.germ V y hyV d) ∧ d * g.1 ∈ Ideal.span {a} := by
    intro g
    apply IrreducibleComponentPreimages.exists_unit_mul_mem_of_germ_mem hV y hyV
    have hg : g.1 ∈ I.ideal V' := hs ▸ Submodule.subset_span g.2
    have : Y.presheaf.germ V y hyV g.1 ∈ Ideal.map (Y.presheaf.germ V y hyV).hom (I.ideal V') :=
      Ideal.mem_map_of_mem _ hg
    rw [← hmap, ← hga, ← Set.image_singleton, ← Ideal.map_span] at this
    exact this
  choose d hdu hdm using hgen
  let h₁ : Γ(Y, V) := ∏ g : s, d g
  have hu₁ : IsUnit (Y.presheaf.germ V y hyV h₁) := by
    simp only [h₁, map_prod]
    exact Finset.prod_induction _ IsUnit (fun _ _ => IsUnit.mul) isUnit_one fun g _ => hdu g
  have hcol : I.ideal V' ≤ Submodule.comap (LinearMap.mulLeft Γ(Y, V) h₁) (Ideal.span {a}) := by
    rw [← hs, Submodule.span_le]
    classical
    intro g hg
    show h₁ * g ∈ Ideal.span {a}
    have e : h₁ = (∏ g' ∈ Finset.univ.erase (⟨g, hg⟩ : s), d g') * d ⟨g, hg⟩ :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ _)).symm
    rw [e, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hdm ⟨g, hg⟩)
  let h : Γ(Y, V) := h₁ * h₂
  have hyD : y ∈ Y.basicOpen h := (Y.mem_basicOpen h y hyV).2 (by
    simp only [h, map_mul]; exact hu₁.mul hu₂)
  let D : Y.affineOpens := Y.affineBasicOpen (U := V') h
  let ρ := Y.presheaf.map (homOfLE (Y.basicOpen_le h)).op
  have hρ : IsUnit (ρ h) := Y.toRingedSpace.isUnit_res_basicOpen h
  have hρ₁ : IsUnit (ρ h₁) := by
    simp only [h, map_mul] at hρ; exact isUnit_of_mul_isUnit_left hρ
  have hρ₂ : IsUnit (ρ h₂) := by
    simp only [h, map_mul] at hρ; exact isUnit_of_mul_isUnit_right hρ
  refine ⟨D, hyD, n, fun i => ρ (f i), T, ?_, ?_⟩
  · have e : (fun i => Y.presheaf.germ D.1 y hyD (ρ (f i))) = r := by
      funext i
      show Y.presheaf.germ (Y.basicOpen h) y hyD (ρ (f i)) = r i
      rw [TopCat.Presheaf.germ_res_apply]
      exact hgf i
    rw [e]; exact hR
  · rw [← I.map_ideal' (U := D) (V := V') (homOfLE (Y.basicOpen_le h)).op]
    show Ideal.map ρ.hom (I.ideal V') = Ideal.span {∏ i ∈ T, ρ (f i)}
    have ha : ∏ i ∈ T, ρ (f i) = ρ a := by simp only [a, map_prod]
    rw [ha]
    apply le_antisymm
    · rw [Ideal.map_le_iff_le_comap]
      intro x hx
      have h1 : h₁ * x ∈ Ideal.span {a} := hcol hx
      have h2 : ρ (h₁ * x) ∈ Ideal.span {ρ a} := by
        rw [← Set.image_singleton, ← Ideal.map_span]; exact Ideal.mem_map_of_mem _ h1
      rw [map_mul, Ideal.unit_mul_mem_iff_mem _ hρ₁] at h2
      exact h2
    · rw [Ideal.span_le, Set.singleton_subset_iff]
      have h2 : ρ (h₂ * a) ∈ Ideal.map ρ.hom (I.ideal V') := Ideal.mem_map_of_mem _ hm₂
      rw [map_mul, Ideal.unit_mul_mem_iff_mem _ hρ₂] at h2
      exact h2
end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyZeroLaurentSurjective
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.MultiplicativeGroupGlobalSections

open LaurentPolynomial in

theorem laurent_ringHom_ext {R S : Type} [CommRing R] [CommRing S] {f g : LaurentPolynomial R →+* S}
    (hC : f.comp C = g.comp C) (hT : f (T 1) = g (T 1)) : f = g := by
  have h1 : f (T 1) * f (T (-1)) = 1 := by rw [← map_mul, ← T_add]; simp
  have h2 : g (T 1) * g (T (-1)) = 1 := by rw [← map_mul, ← T_add]; simp
  have hTm : f (T (-1)) = g (T (-1)) :=
    calc f (T (-1)) = f (T (-1)) * (g (T 1) * g (T (-1))) := by rw [h2, mul_one]
      _ = (f (T 1) * f (T (-1))) * g (T (-1)) := by rw [← hT]; ring
      _ = g (T (-1)) := by rw [h1, one_mul]
  have hTn : ∀ n : ℤ, f (T n) = g (T n) := by
    intro n
    induction n using Int.induction_on with
    | zero => simp [T_zero]
    | succ n ih => rw [T_add, map_mul, map_mul, ih, hT]
    | pred n ih => rw [sub_eq_add_neg, T_add, map_mul, map_mul, ih, hTm]
  apply AddMonoidAlgebra.ringHom_ext
  · intro b
    rw [single_eq_C]
    exact congrArg (fun φ : R →+* S => φ b) hC
  · intro n
    exact hTn n

theorem pull_spMap_id (q : ℕ) (A : Type) [CommRing A] (n i : ℤ) (x : Ht q (sp A) n i) :
    pull _ (spMap (RingHom.id A)) _ n x = x := by
  have h : spMap (RingHom.id A) = 𝟙 (sp A) := by
    simp only [spMap]
    rw [show CommRingCat.ofHom (RingHom.id A) = 𝟙 (CommRingCat.of A) from rfl, Spec.map_id, CategoryTheory.Functor.map_id]
  rw [h, pull_id]

open LaurentPolynomial GmPhiNat in

theorem exists_ht_zero_pull_laurent_eq (q : ℕ) [NeZero q] (R : Type) [CommRing R] (hq : IsUnit (q : R)) (i : ℤ)
    (y : Ht q (sp (LaurentPolynomial R)) 0 i) :
    ∃ z : Ht q (sp R) 0 i, pull _ (spMap (LaurentPolynomial.C : R →+* LaurentPolynomial R)) _ 0 z = y := by
  let ev₁ : LaurentPolynomial R →+* R := eval₂ (RingHom.id R) 1
  have hev : ev₁.comp C = RingHom.id R := RingHom.ext fun a => eval₂_C _ _ a
  refine ⟨pull _ (spMap ev₁) _ 0 y, ?_⟩
  symm
  rw [← sub_eq_zero]
  have hqL : IsUnit (q : LaurentPolynomial R) := by simpa using hq.map (C : R →+* LaurentPolynomial R)
  apply GlobalTheory.EtC.GeomZero.eq_zero_of_geom q (LaurentPolynomial R) hqL i
  intro K _ _ f
  set y' := y - pull _ (spMap (C : R →+* LaurentPolynomial R)) _ 0 (pull _ (spMap ev₁) _ 0 y) with hy'

  have h0 : pull _ (spMap ev₁) _ 0 y' = 0 := by
    rw [hy', map_sub, ← pull_spMap_comp, hev, pull_spMap_id, sub_self]
  let f₀ : R →+* K := f.comp C
  have hT1 : IsUnit (f (T 1)) := by
    refine isUnit_iff_exists_inv.2 ⟨f (T (-1)), ?_⟩
    rw [← map_mul, ← T_add]; simp
  let u : Kˣ := hT1.unit
  let evu : LaurentPolynomial K →+* K := eval₂ (RingHom.id K) u
  have hf : f = evu.comp (laurentMap f₀) := by
    apply laurent_ringHom_ext
    · rw [RingHom.comp_assoc, laurentMap_C, ← RingHom.comp_assoc]
      ext a
      simp [evu, f₀, eval₂_C]
    · simp [evu, laurentMap_T, eval₂_T, u]
  let ev₁K : LaurentPolynomial K →+* K := eval₂ (RingHom.id K) 1
  have hevK : ev₁K.comp C = RingHom.id K := RingHom.ext fun a => eval₂_C _ _ a
  have hcomm : ev₁K.comp (laurentMap f₀) = f₀.comp ev₁ := by
    apply laurent_ringHom_ext
    · rw [RingHom.comp_assoc, laurentMap_C, ← RingHom.comp_assoc, hevK, RingHom.comp_assoc, hev]
      rfl
    · simp [ev₁K, ev₁, laurentMap_T, eval₂_T]
  have hqK : IsUnit (q : K) := by simpa using hq.map f₀
  have hζ : ∃ ζ : K, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
    have hdeg : (Polynomial.cyclotomic q K).degree ≠ 0 := by
      rw [Polynomial.degree_cyclotomic]
      exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
    obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root _ hdeg
    refine ⟨ζ, ?_⟩
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
    exact hζ
  have hbij := GlobalTheory.EtC.h_zero_pull_bijective q K (LaurentPolynomial K) (C : K →+* LaurentPolynomial K) hqK hζ
    inferInstance (fun e he => IsIdempotentElem.iff_eq_zero_or_one.1 he) (fun e he => IsIdempotentElem.iff_eq_zero_or_one.1 he) i
  have hw : pull _ (spMap (laurentMap f₀)) _ 0 y' = 0 := by
    obtain ⟨v, hv⟩ := hbij.2 (pull _ (spMap (laurentMap f₀)) _ 0 y')
    have hv0 : v = 0 := by
      have e1 : pull _ (spMap ev₁K) _ 0 (pull _ (spMap (C : K →+* LaurentPolynomial K)) _ 0 v) = v := by
        rw [← pull_spMap_comp, hevK, pull_spMap_id]
      rw [← e1, hv, ← pull_spMap_comp, hcomm, pull_spMap_comp, h0, map_zero]
    rw [← hv, hv0, map_zero]
  rw [hf, pull_spMap_comp, hw, map_zero]

end GlobalTheory.EtC.MultiplicativeGroupGlobalSections

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCohomologyZeroStrictlyHenselianEquiv
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.CyclotomicGlobalSections

theorem exists_cyclotomic_root (q : ℕ) [NeZero q] (A : Type) [CommRing A] (hA : SH A) (hq : IsUnit (q : A)) :
    ∃ ζ : A, Polynomial.aeval ζ (Polynomial.cyclotomic q ℤ) = 0 := by
  obtain ⟨hH, hsep⟩ := hA
  haveI := hH
  have hqk : (q : IsLocalRing.ResidueField A) ≠ 0 := by
    have := hq.map (IsLocalRing.residue A)
    simpa using this.ne_zero
  have hsepk : (Polynomial.cyclotomic q (IsLocalRing.ResidueField A)).Separable :=
    (Polynomial.separable_X_pow_sub_C 1 hqk one_ne_zero).of_dvd (Polynomial.cyclotomic.dvd_X_pow_sub_one q _)
  have hdeg : (Polynomial.cyclotomic q (IsLocalRing.ResidueField A)).degree ≠ 0 := by
    rw [Polynomial.degree_cyclotomic]
    exact_mod_cast (Nat.totient_pos.2 (Nat.pos_of_ne_zero (NeZero.ne q))).ne'
  obtain ⟨a0, ha0⟩ := IsSepClosed.exists_root _ hdeg hsepk
  obtain ⟨b0, rfl⟩ := IsLocalRing.residue_surjective a0
  have hred : ∀ p : Polynomial A, IsLocalRing.residue A (p.eval b0) =
      (p.map (IsLocalRing.residue A)).eval (IsLocalRing.residue A b0) := fun p => by
    rw [Polynomial.eval_map, Polynomial.eval₂_hom]
  have h1 : (Polynomial.cyclotomic q A).eval b0 ∈ IsLocalRing.maximalIdeal A := by
    rw [← IsLocalRing.residue_eq_zero_iff, hred, Polynomial.map_cyclotomic]
    all_goals exact ha0
  have h2 : IsUnit ((Polynomial.derivative (Polynomial.cyclotomic q A)).eval b0) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hred, ← Polynomial.derivative_map, Polynomial.map_cyclotomic]
    have := hsepk.aeval_derivative_ne_zero (x := IsLocalRing.residue A b0) (by simpa [Polynomial.aeval_def] using ha0)
    simpa [Polynomial.aeval_def] using this
  obtain ⟨a, ha, -⟩ := HenselianLocalRing.is_henselian (Polynomial.cyclotomic q A)
    (Polynomial.cyclotomic.monic q A) b0 h1 h2
  refine ⟨a, ?_⟩
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map, Polynomial.map_cyclotomic]
  exact ha

end GlobalTheory.EtC.CyclotomicGlobalSections

open GlobalTheory.EtC.ConnectedGlobalSections in

theorem GlobalTheory.EtC.tateTwistCohomology_zero_strictlyHenselian_equiv : ∀ (q : ℕ) [NeZero q] (A : Type) [CommRing A], SH A → IsUnit (q : A) →
    ∀ j : ℤ, Nonempty (Ht q (sp A) 0 j ≃+ ZMod q) := by
  intro q _ A _ hA hq j
  obtain ⟨ζ0, hζ0⟩ := GlobalTheory.EtC.CyclotomicGlobalSections.exists_cyclotomic_root q A hA hq
  obtain ⟨hH, -⟩ := hA
  haveI := hH
  obtain ⟨-, e, -, -⟩ := GlobalTheory.T.etaleCohomology_negative_vanishing_degree_zero (ZMod q) (tw q j)
  haveI : Nonempty (Spec (CommRingCat.of A)) := inferInstance
  let ζ : Prim q Γ(Spec (CommRingCat.of A), ⊤) :=
    Prim.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom ⟨ζ0, hq, hζ0⟩
  have hidem : ∀ x : A, IsIdempotentElem x → x = 0 ∨ x = 1 := fun x hx => by
    have h0 : x * (1 - x) = 0 := by rw [mul_sub, mul_one, hx.eq, sub_self]
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self x with hu | hu
    · exact Or.inr (sub_eq_zero.1 ((hu.mul_right_eq_zero).1 h0)).symm
    · exact Or.inl ((hu.mul_left_eq_zero).1 h0)
  let φ : ZMod q →+ Sec (tw q j) (Spec (CommRingCat.of A)) :=
    { toFun := fun c => (ULift.up c : ULift.{1} (ZMod q)) • twGen j ζ
      map_zero' := zero_smul _ _
      map_add' := fun c d => add_smul (ULift.up c : ULift.{1} (ZMod q)) (ULift.up d) (twGen j ζ) }
  have hφ : ∀ c : ZMod q, φ c = c.val • twGen j ζ := fun c => by
    rw [nsmul_eq_up, ZMod.natCast_zmod_val]; rfl
  have hbij : Function.Bijective φ := by
    constructor
    · intro c d h
      rw [hφ, hφ] at h
      exact scalar_eq ζ c d h
    · intro y
      obtain ⟨n, rfl⟩ := sec_eq_nsmul _ (clopen_of_idem A hidem) ζ y
      exact ⟨(n : ZMod q), by rw [hφ, nsmul_eq_up, nsmul_eq_up, ZMod.natCast_zmod_val]⟩
  exact ⟨((AddEquiv.ofBijective φ hbij).trans (e _)).symm⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedTransport
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.HeckeGal
open GlobalTheory.IndefiniteRowSideFullHecke.ToricSymbols (IsTwistedSum IsSymbol conjChar classOf)
open GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport (IsConjWt IsConjChar lamF upIdele)

namespace GlobalTheory.ToricTransport

def coordIn (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ) (Ω T : ℂ) : ℂ :=
  (C0 E d (2 * s) κ : ℂ) * T / Ω ^ (2 * s * Fintype.card I + 2 * ∑ i, κ i)

def IsDatum {K E : Type} [Field K] [Field E] [NumberField E] [Algebra K E] {I : Type} [Fintype I] (ι : K →+* ℂ)
    (φ : I → E →+* ℂ) (s : ℕ) (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E) : Prop :=
  UnramFin E ∧ IsCMType φ ∧ (∀ i, (φ i).comp (algebraMap K E) = ι) ∧ 1 ≤ s ∧ (∀ i, 1 ≤ κ i) ∧ IsBaseCond 𝔣 ∧ IsFinSetSplitPlacesCoprimeConductor 𝔣 Q ∧
    IsValChar φ s κ 𝔣 ∅ χ

def TwistedTransport : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (d : ℕ) (δ : K) (ι : K →+* ℂ),
    Module.finrank ℚ K = 2 → 0 < d → δ ^ 2 = -(d : K) →
    ∃ Ω₀ : ℂ, Ω₀ ≠ 0 ∧
      (∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
        (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E), IsDatum ι φ s κ 𝔣 Q χ →
        ∀ (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) (T : ℂ), IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T → IsAlgebraic ℚ (coordIn E d s κ Ω₀ T)) ∧
      ∀ (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] (j : Ω →+* ℂ) (art : Ideles K →* Gab K Ω),
        j.comp (algebraMap K Ω) = ι → IsGlobalArtin art →
        ∀ (g : ℂ ≃+* ℂ) (σ : Formalism.ConjugateSelfDual.G K Ω) (t : (Af K)ˣ), (∀ x, j (σ x) = g (j x)) → IsSymbol art t σ →
        ∃ Ω₁ : ℂ, Ω₁ ≠ 0 ∧
          ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [Algebra K E] (I : Type) [Fintype I] (φ : I → E →+* ℂ) (s : ℕ)
            (κ : I → ℕ) (𝔣 : Ideal (OF E)) (Q : Finset (HeightOneSpectrum (OF E))) (χ : HChar E), IsDatum ι φ s κ 𝔣 Q χ →
            ∀ (κ' : I → ℕ) (χ' : HChar E), IsConjWt φ g κ κ' → IsConjChar φ s κ' g χ χ' →
            ∀ (ψ : PicO (condQ 𝔣 Q) →* ℂˣ) (T T' : ℂ), IsTwistedSum φ s κ (condQ 𝔣 Q) χ ψ T →
              IsTwistedSum φ s κ' (condQ 𝔣 Q) χ' (conjChar g ψ) T' →
              g (coordIn E d s κ Ω₀ T) =
                coordIn E d s κ Ω₁ ((((modF t : ℝ) : ℂ) ^ (∑ i, κ i))⁻¹ *
                  (lamF s χ' (upIdele K E t) * ((conjChar g ψ (classOf K (condQ 𝔣 Q) t) : ℂˣ) : ℂ))⁻¹ * T')

example (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] (d s : ℕ) (κ : I → ℕ) (Ω T : ℂ) (Λ : PeriodPair)
    (h : Ω ^ 12 = latDisc Λ) : coordIn E d s κ Ω T ^ 12 = beta E d s κ Λ T := by
  rw [beta_eq, coordIn, div_pow, ← h, ← pow_mul, ← pow_mul, mul_comm 12]

theorem coordIn_div (E : Type) [Field E] [NumberField E] {I : Type} [Fintype I] {d s : ℕ} (hd : 0 < d) (hs : 1 ≤ s) (κ : I → ℕ)
    {Ω : ℂ} (hΩ : Ω ≠ 0) (T T₀ : ℂ) : coordIn E d s κ Ω T / coordIn E d s κ Ω T₀ = T / T₀ := by
  have hC : (C0 E d (2 * s) κ : ℂ) ≠ 0 := by exact_mod_cast (cmValueConst_pos E hd (by omega) κ).ne'
  rw [coordIn, coordIn, div_div_div_cancel_right₀ (pow_ne_zero _ hΩ), mul_div_mul_left _ _ hC]

end GlobalTheory.ToricTransport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoCocycleCoboundaryOfBasisFunctorStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twoCocycle_coboundary_of_basisFunctor : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ T : C, ∃ (n : ℕ) (b : Fin n → (F).obj T), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S : C) (u : T ⟶ S), IsUnit (mp (F) u (b i)) → ∃ (t : C') (v : T ⟶ G.obj t) (w : G.obj t ⟶ S), v ≫ w = u) → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → (F).obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp (F) u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → (∀ (T : C) (z : ∀ t t' t'', (T ⟶ G.obj t) → (t ⟶ t') → (t' ⟶ t'') → (F).obj (G.obj t'')), (∀ t t' t'' t''' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t'') (c : t'' ⟶ t'''), mp (F) (G.map c) (z t t' t'' u a b) + z t t'' t''' u (a ≫ b) c = z t t' t''' u a (b ≫ c) + z t' t'' t''' (u ≫ G.map a) b c) → ∃ y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t'), ∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), mp (F) (G.map b) (y t t' u a) - y t t'' u (a ≫ b) + y t' t'' (u ≫ G.map a) b = z t t' t'' u a b) := by
  first | exact @GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.twoCocycle_coboundary_of_basisFunctor_alt | exact GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.twoCocycle_coboundary_of_basisFunctor_alt | (intros; apply GlobalTheory.CatCoh.Desc.VandermondeTwoBasis.twoCocycle_coboundary_of_basisFunctor_alt <;> assumption)
end

