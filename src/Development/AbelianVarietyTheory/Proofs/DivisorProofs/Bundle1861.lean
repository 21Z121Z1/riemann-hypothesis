import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1787
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1821
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1806
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1830
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1748
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1742
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1824
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualLatticePairingDual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1833
import Formalism.DoubleCosetMeasures.LowerUnipotentOrbits.RelIndexMulMeasure
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MeasureToRealEqMass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1796
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1832
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicUnipotentRadicalCoveredByLeviConjugates
section
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis.SphericalEisensteinCover

theorem isCompact_entries {A : Type} [TopologicalSpace A] (a b : ℕ) {Ω : Set A} (hΩ : IsCompact Ω) :
    IsCompact {ω : Matrix (Fin a) (Fin b) A | ∀ i k, ω i k ∈ Ω} := by
  have e : {ω : Matrix (Fin a) (Fin b) A | ∀ i k, ω i k ∈ Ω} =
      (Set.univ.pi fun _ => Set.univ.pi fun _ => Ω : Set (Matrix (Fin a) (Fin b) A)) :=
    Set.ext fun ω => ⟨fun h i _ k _ => h i k, fun h i k => h i trivial k trivial⟩
  rw [e]
  exact isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ

variable {k A : Type} [Field k] [CharZero k] [CommRing A] [Algebra k A] (s : A →+* A)

theorem cT_add {a b : ℕ} (M N : Matrix (Fin a) (Fin b) A) : cT s (M + N) = cT s M + cT s N := by
  ext; simp [cT]

theorem cT_neg {a b : ℕ} (M : Matrix (Fin a) (Fin b) A) : cT s (-M) = -cT s M := by
  ext; simp [cT]

theorem cT_sub {a b : ℕ} (M N : Matrix (Fin a) (Fin b) A) : cT s (M - N) = cT s M - cT s N := by
  ext; simp [cT]

theorem cT_smul (hk : ∀ (c : k) x, s (c • x) = c • s x) {a b : ℕ} (c : k) (M : Matrix (Fin a) (Fin b) A) :
    cT s (c • M) = c • cT s M := by
  ext; simp [cT, hk]

theorem cT_cT (hs : ∀ x, s (s x) = x) {a b : ℕ} (M : Matrix (Fin a) (Fin b) A) : cT s (cT s M) = M := by
  ext; simp [cT, hs]

variable {j m : ℕ} (K : Matrix (Fin m) (Fin m) A)

theorem cT_pair (hs : ∀ x, s (s x) = x) (hK : cT s K = K) (u v : Matrix (Fin j) (Fin m) A) :
    cT s (u * (K * cT s v)) = v * (K * cT s u) := by
  rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_cT s hs, hK, Matrix.mul_assoc]

theorem skew_rest (hs : ∀ x, s (s x) = x) (hk : ∀ (c : k) x, s (c • x) = c • s x) (hK : cT s K = K)
    (X y p : Matrix (Fin j) (Fin m) A) (c : Matrix (Fin j) (Fin j) A)
    (hc : c + cT s c + (X + (y + p)) * (K * cT s (X + (y + p))) = 0) :
    cT s (c + X * (K * cT s (X + (y + p))) - (2⁻¹ : k) • (X * (K * cT s X)) + (2⁻¹ : k) • (y * (K * cT s y)) +
      (2⁻¹ : k) • (p * (K * cT s p)) + y * (K * cT s p)) =
    -(c + X * (K * cT s (X + (y + p))) - (2⁻¹ : k) • (X * (K * cT s X)) + (2⁻¹ : k) • (y * (K * cT s y)) +
      (2⁻¹ : k) • (p * (K * cT s p)) + y * (K * cT s p)) := by
  have hcc : cT s c = -c - (X + (y + p)) * (K * cT s (X + (y + p))) := by
    calc cT s c = (c + cT s c + (X + (y + p)) * (K * cT s (X + (y + p)))) - c - (X + (y + p)) * (K * cT s (X + (y + p))) := by abel
      _ = _ := by rw [hc]; abel
  simp only [cT_add, cT_sub, cT_smul s hk, cT_pair s K hs hK, hcc]
  simp only [cT_add, cT_pair s K hs hK, Matrix.mul_add, Matrix.add_mul, smul_add, neg_add, sub_eq_add_neg]
  module

theorem rel_half (hs : ∀ x, s (s x) = x) (hk : ∀ (c : k) x, s (c • x) = c • s x) (hK : cT s K = K)
    (b : Matrix (Fin j) (Fin m) A) (z : Matrix (Fin j) (Fin j) A) (hz : cT s z = -z) :
    (z - (2⁻¹ : k) • (b * (K * cT s b))) + cT s (z - (2⁻¹ : k) • (b * (K * cT s b))) + b * (K * cT s b) = 0 := by
  rw [cT_sub, cT_smul s hk, cT_pair s K hs hK, hz]
  module

theorem final_eq (X y p : Matrix (Fin j) (Fin m) A) (c r z ws : Matrix (Fin j) (Fin j) A)
    (hR : c + X * (K * cT s (X + (y + p))) - (2⁻¹ : k) • (X * (K * cT s X)) + (2⁻¹ : k) • (y * (K * cT s y)) +
      (2⁻¹ : k) • (p * (K * cT s p)) + y * (K * cT s p) = r + (z + ws)) :
    (-((2⁻¹ : k) • (X * (K * cT s X))) - r) + c - (-X) * (K * cT s (X + (y + p))) =
      (z - (2⁻¹ : k) • (y * (K * cT s y))) + (ws - (2⁻¹ : k) • (p * (K * cT s p))) - y * (K * cT s p) := by
  have h := sub_eq_zero.2 hR
  rw [← sub_eq_zero]
  rw [← h, Matrix.neg_mul]
  module

end GlobalTheory.SphEis.SphericalEisensteinCover

namespace GlobalTheory.SphEis

open GlobalTheory.SphEis.SphericalEisensteinCover in

theorem cover_unipRad : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ lv : GL (Fin j) (AF F ⊗[F] E) →* GAd σ J, IsLv σ J C D Z lv → ∃ (V : Set (GAd σ J)) (B : ℝ), IsCompact V ∧ ∀ μ : Fin j → ℕ, ∃ Y : Finset (GAd σ J), (Y.card : ℝ) ≤ B * ∏ i, bse F ^ ((m + j) * μ i) ∧ (∀ y ∈ Y, y ∈ unipRad σ J C) ∧ ∀ u ∈ unipRad σ J C, ∃ γ ∈ ratPts σ J, γ ∈ unipRad σ J C ∧ ∃ y ∈ Y, ∃ w ∈ V, w ∈ unipRad σ J C ∧ γ * u = y * lv (tor F E fun i => (μ i : ℤ)) * w * (lv (tor F E fun i => (μ i : ℤ)))⁻¹ := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hFr lv hlv
  classical
  have hcm := hFr.cm
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _

  have hs : ∀ x, sigR (AF F) σ (sigR (AF F) σ x) = x := fun a => by
    induction a using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul a x => exact congrArg (a ⊗ₜ[F] ·) (sigma_sigma hcm x)
  have hk : ∀ (c : F) x, sigR (AF F) σ (c • x) = c • sigR (AF F) σ x := fun c x =>
    map_smul (Algebra.TensorProduct.map (AlgHom.id F (AF F)) σ) c x
  have hsc : Continuous (sigR (AF F) σ) := by
    have e : (sigR (AF F) σ : AF F ⊗[F] E → AF F ⊗[F] E) = LinearMap.baseChange (AF F) σ.toLinearMap := by
      funext x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a x => rfl
    rw [e]
    exact IsModuleTopology.continuous_of_linearMap _

  have hJ₀ : cT (σ : E →+* E) J₀ = J₀ := Matrix.ext fun i k => hFr.herm₀.1 i k
  have hJ₀i : cT (σ : E →+* E) J₀⁻¹ = J₀⁻¹ := by
    have hu : IsUnit J₀.det := IsUnit.mk0 _ hFr.herm₀.2
    refine (Matrix.inv_eq_left_inv ?_).symm
    calc cT (σ : E →+* E) J₀⁻¹ * J₀ = cT (σ : E →+* E) J₀⁻¹ * cT (σ : E →+* E) J₀ := by rw [hJ₀]
      _ = cT (σ : E →+* E) (J₀ * J₀⁻¹) := (Formalism.UG.cT_mul _ _ _).symm
      _ = 1 := by rw [Matrix.mul_nonsing_inv _ hu, Formalism.UG.cT_one]
  have hK : cT (sigR (AF F) σ) (adMat F J₀⁻¹) = adMat F J₀⁻¹ := congrArg (adMat F) hJ₀i

  set K : Matrix (Fin m) (Fin m) (AF F ⊗[F] E) := adMat F J₀⁻¹ with hKdef
  have hplus : ∀ b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E), plus σ J₀ b = K * cT (sigR (AF F) σ) b := fun b => rfl
  obtain ⟨Ω₁, B₁, hΩ₁, hrect⟩ := GlobalTheory.T.cover_rectangularAdelicMatrices_shrunkCompact F E σ hcm j m
  obtain ⟨Ω₂, B₂, hΩ₂, hskew⟩ := GlobalTheory.T.cover_skewHermitianAdelicMatrices_shrunkCompact F E σ hcm j
  set S₁ : Set (Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) := {ω | ∀ i k, ω i k ∈ Ω₁} with hS₁
  set S₂ : Set (Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := {ω | ∀ i k, ω i k ∈ Ω₂} with hS₂
  have hS₁c : IsCompact S₁ := isCompact_entries j m hΩ₁
  have hS₂c : IsCompact S₂ := isCompact_entries j j hΩ₂
  have hcont : ∀ i k, Continuous fun q : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) =>
      (q.2 - (2⁻¹ : F) • (q.1 * (K * cT (sigR (AF F) σ) q.1))) i k := fun i k => by
    have h1 : Continuous fun q : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) =>
        q.1 * (K * cT (sigR (AF F) σ) q.1) :=
      continuous_fst.matrix_mul (continuous_const.matrix_mul (continuous_fst.matrix_map hsc).matrix_transpose)
    have hsm : Continuous fun x : AF F ⊗[F] E => (2⁻¹ : F) • x := by
      simp only [Algebra.smul_def]; exact continuous_const.mul continuous_id
    simp only [Matrix.sub_apply, Matrix.smul_apply]
    exact ((continuous_apply_apply i k).comp continuous_snd).sub (hsm.comp (h1.matrix_elem i k))
  set Ω₃ : Set (AF F ⊗[F] E) := Ω₁ ∪ ⋃ (i : Fin j) (k : Fin j),
    (fun q : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) =>
      (q.2 - (2⁻¹ : F) • (q.1 * (K * cT (sigR (AF F) σ) q.1))) i k) '' (S₁ ×ˢ S₂) with hΩ₃
  have hΩ₃c : IsCompact Ω₃ :=
    hΩ₁.union (isCompact_iUnion fun i => isCompact_iUnion fun k => (hS₁c.prod hS₂c).image (hcont i k))
  obtain ⟨V, hV, hVmem⟩ := GlobalTheory.T.exists_isCompact_of_unipotentCoordinates_mem F E σ n J j m C D Z J₀ hFr Ω₃ hΩ₃c
  refine ⟨V, B₁ * B₂, hV, fun μ => ?_⟩

  obtain ⟨Y₁, hY₁, hcov₁⟩ := hrect μ
  obtain ⟨Y₂, hY₂, hY₂sk, hcov₂⟩ := hskew μ
  have crd2 := GlobalTheory.T.exists_unipotentRadical_point_with_coords F E σ n J j m C D Z J₀ hFr
  have hrel : ∀ (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (z : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)),
      cT (sigR (AF F) σ) z = -z →
      (z - (2⁻¹ : F) • (b * plus σ J₀ b)) + cT (sigR (AF F) σ) (z - (2⁻¹ : F) • (b * plus σ J₀ b)) +
        b * plus σ J₀ b = 0 :=
    fun b z hz => rel_half (sigR (AF F) σ) K hs hk hK b z hz
  let f : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → GAd σ J := fun q =>
    if hq : cT (sigR (AF F) σ) q.2 = -q.2 then Classical.choose (crd2 q.1 _ (hrel q.1 q.2 hq)) else 1
  have hf : ∀ b z, cT (sigR (AF F) σ) z = -z → f (b, z) ∈ unipRad σ J C ∧
      Crd σ J C D Z J₀ (f (b, z)) b (z - (2⁻¹ : F) • (b * plus σ J₀ b)) := by
    intro b z hz
    simp only [f, dif_pos hz]
    exact Classical.choose_spec (crd2 b _ (hrel b z hz))
  refine ⟨(Y₁ ×ˢ Y₂).image f, ?_, ?_, fun u hu => ?_⟩
  · refine (Nat.cast_le.mpr Finset.card_image_le).trans ?_
    rw [Finset.card_product, Nat.cast_mul]
    refine (mul_le_mul hY₁ hY₂ (Nat.cast_nonneg _) ((Nat.cast_nonneg _).trans hY₁)).trans (le_of_eq ?_)
    simp only [add_mul, pow_add, Finset.prod_mul_distrib]
    ring
  · intro y hy
    obtain ⟨⟨b, z⟩, hq, rfl⟩ := Finset.mem_image.1 hy
    exact (hf b z (hY₂sk z (Finset.mem_product.1 hq).2)).1
  obtain ⟨b, c, hbc, hcond⟩ := GlobalTheory.T.exists_unipotentFrameCoords_of_mem_isotropicUnipotentRadical F E σ n J j m C D Z J₀ hFr u hu
  obtain ⟨x₀, y, hy, ω, hω, hb⟩ := hcov₁ b
  set t := tor F E fun i => (μ i : ℤ) with ht
  have hcond' : c + cT (sigR (AF F) σ) c + (adMat F x₀ + (y + t.1 * ω)) *
      (K * cT (sigR (AF F) σ) (adMat F x₀ + (y + t.1 * ω))) = 0 := by
    rw [← hb]; exact hcond
  have hRsk := skew_rest (sigR (AF F) σ) K hs hk hK (adMat F x₀) y (t.1 * ω) c hcond'
  obtain ⟨x₁, hx₁, z, hz, ωs, hωs, hωsΩ, hR⟩ := hcov₂ _ hRsk

  let c₀ : Matrix (Fin j) (Fin j) E := -((2⁻¹ : F) • (x₀ * (J₀⁻¹ * cT (σ : E →+* E) x₀))) - x₁
  have hneg : adMat F (-x₀) = -adMat F x₀ := by ext; simp
  have hc₀ : adMat F c₀ = -((2⁻¹ : F) • (adMat F x₀ * (K * cT (sigR (AF F) σ) (adMat F x₀)))) - adMat F x₁ := by
    have e1 : adMat F (x₀ * (J₀⁻¹ * cT (σ : E →+* E) x₀)) = adMat F x₀ * (K * cT (sigR (AF F) σ) (adMat F x₀)) := by
      simp only [adMat, Matrix.map_mul]; rfl
    have e2 : adMat F ((2⁻¹ : F) • (x₀ * (J₀⁻¹ * cT (σ : E →+* E) x₀))) =
        (2⁻¹ : F) • adMat F (x₀ * (J₀⁻¹ * cT (σ : E →+* E) x₀)) :=
      Matrix.map_smul _ _ (fun a => map_smul (Algebra.TensorProduct.includeRight : E →ₐ[F] AF F ⊗[F] E) (2⁻¹ : F) a) _
    have e3 : ∀ P Q : Matrix (Fin j) (Fin j) E, adMat F (P - Q) = adMat F P - adMat F Q := fun P Q => by ext; simp
    have e4 : ∀ P : Matrix (Fin j) (Fin j) E, adMat F (-P) = -adMat F P := fun P => by ext; simp
    simp only [c₀]
    rw [e3, e4, e2, e1]
  have hx₁' : cT (sigR (AF F) σ) (adMat F x₁) = -adMat F x₁ := by
    show adMat F (cT (σ : E →+* E) x₁) = _
    rw [hx₁]; ext; simp
  have hγrel : adMat F c₀ + cT (sigR (AF F) σ) (adMat F c₀) + adMat F (-x₀) * plus σ J₀ (adMat F (-x₀)) = 0 := by
    rw [hc₀, hneg, hplus]
    simp only [cT_sub, cT_neg, cT_smul _ hk, cT_pair _ K hs hK, hx₁', Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    module
  obtain ⟨γ, hγU, hγC⟩ := crd2 (adMat F (-x₀)) (adMat F c₀) hγrel
  have hγrat := GlobalTheory.T.mem_rationalPoints_of_unipotentCoords_rational F E σ n J j m C D Z J₀ hFr γ (-x₀) c₀ hγC

  obtain ⟨w, hwU, hwC⟩ := crd2 ω (ωs - (2⁻¹ : F) • (ω * plus σ J₀ ω)) (hrel ω ωs hωs)
  have hwV : w ∈ V := hVmem w ω _ hwC (fun i k => Or.inl (hω i k))
    (fun i k => Or.inr (Set.mem_iUnion₂.2 ⟨i, k, ⟨(ω, ωs), ⟨hω, hωsΩ⟩, rfl⟩⟩))

  have hy'mem : f (y, z) ∈ (Y₁ ×ˢ Y₂).image f := Finset.mem_image_of_mem f (Finset.mem_product.2 ⟨hy, hz⟩)
  obtain ⟨hy'U, hy'C⟩ := hf y z (hY₂sk z hz)

  have law := GlobalTheory.T.unipotentRadical_coordinates_groupLaw F E σ n J j m C D Z J₀ hFr lv hlv
  have h1 := (law γ u (adMat F (-x₀)) (adMat F c₀) b c hγC).1 hbc
  have hcj := (law w w ω _ 0 0 hwC).2.2 t
  have h2 := (law (f (y, z)) _ y _ _ _ hy'C).1 hcj
  have eb : adMat F (-x₀) + b = y + t.1 * ω := by rw [hb, hneg]; abel
  have ec : adMat F c₀ + c - adMat F (-x₀) * plus σ J₀ b =
      (z - (2⁻¹ : F) • (y * plus σ J₀ y)) + t.1 * (ωs - (2⁻¹ : F) • (ω * plus σ J₀ ω)) * cT (sigR (AF F) σ) t.1 -
        y * plus σ J₀ (t.1 * ω) := by
    have hconj : t.1 * (ωs - (2⁻¹ : F) • (ω * plus σ J₀ ω)) * cT (sigR (AF F) σ) t.1 =
        t.1 * ωs * cT (sigR (AF F) σ) t.1 - (2⁻¹ : F) • ((t.1 * ω) * plus σ J₀ (t.1 * ω)) := by
      simp only [hplus, Formalism.UG.cT_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    rw [hconj, hc₀, hneg, hb]
    simp only [hplus]
    exact final_eq (sigR (AF F) σ) K (adMat F x₀) y (t.1 * ω) c (adMat F x₁) z (t.1 * ωs * cT (sigR (AF F) σ) t.1) hR
  rw [eb, ec] at h1
  have heq := (law (γ * u) _ _ _ 0 0 h1).2.1 h2
  refine ⟨γ, hγrat, hγU, f (y, z), hy'mem, w, hwV, hwU, ?_⟩
  rw [heq]
  simp only [mul_assoc]

end GlobalTheory.SphEis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatPtLeClosureAndSelfDual
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.VacAny
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.BigNZ GlobalTheory.AdelicU GlobalTheory.WeilM
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA skewGram mulG colV adjV₁)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep IsTriple Acts SInf At latAtV realAd evI)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.BigDat

namespace GlobalTheory.BigDatLat

open GlobalTheory.LatVac

variable {D : D7}

theorem smul_eq_of_at {M : Type} [AddCommGroup M] [Module (AF D.host.F) M] {v : Pl D.host.F} {z : M}
    (h : At (evFin D.host.F v) z) : liftV v (1 : Fv D.host.F v) • z = z := by
  have h1 := h (1 - liftV v 1) (by rw [map_sub, map_one, evFin_liftV, sub_self])
  rw [sub_smul, one_smul, sub_eq_zero] at h1
  exact h1.symm

theorem at_smul {M : Type} [AddCommGroup M] [Module (AF D.host.F) M] (v : Pl D.host.F) (z : M) :
    At (evFin D.host.F v) (liftV v (1 : Fv D.host.F v) • z) := fun u hu => by
  rw [smul_smul, ← smul_eq_mul u, at_liftV v 1 u hu, zero_smul]

theorem cA_smul (c : AF D.host.F) (z : AE D) : cA D (c • z) = c • cA D z :=
  map_smul (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) c z

theorem symplO_swap (S T : HSp D) (c : AF D.host.F) (x y : WO S T) : symplO S T x (c • y) = symplO S T (c • x) y := by
  have h : hO S T x (c • y) = hO S T (c • x) y := by
    unfold hO
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
      Finset.sum_congr rfl fun _ _ => ?_
    rw [Matrix.smul_apply, Matrix.smul_apply, cA_smul, mul_smul_comm, smul_mul_assoc, smul_mul_assoc, mul_smul_comm]
  unfold symplO
  rw [h]

theorem infPart_smul (v : Pl D.host.F) (z : AE D) : infPart D (liftV v (1 : Fv D.host.F v) • z) = 0 := by
  rw [Algebra.smul_def, RingHom.map_mul]
  have : infPart D (algebraMap (AF D.host.F) (AE D) (liftV v (1 : Fv D.host.F v))) = 0 := infPart_pair _ _
  rw [this, zero_mul]

theorem smul_mem {S T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} (v : Pl D.host.F)
    {u : WO S T} (hu : u ∈ latO S T LS LT fun _ => True) :
    liftV v (1 : Fv D.host.F v) • u ∈ latO S T LS LT fun _ => True := by
  refine latO_induction (p := fun u => liftV v (1 : Fv D.host.F v) • u ∈ latO S T LS LT fun _ => True) ?_ ?_ ?_ ?_ hu
  · intro α hα M hM
    have h : liftV v (1 : Fv D.host.F v) • finTens α M = finTens (singleFin v 1 * α) M := by
      ext i j
      change (pairA D.host.F 0 (singleFin v 1) * pairA D.host.F 0 α) ⊗ₜ[D.host.F] M i j = _
      rw [pair_mul]
      rfl
    rw [h]
    refine finTens_mem_latO (mul_mem_intAf (fun w => ?_) hα) hM
    by_cases hw : w = v
    · subst hw
      rw [evalV_singleFin_self]
      exact one_mem _
    · rw [evalV_singleFin_ne hw]
      exact zero_mem _
  · rw [smul_zero]; exact zero_mem _
  · intro x y hx hy; rw [smul_add]; exact add_mem hx hy
  · intro x hx; rw [smul_neg]; exact neg_mem hx

theorem isHalf_smul {m n : ℕ} {ε : AE D} (c : AF D.host.F) {u : Mx D m n} (hu : IsHalf ε u) : IsHalf ε (c • u) :=
  fun i j => by rw [Matrix.smul_apply, mul_smul_comm, hu]

theorem isHalf_zero {m n : ℕ} (ε : AE D) : IsHalf ε (0 : Mx D m n) := fun _ _ => mul_zero _

section Pair

variable {S T S' T' : HSp D} {P : Type} [AddCommGroup P] [Module (AF D.host.F) P]
  (m : P ≃ₗ[AF D.host.F] WO S T × WO S' T') (v : Pl D.host.F) (Λ : AddSubgroup P)

theorem le_of_gen {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)}
    {LS' : Set (Fin S'.rank → D.host.E)} {LT' : Set (Fin T'.rank → D.host.E)}
    (hΛ : ∀ u, u ∈ Λ ↔ At (evFin D.host.F v) u ∧ (m u).1 ∈ latO S T LS LT (fun _ => True) ∧
      (m u).2 ∈ latO S' T' LS' LT' fun _ => True) (H : AddSubgroup P) (h2 : ∀ u ∈ Λ, 2 • u ∈ H)
    (hh : ∀ ε, IsSplitIdem D ε → ∀ u ∈ Λ, IsHalf ε (m u).1 → IsHalf ε (m u).2 → u ∈ H) : Λ ≤ H := by
  let f : WO S T × WO S' T' →ₗ[AF D.host.F] P := liftV v (1 : Fv D.host.F v) • m.symm.toLinearMap
  have hf : ∀ x, f x = liftV v (1 : Fv D.host.F v) • m.symm x := fun _ => rfl
  have hm : ∀ x, m (f x) = liftV v (1 : Fv D.host.F v) • x := fun x => by rw [hf, map_smul, m.apply_symm_apply]
  have hin : ∀ x : WO S T × WO S' T', x.1 ∈ latO S T LS LT (fun _ => True) →
      x.2 ∈ latO S' T' LS' LT' (fun _ => True) → f x ∈ Λ := fun x h1 h2 =>
    (hΛ _).2 ⟨at_smul v _, by rw [hm]; exact smul_mem v h1, by rw [hm]; exact smul_mem v h2⟩
  intro u hu
  obtain ⟨ha, h1, h1'⟩ := (hΛ u).1 hu
  have e : u = f ((m u).1, 0) + f (0, (m u).2) := by
    rw [← map_add, Prod.mk_add_mk, add_zero, zero_add, hf, Prod.mk.eta, m.symm_apply_apply, smul_eq_of_at ha]
  rw [e]
  refine add_mem ?_ ?_
  · refine le_of_two_of_half (H.comap (f ∘ₗ LinearMap.inl _ _ _).toAddMonoidHom) (fun x hx => ?_) (fun ε hε x hx hx' => ?_) h1
    · rw [AddSubgroup.mem_comap, map_nsmul]
      exact h2 _ (hin (x, 0) hx (zero_mem _))
    · exact hh ε hε (f (x, 0)) (hin (x, 0) hx (zero_mem _)) (by rw [hm]; exact isHalf_smul _ hx')
        (by rw [hm]; exact isHalf_smul _ (isHalf_zero ε))
  · refine le_of_two_of_half (H.comap (f ∘ₗ LinearMap.inr _ _ _).toAddMonoidHom) (fun x hx => ?_) (fun ε hε x hx hx' => ?_) h1'
    · rw [AddSubgroup.mem_comap, map_nsmul]
      exact h2 _ (hin (0, x) (zero_mem _) hx)
    · exact hh ε hε (f (0, x)) (hin (0, x) (zero_mem _) hx) (by rw [hm]; exact isHalf_smul _ (isHalf_zero ε))
        (by rw [hm]; exact isHalf_smul _ hx')

theorem mem_iff_char {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {ΛS' : Submodule (𝓞 D.host.E) (Fin S'.rank → D.host.E)} {ΛT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (hS' : IsSelfDualC S' ΛS') (hT' : IsSelfDualC T' ΛT')
    (hΛ : ∀ u, u ∈ Λ ↔ At (evFin D.host.F v) u ∧ (m u).1 ∈ latO S T ΛS ΛT (fun _ => True) ∧
      (m u).2 ∈ latO S' T' ΛS' ΛT' fun _ => True) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    (B : P → P → AF D.host.F) (hB : ∀ x y, B x y = symplO S T (m x).1 (m y).1 + symplO S' T' (m x).2 (m y).2)
    {z : P} (hz : At (evFin D.host.F v) z) : z ∈ Λ ↔ ∀ γ ∈ Λ, ψ (B z γ) = 1 := by
  constructor
  · intro h γ hγ
    obtain ⟨-, a, b⟩ := (hΛ z).1 h
    obtain ⟨-, a', b'⟩ := (hΛ γ).1 hγ
    rw [hB, AddChar.map_add_eq_mul, char_sympl_eq_one hψ hS hT a a', char_sympl_eq_one hψ hS' hT' b b', one_mul]
  · intro h
    have hm : ∀ x, m (liftV v (1 : Fv D.host.F v) • m.symm x) = liftV v (1 : Fv D.host.F v) • x := fun x => by
      rw [map_smul, m.apply_symm_apply]
    have hz' : liftV v (1 : Fv D.host.F v) • m z = m z := by rw [← map_smul, smul_eq_of_at hz]
    have hz1 : liftV v (1 : Fv D.host.F v) • (m z).1 = (m z).1 := congrArg Prod.fst hz'
    have hz2 : liftV v (1 : Fv D.host.F v) • (m z).2 = (m z).2 := congrArg Prod.snd hz'
    have key : ∀ x : WO S T × WO S' T', x.1 ∈ latO S T ΛS ΛT (fun _ => True) →
        x.2 ∈ latO S' T' ΛS' ΛT' (fun _ => True) → ψ (symplO S T (m z).1 x.1 + symplO S' T' (m z).2 x.2) = 1 := fun x h1 h2 => by
      have := h _ ((hΛ (liftV v (1 : Fv D.host.F v) • m.symm x)).2
        ⟨at_smul v _, by rw [hm]; exact smul_mem v h1, by rw [hm]; exact smul_mem v h2⟩)
      rwa [hB, hm, Prod.smul_fst, Prod.smul_snd, symplO_swap, symplO_swap, hz1, hz2] at this
    refine (hΛ z).2 ⟨hz, mem_of_char hψ hS hT ?_ fun x hx => ?_, mem_of_char hψ hS' hT' ?_ fun x hx => ?_⟩
    · rw [← hz1]
      exact Matrix.ext fun _ _ => infPart_smul v _
    · have h0 : symplO S' T' (m z).2 0 = 0 := (symplHom S' T' (m z).2).map_zero
      have := key (x, 0) hx (zero_mem _)
      rwa [h0, add_zero] at this
    · rw [← hz2]
      exact Matrix.ext fun _ _ => infPart_smul v _
    · have h0 : symplO S T (m z).1 0 = 0 := (symplHom S T (m z).1).map_zero
      have := key (0, x) (zero_mem _) hx
      rwa [h0, zero_add] at this

end Pair

theorem latPt_le_closure_and_selfDual : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (i j : Fin D.R.m) (e : Num G i j) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j),
    Γ.V.J = (1 : D.host.E) • (spW G i j).gram → Γ.W.J = skewGram (spV G i j) (spV₁ G i j) e → ∀ v : Pl D.host.F, latPt e v ≤ AddSubgroup.closure (genPt e v) ∧
      ∀ z : Pt G i j, At (evFin D.host.F v) z → (z ∈ latPt e v ↔ ∀ γ ∈ latPt e v, W.ψ (sympPt Γ z γ) = 1) := by
  intro D T L sc G μ₀ hL W i j e Γ hW hWW v
  have a := (node_isV G hL (X := .grid (i + 1) (j + 1)) ⟨i.2, j.2⟩).sd
  refine ⟨le_of_gen (maps e) v _ (fun _ => Iff.rfl) _ (fun u hu => AddSubgroup.subset_closure (Or.inl ⟨u, hu, rfl⟩))
    fun ε hε u hu h1 h2 => AddSubgroup.subset_closure (Or.inr ⟨hu, ε, hε, h1, h2⟩), fun z hz => ?_⟩
  exact mem_iff_char (maps e) v _ (isSelfDualC_neg a) (node_isV G hL (X := .grid i (j + 1)) ⟨i.2.le, j.2⟩).sd
    (node_isV G hL (X := .grid (i + 1) j) ⟨i.2, j.2.le⟩).sd a (fun _ => Iff.rfl) W.ψ_std (sympPt Γ) (symp_eq e Γ hW hWW) hz

end GlobalTheory.BigDatLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMeasureEqRelIndexSmul
section
open NumberField MeasureTheory
open scoped Classical
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 Hf lamOf area Th U)
open Formalism.MainNotions.StandardLatticesGL3 (WeilO HeckeU TT stdL pt oddE0)
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact
open GlobalTheory.BotFormula (IsFinPt)
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsDefiniteSpace IsOpenCompactLevel)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LevelIndexMeasure

theorem measure_eq_relIndex_smul : ∀ {D : D7} (V : HSp D) (n : ℕ) (ι : Formalism.MainNotions.StandardLatticesGL3.GA D n →* GA D V) (J J₀ : Subgroup (Formalism.MainNotions.StandardLatticesGL3.GA D n))
  (K K₀ : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (μ μ₀ : Measure (GA D V)), ι.range = GfC V → J ≤ J₀ → J.relIndex J₀ ≠ 0 →
  IsOpenCompactLevel V K → IsOpenCompactLevel V K₀ → (∀ x, Lev.finE V (ι x) ∈ K ↔ x ∈ J) → (∀ x, Lev.finE V (ι x) ∈ K₀ ↔ x ∈ J₀) →
  Lev.IsMeasLevDef V K μ → Lev.IsMeasLevDef V K₀ μ₀ → μ = (J.relIndex J₀ : ENNReal) • μ₀ := by
  intro D V n ι J J₀ K K₀ μ μ₀ hι hJ hJi hK hK₀ hJK hJK₀ hμ hμ₀
  obtain ⟨hLC, hSC, hT2, hB, hTG, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  haveI := hLC; haveI := hSC; haveI := hT2; haveI := hB; haveI := hTG
  haveI : μ.IsHaarMeasure := hμ.1
  haveI : μ₀.IsHaarMeasure := hμ₀.1

  have hfin : ∀ g : GA D V, ∃ x, Lev.finE V (ι x) = Lev.finE V g := by
    intro g
    obtain ⟨k, k1, k2⟩ := GlobalTheory.UnitarySplit.ga_glue V 1 _ (one_mem _) (GlobalTheory.UnitarySplit.finHom_mem V g)
    have hk : k ∈ ι.range := by
      rw [hι]
      exact MonoidHom.mem_ker.2 k1
    obtain ⟨x, rfl⟩ := hk
    refine ⟨x, ?_⟩
    show Formalism.UG.bc (Lev.swapAE D) (finHom V (ι x)) = Formalism.UG.bc (Lev.swapAE D) (finHom V g)
    rw [k2]
  have hHH : K.comap (Lev.finE V) ≤ K₀.comap (Lev.finE V) := by
    intro g hg
    obtain ⟨x, hx⟩ := hfin g
    change Lev.finE V g ∈ K at hg
    show Lev.finE V g ∈ K₀
    rw [← hx] at hg ⊢
    exact (hJK₀ x).2 (hJ ((hJK x).1 hg))
  have e1 : J = K.comap ((Lev.finE V).comp ι) := by
    ext x
    exact (hJK x).symm
  have e2 : (J₀.map ι).map (Lev.finE V) = (K₀.comap (Lev.finE V)).map (Lev.finE V) := by
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨ι x, (hJK₀ x).2 hx, rfl⟩
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨x, hx⟩ := hfin g
      refine ⟨ι x, ⟨x, (hJK₀ x).1 ?_, rfl⟩, hx⟩
      rw [hx]
      exact hg
  have hidx : (K.comap (Lev.finE V)).relIndex (K₀.comap (Lev.finE V)) = J.relIndex J₀ := by
    rw [e1, Subgroup.relIndex_comap, Subgroup.relIndex_comap, ← Subgroup.map_map, e2]
  haveI : ((K.comap (Lev.finE V)).subgroupOf (K₀.comap (Lev.finE V))).FiniteIndex := ⟨hidx.trans_ne hJi⟩
  have hm := Formalism.DoubleCosetMeasures.P.GLRed.relIndex_mul_measure _ _ hHH hK.1.measurableSet μ
  rw [hidx, GlobalTheory.Mass.Levels.measure_comap_finE hμ, mul_one] at hm
  have h0 : μ₀ (K₀.comap (Lev.finE V)) = 1 := GlobalTheory.Mass.Levels.measure_comap_finE hμ₀
  have heq := Measure.isMulLeftInvariant_eq_smul μ μ₀
  have hc : ((Measure.haarScalarFactor μ μ₀ : NNReal) : ENNReal) = (J.relIndex J₀ : ENNReal) := by
    have := congrArg (fun m : Measure (GA D V) => m ((K₀.comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V))) heq
    simp only [Measure.smul_apply, h0, ← hm] at this
    rw [this, ENNReal.smul_def, smul_eq_mul, mul_one]
  ext s hs
  rw [heq, Measure.smul_apply, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, smul_eq_mul, hc]

end GlobalTheory.LevelIndexMeasure
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierDoubleReflectionStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fourier_double_reflection : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ v : Pl F, (∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ], ∀ φ ∈ SB (κ → Fv F v), fourV ψ v (fourV ψ v φ) = fun x => φ (-x) := by
  first | exact @GlobalTheory.WeylFour.LocInv.fourV_fourV | exact GlobalTheory.WeylFour.LocInv.fourV_fourV | (intros; apply GlobalTheory.WeylFour.LocInv.fourV_fourV <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFourierSchrodingerIntertwineStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_fourier_schrodinger_intertwine : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (v : Pl F) (κ : Type) [Fintype κ]
    (w : (κ → Fv F v) × (κ → Fv F v)) (φ : (κ → Fv F v) → ℂ),
    fourV ψ v (schr (GlobalTheory.LatVac.psiAt ψ v) w φ) = schr (GlobalTheory.LatVac.psiAt ψ v) (w.2, -w.1) (fourV ψ v φ) := by
  first | exact @GlobalTheory.WeylFour.schr_fourV_loc | exact GlobalTheory.WeylFour.schr_fourV_loc | (intros; apply GlobalTheory.WeylFour.schr_fourV_loc <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivisibleGroupLatticeFreeRankHeightStatement
section
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivisibleGroup_lattice_free_rank_height : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ G : PDivGroup p O, HasDatum hε G → Module.Free (Ainf p O) (latt G) ∧ Module.Finite (Ainf p O) (latt G) ∧ Module.finrank (Ainf p O) (latt G) = G.height := by
  first | exact @GlobalTheory.PDivLat.latt_free_finrank | exact GlobalTheory.PDivLat.latt_free_finrank | (intros; apply GlobalTheory.PDivLat.latt_free_finrank <;> assumption)
end

