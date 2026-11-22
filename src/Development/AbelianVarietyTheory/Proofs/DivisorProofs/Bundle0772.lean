import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0762
import Development.AbelianVarietyTheory.Definitions.Divisors.PrimitiveCrystalHodgeLiftClasses
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0757
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0753
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0751
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumPadicLogLe
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0759
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeOfIsotropicSignature
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible NumberField IsDedekindDomain MeasureTheory Filter Topology GlobalTheory.ThetaInner
open scoped InnerProductSpace
open Matrix

namespace GlobalTheory.WittSignature

open scoped ComplexOrder in

theorem le_of_isotropic_standard {p q k : ℕ} (N : Matrix (Fin p ⊕ Fin q) (Fin k) ℂ) (L : Matrix (Fin k) (Fin p ⊕ Fin q) ℂ)
    (hL : L * N = 1) (h : Nᴴ * Formalism.UG.Jpq p q * N = 0) : k ≤ p ∧ k ≤ q := by
  have key : ∀ v : Fin k → ℂ, star ((N *ᵥ v) ∘ Sum.inl) ⬝ᵥ ((N *ᵥ v) ∘ Sum.inl) =
      star ((N *ᵥ v) ∘ Sum.inr) ⬝ᵥ ((N *ᵥ v) ∘ Sum.inr) := by
    intro v
    have h1 : star (N *ᵥ v) ⬝ᵥ (Formalism.UG.Jpq p q *ᵥ (N *ᵥ v)) = 0 := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h]
      simp
    generalize N *ᵥ v = x at h1 ⊢
    rw [Formalism.UG.Jpq, Matrix.fromBlocks_mulVec] at h1
    simp only [dotProduct, Fintype.sum_sum_type, Matrix.one_mulVec, Matrix.zero_mulVec, Matrix.neg_mulVec, add_zero, zero_add,
      Sum.elim_inl, Sum.elim_inr, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib] at h1
    simp only [dotProduct]
    exact add_neg_eq_zero.1 h1
  have inj : ∀ v : Fin k → ℂ, (N *ᵥ v) ∘ Sum.inl = 0 → (N *ᵥ v) ∘ Sum.inr = 0 → v = 0 := by
    intro v h1 h2
    have h3 : N *ᵥ v = 0 := by
      funext i
      rcases i with i | i
      · exact congrFun h1 i
      · exact congrFun h2 i
    have : (L * N) *ᵥ v = 0 := by rw [← Matrix.mulVec_mulVec, h3, Matrix.mulVec_zero]
    simpa [hL] using this
  constructor
  · have hf : Function.Injective ((LinearMap.funLeft ℂ ℂ (Sum.inl : Fin p → Fin p ⊕ Fin q)).comp N.mulVecLin) := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      have h1 : (N *ᵥ v) ∘ Sum.inl = 0 := hv
      have h2 := key v
      rw [h1, dotProduct_zero] at h2
      exact inj v h1 (dotProduct_star_self_eq_zero.1 h2.symm)
    simpa using LinearMap.finrank_le_finrank_of_injective hf
  · have hf : Function.Injective ((LinearMap.funLeft ℂ ℂ (Sum.inr : Fin q → Fin p ⊕ Fin q)).comp N.mulVecLin) := by
      rw [injective_iff_map_eq_zero]
      intro v hv
      have h1 : (N *ᵥ v) ∘ Sum.inr = 0 := hv
      have h2 := key v
      rw [h1, dotProduct_zero] at h2
      exact inj v (dotProduct_star_self_eq_zero.1 h2) h1
    simpa using LinearMap.finrank_le_finrank_of_injective hf

theorem le_of_isotropic_signature {n p q k : ℕ} (J : Matrix (Fin n) (Fin n) ℂ) (hJ : Formalism.UG.HasSignature J p q)
    (M : Matrix (Fin n) (Fin k) ℂ) (L : Matrix (Fin k) (Fin n) ℂ)
    (hL : L * M = 1) (h : Mᴴ * J * M = 0) : k ≤ p ∧ k ≤ q := by
  obtain ⟨e, P, hP⟩ := hJ
  have hP' : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * J.submatrix e.symm e.symm *
      (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) = Formalism.UG.Jpq p q := hP
  have hPP : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * (P⁻¹ : GL _ ℂ) = 1 := P.mul_inv
  have hN : (P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ).val * M.submatrix e.symm id) = M.submatrix e.symm id := by
    rw [← Matrix.mul_assoc, hPP, Matrix.one_mul]
  refine le_of_isotropic_standard ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ).val * M.submatrix e.symm id) (L.submatrix id e.symm * P.val) ?_ ?_
  · rw [Matrix.mul_assoc, hN, Matrix.submatrix_mul_equiv, hL, Matrix.submatrix_id_id]
  · rw [← hP']
    generalize ((P⁻¹ : GL _ ℂ) : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * M.submatrix e.symm id = N at hN ⊢
    calc _ = ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * N)ᴴ * J.submatrix e.symm e.symm *
          ((P : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * N) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = 0 := by
          rw [hN, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h]
          rfl

theorem wittIdx_le_signature : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E), S.SigOK → ∀ τ : E →+* ℂ, (∀ a : E, τ (star a) = starRingEnd ℂ (τ a)) → wittIdx S ≤ (S.sig τ).1 ∧ wittIdx S ≤ (S.sig τ).2 := by
  intro E _ _ _ S hS τ hτ
  have main : ∀ W : Submodule E S.V, (∀ x ∈ W, ∀ y ∈ W, S.hT x y = 0) →
      Module.finrank E W ≤ (S.sig τ).1 ∧ Module.finrank E W ≤ (S.sig τ).2 := by
    intro W hW
    let b := Module.finBasis E W
    obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective W.subtype W.ker_subtype
    let M := LinearMap.toMatrix b S.frame W.subtype
    let L := LinearMap.toMatrix S.frame b g
    have hL : L * M = 1 := by
      rw [← LinearMap.toMatrix_comp, hg, LinearMap.toMatrix_id]
    have hb : ∀ i, (b i : S.V) = ∑ a, M a i • S.frame a := by
      intro i
      simp only [M, LinearMap.toMatrix_apply, Submodule.subtype_apply]
      exact (S.frame.sum_repr _).symm
    have h : Mᴴ * S.gram * M = 0 := by
      ext i j
      have h0 := hW _ (b i).2 _ (b j).2
      rw [hb i, hb j] at h0
      simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply,
        starRingEnd_apply] at h0
      simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, HSpace.gram, Matrix.zero_apply]
      rw [← h0]
      exact Finset.sum_congr rfl fun a _ => mul_comm _ _
    refine le_of_isotropic_signature _ (hS τ) (M.map τ) (L.map τ) ?_ ?_
    · rw [← Matrix.map_mul, hL, Matrix.map_one _ (map_zero τ) (map_one τ)]
    · have : (M.map τ)ᴴ = (Mᴴ).map τ := by
        ext i j
        simp [Matrix.conjTranspose_apply, hτ]
      rw [this, ← Matrix.map_mul, ← Matrix.map_mul, h, Matrix.map_zero _ (map_zero τ)]
  constructor
  · refine csSup_le' ?_
    rintro k ⟨W, rfl, hW⟩
    exact (main W hW).1
  · refine csSup_le' ?_
    rintro k ⟨W, rfl, hW⟩
    exact (main W hW).2

end GlobalTheory.WittSignature
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAbelianSchemeAlongSquareZeroFactorization
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

theorem corr_crysToDR_step_iff {R R₁ R₀ : Type} [CommRing R] [CommRing R₁] [CommRing R₀] {I : Ideal R}
    {I₁ : Ideal R₁} {κ : DividedPowers I} {κ₁ : DividedPowers I₁} {π : R →+* R₀} {ρ : R →+* R₁}
    {π₁ : R₁ →+* R₀} {A₀ : Over (Sp R₀)} [GrpObj A₀] {X₁ : Over (Sp R₁)} [GrpObj X₁] {X : Over (Sp R)}
    [GrpObj X] {i₁ : A₀.left ⟶ X₁.left} {i₂ : X₁.left ⟶ X.left} {i : A₀.left ⟶ X.left}
    (h₁ : IsGrpPullback A₀ X₁ (spMap π₁) i₁) (h₂ : IsGrpPullback X₁ X (spMap ρ) i₂)
    (h : IsGrpPullback A₀ X (spMap π) i) (e : i₁ ≫ i₂ = i)
    (M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _))
    (hs : Function.Surjective (liftMor κ h).pull) (d : Crys κ (spMap π) A₀) (d₁ : Crys κ₁ (spMap π₁) A₀) :
    (redMor h₂).Corr (crysToDR κ h d) (crysToDR κ₁ h₁ d₁) ↔ M.Corr d d₁ := by
  have k := (liftMor κ h).comp M
  have e1 : ∀ c, (liftMor κ₁ h₁).pull ((redMor h₂).pull c) = k.pull c := fun c ↦
    GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) (by rw [Category.id_comp, e]) c
  have e2 : ∀ c, M.pull ((liftMor κ h).pull c) = k.pull c := fun c ↦
    GrpMor.pull_pull _ _ _ (fun _ ↦ rfl) rfl c
  constructor
  · intro H c
    obtain ⟨c, rfl⟩ := hs c
    have := H c
    rw [crysToDR_apply, crysToDR_apply, e1, ← e2] at this
    exact this
  · intro H c
    rw [crysToDR_apply, crysToDR_apply, e1, ← e2]
    exact H _

theorem liftObj_step : AbelianDeRham → AbelianUnobstructed → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁]
    [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    LiftObj (divided₂ hJ) ρ → LiftObj κ₁ π₁ → LiftObj κ π := by
  intro P U R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ S L₂ L₁
  intro g A₀ _ A' _ i' h' hA' hg F hF
  have hπ : Function.Surjective π := S.comp ▸ S.surj₁.comp S.surj
  have hrig := P.2.2.2.1
  have hsp : spMap π = spMap π₁ ≫ spMap ρ := by rw [← S.comp, Cris.spMap_comp]
  have M : GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _) := GrpMor.of_hom S.dp hsp (𝟙 A₀)

  obtain ⟨A₁, _, i₁, i₂, h₁, h₂, e₁₂, hA₁, hg₁⟩ :=
    GlobalTheory.T.exists_intermediate_grpPullback_abelianScheme R R₁ R₀ ρ π₁ g A₀ A' i' (by rw [S.comp]; exact h') hA' hg
  obtain ⟨F₁, hF₁, hF₁F⟩ :=
    GlobalTheory.T.group_scheme_divided_power_lift_tower P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ S g A₀ A₁ A' i₁ i₂ i' h₁ h₂ h' e₁₂ hA' hg F hF

  obtain ⟨B₁, _, j₁, k₁, hB₁, hgB₁, hfB₁⟩ := L₁ g A₀ A₁ i₁ h₁ hA₁ hg₁ F₁ hF₁
  obtain ⟨C, _, j₂, k₂, hC⟩ := U R J hJ R₁ ρ S.surj S.kerJ B₁ hB₁
  have hgC : SmoothOfRelativeDimension g C.hom :=
    GlobalTheory.T.smoothOfRelativeDimension_of_nilpotent_reduction R R₁ ρ S.surj (by rw [S.kerJ]; exact ⟨2, hJ⟩) g C B₁ j₂ k₂.1 hC.smooth hgB₁
  have kC : IsGrpPullback A₀ C (spMap π) (j₁ ≫ j₂) := (k₁.comp k₂).congr hsp.symm rfl
  have b' : Function.Bijective (crysToDR κ h') :=
    AbelianDeRham.Rigid.crysToDR_bijective hrig hA' hg S.nil hπ S.ker h'
  have bC : Function.Bijective (crysToDR κ kC) :=
    AbelianDeRham.Rigid.crysToDR_bijective hrig hC hgC S.nil hπ S.ker kC
  have bB₁ : Function.Bijective (crysToDR κ₁ k₁) :=
    AbelianDeRham.Rigid.crysToDR_bijective hrig hB₁ hgB₁ S.nil₁ S.surj₁ S.ker₁ k₁
  have s' := (hrig R A' g hA' hg I κ S.nil R₀ π hπ S.ker A₀ i' h').2
  have sC := (hrig R C g hC hgC I κ S.nil R₀ π hπ S.ker A₀ _ kC).2

  set E := F.comap (crysToDR κ h') with hE
  set FC := E.map (crysToDR κ kC) with hFC
  have hFCa : IsAdmissible k₂ FC := by
    obtain ⟨N, hN⟩ := hF.1
    refine ⟨⟨(N.comap (crysToDR κ h')).map (crysToDR κ kC), ?_⟩, fun y ↦ ?_⟩
    · exact (Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ bC)).isCompl
        ((Submodule.orderIsoMapComap (LinearEquiv.ofBijective _ b')).symm.isCompl hN)
    obtain ⟨d₁, rfl⟩ := bB₁.2 y
    have l1 : crysToDR κ₁ k₁ d₁ ∈ Fil B₁ ↔ ∃ d ∈ E, M.Corr d d₁ := by
      change d₁ ∈ liftFil κ₁ k₁ ↔ _
      rw [hfB₁, Submodule.mem_comap, hF₁F]
      constructor
      · rintro ⟨x, hx, ex⟩
        obtain ⟨d, rfl⟩ := b'.2 x
        exact ⟨d, hx, (corr_crysToDR_step_iff h₁ h₂ h' e₁₂ M s' d d₁).1 ex⟩
      · rintro ⟨d, hd, ed⟩
        exact ⟨_, hd, (corr_crysToDR_step_iff h₁ h₂ h' e₁₂ M s' d d₁).2 ed⟩
    rw [l1]
    constructor
    · rintro ⟨d, hd, ed⟩
      exact ⟨_, ⟨d, hd, rfl⟩, (corr_crysToDR_step_iff k₁ k₂ kC rfl M sC d d₁).2 ed⟩
    · rintro ⟨_, ⟨d, hd, rfl⟩, ex⟩
      exact ⟨d, hd, (corr_crysToDR_step_iff k₁ k₂ kC rfl M sC d d₁).1 ex⟩

  obtain ⟨A, _, j₃, k₃, hA, hgA, hfA⟩ := L₂ g B₁ C j₂ k₂ hC hgC FC hFCa
  have kA : IsGrpPullback A₀ A (spMap π) (j₁ ≫ j₃) := (k₁.comp k₃).congr hsp.symm rfl
  refine ⟨A, inferInstance, j₁ ≫ j₃, kA, hA, hgA, ?_⟩
  obtain ⟨N, -, hNC⟩ :=
    GlobalTheory.T.deRham_crystal_two_reductions_agree P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ S g A₀ B₁ C j₁ j₂ (j₁ ≫ j₂) k₁ k₂ kC rfl hC hgC
  obtain ⟨N', -, hNA⟩ :=
    GlobalTheory.T.deRham_crystal_two_reductions_agree P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ S g A₀ B₁ A j₁ j₃ (j₁ ≫ j₃) k₁ k₃ kA rfl hA hgA
  obtain rfl : N' = N := rfl
  ext d
  change crysToDR κ kA d ∈ Fil A ↔ d ∈ E
  rw [hNA d]
  change _ ∈ liftFil (divided₂ hJ) k₃ ↔ _
  rw [hfA, Submodule.mem_comap, ← hNC d]
  exact ⟨fun ⟨d', hd', e⟩ ↦ bC.1 e ▸ hd', fun hd ↦ ⟨d, hd, rfl⟩⟩

end GlobalTheory.SqLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHomOfIsStep
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj DividedPowers
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.Published GlobalTheory.Published.GrothendieckMessing

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SqLift

section Step

variable {R R₁ R₀ : Type} [CommRing R] [CommRing R₁] [CommRing R₀] {I J : Ideal R} {I₁ : Ideal R₁}
  {κ : DividedPowers I} {π : R →+* R₀} {hJ : J ^ 2 = 0} {ρ : R →+* R₁} {κ₁ : DividedPowers I₁}
  {π₁ : R₁ →+* R₀}

theorem IsStep.spMap_eq (st : IsStep κ π hJ ρ κ₁ π₁) : spMap π = spMap π₁ ≫ spMap ρ := by
  rw [← st.comp, Cris.spMap_comp]

theorem IsStep.idMor (st : IsStep κ π hJ ρ κ₁ π₁) (A₀ : Over (Sp R₀)) [GrpObj A₀] :
    GrpMor κ (spMap π) A₀ κ₁ (spMap π₁) A₀ ρ (𝟙 _) (𝟙 _) :=
  GrpMor.of_hom st.dp st.spMap_eq (𝟙 A₀)

def redSub (hρ : Function.Surjective ρ) {A₁ : Over (Sp R₁)} [GrpObj A₁] {A : Over (Sp R)} [GrpObj A]
    {i₂ : A₁.left ⟶ A.left} (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (F : Submodule R (HdR A)) :
    Submodule R₁ (HdR A₁) where
  carrier := {y | ∃ x ∈ F, (redMor h₂).Corr x y}
  add_mem' := by
    rintro y y' ⟨x, hx, e⟩ ⟨x', hx', e'⟩
    exact ⟨x + x', F.add_mem hx hx', fun c ↦ by
      rw [LinearMap.add_apply, LinearMap.add_apply, e, e', map_add]⟩
  zero_mem' := ⟨0, F.zero_mem, fun c ↦ by simp⟩
  smul_mem' := by
    rintro r₁ y ⟨x, hx, e⟩
    obtain ⟨r, rfl⟩ := hρ r₁
    exact ⟨r • x, F.smul_mem r hx, fun c ↦ by
      rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, e, map_mul]⟩

theorem mem_liftFil_iff (P : AbelianDeRham) (st : IsStep κ π hJ ρ κ₁ π₁) {g : ℕ} {A₀ : Over (Sp R₀)}
    [GrpObj A₀] {A₁ : Over (Sp R₁)} [GrpObj A₁] {A : Over (Sp R)} [GrpObj A] {i₁ : A₀.left ⟶ A₁.left}
    {i₂ : A₁.left ⟶ A.left} {i : A₀.left ⟶ A.left} (h₁ : IsGrpPullback A₀ A₁ (spMap π₁) i₁)
    (h₂ : IsGrpPullback A₁ A (spMap ρ) i₂) (h : IsGrpPullback A₀ A (spMap π) i) (ei : i₁ ≫ i₂ = i)
    (hA : IsAbelianScheme A) (hg : SmoothOfRelativeDimension g A.hom) (d₁ : Crys κ₁ (spMap π₁) A₀) :
    d₁ ∈ liftFil κ₁ h₁ ↔ ∃ d ∈ liftFil κ h, (st.idMor A₀).Corr d d₁ := by
  have T := GlobalTheory.T.hodgeFiltration_middle_eq_reduction_of_top P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st g A₀ A₁ A i₁ i₂ i h₁ h₂ h ei hA hg
    (st.idMor A₀) (Fil A) (redSub st.surj h₂ (Fil A)) (fun _ ↦ Iff.rfl)
  have e : Fil A₁ = redSub st.surj h₂ (Fil A) := Submodule.ext T.2
  rw [liftFil, Submodule.mem_comap, e, T.1 d₁]
  exact Iff.rfl

theorem dualMap_push {A₀ B₀ : Over (Sp R₀)} [GrpObj A₀] [GrpObj B₀] {A₁ B₁ : Over (Sp R₁)} [GrpObj A₁]
    [GrpObj B₁] {i₁ : A₀.left ⟶ A₁.left} {j₁ : B₀.left ⟶ B₁.left}
    (NA : GrpMor (divided₂ hJ) (spMap ρ) A₁ κ (spMap π) A₀ (RingHom.id R) (spMap π₁) i₁)
    (NB : GrpMor (divided₂ hJ) (spMap ρ) B₁ κ (spMap π) B₀ (RingHom.id R) (spMap π₁) j₁)
    (f₀ : A₀ ⟶ B₀) (f₁ : A₁ ⟶ B₁) [IsMonHom f₀] [IsMonHom f₁] (e : i₁ ≫ f₁.left = f₀.left ≫ j₁)
    (d : Crys κ (spMap π) A₀) :
    (NB.pull : prim (divided₂ hJ) (spMap ρ) B₁ →ₗ[R] prim κ (spMap π) B₀).dualMap (push κ (spMap π) f₀ d) =
      push (divided₂ hJ) (spMap ρ) f₁
        ((NA.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀).dualMap d) := by
  refine LinearMap.ext fun c ↦ ?_
  have m := (homMor (divided₂ hJ) (spMap ρ) f₁).comp NA
  have e1 : (homMor κ (spMap π) f₀).pull (NB.pull c) = m.pull c :=
    GrpMor.pull_pull NB (homMor κ (spMap π) f₀) m (fun _ ↦ rfl) e.symm c
  have e2 : NA.pull ((homMor (divided₂ hJ) (spMap ρ) f₁).pull c) = m.pull c :=
    GrpMor.pull_pull (homMor (divided₂ hJ) (spMap ρ) f₁) NA m (fun _ ↦ rfl) rfl c
  exact congrArg d (e1.trans e2.symm)

end Step

theorem liftHom_of_isStep : AbelianDeRham → ∀ (R R₁ R₀ : Type) [CommRing R] [CommRing R₁] [CommRing R₀] (I J : Ideal R) (I₁ : Ideal R₁) (κ : DividedPowers I) (π : R →+* R₀)
    (hJ : J ^ 2 = 0) (ρ : R →+* R₁) (κ₁ : DividedPowers I₁) (π₁ : R₁ →+* R₀), IsStep κ π hJ ρ κ₁ π₁ →
    LiftHom (divided₂ hJ) ρ → LiftHom κ₁ π₁ → LiftHom κ π := by
  intro P R R₁ R₀ _ _ _ I J I₁ κ π hJ ρ κ₁ π₁ st H₂ H₁
  intro g A₀ _ A _ i h hA hg g' B₀ _ B _ j k hB hg' f₀ _ hf
  have hc : spMap (π₁.comp ρ) = spMap π := by rw [st.comp]
  obtain ⟨A₁, _, i₁, i₂, h₁, h₂, ei, hA₁, hgA⟩ :=
    GlobalTheory.T.exists_intermediate_grpPullback_abelianScheme R R₁ R₀ ρ π₁ g A₀ A i (by rw [hc]; exact h) hA hg
  obtain ⟨B₁, _, j₁, j₂, k₁, k₂, ej, hB₁, hgB⟩ :=
    GlobalTheory.T.exists_intermediate_grpPullback_abelianScheme R R₁ R₀ ρ π₁ g' B₀ B j (by rw [hc]; exact k) hB hg'

  have hf₁ : ∀ d₁ ∈ liftFil κ₁ h₁, push κ₁ (spMap π₁) f₀ d₁ ∈ liftFil κ₁ k₁ := by
    intro d₁ hd₁
    obtain ⟨d, hd, e⟩ := (mem_liftFil_iff P st h₁ h₂ h ei hA hg d₁).1 hd₁
    exact (mem_liftFil_iff P st k₁ k₂ k ej hB hg' _).2
      ⟨_, hf d hd, GrpMor.Corr.push (st.idMor B₀) f₀ f₀ (by simp) e⟩
  obtain ⟨f₁, ⟨_, ef₁⟩, uf₁⟩ := H₁ g A₀ A₁ i₁ h₁ hA₁ hgA g' B₀ B₁ j₁ k₁ hB₁ hgB f₀ hf₁

  obtain ⟨NA, bA, cA⟩ := GlobalTheory.T.deRham_crystal_two_reductions_agree P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st g A₀ A₁ A i₁ i₂ i h₁ h₂ h ei hA hg
  obtain ⟨NB, -, cB⟩ := GlobalTheory.T.deRham_crystal_two_reductions_agree P R R₁ R₀ I J I₁ κ π hJ ρ κ₁ π₁ st g' B₀ B₁ B j₁ j₂ j k₁ k₂ k ej hB hg'
  have sA : Function.Surjective
      (NA.pull : prim (divided₂ hJ) (spMap ρ) A₁ →ₗ[R] prim κ (spMap π) A₀).dualMap :=
    (LinearEquiv.ofBijective _ bA).dualMap.surjective
  have hf₂ : ∀ e ∈ liftFil (divided₂ hJ) h₂, push (divided₂ hJ) (spMap ρ) f₁ e ∈ liftFil (divided₂ hJ) k₂ := by
    intro e he
    obtain ⟨d, rfl⟩ := sA e
    have hd : d ∈ liftFil κ h := by
      rw [liftFil, Submodule.mem_comap, cA]; exact he
    have hk := hf d hd
    rw [liftFil, Submodule.mem_comap, cB] at hk
    rw [liftFil, Submodule.mem_comap, ← dualMap_push NA NB f₀ f₁ ef₁ d]
    exact hk
  obtain ⟨f, ⟨_, ef⟩, uf⟩ := H₂ g A₁ A i₂ h₂ hA hg g' B₁ B j₂ k₂ hB hg' f₁ hf₂
  refine ⟨f, ⟨inferInstance, ?_⟩, ?_⟩
  · rw [← ei, ← ej, Category.assoc, ef, ← Category.assoc, ef₁, Category.assoc]
  · rintro f' ⟨_, ef'⟩
    let f₁' : A₁ ⟶ B₁ := Over.homMk (k₂.1.lift (i₂ ≫ f'.left) A₁.hom
      (by rw [Category.assoc, Over.w f', h₂.1.w])) (k₂.1.lift_snd _ _ _)
    have e₁ : f₁'.left ≫ j₂ = i₂ ≫ f'.left := k₂.1.lift_fst _ _ _
    haveI := ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback h₂ k₂ f' f₁' e₁
    have e₂ : i₁ ≫ f₁'.left = f₀.left ≫ j₁ := by
      refine k₂.1.hom_ext ?_ ?_
      · rw [Category.assoc, e₁, ← Category.assoc, ei, ef', Category.assoc, ej]
      · rw [Category.assoc, Category.assoc, Over.w f₁', h₁.1.w, k₁.1.w, ← Category.assoc, Over.w f₀]
    have e₃ : f₁' = f₁ := uf₁ f₁' ⟨inferInstance, e₂⟩
    exact uf f' ⟨inferInstance, by rw [← e₁, e₃]⟩

end GlobalTheory.SqLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LossSumPrimes
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

noncomputable section

namespace GlobalTheory.ConjLossPrimes

theorem bound_one {D : D7} {L : SizeData₂ D} {c : ErrC}
    (hc : c.dig = 3) (P : ParameterChoice' D L) (hS : SizesAt L) (hx : 2 ≤ L.sc.x) (j : ℕ)
    (hj : j ∈ SizeData₂.lifts D) (Q : Finset ℕ)
    (hQ : ∀ p ∈ Q, p.Prime ∧ (p : ℝ) ≤ L.sc.X'' D.R.n) :
    ∑ p ∈ Q, 2 * Real.log (p : ℝ) * |EatC L c j p| ≤ 2 * (9 * (1 / L.sc.eps + 1)) * L.B0 := by
  have hEg : ∀ p ∈ Q, 2 * Real.log (p : ℝ) * |EatC L c j p| = 2 * (Real.log (p : ℝ) * |(padicValNat p 1 : ℝ) +
    (if (p : ℝ) ≤ L.sc.X'' D.R.n then 3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.logb p L.sc.a +
      (∑ τ : D.what₂.Tau, wj D j τ) / ((p : ℝ) ^ 2 - 1) else 0)|) := by
    intro p hp
    have e0 : padicValNat p 1 = 0 := by simp
    rw [if_pos (hQ p hp).2, e0, Nat.cast_zero, zero_add]
    unfold EatC Formalism.MainNotions.G.Nm
    rw [hc, mul_assoc]
  rw [Finset.sum_congr rfl hEg]
  rw [← Finset.mul_sum, mul_assoc (2 : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  have hL := HCEntries.one_le_scL L
  have hb := HCEntries.one_le_b L
  have hk := HCEntries.one_le_k D
  have ht := HCEntries.one_le_letterBlockLength D
  have hmn := D.R.two_le_m
  have hkn := D.R.m_add_three_le_k
  have hmfn : D.R.m ≤ D.R.f := D.R.m_le_f
  have hm : (1 : ℝ) ≤ D.R.m := by exact_mod_cast (by omega : 1 ≤ D.R.m)
  have hf : (1 : ℝ) ≤ D.R.f := by exact_mod_cast (by omega : 1 ≤ D.R.f)
  have hN : (1 : ℝ) ≤ D.R.N D.R.m := by
    exact_mod_cast (by unfold Ranks.N; omega : 1 ≤ D.R.N D.R.m)
  have hη0 := L.etaSz_pos.le
  have hNη : (D.R.N D.R.m : ℝ) ^ 2 ≤ L.etaSz := by
    have a1 := P.h0_ge.2.2.2.2.1
    have a2 : LevelStarExponents.h0 L ≤ L.etaSz := div_le_self hη0 hm
    have a3 : (D.R.N D.R.m : ℝ) ^ 2 ≤ (D.R.N D.R.m : ℝ) ^ 3 := pow_le_pow_right₀ hN (by norm_num)
    have a4 : 0 ≤ (D.R.N D.R.m : ℝ) ^ 3 := by positivity
    linarith
  have hx0 : 0 < L.sc.x := by linarith
  have ha : L.sc.a = L.sc.x * L.sc.b := rfl
  have ha1 : 1 ≤ L.sc.a := by rw [ha]; exact one_le_mul_of_one_le_of_one_le (by linarith) hb
  have hN2 : (1 : ℝ) ≤ (D.R.N D.R.m : ℝ) ^ 2 := one_le_pow₀ hN
  have hw : (D.R.N D.R.m : ℝ) ^ 2 * L.sc.x ≤ L.sc.w'' D.R.n := by
    have a1 := P.teta
    rw [le_div_iff₀ hx0] at a1
    exact (mul_le_mul_of_nonneg_right (hNη.trans (le_mul_of_one_le_left hη0 ht)) hx0.le).trans a1
  have hw1 : 1 ≤ L.sc.w'' D.R.n := (one_le_mul_of_one_le_of_one_le hN2 (by linarith)).trans hw
  have hX0 : 0 ≤ L.sc.X'' D.R.n := by unfold Scale.X''; positivity
  have hXa : L.sc.X'' D.R.n ≤ L.sc.a := div_le_self (by linarith) hw1
  have hXN : L.sc.X'' D.R.n * (D.R.N D.R.m : ℝ) ^ 2 ≤ L.sc.b := by
    unfold Scale.X''
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith), ha]
    have := mul_le_mul_of_nonneg_left hw (by linarith : 0 ≤ L.sc.b)
    linarith
  obtain ⟨hj1, hjm⟩ := Finset.mem_Icc.1 hj
  have hwj := HCEntries.wj_bounds hS hx j hj1 hjm
  have hW0 : 0 ≤ ∑ τ : D.what₂.Tau, wj D j τ := Finset.sum_nonneg fun τ _ => (hwj τ).1
  have hcard : Fintype.card D.what₂.Tau = D.R.f := D.what₂.card_Tau
  have hW : ∑ τ : D.what₂.Tau, wj D j τ ≤ D.R.f * (3 * L.sc.b) := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun τ : D.what₂.Tau => wj D j τ) _ fun τ _ => (hwj τ).2
    rwa [Finset.card_univ, hcard, nsmul_eq_mul] at this
  have hla0 : 0 ≤ Real.log L.sc.a := Real.log_nonneg ha1
  have he := L.sc.eps_pos
  have hla : Real.log L.sc.a ≤ (1 / L.sc.eps + 1) * L.sc.L := by
    rw [ha, Real.log_mul hx0.ne' (by linarith)]
    have a1 : Real.log L.sc.b = L.sc.L := Real.log_exp _
    have a2 : Real.log L.sc.x ≤ L.sc.L / L.sc.eps := Real.log_le_rpow_div hx0.le he
    rw [a1]
    calc _ ≤ L.sc.L / L.sc.eps + L.sc.L := by linarith
      _ = _ := by ring
  have hB : L.B0 = D.R.f * D.R.m * L.sc.b * L.sc.L := rfl
  have hfb : 0 ≤ (D.R.f : ℝ) * L.sc.b := by positivity
  have hB1 : D.R.f * L.sc.b * L.sc.L ≤ L.B0 := by
    have : L.B0 = D.R.m * (D.R.f * L.sc.b * L.sc.L) := by rw [hB]; ring
    rw [this]
    exact le_mul_of_one_le_left (by positivity) hm
  have hfl : D.R.f * L.sc.b * Real.log L.sc.a ≤ (1 / L.sc.eps + 1) * L.B0 := by
    calc _ ≤ D.R.f * L.sc.b * ((1 / L.sc.eps + 1) * L.sc.L) := mul_le_mul_of_nonneg_left hla hfb
      _ = (1 / L.sc.eps + 1) * (D.R.f * L.sc.b * L.sc.L) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hB1 (by positivity)
  have t2 : L.sc.X'' D.R.n * (3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2 * Real.log L.sc.a) ≤
      3 * (D.R.f * L.sc.b * Real.log L.sc.a) := by
    calc _ = 3 * (D.R.f * (L.sc.X'' D.R.n * (D.R.N D.R.m : ℝ) ^ 2) * Real.log L.sc.a) := by ring
      _ ≤ _ := by gcongr
  have t3 : (∑ τ : D.what₂.Tau, wj D j τ) * Real.log L.sc.a ≤ 3 * (D.R.f * L.sc.b * Real.log L.sc.a) := by
    calc _ ≤ D.R.f * (3 * L.sc.b) * Real.log L.sc.a := mul_le_mul_of_nonneg_right hW hla0
      _ = _ := by ring
  have key := GlobalTheory.ConjLoss.sum_primes_le Q (fun p hp => (hQ p hp).1)
    1 (L.sc.X'' D.R.n) L.sc.a (3 * (D.R.f : ℝ) * (D.R.N D.R.m : ℝ) ^ 2)
    (∑ τ : D.what₂.Tau, wj D j τ) hX0 hXa ha1 (by positivity) hW0
  refine key.trans ?_
  rw [Nat.cast_one, Real.log_one]
  linarith

theorem loss_sum_primes : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, ∀ j ∈ SizeData₂.lifts (Fm.D x i), ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ (p : ℝ) ≤ (Fm.L x i).sc.X'' (Fm.D x i).R.n) → ∑ p ∈ P, 2 * Real.log (p : ℝ) * |EatC (Fm.L x i) Fm.cX.err j p| ≤ C * (Fm.L x i).B0 := by
  intro eps Fm h0 h1
  refine ⟨2 * (9 * (1 / eps + 1)), 2, by positivity, ?_⟩
  intro x hx0 hx i j hj Q hQ
  have hsx : (Fm.L x i).sc.x = x := Fm.L_x x i hx
  have hse : (Fm.L x i).sc.eps = eps := Fm.L_eps x i
  have := bound_one (c := Fm.cX.err) Fm.fixed.2.2.2.2.2.1 (Fm.params x hx i) (Fm.sizes x hx i)
    (by rw [hsx]; exact hx0) j hj Q hQ
  rwa [hse] at this

end GlobalTheory.ConjLossPrimes

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteLieAction
section
open NumberField GlobalTheory.CuspRep

namespace GlobalTheory.CuspRep

theorem Zalg_mul_lie : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (X : GlobalTheory.CuspRep.Lie E a)
    (z : Module.End ℂ (GlobalTheory.CuspRep.Sm E a)), z ∈ GlobalTheory.CuspRep.Zalg E a →
      z * GlobalTheory.CuspRep.lie E a X = GlobalTheory.CuspRep.lie E a X * z := by
  intro E _ _ _ a X z hz
  have h : GlobalTheory.CuspRep.Zalg E a ≤ Subalgebra.centralizer ℂ {GlobalTheory.CuspRep.lie E a X} := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    intro y hy
    rw [Set.mem_singleton_iff.1 hy]
    exact (commute_cap_lie τ u X).eq.symm
  exact ((Subalgebra.mem_centralizer_iff ℂ).1 (h hz) _ rfl).symm

end GlobalTheory.CuspRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIdempotentSplitFieldStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pDivGroup_idempotent_split_field : ∀ (p : ℕ) [Fact p.Prime] (k : Type) [Field k] (G : PDivGroup p k) (u v : G ⟶ G), u + v = 𝟙 G → u ≫ v = 0 → v ≫ u = 0 → ∃ (K : PDivGroup p k) (i : K ⟶ G) (q : G ⟶ K), i ≫ q = 𝟙 K ∧ q ≫ i = v ∧ ∀ n : ℕ, Function.Surjective (i.app n) ∧ RingHom.ker (i.app n) = kerIdeal (u.app n) := by
  first | exact @GlobalTheory.PDivGroup.idempotent_split | exact GlobalTheory.PDivGroup.idempotent_split | (intros; apply GlobalTheory.PDivGroup.idempotent_split <;> assumption)
end

