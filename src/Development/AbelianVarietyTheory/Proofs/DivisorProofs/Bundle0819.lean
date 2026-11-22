import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0796
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0775
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0817
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0790
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0726
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0810
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfSmallExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0777
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0797
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLevelTypePrimeDatumLocallySmall
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTaylorExpansionOrderOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0022
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEqZeroOfConnecting
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0654
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0807
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0766
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyFieldAddEquivGalois
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleDegreeCountAlongFamilyStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degreeCountBound_of_eps_lt_one_div_52 : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.DegreeCountBound (Fm.D x i) (Fm.L x i) C := by
  first | exact @GlobalTheory.AdmissibleDegree.admissibleDegreeCount_along_family | exact GlobalTheory.AdmissibleDegree.admissibleDegreeCount_along_family | (intros; apply GlobalTheory.AdmissibleDegree.admissibleDegreeCount_along_family <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleOffTypeFamilyBound
section
open Formalism.BasicNotions Formalism.BasicNotions.DV Formalism.MainNotions NumberField Classical

namespace GlobalTheory.LevelBudget

variable {D : D7} {L : SizeData₂ D}

theorem ETpi_le (h : SizesAt L) (P : ParameterChoice' D L) (hx : 2 ≤ L.sc.x) (u : D.what₂.Word) :
    Formalism.MainNotions.product_first_zeroth_parts.ETpi D u ≤ 12 * D.R.f * L.sc.b := by
  have hb := GlobalTheory.HCEntries.one_le_b L
  have hf0 : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  unfold Formalism.MainNotions.product_first_zeroth_parts.ETpi
  have hN := GlobalTheory.LevelLoss.N_le_b h P
  have hNe : (D.R.N D.R.m : ℝ) = D.R.k + D.R.m * (D.R.t + 1) := by unfold Ranks.N; push_cast; ring
  have r2 := (GlobalTheory.FockDegreeGap.ranks_le D).2
  have hk0 : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
  have h1 : ∑ τ : D.what₂.Tau, (Formalism.MainNotions.product_first_zeroth_parts.Wt D u τ : ℝ) ≤ D.R.f * (5 * L.sc.b) := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun τ : D.what₂.Tau => (Formalism.MainNotions.product_first_zeroth_parts.Wt D u τ : ℝ)) _
      (fun τ _ => GlobalTheory.LevelLoss.Wtau_le h P hx u τ)
    rwa [Finset.card_univ, D.what₂.card_Tau, nsmul_eq_mul] at this
  have h2 : ((Formalism.MainNotions.product_first_zeroth_parts.tops D).card : ℝ) ≤ D.R.f := by
    have := Finset.card_le_univ (Formalism.MainNotions.product_first_zeroth_parts.tops D)
    rw [D.what₂.card_Tau] at this
    exact_mod_cast this
  have h3 : ((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1) ≤ L.sc.b := by nlinarith
  have h4 : ((Formalism.MainNotions.product_first_zeroth_parts.tops D).card : ℝ) * (((D.R.t : ℝ) + 1) * ((D.R.m : ℝ) + 1)) ≤ D.R.f * L.sc.b :=
    mul_le_mul h2 h3 (by positivity) hf0
  have h5 : (D.R.f : ℝ) * D.R.N D.R.m ≤ D.R.f * L.sc.b :=
    mul_le_mul_of_nonneg_left (by linarith [Nat.cast_nonneg (α := ℝ) (D.R.N D.R.m)]) hf0
  have h6 : 0 ≤ (D.R.f : ℝ) * L.sc.b := by positivity
  nlinarith

theorem admissible_off_type_level_budget : ∀ {eps : ℝ} (Fm : FamP eps), 0 < eps → eps < 1 / 52 → TuSize Fm → ∃ C x0 : ℝ, 0 ≤ C ∧ ∀ x, x0 ≤ x → ∀ hx : Fm.x1 < x, ∀ i : Fm.Ix x, Formalism.MainNotions.WeightDegreeSizes.LevelPrimeBudget (Fm.D x i) (Fm.L x i) C := by
  intro eps Fm _ _ ⟨x₁, h1⟩
  refine ⟨max (12 * Fm.CTu) 0, max 2 x₁, le_max_right _ _, fun x hx0 hx i u => ⟨fun S hS => GlobalTheory.SeenHalf.seen_half Fm x hx i u S hS, ?_⟩⟩
  have a := ETpi_le (Fm.sizes x hx i) (Fm.params x hx i)
    (by rw [Fm.L_x x i hx]; exact (le_max_left _ _).trans hx0) u
  have b := (h1 x ((le_max_right _ _).trans hx0) i).2 u
  have hb := GlobalTheory.HCEntries.one_le_b (Fm.L x i)
  have hT : (1 : ℝ) ≤ (((Fm.D x i).mem u).A.T : ℝ) := by exact_mod_cast ((Fm.D x i).mem u).A.T_prime.one_le
  have hl : 0 ≤ Real.log (((Fm.D x i).mem u).A.T : ℝ) := Real.log_nonneg hT
  have e : (Fm.L x i).B0 = (Fm.D x i).R.f * (Fm.D x i).R.m * (Fm.L x i).sc.b * (Fm.L x i).sc.L := rfl
  have hB : 0 ≤ (Fm.L x i).B0 := Formalism.MainNotions.WeightDegreeSizes.loss_bound_nonneg _
  calc Formalism.MainNotions.product_first_zeroth_parts.ETpi (Fm.D x i) u * Real.log (((Fm.D x i).mem u).A.T : ℝ)
      ≤ 12 * (Fm.D x i).R.f * (Fm.L x i).sc.b * Real.log (((Fm.D x i).mem u).A.T : ℝ) :=
        mul_le_mul_of_nonneg_right a hl
    _ ≤ 12 * (Fm.D x i).R.f * (Fm.L x i).sc.b * (Fm.CTu * (Fm.D x i).R.m * (Fm.L x i).sc.L) :=
        mul_le_mul_of_nonneg_left b (by positivity)
    _ = 12 * Fm.CTu * (Fm.L x i).B0 := by rw [e]; ring
    _ ≤ max (12 * Fm.CTu) 0 * (Fm.L x i).B0 := mul_le_mul_of_nonneg_right (le_max_left _ _) hB

end GlobalTheory.LevelBudget
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArtinianLiftAxesWedge
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh.SmallStepSurj

theorem spMap_comp_hom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

theorem surj_of_smallExt : ∀ (R : Type) [CommRing R] [IsLocalRing R] (t : R) (R' : Type) [CommRing R'] (σ' : R →+* R'), Function.Surjective σ' → RingHom.ker σ' = Ideal.span {t} → t ≠ 0 → (∀ a ∈ IsLocalRing.maximalIdeal R, a * t = 0) → (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) → (∀ (B : Over (Sp R')) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (∀ (k : Type) [Field k] (σ : R' →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ B.left) (w : IsPullback ψ s₀ B.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) ∧ StructureSheafH1Primitive B) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → (∀ (k : Type) [Field k] (σ : R →+* k), Function.Surjective σ → ∀ (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ A.left) (w : IsPullback ψ s₀ A.hom (spMap σ)), Function.Surjective (pullHO1 w.w)) := by
  intro R _ _ t R' _ σ' hσ' hker ht hm hfield hR' A _ g hA hg k _ σ hσ X₀ s₀ ψ w
  have hkerσ : RingHom.ker σ = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective σ hσ)
  by_cases htm : t ∈ IsLocalRing.maximalIdeal R
  ·
    let R₀ := R ⧸ IsLocalRing.maximalIdeal R
    let σ₀ : R →+* R₀ := Ideal.Quotient.mk _
    have hR₀ : IsField R₀ :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 (IsLocalRing.maximalIdeal.isMaximal R)
    have hse : SmallExt t σ' σ₀ := by
      refine ⟨hσ', hker, Ideal.Quotient.mk_surjective, fun a => ?_⟩
      rw [Ideal.Quotient.eq_zero_iff_mem]
      constructor
      · exact hm a
      · intro hat
        by_contra hna
        have hu : IsUnit a := by
          by_contra hnu
          exact hna ((IsLocalRing.mem_maximalIdeal a).2 hnu)
        exact ht (hu.mul_right_eq_zero.1 hat)

    have hP' := IsPullback.of_hasPullback A.hom (spMap σ')
    have hP₀ := IsPullback.of_hasPullback A.hom (spMap σ₀)
    obtain ⟨i', hg', hab', hsm'⟩ := GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' R R' σ' A _ _ _ hP'
    obtain ⟨i₀, hg₀, hab₀, hsm₀⟩ := GlobalTheory.T.exists_grpObj_isGrpPullback_of_isPullback' R R₀ σ₀ A _ _ _ hP₀
    have hstep := GlobalTheory.T.small_extension_primitive_lift R R' R₀ t σ' σ₀ g A _ _ _ _ hg' hg₀ hse hA hg
      (hR' _ g (hab' hA) (hsm' g hg)).2 (hfield R₀ hR₀ _ g (hab₀ hA) (hsm₀ g hg)).2.1

    have hle : RingHom.ker σ' ≤ RingHom.ker σ := by
      rw [hker, Ideal.span_le, Set.singleton_subset_iff, hkerσ]; exact htm
    let τ : R' →+* k := RingHom.liftOfRightInverse σ' (Function.surjInv hσ') (Function.rightInverse_surjInv hσ') ⟨σ, hle⟩
    have hτ : ∀ r, τ (σ' r) = σ r := fun r =>
      RingHom.liftOfRightInverse_comp_apply σ' (Function.surjInv hσ') (Function.rightInverse_surjInv hσ') ⟨σ, hle⟩ r
    have hτs : Function.Surjective τ := fun y => by
      obtain ⟨x, rfl⟩ := hσ y; exact ⟨σ' x, hτ x⟩
    have hcomp : spMap σ = spMap τ ≫ spMap σ' := by
      rw [← spMap_comp_hom]; congr 1; ext r; exact (hτ r).symm
    let ψ' : X₀ ⟶ pullback A.hom (spMap σ') := hP'.lift ψ (s₀ ≫ spMap τ) (by rw [w.w, hcomp, Category.assoc])
    have hψ' : ψ' ≫ pullback.fst A.hom (spMap σ') = ψ := hP'.lift_fst _ _ _
    have w' : IsPullback ψ' s₀ (pullback.snd A.hom (spMap σ')) (spMap τ) := by
      refine IsPullback.of_right ?_ (hP'.lift_snd _ _ _) hP'
      rw [hψ', ← hcomp]; exact w
    have hsurj := (hR' (Over.mk (pullback.snd A.hom (spMap σ'))) g (hab' hA) (hsm' g hg)).1 k τ hτs X₀ s₀ ψ' w'
    intro y
    obtain ⟨x', rfl⟩ := hsurj y
    obtain ⟨a, rfl⟩ := hstep x'
    refine ⟨a, ?_⟩
    exact ((GlobalTheory.T.structureSheafCohomology_pullback_comp_cup_id).1 R R' A.left (pullback A.hom (spMap σ')) A.hom (pullback.snd A.hom (spMap σ'))
      σ' (pullback.fst A.hom (spMap σ')) hg'.1.w k X₀ s₀ τ ψ' w'.w σ ψ w.w hψ'.symm (fun r => (hτ r).symm)).1 a |>.symm
  ·
    have hu : IsUnit t := by
      by_contra hnu
      exact htm ((IsLocalRing.mem_maximalIdeal t).2 hnu)
    have hinj : Function.Injective σ := by
      rw [injective_iff_map_eq_zero]
      intro a ha
      have hma : a ∈ IsLocalRing.maximalIdeal R := by rw [← hkerσ]; exact ha
      exact (hu.mul_left_eq_zero).1 (hm a hma)
    exact GlobalTheory.T.pull_h1_surjective_of_bijective R k σ A.left X₀ A.hom s₀ ψ w ⟨hinj, hσ⟩

end GlobalTheory.AbCoh.SmallStepSurj
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardSqModPrime
section
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem card_sq_mod_prime : ∀ (p : ℕ), p.Prime → p % 4 = 3 →
    2 * Fintype.card (Sq p) + 1 = p ∧ Odd (Fintype.card (Sq p)) := by
  intro p hp h4
  obtain ⟨e, -⟩ := GlobalTheory.T.nonzeroSquares_sum_equiv_Ico_mod_four p hp h4
  have hc := Fintype.card_congr e
  rw [Fintype.card_sum] at hc
  have h2 : Fintype.card (Finset.Ico 1 p : Finset ℕ) = p - 1 := by
    simp
  rw [h2] at hc
  have hp2 := hp.two_le
  have hsum : 2 * Fintype.card (Sq p) + 1 = p := by omega
  refine ⟨hsum, ?_⟩
  rw [Nat.odd_iff]
  omega

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechPicardClassEqZeroOfSquareZeroRetractionStatement
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechPicardClass_eq_zero_of_squareZero_retraction : ∀ {X X' : Scheme.{0}} (i : X ⟶ X') (q : X' ⟶ X), i ≫ q = 𝟙 X → (∀ x, i (q x) = x) → IsUnit (2 : Γ(X', ⊤)) → (∀ (W : X'.Opens) (f g : Γ(X', W)), (i.app W).hom f = 0 → (i.app W).hom g = 0 → f * g = 0) → ∀ (c : GlobalTheory.CechPic.Pic X'), GlobalTheory.CechPic.pull i c = 0 → 2 • c = 0 → c = 0 := by
  first | exact @GlobalTheory.CechPic.eq_zero_of_sqZero_retract | exact GlobalTheory.CechPic.eq_zero_of_sqZero_retract | (intros; apply GlobalTheory.CechPic.eq_zero_of_sqZero_retract <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantEleventh
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.IndexCount

open Formalism.L2.Col.Loc Formalism.L2.Col.LocE GlobalTheory.RowTypeInv GlobalTheory.SymLevelDatum

section

variable {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) (q : ℕ)

theorem sclLat_anti (hq : q ≠ 0) {N : ℕ} {e e' : ℕ → ℤ} (h : ∀ l, e l ≤ e' l) : sclLat P q N e' ≤ sclLat P q N e := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  intro x hx
  rw [mem_sclLat] at hx ⊢
  intro l
  obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (sub_nonneg.2 (h l.1))
  have h1 : IntAt P ((q : E) ^ k) := (intRing P).pow_mem (intAt_natCast P q) k
  convert h1.mul (hx l) using 1
  rw [show e' l.1 = e l.1 + k by omega, zpow_add₀ hq', zpow_natCast]
  field_simp

theorem mem_sclLat_succ (hq : q ≠ 0) {N : ℕ} (e : ℕ → ℤ) (x : Sp E N) :
    x ∈ sclLat P q N (fun l => e l + 1) ↔ (q : E)⁻¹ • x ∈ sclLat P q N e := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  rw [mem_sclLat, mem_sclLat]
  refine forall_congr' fun l => ?_
  rw [zpow_add₀ hq', zpow_one, Pi.smul_apply, smul_eq_mul, mul_inv, mul_assoc]

theorem mem_stabL_of_cong {N : ℕ} {M₀ M M₁ : Submodule (𝓞 E) (Sp E N)} (h₀ : M₀ ≤ M) (h₁ : M ≤ M₁)
    {κ : Sp E N ≃ₗ[E] Sp E N} (hκ : κ ∈ stabL E N M₁) (hc : ∀ y ∈ M₁, κ y - y ∈ M₀) : κ ∈ stabL E N M := by
  intro x
  constructor
  · intro hx
    simpa using M.sub_mem hx (h₀ (hc x ((hκ x).1 (h₁ hx))))
  · intro hx
    simpa using M.add_mem (h₀ (hc x (h₁ hx))) hx

noncomputable def resMat {N : ℕ} (e : ℕ → ℤ) (h : Sp E N ≃ₗ[E] Sp E N) : Fin N × Fin N → 𝓞 E ⧸ P.asIdeal :=
  fun p => redP P (h (eN E N p.2.1) p.1 * (q : E) ^ (e p.2.1 - e p.1.1))

theorem cong_of_resMat_eq (hq : q ≠ 0) (hdiv : ∀ a : E, IntAt P a → redP P a = 0 → IntAt P (a / (q : E)))
    {N : ℕ} {e : ℕ → ℤ} {h h' : Sp E N ≃ₗ[E] Sp E N} (hh : h ∈ stabL E N (sclLat P q N e))
    (hh' : h' ∈ stabL E N (sclLat P q N e)) (hres : resMat P q e h = resMat P q e h') :
    ∀ y ∈ sclLat P q N e, (h⁻¹ * h') y - y ∈ sclLat P q N (fun l => e l + 1) := by
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  have a1 := (maps_iff P q hq e e h.toLinearMap).1 fun y hy => (hh y).2 hy
  have a2 := (maps_iff P q hq e e h'.toLinearMap).1 fun y hy => (hh' y).2 hy
  have a3 := (maps_iff P q hq e (fun l => e l + 1) (h'.toLinearMap - h.toLinearMap)).2 fun l l' => by
    have b1 : IntAt P (h' (eN E N l'.1) l * (q : E) ^ (e l'.1 - e l.1) - h (eN E N l'.1) l * (q : E) ^ (e l'.1 - e l.1)) :=
      (intRing P).sub_mem (a2 l l') (a1 l l')
    have b2 := reduction_add b1 (a1 l l')
    have b3 : redP P (h (eN E N l'.1) l * (q : E) ^ (e l'.1 - e l.1)) =
      redP P (h' (eN E N l'.1) l * (q : E) ^ (e l'.1 - e l.1)) := congrFun hres (l, l')
    erw [sub_add_cancel, b3, right_eq_add] at b2
    convert hdiv _ b1 b2 using 1
    rw [show e l'.1 - (e l.1 + 1) = e l'.1 - e l.1 - 1 by ring, zpow_sub_one₀ hq']
    simp only [LinearMap.sub_apply, Pi.sub_apply, LinearEquiv.coe_coe]
    field_simp
  intro y hy
  have a4 := a3 y hy
  rw [mem_sclLat_succ P q hq] at a4 ⊢
  rw [← hh, map_smul, map_sub]
  simpa using a4

theorem mem_JGsym_of_cong (hq : q ≠ 0) (k rS r t n c : ℕ) {κ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hκ : κ ∈ stabL E (n + c) (lamY P q n c fun i => i + 1))
    (hc : ∀ y ∈ lamY P q n c fun i => i + 1, κ y - y ∈ sclLat P q (n + c) (fun l => scE n (fun i => i + 1) l + 1)) :
    κ ∈ JGsym P q k rS r t n c := by
  have h₀ : ∀ s, sclLat P q (n + c) (fun l => scE n (fun i => i + 1) l + 1) ≤ flagS P q k rS n c s := fun s =>
    sclLat_anti P q hq fun l => by split_ifs <;> omega
  have h₁ : ∀ s, flagS P q k rS n c s ≤ lamY P q n c fun i => i + 1 := fun s =>
    sclLat_anti P q hq fun l => by split_ifs <;> omega
  refine ⟨hκ, fun s _ => mem_stabL_of_cong (h₀ s) (h₁ s) hκ hc, fun s _ => ⟨mem_stabL_of_cong (h₀ s) (h₁ s) hκ hc, h₀ s (hc _ ?_)⟩⟩
  have hq' : (q : E) ≠ 0 := Nat.cast_ne_zero.2 hq
  unfold lamY bvecS bvecG
  rw [mem_sclLat]
  intro i
  by_cases hi : i.1 = fIdx k c n (symIdxInv k rS s)
  · simp only [Pi.smul_apply, eN, hi, if_true, smul_eq_mul, mul_one]
    rw [inv_mul_cancel₀ (zpow_ne_zero _ hq')]
    exact intAt_one P
  · simp only [Pi.smul_apply, eN, hi, if_false, smul_eq_mul, mul_zero]
    exact intAt_zero P

end

theorem card_index_le : ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), Hyp N s W Ch G sel mu cst I dl χ cD pl u δ → ∀ j, j + 2 ≤ N.R.m → (Fintype.card (I.β j) : ℝ) ≤ Real.exp (C * errUnit N (Pr.T u)) := by
  classical
  refine ⟨1, by norm_num, ?_⟩
  intro D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H j hj
  obtain ⟨hvG, -, -, hprod, -⟩ := BadPrimes.bad_primes D N X s Pr W Ch G sel Sg mu cst I dl χ cD pl u δ H
  obtain ⟨⟨-, -, -, -, -, -, hX, -, -, hPr, -, -, hg, -⟩, -, -, -, -, hsh, hI, -⟩ := H
  have hq : ∀ P : HeightOneSpectrum (𝓞 X.E), Formalism.L2.Col.qOf P ≠ 0 := fun P h =>
    P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  have hgg : 0 < Pr.g 0 * Pr.g 1 := Nat.mul_pos (hPr.g_prime 0).pos (hPr.g_prime 1).pos
  have h1 : Fintype.card (I.β j) ≤ (Pr.g 0 * Pr.g 1) ^ (N.R.f * N.Nm ^ 2) := by
    rcases j with _ | i
    · obtain ⟨b, hb⟩ := hI.zero_uniq
      exact (Fintype.card_le_one_iff.2 fun a a' => (hb a).trans (hb a').symm).trans (Nat.one_le_pow _ _ hgg)
    · set n := N.R.N (i + 1) + cOf N.R (i + 1) with hn
      haveI : ∀ P : rowSG Pr sel mu, Finite (𝓞 X.E ⧸ P.1.asIdeal) := fun P => finite_res P.1
      let φ : I.β (i + 1) → ∀ P : rowSG Pr sel mu, Fin n × Fin n → 𝓞 X.E ⧸ P.1.asIdeal := fun b P =>
        resMat P.1 (Formalism.L2.Col.qOf P.1) (scE (N.R.N (i + 1)) fun i => i + 1) (I.h (i + 1) b P)
      have hφ : Function.Injective φ := by
        intro b b' hbb
        refine hI.inj i (by omega) b b' fun P => ?_
        have hP := hvG P.1 P.2
        have s1 := hI.stabG _ b P hP
        have s2 := hI.stabG _ b' P hP
        unfold lamYat at s1 s2
        rw [if_pos hP] at s1 s2
        refine ⟨1, Subgroup.one_mem _, (I.h (i + 1) b P)⁻¹ * I.h (i + 1) b' P, ?_, by group⟩
        unfold Jat
        rw [if_pos hP, hsh, if_pos rfl]
        exact mem_JGsym_of_cong _ _ (hq _) _ _ _ _ _ _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ s1) s2)
          (cong_of_resMat_eq _ _ (hq _) (GlobalTheory.TypePrimeUnif.intAt_div_qOf X Pr hX.ok hPr P.1 hP) s1 s2 (congrFun hbb P))
      have h2 := Nat.card_le_card_of_injective φ hφ
      have h3 : ∀ P : rowSG Pr sel mu, Nat.card (Fin n × Fin n → 𝓞 X.E ⧸ P.1.asIdeal) = Formalism.L2.Col.qOf P.1 ^ (n * n) := fun P => by
        rw [Nat.card_fun, Nat.card_prod, Nat.card_fin]
        rfl
      rw [Nat.card_eq_fintype_card, Nat.card_pi, Finset.prod_congr rfl fun P _ => h3 P, Finset.prod_pow, hprod, ← pow_mul] at h2
      refine h2.trans (Nat.pow_le_pow_right hgg (Nat.mul_le_mul_left _ ?_))
      have h4 : n ≤ N.Nm := by
        rw [hn]
        unfold NumDatum.Nm Ranks.N cOf
        obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (show i + 1 ≤ N.R.m by omega)
        rw [hd]
        have : i + 1 + d - 1 - (i + 1) ≤ d := by omega
        nlinarith [Nat.zero_le (d * N.R.t)]
      rw [sq]
      exact Nat.mul_le_mul h4 h4
  rw [hg 0, hg 1] at h1
  have g0 : (1 : ℝ) ≤ N.g 0 := by rw [← hg 0]; exact_mod_cast (hPr.g_prime 0).one_le
  have g1 : (1 : ℝ) ≤ N.g 1 := by rw [← hg 1]; exact_mod_cast (hPr.g_prime 1).one_le
  have hT : (1 : ℝ) ≤ Pr.T u := by exact_mod_cast (hPr.T_prime u).one_le
  have gg : (1 : ℝ) ≤ (N.g 0 : ℝ) * N.g 1 := one_le_mul_of_one_le_of_one_le g0 g1
  have ggT : (N.g 0 : ℝ) * N.g 1 ≤ (N.g 0 : ℝ) * N.g 1 * Pr.T u := le_mul_of_one_le_right (by linarith) hT
  have he : N.R.f * N.Nm ^ 2 ≤ N.R.f * (N.R.m ^ 2 * N.Nm ^ 2) :=
    Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (Nat.pow_pos (by omega)))
  calc (Fintype.card (I.β j) : ℝ) ≤ ((N.g 0 : ℝ) * N.g 1) ^ (N.R.f * N.Nm ^ 2) := by exact_mod_cast h1
    _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (N.R.f * N.Nm ^ 2) := pow_le_pow_left₀ (by linarith) ggT _
    _ ≤ ((N.g 0 : ℝ) * N.g 1 * Pr.T u) ^ (N.R.f * (N.R.m ^ 2 * N.Nm ^ 2)) := pow_le_pow_right₀ (gg.trans ggT) he
    _ = Real.exp (1 * errUnit N (Pr.T u)) := by
      rw [← Real.exp_log (show 0 < (N.g 0 : ℝ) * N.g 1 * Pr.T u by linarith), ← Real.exp_nat_mul, Real.exp_eq_exp]
      unfold errUnit
      push_cast
      ring

end GlobalTheory.IndexCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantSecondStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_sum_local_constant_second : ∀ (D : D7) (N : NumDatum) (X : Fields) (s : Seam D X) (Pr : Primes X) (W : Wts X Pr.Word N.R) (Ch : Chars X Pr N.R.m) (G : ChGlob X N.R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (Sg : Set ℕ) (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (I : ChIdx X Pr N.R (QE sel (mu : Chr X.F X.E X.K))) (dl : ℂ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (pl : RPl N.R ≃ X.Tau) (u : Pr.Word) (δ : Code N), Hyp N s W Ch G sel mu cst I dl χ cD pl u δ → (∀ P ∈ rowSG Pr sel mu, P ∈ Pr.vGs) ∧ (∀ P ∈ Pr.vGs, ∃ i, P ∈ Pr.vG i ∧ Formalism.L2.Col.qOf P = Pr.g i ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal ∧ ((Pr.g i : ℕ) : 𝓞 X.E) ∉ P.asIdeal ^ 2 ∧ ((Pr.g (1 - i) : ℕ) : 𝓞 X.E) ∉ P.asIdeal ∧ ((Pr.T u : ℕ) : 𝓞 X.E) ∉ P.asIdeal ∧ Pr.piT u ∉ P.asIdeal) ∧ (∀ P ∈ Pr.vT u, ((Pr.T u : ℕ) : 𝓞 X.E) ∈ P.asIdeal) ∧ (∏ P : rowSG Pr sel mu, Formalism.L2.Col.qOf P.1) = (Pr.g 0 * Pr.g 1) ^ N.R.f ∧ Odd (Pr.T u) ∧ (∀ i, Odd (Pr.g i)) ∧ ∀ P ∈ Sall sel mu u, conjPrime₂ P ∉ Sall sel mu u ∧ (2 : 𝓞 X.E) ∉ P.asIdeal := by
  first | exact @GlobalTheory.ColNorms.BadPrimes.bad_primes | exact GlobalTheory.ColNorms.BadPrimes.bad_primes | (intros; apply GlobalTheory.ColNorms.BadPrimes.bad_primes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterSumLocalConstantThird
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder

namespace GlobalTheory.ColNormsUnit

theorem mem_of_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A} (h : P ∈ divs a) :
    a ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · exact hf.mem_toFinset.1 h
  · simp at h

theorem qe_one {X : Fields} (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ} :
    QE sel ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
  have h : Qprime ((1 : Tup X.F X.E X.K Sg) : Chr X.F X.E X.K) = ∅ := by
    change Qprime (1 : Chr X.F X.E X.K) = ∅
    ext v
    simp [Qprime, MonoidHom.ker_one]
  unfold QE
  split_ifs with hf
  · rw [(Set.Finite.toFinset_eq_empty (h := hf)).2 h]
    rfl
  · rfl

theorem exists_prime {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E))
    {Sg : Set ℕ} (u : Pr.Word) (P : HeightOneSpectrum (𝓞 X.E)) (hP : P ∈ Sall sel (1 : Tup X.F X.E X.K Sg) u) :
    ∃ l : ℕ, l.Prime ∧ (l : 𝓞 X.E) ∈ P.asIdeal ∧ ¬ l ∣ Pr.cond := by
  classical
  have hg : ∀ i, P ∈ Pr.vG i → ∃ l : ℕ, l.Prime ∧ (l : 𝓞 X.E) ∈ P.asIdeal ∧ ¬ l ∣ Pr.cond := by
    intro i hi
    refine ⟨Pr.g i, hPr.g_prime i, hPr.piG_norm i ▸ P.asIdeal.mul_mem_left _ (mem_of_divs hi), fun hd => ?_⟩
    have h1 : Pr.g i ≡ 1 [MOD Pr.g i] := (hPr.g_cong i).of_dvd hd
    have h2 : Pr.g i ∣ 1 := (Nat.modEq_zero_iff_dvd).1 (h1.symm.trans ((Nat.modEq_zero_iff_dvd).2 dvd_rfl))
    exact (hPr.g_prime i).one_lt.ne' (Nat.dvd_one.1 h2)
  unfold Sall at hP
  simp only [rowSG, uSG, qe_one, Primes.vGs, Finset.mem_union, Finset.notMem_empty, or_false] at hP
  rcases hP with h | h | h
  · have h0 : Pr.piT u ∈ P.asIdeal := mem_of_divs h
    have hT : (Pr.T u : 𝓞 X.E) ∈ P.asIdeal := hPr.piT_norm u ▸ P.asIdeal.mul_mem_right _ h0
    refine ⟨Pr.T u, hPr.T_prime u, hT, fun hd => ?_⟩
    have h1 : (Pr.T u : 𝓞 X.E) ∣ Pr.piT u - 1 :=
      (Nat.cast_dvd_cast (hd.mul_right _)).trans (hPr.piT_cong u)
    have h2 : Pr.piT u - 1 ∈ P.asIdeal := Ideal.mem_of_dvd _ h1 hT
    have h3 := P.asIdeal.sub_mem h0 h2
    rw [sub_sub_cancel] at h3
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h3)
  · exact hg 0 h
  · exact hg 1 h

end GlobalTheory.ColNormsUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CloseTaylorShiftStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj Filter Topology TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.AnPer GlobalTheory.PeriodFamily
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.close_taylor_shift_alt : ∀ {I : Type} [Fintype I] [DecidableEq I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {F₀ : Fam Empty g Λ} (K : Charts F) (K₀ : Charts F₀) {R : Type} [CommRing R] [Algebra ℂ R] (J : Ideal R) (N : ℕ), (∀ s : Fin (N + 1) → R, (∀ a, s a ∈ J) → ∏ a, s a = 0) → ∀ (r : ℕ) (m : Fin r → I → R), (∀ j i, m j i ∈ J) → (∀ j i i', m j i * m j i' = 0) → (∀ l z, F₀.τ l z = F.τ l 0) → ∀ (l : Λ) (k k' : K.K) (k₀ k₀' : K₀.K) (h : K.le l k' k) (h₀ : K₀.le l k₀' k₀), (∀ p ∈ K₀.W k₀', (((0 : I → ℂ), p.2) : Tot I g) ∈ K.W k') → ∀ (ρ : Hol (K.W k) →+* R ⊗[ℂ] Hol (K₀.W k₀)) (ρ' : Hol (K.W k') →+* R ⊗[ℂ] Hol (K₀.W k₀')), IsTay N (fun i ↦ ∑ j, m j i) ρ → IsTay N (fun i ↦ ∑ j, m j i) ρ' → Close (J.map (Algebra.TensorProduct.includeLeft : R →ₐ[ℂ] R ⊗[ℂ] Hol (K₀.W k₀'))) (ρ'.comp (Charts.sh h)) ((Algebra.TensorProduct.map (AlgHom.id ℂ R) (Charts.shA h₀)).toRingHom.comp ρ) := by
  first | exact @GlobalTheory.AnPer.close_taylor_shift | exact GlobalTheory.AnPer.close_taylor_shift | (intros; apply GlobalTheory.AnPer.close_taylor_shift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubfunctorStalkIdealCriterionStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.AbLaw GlobalTheory.CatCoh GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_subfunctor_stalk_ideal_criterion : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (H : Over (Sp K)) [GrpObj H] (j : H ⟶ A), IsMonHom j → IsClosedImmersion j.left → IsFinite H.hom → ∀ x₀ : A.left, x₀ ∈ Set.range (η[A]).left.base → ∀ J : Ideal (A.left.presheaf.stalk x₀), (∀ (R' : Type) [CommRing R'] (ψ : A.left.presheaf.stalk x₀ →+* R'), (∃ y : Sp R' ⟶ H.left, y ≫ j.left = Spec.map (CommRingCat.ofHom ψ) ≫ A.left.fromSpecStalk x₀) ↔ J ≤ RingHom.ker ψ) → J ≠ ⊤ ∧ IsArtinianRing (A.left.presheaf.stalk x₀ ⧸ J) := by
  first | exact @GlobalTheory.FinStalk.stalk_quotient_ne_top_and_isArtinianRing | exact GlobalTheory.FinStalk.stalk_quotient_ne_top_and_isArtinianRing | (intros; apply GlobalTheory.FinStalk.stalk_quotient_ne_top_and_isArtinianRing <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CobOneEvDefectDvd
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup

namespace GlobalTheory.QLog

theorem cobOne_ev_defect_dvd : ∀ (p : ℕ) [Fact p.Prime] (O E : Type) [CommRing O] [CommRing E] [Algebra O E], IsFrame p E (RingHom.id O) → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), ∀ (f : MvPowerSeries (Fin d) E), QL c.μ ⊤ f → ∀ (n : ℕ) (s : MvPowerSeries (Fin d) O), map (algebraMap O E) s = defect c.μ (p ^ n) f → ∃ z, cobOne O (G.A n) (c.ev n s) = (p : O) ^ n • z := by
  intro p _ O E _ _ _ hF G d c f hf n s hs
  haveI : IsAdicComplete (Ideal.span {(p : O)}) O := hF.complete
  obtain ⟨hf0, -, hfc⟩ := hf
  obtain ⟨κ, -, hκ⟩ := ((series_in_ideal_iff_image O E (Fin d ⊕ Fin d) ⊤ _).1).1 hfc
  obtain ⟨-, hκ0, hrest⟩ := GlobalTheory.T.integral_coboundary_representative_cocycle_rules O E d c.μ c.isLaw hF.inj f κ hκ
  have hcob := (hrest (p ^ n) s hs).1
  refine ⟨c.ev₂ n κ, ?_⟩
  rw [← (GlobalTheory.T.formalChart_evalSquare_properties p O G d c n s).2.2.2, hcob, map_sub, map_smul,
    (GlobalTheory.T.ev_subst_natMultiple_prime_pow_constant p O G d c n).2.1 κ, hκ0 hf0, map_zero, sub_zero, Nat.cast_pow]

end GlobalTheory.QLog
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyFieldAddEquivGaloisStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_cohomology_addEquiv_galois_cohomology : ∀ (R : Type) [CommRing R] (F : Shv R), Finitary F → ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (M : Rep.{0} R (Ω ≃ₐ[K] Ω)) [GroundTheory.ProfCoh.IsDiscreteRep M] (e : M ≃+ Sec F (Spec (CommRingCat.of Ω))), (∀ (σ : Ω ≃ₐ[K] Ω) (m : M), e (M.ρ σ m) = Sec.res (Spec.map (CommRingCat.ofHom (σ : Ω →+* Ω))) (e m)) → ∀ n : ℕ, Nonempty (H R (sp K) F n ≃+ GroundTheory.ProfCoh.cohomology M n) := by
  first
  | exact @GlobalTheory.EtC.GalFld.cohomology_field_addEquiv_galois
  | exact GlobalTheory.EtC.GalFld.cohomology_field_addEquiv_galois
  | (intros; apply GlobalTheory.EtC.GalFld.cohomology_field_addEquiv_galois <;> assumption)
end

