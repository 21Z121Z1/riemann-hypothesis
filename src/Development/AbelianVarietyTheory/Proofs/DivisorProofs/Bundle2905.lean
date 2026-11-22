import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2804
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0084
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2761
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2624
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniformBaseChange.PullGt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonHomExtensionOpenPartField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0691
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0714
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2845
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2859
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2851
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2805
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2749
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultiplicationPullbackIntegralFamilyOdd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0083
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2427
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.Bundle0013
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0088
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2838
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LocGenOfThickenings
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLogCanonicalMultipleOfGloballyKltStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_logCanonicalMultiple_of_globally_klt : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p →
  topologicalKrullDim X = n → ∀ Δ : X → ℚ, IsEffQDiv Δ → (∀ y, KltAt p n Δ y) →
  ∃ (m : ℕ) (G : CartierDiv X), 0 < m ∧ IsLogCanonicalMultiple p n Δ m G := by
  first | exact @GlobalTheory.Discrepancy.exists_isLogCanonicalMultiple_of_kltAt | exact GlobalTheory.Discrepancy.exists_isLogCanonicalMultiple_of_kltAt | (intros; apply GlobalTheory.Discrepancy.exists_isLogCanonicalMultiple_of_kltAt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMatrixUnitsExtendNormalNoetherian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.SiegTh Classical
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EighthPowerUnits

section Rel

variable {S' S : Scheme.{0}} {j : S' ⟶ S} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G]
  {φ : G'.left ⟶ G.left}

theorem one_left_comp (hφ : IsGrpPullback G' G j φ) :
    (1 : G' ⟶ G').left ≫ φ = φ ≫ (1 : G ⟶ G).left := by
  let φ₀ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ hφ.1.w
  let z : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk ((1 : G' ⟶ G').left ≫ φ)
    (by rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w]; rfl)
  have h := hφ.2 G' 1 1 z z rfl rfl
  rw [_root_.mul_one] at h
  have hz : z = 1 := mul_eq_left.1 (Over.OverMorphism.ext h)
  have h1 : φ₀ ≫ (1 : G ⟶ G) = 1 := MonObj.comp_one _
  have h2 : z.left = (φ₀ ≫ (1 : G ⟶ G)).left := congrArg (fun w => w.left) (hz.trans h1.symm)
  rw [Over.comp_left] at h2
  exact h2

theorem mul_left_comp (hφ : IsGrpPullback G' G j φ) {e₁ e₂ : G' ⟶ G'} {F₁ F₂ : G ⟶ G}
    (h₁ : e₁.left ≫ φ = φ ≫ F₁.left) (h₂ : e₂.left ≫ φ = φ ≫ F₂.left) :
    (e₁ * e₂).left ≫ φ = φ ≫ (F₁ * F₂).left := by
  let φ₀ : Over.mk (G'.hom ≫ j) ⟶ G := Over.homMk φ hφ.1.w
  have h := hφ.2 G' e₁ e₂ (φ₀ ≫ F₁) (φ₀ ≫ F₂) h₁.symm h₂.symm
  rw [← MonObj.comp_mul] at h
  exact h.symm

theorem comp_left_comp {e₁ e₂ : G' ⟶ G'} {F₁ F₂ : G ⟶ G}
    (h₁ : e₁.left ≫ φ = φ ≫ F₁.left) (h₂ : e₂.left ≫ φ = φ ≫ F₂.left) :
    (e₁ ≫ e₂).left ≫ φ = φ ≫ (F₁ ≫ F₂).left := by
  rw [Over.comp_left, Over.comp_left, Category.assoc, h₂, ← Category.assoc, h₁, Category.assoc]

end Rel

theorem exists_matrixUnits_extend : ∀ {S B : Scheme.{0}} [AlgebraicGeometry.IsNoetherian S] (hS : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme S) (U₀ : S.Opens) (hU : Dense (U₀ : Set S)) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (G' : Over U₀.toScheme) [GrpObj G'] (P : Over B) [GrpObj P] [IsCommMonObj P] (f : U₀.toScheme ⟶ B) (φ : G'.left ⟶ G.left) (ψ : G'.left ⟶ P.left) (hφ : IsGrpPullback G' G U₀.ι φ) (hψ : IsGrpPullback G' P f ψ) (E' : Fin 8 → Fin 8 → (P ⟶ P)) (hE' : ∀ a b, IsMonHom (E' a b)) (hrel : ∀ a b c d, E' a b ≫ E' c d = if b = c then E' a d else 1) (hsum : ∏ a, E' a a = 𝟙 P), ∃ E : Fin 8 → Fin 8 → (G ⟶ G), (∀ a b, IsMonHom (E a b)) ∧ (∀ a b c d, E a b ≫ E c d = if b = c then E a d else 1) ∧ ∏ a, E a a = 𝟙 G ∧ ∀ a b, ∃ e : G' ⟶ G', IsMonHom e ∧ e.left ≫ φ = φ ≫ (E a b).left ∧ e.left ≫ ψ = ψ ≫ (E' a b).left := by
  intro S B _ hS U₀ hU G _ _ hG G' _ P _ _ f φ ψ hφ hψ E' hE' hrel hsum
  have : IsDominant U₀.ι := AlgebraicGeometry.Opens.isDominant_ι hU
  obtain ⟨_, _⟩ := GlobalTheory.Published.SemiAbelianHomExtension.quasiCompact_and_dominant hS U₀.ι
  obtain ⟨_, _⟩ := GlobalTheory.ExtUnique.flat_and_isSeparated_of_isSemiAbelian G hG
  let e : Fin 8 → Fin 8 → (G' ⟶ G') := fun a b =>
    Over.homMk (hψ.1.lift (ψ ≫ (E' a b).left) G'.hom (by rw [Category.assoc, Over.w, hψ.1.w]))
      (hψ.1.lift_snd _ _ _)
  have he : ∀ a b, (e a b).left ≫ ψ = ψ ≫ (E' a b).left := fun a b => hψ.1.lift_fst _ _ _
  have heM : ∀ a b, IsMonHom (e a b) := fun a b => by
    haveI := hE' a b
    exact ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.isMonHom_of_grpPullback hψ hψ (E' a b) (e a b) (he a b)
  have uq : ∀ {x y : G' ⟶ G'} {F : P ⟶ P}, x.left ≫ ψ = ψ ≫ F.left → y.left ≫ ψ = ψ ≫ F.left → x = y :=
    fun hx hy => Over.OverMorphism.ext (hψ.1.hom_ext (hx.trans hy.symm) ((Over.w _).trans (Over.w _).symm))
  have uG : ∀ {F₁ F₂ : G ⟶ G}, φ ≫ F₁.left = φ ≫ F₂.left → F₁ = F₂ :=
    fun h => GlobalTheory.ExtUnique.over_hom_ext_of_isPullback hφ.1 h
  have ext : ∀ a b, ∃ F : G ⟶ G, IsMonHom F ∧ (e a b).left ≫ φ = φ ≫ F.left := fun a b => by
    haveI := heM a b
    exact (GlobalTheory.Published.SemiAbelianHomExtension.of_isGrpPullback GlobalTheory.semiAbelianHomExtension_holds hS hG hG hφ hφ
      (e a b)).exists
  choose E hE using ext
  refine ⟨E, fun a b => (hE a b).1, ?_, ?_, fun a b => ⟨e a b, heM a b, (hE a b).2, he a b⟩⟩
  · intro a b c d
    apply uG
    by_cases hbc : b = c
    · subst hbc
      rw [if_pos rfl]
      have h1 := comp_left_comp (he a b) (he b d)
      rw [hrel, if_pos rfl] at h1
      have h2 : e a b ≫ e b d = e a d := uq h1 (he a d)
      rw [← comp_left_comp (hE a b).2 (hE b d).2, h2, (hE a d).2]
    · rw [if_neg hbc]
      have h1 := comp_left_comp (he a b) (he c d)
      rw [hrel, if_neg hbc] at h1
      have h2 : e a b ≫ e c d = 1 := uq h1 (one_left_comp hψ)
      rw [← comp_left_comp (hE a b).2 (hE c d).2, h2, one_left_comp hφ]
  · have key : ∀ s : Finset (Fin 8), ∃ x : G' ⟶ G', x.left ≫ φ = φ ≫ (∏ a ∈ s, E a a).left ∧
        x.left ≫ ψ = ψ ≫ (∏ a ∈ s, E' a a).left := by
      intro s
      refine Finset.induction_on s ?_ ?_
      · refine ⟨1, ?_, ?_⟩
        · rw [Finset.prod_empty]; exact one_left_comp hφ
        · rw [Finset.prod_empty]; exact one_left_comp hψ
      · intro a s ha ih
        obtain ⟨x, h1, h2⟩ := ih
        refine ⟨e a a * x, ?_, ?_⟩
        · rw [Finset.prod_insert ha]; exact mul_left_comp hφ (hE a a).2 h1
        · rw [Finset.prod_insert ha]; exact mul_left_comp hψ (he a a) h2
    obtain ⟨x, h1, h2⟩ := key Finset.univ
    rw [hsum] at h2
    have hx : x = 𝟙 G' := uq h2 (by simp)
    apply uG
    rw [← h1, hx]
    simp

end GlobalTheory.EighthPowerUnits
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonHomExtensionOpenPartFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monHom_extension_openPart_field : ∀ (K : Type) [Field K] (H G V : Over (Sp K)) [GrpObj H] [GrpObj G], GlobalTheory.SS.SmConn H → GlobalTheory.SS.SmConn G → ∀ (j : V ⟶ H) (f : V ⟶ G), IsOpenImmersion j.left → Nonempty V.left → (∀ (Z : Over (Sp K)) (u₁ u₂ u₃ : Z ⟶ V), (u₁ ≫ j) * (u₂ ≫ j) = u₃ ≫ j → (u₁ ≫ f) * (u₂ ≫ f) = u₃ ≫ f) → ∃ F : H ⟶ G, IsMonHom F ∧ j ≫ F = f := by
  first | exact @GlobalTheory.GenericHomField.exists_monHom_extension_of_field | exact GlobalTheory.GenericHomField.exists_monHom_extension_of_field | (intros; apply GlobalTheory.GenericHomField.exists_monHom_extension_of_field <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMonomialTrivialisationSqrtRefinedPolarised
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MonoTriv

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues Formalism.L2.Pj

theorem psiCoord_zero {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegPre R) (hB : D.TauBimult)
    (x : (FractionRing R)ˣ) (hx : IsPsiCoord D 0 x) :
    ∃ u : Rˣ, (x : FractionRing R) = algebraMap R (FractionRing R) u := by
  obtain ⟨j, hj⟩ := PsiCoordLocal.exists_chart_top D 0
  have h := PsiCoordLocal.generic_le D 0 j hj
  have hU := PsiCoordLocal.psiUnitOn_zero D hB
  obtain ⟨s, -, e⟩ := hU j ⊤ (isAffineOpen_top _) (Set.subset_univ _) hj h
  obtain ⟨r, rfl⟩ := PsiCoordLocal.toOpen_top_bijective.2 s
  have hr : PsiCoord D 0 r := ⟨j, hj, h, e⟩
  have hu : IsUnit r := IsLocalRing.notMem_maximalIdeal.1
    (PsiCoordLocal.not_mem_of_coord (𝔭 := closedPoint R) isOpen_univ trivial hU hr)
  obtain ⟨x₀, hx₀, e₀⟩ := (GlobalTheory.PeriodFormCompare.psiCoord_iff D 0 r).1 hr
  obtain ⟨v, hv⟩ := IsPsiCoord.unique hx hx₀
  refine ⟨v * hu.unit, ?_⟩
  rw [hv, Units.val_mul, e₀, Units.val_mul, IsUnit.unit_spec, map_mul]
  rfl

theorem exists_unit_of_sq {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (g : FractionRing R) (w : Rˣ)
    (h : g ^ 2 = algebraMap R (FractionRing R) w) : ∃ a : Rˣ, g = algebraMap R (FractionRing R) a := by
  have hw : algebraMap R (FractionRing R) (w : R) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 w.ne_zero
  have hg : g ≠ 0 := by rintro rfl; exact hw (by rw [← h]; ring)
  have int : ∀ (g : FractionRing R) (w : Rˣ), g ^ 2 = algebraMap R (FractionRing R) w →
      ∃ a : R, algebraMap R (FractionRing R) a = g := fun g w h => by
    refine IsIntegrallyClosed.isIntegral_iff.1 ⟨Polynomial.X ^ 2 - Polynomial.C (w : R),
      Polynomial.monic_X_pow_sub_C _ two_ne_zero, ?_⟩
    simp [h]
  obtain ⟨a, ha⟩ := int g w h
  obtain ⟨b, hb⟩ := int g⁻¹ w⁻¹ (by
    rw [inv_pow, h]
    exact inv_eq_of_mul_eq_one_right (by rw [← map_mul, Units.mul_inv, map_one]))
  have hab : a * b = 1 := IsFractionRing.injective R (FractionRing R) (by
    rw [map_mul, ha, hb, mul_inv_cancel₀ hg, map_one])
  exact ⟨⟨a, b, hab, by rw [mul_comm, hab]⟩, ha.symm⟩

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) [IsLocalRing R'] (m : ℕ) (t : Fin m → R) (r : Fin m → R') (δ : Fin m → LinearMap.BilinForm ℤ Q.X), IsCN R' → Function.Injective ρ → Half Q ρ D e (fun _ _ => 1) → D.PsiEven → D.TauBimult → Q.IsMonomialTau t δ → (∀ i y, 0 ≤ δ i y y) → (∀ i, t i ≠ 0) → (∀ i, r i ^ 2 = ρ (t i)) → IsMonomial D r fun i => (2 : ℤ) • pull e.toIntLinearEquiv.toLinearMap (δ i) := by
  intro R _ _ R' _ _ Q ρ D e _ m t r δ hCN hρ hH hE hB hQ hδ ht hr y
  haveI : IsIntegrallyClosed R' := hCN.2.1
  set n : Fin m → ℕ := fun i => (δ i (e y) (e y)).toNat with hn_def
  have hn : ∀ i, δ i (e y) (e y) = n i := fun i => (Int.toNat_of_nonneg (hδ i (e y))).symm
  obtain ⟨x, hx⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord R' D y (-y)
  obtain ⟨k, hk, hkc⟩ := hQ (e y) (e (-y))
  obtain ⟨u₁, hu₁⟩ := GlobalTheory.T.refining_degenerationData_tauCoordinate_unit R R' Q ρ D e hρ hH.refines y (-y) k hkc x hx
  have h0 : IsPsiCoord D (y + -y) (psiCoord D 0) := by rw [add_neg_cancel]; exact psiCoord_spec D 0
  obtain ⟨u₂, hu₂⟩ := GlobalTheory.T.tauCoordinate_eq_unit_mul_psi_quotient R' D y (-y) x _ _ _ hx h0 (psiCoord_spec D y) (psiCoord_spec D (-y))
  obtain ⟨u₃, hu₃⟩ := GlobalTheory.T.psiEven_coordinates_neg_differ_by_unit R' D hE y _ _ (psiCoord_spec D y) (psiCoord_spec D (-y))
  obtain ⟨u₄, hu₄⟩ := psiCoord_zero D hB _ (psiCoord_spec D 0)
  set X : FractionRing R' := (psiCoord D y : FractionRing R') with hX
  have hX0 : X ≠ 0 := (psiCoord D y).ne_zero
  have hσ : ∀ s, IsFractionRing.lift (A := R) (K := FractionRing R)
      (g := (algebraMap R' (FractionRing R')).comp ρ) ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (algebraMap R (FractionRing R) s) =
      algebraMap R' (FractionRing R') (ρ s) := fun s => IsFractionRing.lift_algebraMap _ s
  have hneg : ∀ i, δ i (e y) (e (-y)) = -(n i : ℤ) := fun i => by
    rw [map_neg, map_neg, hn]
  have hr0 : ∀ i, algebraMap R' (FractionRing R') (r i) ≠ 0 := fun i h => by
    have : algebraMap R' (FractionRing R') (ρ (t i)) = 0 := by rw [← hr i, map_pow, h, zero_pow two_ne_zero]
    exact ht i (hρ ((IsFractionRing.injective R' (FractionRing R')) (by rw [this, map_zero, map_zero])))
  set P : FractionRing R' := ∏ i, algebraMap R' (FractionRing R') (r i) ^ n i with hP
  have hP0 : P ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hr0 i)
  have hk' : IsFractionRing.lift (A := R) (K := FractionRing R)
      (g := (algebraMap R' (FractionRing R')).comp ρ) ((IsFractionRing.injective R' (FractionRing R')).comp hρ) (k : FractionRing R) = (P ^ 2)⁻¹ := by
    rw [hk, map_prod, hP, ← Finset.prod_pow, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_zpow₀, hσ, hneg, ← hr i, map_pow, zpow_neg, zpow_natCast, ← pow_mul, ← pow_mul, mul_comm]
  rw [hk'] at hu₁
  rw [hu₄, hu₃] at hu₂
  have hsq : (X / P) ^ 2 = algebraMap R' (FractionRing R') (u₂ * u₄ * u₃⁻¹ * u₁⁻¹ : R'ˣ) := by
    have h1 := hu₁.symm.trans hu₂
    have hu : ∀ u : R'ˣ, algebraMap R' (FractionRing R') (u : R') ≠ 0 := fun u =>
      (map_ne_zero_iff _ (IsFractionRing.injective R' (FractionRing R'))).2 u.ne_zero
    simp only [Units.val_mul, map_mul, map_units_inv]
    have := hu u₁; have := hu u₂; have := hu u₃; have := hu u₄
    have h1' : algebraMap R' (FractionRing R') (u₁ : R') = algebraMap R' (FractionRing R') (u₂ : R') *
        algebraMap R' (FractionRing R') (u₄ : R') * X⁻¹ * (algebraMap R' (FractionRing R') (u₃ : R') * X)⁻¹ * P ^ 2 := by
      rw [← h1, inv_mul_cancel_right₀ (pow_ne_zero 2 hP0)]
    rw [h1']
    field_simp
  obtain ⟨a, ha⟩ := exists_unit_of_sq (X / P) _ hsq
  have hcoord : PsiCoord D y (a * ∏ i, r i ^ n i) := (GlobalTheory.PeriodFormCompare.psiCoord_iff D y _).2
    ⟨psiCoord D y, psiCoord_spec D y, by
      rw [map_mul, map_prod, ← ha]; simp only [map_pow]; rw [← hP, div_mul_cancel₀ _ hP0]⟩
  refine ⟨a, n, fun i => ?_, hcoord⟩
  simp [pull, hn]

end GlobalTheory.MonoTriv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismOfSectionRatiosVeryAmpleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_morphism_of_sectionRatios_veryAmple : ∀ (K : Type) [Field K] (A : Over (Sp K)) [IsIntegral A.left] (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (π : A.left ⟶ X) (k k' m : ℕ) (σ : Fin (m + 1) → H0 L k), VeryAmpleAlong A.hom π L σ → ∀ (s₀ : H0 L k) (t₀ : H0 L k') (t : Fin (m + 1) → H0 L k'), (∃ a : A.left, π a ∈ nonzeroLocus t₀) → ∀ (Y : Over (Sp K)) (x y : Y ⟶ A), IsDominant x.left → (∀ i, SecRatioEq L (y.left ≫ π) (x.left ≫ π) (σ i) s₀ (t i) t₀) → ∃ (V : Over (Sp K)) (j f : V ⟶ A), IsOpenImmersion j.left ∧ Nonempty V.left ∧ ∀ (Z : Over (Sp K)) (u : Z ⟶ V) (z : Z ⟶ A), (∀ i, SecRatioEq L (z.left ≫ π) ((u ≫ j).left ≫ π) (σ i) s₀ (t i) t₀) → u ≫ f = z := by
  first | exact @GlobalTheory.Mum.exists_morphism_of_secRatio | exact GlobalTheory.Mum.exists_morphism_of_secRatio | (intros; apply GlobalTheory.Mum.exists_morphism_of_secRatio <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultiplicationPullbackGenericSectionCoverStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiplicationPullback_genericSection_cover : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (m : ℕ), Odd m → ∀ θ₀ : SecK C.P.L.L C.α 1, ∃ S : SecK C.P.L.L C.α (m ^ 2), MulSecK C m θ₀ S := by
  first | exact @GlobalTheory.Mum.exists_mulSecK | exact GlobalTheory.Mum.exists_mulSecK | (intros; apply GlobalTheory.Mum.exists_mulSecK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMultiplicationPullbackIntegralFamilyOddStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_multiplicationPullback_integralFamily_odd : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (m : ℕ), Odd m → ∀ F₁ : IntFam (maximalIdeal R) D.toPre 1, ∃ G : IntFam (maximalIdeal R) D.toPre (m ^ 2), MulFam m F₁ G := by
  first | exact @GlobalTheory.Mum.exists_intFam_mul | exact GlobalTheory.Mum.exists_intFam_mul | (intros; apply GlobalTheory.Mum.exists_intFam_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoCompCartesianHomValues
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HalfBC GlobalTheory.PrimCocycle

namespace GlobalTheory.TautPull

theorem lamIso_comp_exists : ∀ {S S' S₁ : Scheme.{0}} {B : Over S₁} {G : Over S} {G' : Over S'} [GrpObj B] [IsCommMonObj B] [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] {M : LB B.left} {L : LB G.left} {L' : LB G'.left} {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f φ) {β₂ : (G2 G).left ⟶ (G2 B).left}, M.IsLB → L.IsLB → L'.IsLB → ∀ (w : LB.Iso (abelian₂ G L) ((abelian₂ B M).pull β₂)) (v : LB.Iso L' (L.pull φ)), w.IsGen → v.IsGen → ∃ w'' : LB.Iso (abelian₂ G' L') ((abelian₂ B M).pull (sqOf gp ≫ β₂)), w''.IsGen ∧ ∀ (Z : Scheme.{0}) (p : Z ⟶ (G2 G').left) (z : Z) (J : (Z ⟶ B.left) → M.ι) (J₁ : (Z ⟶ G.left) → L.ι) (J' : (Z ⟶ G'.left) → L'.ι), Good M z J → Good L z J₁ → Good L' z J' → lamVal w'' p z J J' = lamVal w (p ≫ sqOf gp) z J J₁ * ∏ I, gw v (p ≫ lamφ G' I) z (J₁ ((p ≫ lamφ G' I) ≫ φ)) (J' (p ≫ lamφ G' I)) ^ lamε I := by
  intro S S' S₁ B G G' _ _ _ _ _ _ M L L' f φ gp β₂ hM hL hL' w v hw hv
  have hΛB : (abelian₂ B M).IsLB := DVR.linComb_isLB _ hM _ _
  have hΛ : (abelian₂ G L).IsLB := DVR.linComb_isLB _ hL _ _
  have hΛ' : (abelian₂ G' L').IsLB := DVR.linComb_isLB _ hL' _ _
  obtain ⟨w'', T⟩ := exists_comp hΛ w (lamIso gp v) ((isGen_iff _).1 hw)
    (pgen_lamIso gp v ((isGen_iff v).1 hv)) hΛB hΛ'
  refine ⟨w'', (isGen_iff _).2 (T.pgen_comp hΛ ((isGen_iff _).1 hw)
    (pgen_lamIso gp v ((isGen_iff v).1 hv))), ?_⟩
  intro Z p z J J₁ J' hJ hJ₁ hJ'
  have t := T Z p z (fun I => J (p ≫ (sqOf gp ≫ β₂) ≫ lamφ B I))
    (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ G I)) (fun I => J' (p ≫ lamφ G' I))
    (Set.mem_iInter.2 fun I => hJ (p ≫ (sqOf gp ≫ β₂) ≫ lamφ B I))
    (Set.mem_iInter.2 fun I => hJ₁ ((p ≫ sqOf gp) ≫ lamφ G I))
    (Set.mem_iInter.2 fun I => hJ' (p ≫ lamφ G' I))
  refine t.trans (congrArg₂ (· * ·) ?_ ?_)
  · show _ = gw w (p ≫ sqOf gp) z (fun I => J ((p ≫ sqOf gp) ≫ β₂ ≫ lamφ B I))
      (fun I => J₁ ((p ≫ sqOf gp) ≫ lamφ G I))
    simp only [Category.assoc]
  · rw [gw_lamIso gp v p z _ _ (fun I => by
      have := hJ₁ ((p ≫ sqOf gp) ≫ lamφ G I)
      rw [Category.assoc, sqOf_lamφ, ← Category.assoc] at this ⊢
      exact this) (fun I => hJ' (p ≫ lamφ G' I))]
    refine Finset.prod_congr rfl fun I _ => ?_
    rw [Category.assoc, sqOf_lamφ, ← Category.assoc]

end GlobalTheory.TautPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoTwoHomNormalisedAtOriginStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mumfordBundleIso_twoHom_normalisedAtOrigin : ∀ {S : Scheme.{0}} (B₀ B : Over S) [GrpObj B₀] [IsCommMonObj B₀] [GrpObj B] [IsCommMonObj B] (M₀ : LB B₀.left) (M : LB B.left), M₀.IsLB → M.IsLB → ∀ (a b : B₀ ⟶ B) [IsMonHom a] [IsMonHom b], LBIso (abelian₂ B₀ M₀) ((abelian₂ B M).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left) → ∃ w : LB.Iso (abelian₂ B₀ M₀) ((abelian₂ B M).pull (lift (fst B₀ B₀ ≫ a) (snd B₀ B₀ ≫ b) : G2 B₀ ⟶ G2 B).left), w.IsGen ∧ ∀ (T : Over S) (z : T.left) (J : (T.left ⟶ B.left) → M.ι) (J' : (T.left ⟶ B₀.left) → M₀.ι), Good M z J → Good M₀ z J' → GlobalTheory.PolDeg.lamVal w (lift (1 : T ⟶ B₀) (1 : T ⟶ B₀)).left z J J' = 1 := by
  first | exact @GlobalTheory.Mum.Two.exists_lamVal_origin_two | exact GlobalTheory.Mum.Two.exists_lamVal_origin_two | (intros; apply GlobalTheory.Mum.Two.exists_lamVal_origin_two <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordGeneratorAbelianPartAtLevelImports
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.EndRosati

namespace GlobalTheory.HomMum

variable {S : Scheme.{0}}

theorem mφ_comp {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂] (a b : H₁ ⟶ H₂)
    {T : Over S} (x y : T ⟶ H₁) (k : MK) :
    (lift x y).left ≫ mφ H₁ H₂ a b k =
      Sum.elim (fun I : ULift.{0} (Finset (Fin 2)) => (psum H₂ ![x ≫ a, y ≫ b] I.down).left ≫ coprod.inr)
        (fun I : ULift.{0} (Finset (Fin 2)) => (psum H₁ ![x, y] I.down).left ≫ coprod.inl) k := by
  rcases k with I | I
  · have e : lift x y ≫ lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b) ≫ psum H₂ (x2 H₂) I.down =
        psum H₂ ![x ≫ a, y ≫ b] I.down := by
      rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Geo.Tor.comp_psum]
      congr 1
      funext i
      fin_cases i <;> simp [x2]
    show (lift x y).left ≫ (lift (fst H₁ H₁ ≫ a) (snd H₁ H₁ ≫ b)).left ≫ (psum H₂ (x2 H₂) I.down).left ≫ coprod.inr =
      (psum H₂ ![x ≫ a, y ≫ b] I.down).left ≫ coprod.inr
    rw [← e]
    simp only [Over.comp_left, Category.assoc]
  · have e : lift x y ≫ psum H₁ (x2 H₁) I.down = psum H₁ ![x, y] I.down := by
      rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.comp_psum]
      congr 1
      funext i
      fin_cases i <;> simp [x2]
    show (lift x y).left ≫ (psum H₁ (x2 H₁) I.down).left ≫ coprod.inl = (psum H₁ ![x, y] I.down).left ≫ coprod.inl
    rw [← e]
    simp only [Over.comp_left, Category.assoc]

theorem mφ_push {S' : Scheme.{0}} {j : S' ⟶ S} {E₁ E₂ : Over S'} [GrpObj E₁] [IsCommMonObj E₁] [GrpObj E₂]
    [IsCommMonObj E₂] {A₁ A₂ : Over S} [GrpObj A₁] [IsCommMonObj A₁] [GrpObj A₂] [IsCommMonObj A₂]
    (p₁ : (Over.map j).obj E₁ ⟶ A₁) (p₂ : (Over.map j).obj E₂ ⟶ A₂)
    (hm₁ : ∀ {T : Over S'} (x y : T ⟶ E₁), push p₁ (x * y) = push p₁ x * push p₁ y)
    (hm₂ : ∀ {T : Over S'} (x y : T ⟶ E₂), push p₂ (x * y) = push p₂ x * push p₂ y)
    {a' b' : E₁ ⟶ E₂} {a b : A₁ ⟶ A₂} (ha : push p₂ a' = p₁ ≫ a) (hb : push p₂ b' = p₁ ≫ b)
    {T : Over S'} (x y : T ⟶ E₁) (k : MK) :
    (lift (push p₁ x) (push p₁ y)).left ≫ mφ A₁ A₂ a b k =
      (lift x y).left ≫ mφ E₁ E₂ a' b' k ≫ coprod.map p₁.left p₂.left := by
  let ρ₁ : (T ⟶ E₁) →* ((Over.map j).obj T ⟶ A₁) :=
    MonoidHom.mk' (push p₁) fun x y => hm₁ x y
  let ρ₂ : (T ⟶ E₂) →* ((Over.map j).obj T ⟶ A₂) :=
    MonoidHom.mk' (push p₂) fun x y => hm₂ x y
  have pa : ∀ (z : T ⟶ E₁) {c' : E₁ ⟶ E₂} {c : A₁ ⟶ A₂}, push p₂ c' = p₁ ≫ c → push p₂ (z ≫ c') = push p₁ z ≫ c :=
    fun z c' c h => by
      simp only [push, Functor.map_comp, Category.assoc] at h ⊢
      rw [h]
  rw [← Category.assoc, mφ_comp, mφ_comp]
  rcases k with I | I
  · have e := ReciprocityTheory.ChartRestriction.G.Geo.Tor.psum_hom ρ₂ ![x ≫ a', y ≫ b'] I.down
    have e' : (fun i => ρ₂ ((![x ≫ a', y ≫ b'] : Fin 2 → (T ⟶ E₂)) i)) = ![push p₁ x ≫ a, push p₁ y ≫ b] := by
      funext i
      fin_cases i
      · exact pa x ha
      · exact pa y hb
    rw [e'] at e
    show (psum A₂ ![push p₁ x ≫ a, push p₁ y ≫ b] I.down).left ≫ coprod.inr =
      ((psum E₂ ![x ≫ a', y ≫ b'] I.down).left ≫ coprod.inr) ≫ coprod.map p₁.left p₂.left
    rw [← e, Category.assoc, coprod.inr_map, ← Category.assoc]
    rfl
  · have e := ReciprocityTheory.ChartRestriction.G.Geo.Tor.psum_hom ρ₁ ![x, y] I.down
    have e' : (fun i => ρ₁ ((![x, y] : Fin 2 → (T ⟶ E₁)) i)) = ![push p₁ x, push p₁ y] := by
      funext i
      fin_cases i <;> rfl
    rw [e'] at e
    show (psum A₁ ![push p₁ x, push p₁ y] I.down).left ≫ coprod.inl =
      ((psum E₁ ![x, y] I.down).left ≫ coprod.inl) ≫ coprod.map p₁.left p₂.left
    rw [← e, Category.assoc, coprod.inl_map, ← Category.assoc]
    rfl

end GlobalTheory.HomMum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroShortGeneratorSectionImageModelStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_nonzero_shortGenerator_section_imageModel : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (n : ℕ) (w : Fin n → V) (abelian₂ : ℝ), GlobalTheory.CompHt.IsShortGen Nm W w abelian₂ → ∀ x : X, ∃ (j : Fin n) (hj : w j ∈ W), x ∈ ReciprocityTheory.ChartRestriction.G.Out.nonzeroLocus (s ⟨w j, hj⟩) := by
  first | exact @GlobalTheory.ImageModelGen.exists_mem_nonzeroLocus_of_isShortGen | exact GlobalTheory.ImageModelGen.exists_mem_nonzeroLocus_of_isShortGen | (intros; apply GlobalTheory.ImageModelGen.exists_mem_nonzeroLocus_of_isShortGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormBasicOpenFiniteFreeBaseChangeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_basicOpen_finiteFree_baseChange : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁] [Module.Finite R R₁] [Module.Free R R₁] (X X₁ : Scheme.{0}) (p : X ⟶ Sp R) (p₁ : X₁ ⟶ Sp R₁) (b : X₁ ⟶ X), IsPullback b p₁ p (spMap (algebraMap R R₁)) → ∀ (V : X.Opens), IsCompact (V : Set X) → IsQuasiSeparated (V : Set X) → ∀ f : Γ(X₁, b ⁻¹ᵁ V), ∃ n : Γ(X, V), ∀ x : X, x ∈ X.basicOpen n ↔ x ∈ V ∧ ∀ z : X₁, b z = x → z ∈ X₁.basicOpen f := by
  first | exact @GlobalTheory.Mum.NormBC.exists_norm_basicOpen | exact GlobalTheory.Mum.NormBC.exists_norm_basicOpen | (intros; apply GlobalTheory.Mum.NormBC.exists_norm_basicOpen <;> assumption)
end

