import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3256
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3260
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2974
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2681
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2871
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3265
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1690
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0218
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0005
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2561
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2547
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1262
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1249
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinrankRiemannRochNsmulHyperplane
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsClosedImmersionGenericPoint
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1235
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3257
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHodgeDeRhamOfCrystallineLiftStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_hodge_de_rham_of_crystalline_lift : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRham.Hodge := by
  first | exact @GlobalTheory.AbelianHodge.abelianDeRham_hodge | exact GlobalTheory.AbelianHodge.abelianDeRham_hodge | (intros; apply GlobalTheory.AbelianHodge.abelianDeRham_hodge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDifferentialsFromGlobalForms
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
open TensorProduct
namespace GlobalTheory.ParForm

theorem isBaseChange_of_dual {R B M N : Type} [CommRing R] [CommRing B] [Algebra R B] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [Module B N] [IsScalarTower R B N] [Module.Finite R M] [Module.Projective R M]
    [Module.Finite B N] [Module.Projective B N] (f : M →ₗ[R] N)
    (h : ∀ l : M →ₗ[R] B, ∃! δ : N →ₗ[B] B, ∀ w, δ (f w) = l w) : IsBaseChange B f := by
  let F : B ⊗[R] M →ₗ[B] N := f.liftBaseChange B
  have hF : ∀ w, F (1 ⊗ₜ w) = f w := fun w ↦ by simp [F]
  have hd : Function.Bijective F.dualMap := by
    rw [Function.bijective_iff_existsUnique]
    intro φ
    obtain ⟨δ, h1, h2⟩ := h ((φ.restrictScalars R).comp (TensorProduct.mk R B M 1))
    refine ⟨δ, ?_, fun δ' e ↦ h2 δ' fun w ↦ ?_⟩
    · refine (LinearMap.liftBaseChangeEquiv B).symm.injective (LinearMap.ext fun w ↦ ?_)
      simpa [hF] using h1 w
    · rw [← hF]
      exact LinearMap.congr_fun e (1 ⊗ₜ w)
  have hdd : Function.Bijective F.dualMap.dualMap :=
    (LinearEquiv.ofBijective _ hd).dualMap.bijective
  have hb : Function.Bijective F := by
    have e : ⇑(Module.Dual.eval B N) ∘ ⇑F = ⇑F.dualMap.dualMap ∘ ⇑(Module.Dual.eval B (B ⊗[R] M)) :=
      funext fun x ↦ rfl
    rw [← Function.Bijective.of_comp_iff' (Module.bijective_dual_eval B N), e]
    exact hdd.comp (Module.bijective_dual_eval B _)
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective F hb) hF

theorem smooth_sec {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) (hs : Smooth s)
    (U : X.affineOpens) : Algebra.Smooth R (Sec s U.1) := by
  have h1 : RingHom.Smooth (s.appLE ⊤ U.1 le_top).hom :=
    HasRingHomProperty.appLE @Smooth s hs ⟨⊤, isAffineOpen_top _⟩ U le_top
  have h2 : RingHom.Smooth (secMap s U.1).hom :=
    RingHom.Smooth.respectsIso.2 _ (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv h1
  exact h2

theorem par : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Par A.hom := by
  intro H H' R _ A _ g hA hg U
  have hs : Smooth A.hom := SmoothOfRelativeDimension.smooth g A.hom
  have := smooth_sec A.hom hs U.unop
  obtain ⟨-, -, ⟨h1, h2, -⟩, -⟩ := H' R A g hA hg
  exact isBaseChange_of_dual _ (GlobalTheory.T.exists_unique_vectorField_of_globalOneForm_values H H' R A g hA hg U)

end GlobalTheory.ParForm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfCohomologyStructure
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem abelianUnobstructed_of_struct (hO : GlobalTheory.AbCoh.OStr)
    (hF : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧
        GlobalTheory.AbCoh.PrimF A) : GlobalTheory.Published.AbelianUnobstructed := by
  have hS : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
      SmoothOfRelativeDimension g A.hom →
      (Module.Finite R (HO1 A.hom) ∧ Module.Projective R (HO1 A.hom) ∧
        ∀ p : PrimeSpectrum R, Module.rankAtStalk (HO1 A.hom) p = g) ∧
      ∃ e : ⋀[R]^2 (HO1 A.hom) ≃ₗ[R] GlobalTheory.CatCoh.H2 (OAff A.hom),
        ∀ a b, e (exteriorPower.ιMulti R 2 ![a, b]) = GlobalTheory.CatCoh.cup (OAff A.hom) a b := by
    intro R _ A _ g hA hg
    obtain ⟨h1, h2, -, -⟩ := hO R A g hA hg
    exact ⟨h1, h2⟩
  exact GlobalTheory.T.abelianSchemeUnobstructed_of_constantDimension (GlobalTheory.T.abelianScheme_unobstructed_of_forms_structure (GlobalTheory.T.abelianSchemeGlobalFormsPrimitive_of_frames hF) (GlobalTheory.T.primitive_degree_two_extension (GlobalTheory.T.additiveClassDegreeTwo_structureSheaf_vanish hS))
    (GlobalTheory.T.axes_vanishing_degree_one_extension (GlobalTheory.T.axesO1_of_projective_rank_cup hS)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegree
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulIsogeny

theorem bcMap_natCast_smul_id (K : Type) [Field K] (L : Type) [Field L] [Algebra K L] (A : AbVar K) (n : ℕ) :
    bcMap L ((n : ℤ) • 𝟙 A) = (n : ℤ) • 𝟙 (baseChange L A) := by
  ext1
  simp only [bcMap, mk_hom, zsmul_hom, id_hom, zpow_natCast]
  exact GlobalTheory.MulFiniteFlat.pullback_map_mulA _ A.X n

theorem natCast_algClosed (k : Type) [Field k] [IsAlgClosed k] (A : AbVar k) (n : ℕ) (hn : n ≠ 0) :
    IsIsogeny ((n : ℤ) • 𝟙 A) ∧ deg ((n : ℤ) • 𝟙 A) = n ^ (2 * A.dim) := by
  have e : ((n : ℤ) • 𝟙 A).hom = (𝟙 A.X ^ n : A.X ⟶ A.X) := by
    rw [zsmul_hom, id_hom, zpow_natCast]
  obtain ⟨hfin, hfl⟩ := GlobalTheory.MulFiniteFlat.isFinite_and_flat_mul (Sp k) A.X A.ab n (Nat.one_le_iff_ne_zero.2 hn)
  have hmon : IsMonHom (𝟙 A.X ^ n : A.X ⟶ A.X) := e ▸ inferInstanceAs (IsMonHom ((n : ℤ) • 𝟙 A).hom)
  have hsurj : Surjective (𝟙 A.X ^ n : A.X ⟶ A.X).left :=
    (GlobalTheory.flat_and_surjective_of_isFinite_abelianEnd
      GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected k A.X A.ab _ inferInstance hfin).2
  have hiso : IsIsogeny ((n : ℤ) • 𝟙 A) := by
    unfold IsIsogeny
    rw [e]
    exact ⟨hfin, hsurj⟩
  refine ⟨hiso, ?_⟩
  unfold deg
  rw [if_pos hiso, e]
  exact GlobalTheory.UU.MulDegree.finrank_mul_eq k A.X A.dim n A.ab A.smooth hn _

theorem natCast (K : Type) [Field K] (A : AbVar K) (n : ℕ) (hn : n ≠ 0) :
    IsIsogeny ((n : ℤ) • 𝟙 A) ∧ deg ((n : ℤ) • 𝟙 A) = n ^ (2 * A.dim) := by
  obtain ⟨h1, h2⟩ := natCast_algClosed (AlgebraicClosure K) (baseChange (AlgebraicClosure K) A) n hn
  obtain ⟨e1, e2⟩ := GlobalTheory.T.isogeny_baseChange_iff_and_degree_eq K (AlgebraicClosure K) A A ((n : ℤ) • 𝟙 A)
  rw [bcMap_natCast_smul_id] at e1 e2
  exact ⟨e1.1 h1, e2.symm.trans h2⟩

theorem neg_one (K : Type) [Field K] (A : AbVar K) : IsIsogeny (-𝟙 A) ∧ deg (-𝟙 A) = 1 := by
  have hsq : (-𝟙 A) ≫ (-𝟙 A) = 𝟙 A := by simp
  have hsq' : (-𝟙 A).hom.left ≫ (-𝟙 A).hom.left = 𝟙 A.X.left := by
    rw [← Over.comp_left, ← comp_hom, hsq, id_hom, Over.id_left]
  haveI : IsIso (-𝟙 A).hom.left := ⟨⟨(-𝟙 A).hom.left, hsq', hsq'⟩⟩
  have hiso : IsIsogeny (-𝟙 A) := ⟨inferInstance, inferInstance⟩
  refine ⟨hiso, ?_⟩
  unfold deg
  rw [if_pos hiso]
  exact congrFun (Scheme.Hom.finrank_eq_one_of_isIso _) _

theorem mul_isogeny : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℤ), n ≠ 0 → IsIsogeny (n • 𝟙 A) ∧ deg (n • 𝟙 A) = n.natAbs ^ (2 * A.dim) := by
  intro K _ A n hn
  rcases Int.natAbs_eq n with h | h
  · rw [h]
    exact natCast K A n.natAbs (Int.natAbs_ne_zero.2 hn)
  · have e : n • 𝟙 A = ((n.natAbs : ℤ) • 𝟙 A) ≫ (-𝟙 A) := by
      rw [Preadditive.comp_neg, Category.comp_id, ← neg_smul, ← h]
    obtain ⟨h1, h2⟩ := natCast K A n.natAbs (Int.natAbs_ne_zero.2 hn)
    obtain ⟨h3, h4⟩ := neg_one K A
    obtain ⟨h5, h6⟩ := GlobalTheory.T.isogeny_comp_and_degree_mul K A A A _ _ h1 h3
    rw [e]
    exact ⟨h5, by rw [h6, h2, h4, _root_.mul_one]⟩

end GlobalTheory.MulIsogeny
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyStructureSheafCohomologyAnyFieldStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_structureSheaf_cohomology_anyField : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Module.Finite K (HO1 A.hom) ∧ Module.finrank K (HO1 A.hom) = g ∧ WedgeO (OAff A.hom) ∧ NoPrimitiveStructureSheafH2 A ∧ AxesVanishingStructureSheafDegOne A := by
  first | exact @GlobalTheory.AbCoh.abelian_HO_field_any | exact GlobalTheory.AbCoh.abelian_HO_field_any | (intros; apply GlobalTheory.AbCoh.abelian_HO_field_any <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleDeRhamHomologySummandsCrystal
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LiftSys

section Lin

variable {S : Type*} [CommRing S] {M N : Type*} [AddCommGroup M] [Module S M] [AddCommGroup N] [Module S N]

theorem smul_top_le_comap (f : M →ₗ[S] N) (J : Ideal S) :
    J • (⊤ : Submodule S M) ≤ (J • (⊤ : Submodule S N)).comap f :=
  Submodule.smul_le.2 fun r hr n _ ↦ by
    rw [Submodule.mem_comap, map_smul]; exact Submodule.smul_mem_smul hr trivial

theorem mem_smul_top_equiv (e : M ≃ₗ[S] N) (J : Ideal S) (x : M) :
    e x ∈ J • (⊤ : Submodule S N) ↔ x ∈ J • (⊤ : Submodule S M) :=
  ⟨fun h ↦ by simpa using smul_top_le_comap (e.symm : N →ₗ[S] M) J h,
   fun h ↦ smul_top_le_comap (e : M →ₗ[S] N) J h⟩

theorem mem_sup_smul_top_equiv (e : M ≃ₗ[S] N) (J : Ideal S) (K : Submodule S N) (x : M) :
    x ∈ K.comap (e : M →ₗ[S] N) ⊔ J • ⊤ ↔ e x ∈ K ⊔ J • ⊤ := by
  constructor
  · intro h
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 h
    rw [map_add]
    exact Submodule.add_mem_sup ha ((mem_smul_top_equiv e J b).2 hb)
  · intro h
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 h
    have hx : x = e.symm a + e.symm b := by rw [← map_add, hab, LinearEquiv.symm_apply_apply]
    rw [hx]
    refine Submodule.add_mem_sup ?_ ((mem_smul_top_equiv e J _).1 (by simpa using hb))
    simpa using ha

theorem exists_isCompl_comap_iff (e : M ≃ₗ[S] N) (K : Submodule S N) :
    (∃ L, IsCompl K L) ↔ ∃ L, IsCompl (K.comap (e : M →ₗ[S] N)) L := by
  constructor
  · rintro ⟨L, h⟩
    exact ⟨L.comap (e : M →ₗ[S] N), (Submodule.orderIsoMapComap e).symm.isCompl h⟩
  · rintro ⟨L, h⟩
    refine ⟨L.map (e : M →ₗ[S] N), ?_⟩
    have := (Submodule.orderIsoMapComap e).isCompl h
    simpa [Submodule.orderIsoMapComap, Submodule.map_comap_eq_of_surjective e.surjective] using this

end Lin

theorem admissible_classification : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → (∀ K : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) → (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) → ∃ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F ∧ (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h')) ∧ (∀ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F → ∃ K : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) ∧ (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) ∧ (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h')) ∧ ∀ K K' : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) → (∃ N, IsCompl K' N) → (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = (K'.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator → K = K' := by
  intro H1 H2 R R₀ _ _ I hI π hπ hk g A₀ _ A' _ i' h' hA hg
  obtain ⟨-, -, pc, bij, fin, proj, hA₀, hg₀⟩ :=
    abelianLift_facts H1 H2 R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨rs, rk⟩ := GlobalTheory.T.abelianScheme_crystal_reduces_to_deRham_sqZero H1 H2 R R₀ I hI π hπ hk g A₀ A' i' h' hA hg
  obtain ⟨-, ⟨N₀, hN₀⟩, -⟩ := GlobalTheory.AbelianHodge.abelianDeRham_hodge H1 H2 R₀ A₀ g hA₀ hg₀
  let P := prim (divided₂ hI) (spMap π) A₀
  let Ψ : primDR A' ≃ₗ[R] P := LinearEquiv.ofBijective (liftMor (divided₂ hI) h').pull bij
  let Φ : primDR A' ≃ₗ[R] Cr hI π A₀.hom := Ψ.trans (LinearEquiv.ofTop _ pc)
  have hΦ : ∀ c, Φ c = ((Ψ c : P) : Cr hI π A₀.hom) := fun _ ↦ rfl
  let ρ := (GrothendieckMessing.redMor h').pull
  have mT : IsMor (dp0 R₀) (A₀.hom ≫ 𝟙 _) (dp0 R₀) A₀.hom (RingHom.id R₀) (𝟙 _) :=
    IsMor.of_over _ (by simp)
  have mT' : IsMor (dp0 R₀) A₀.hom (dp0 R₀) (A₀.hom ≫ 𝟙 _) (RingHom.id R₀) (𝟙 _) :=
    IsMor.of_over _ (by simp)
  have back : ∀ x, mT'.pull1 (mT.pull1 x) = x := fun x ↦
    (IsMor.pullback1_comp mT mT' (IsMor.id _ _) (fun _ ↦ rfl) (Category.id_comp _) x).trans
      (IsMor.pullCohomologyOne_id _ x)
  have inj : Function.Injective mT.pull1 := Function.LeftInverse.injective back
  have mD : IsMor (dp0 R) (A'.hom ≫ 𝟙 _) (dp0 R₀) A₀.hom π i' :=
    IsMor.of_dividedPowersZeroIdeal _ (by rw [Category.comp_id]; exact h'.1.w)
  have key : ∀ c : primDR A',
      mT.pull1 ((ρ c : primDR A₀) : FirstDeRham (A₀.hom ≫ 𝟙 _)) = rho hI hk A₀.hom (Φ c) := by
    intro c
    rw [hΦ]
    exact (IsMor.pullback1_comp _ mT mD (fun _ ↦ rfl) (Category.id_comp _) c.1).trans
      (IsMor.pullback1_comp _ (redMor hI hk A₀.hom) mD (fun _ ↦ rfl) (Category.id_comp _) c.1).symm
  have F1iff : ∀ c : primDR A', ρ c ∈ PrimitiveSubmodule A₀ ↔ rho hI hk A₀.hom (Φ c) ∈ F1 A₀.hom := by
    intro c
    rw [← key]
    constructor
    · intro h
      exact mT.pullback1_mem_hodgeFiltration h
    · intro h
      have := mT'.pullback1_mem_hodgeFiltration h
      rw [back] at this
      exact this
  have ρker : ∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R (primDR A')) := by
    intro c
    rw [hk, ← mem_smul_top_equiv Φ, ← rk, ← key, map_eq_zero_iff _ inj, Submodule.coe_eq_zero]
  have ρsurj : Function.Surjective ρ := by
    intro y
    obtain ⟨d, hd⟩ := rs (mT.pull1 y.1)
    refine ⟨Φ.symm d, Subtype.ext (inj ?_)⟩
    rw [key, LinearEquiv.apply_symm_apply, hd]
  obtain ⟨D1, D2⟩ := GlobalTheory.T.summand_dualAnnihilator_reduction_projective R R₀ π hπ (primDR A') (primDR A₀) (Module.Finite.equiv Φ.symm)
    (Module.Projective.of_equiv Φ.symm) ρ ρsurj ρker (PrimitiveSubmodule A₀) ⟨N₀, hN₀⟩
  have cond : ∀ K : Submodule R (Cr hI π A₀.hom),
      (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) ↔
        ∀ c, c ∈ K.comap (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom) ⊔ RingHom.ker π • ⊤ ↔
          ρ c ∈ PrimitiveSubmodule A₀ := by
    intro K
    rw [hk]
    constructor
    · intro H c
      rw [mem_sup_smul_top_equiv, F1iff]
      exact H (Φ c)
    · intro H c
      have := H (Φ.symm c)
      rwa [mem_sup_smul_top_equiv, F1iff, LinearEquiv.apply_symm_apply] at this
  have crysSurj : Function.Surjective (crysToDR (divided₂ hI) h') := fun y ↦
    ⟨y.comp (Ψ.symm : P →ₗ[R] primDR A'), LinearMap.ext fun c ↦ by
      rw [crysToDR_apply]
      exact congrArg y (Ψ.symm_apply_apply c)⟩
  have ann : ∀ K : Submodule R (Cr hI π A₀.hom),
      (K.comap P.subtype).dualAnnihilator =
        (K.comap (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom)).dualAnnihilator.comap
          (crysToDR (divided₂ hI) h') := by
    intro K
    ext d
    simp only [Submodule.mem_comap, Submodule.mem_dualAnnihilator, crysToDR_apply]
    constructor
    · intro H c hc
      exact H _ hc
    · intro H p hp
      have e : (liftMor (divided₂ hI) h').pull (Ψ.symm p) = p := Ψ.apply_symm_apply p
      have hm : Φ (Ψ.symm p) ∈ K := by
        rw [hΦ, Ψ.apply_symm_apply]
        exact hp
      have := H (Ψ.symm p) hm
      rwa [crysToDR_apply, e] at this
  have eqiff : ∀ (K : Submodule R (Cr hI π A₀.hom)) (F : Submodule R (HdR A')),
      (K.comap P.subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h') ↔
        (K.comap (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom)).dualAnnihilator = F := by
    intro K F
    rw [ann]
    exact (Submodule.comap_injective_of_surjective crysSurj).eq_iff
  refine ⟨fun K hK hc ↦ ?_, fun F hF ↦ ?_, fun K K' hK hK' he ↦ ?_⟩
  · obtain ⟨c1, -, c3⟩ := D1 _ ((exists_isCompl_comap_iff Φ K).1 hK)
    exact ⟨_, ⟨c1, c3.1 ((cond K).1 hc)⟩, (eqiff K _).2 rfl⟩
  · obtain ⟨K', hK', rfl⟩ := D2 F hF.1
    have hKK : (K'.map (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom)).comap
        (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom) = K' :=
      Submodule.comap_map_eq_of_injective Φ.injective K'
    obtain ⟨-, -, c3⟩ := D1 K' hK'
    refine ⟨K'.map (Φ : primDR A' →ₗ[R] Cr hI π A₀.hom), (exists_isCompl_comap_iff Φ _).2 (by rw [hKK]; exact hK'),
      (cond _).2 (by rw [hKK]; exact c3.2 hF.2), (eqiff _ _).2 (by rw [hKK])⟩
  · rw [ann, ann] at he
    have e := Submodule.comap_injective_of_surjective crysSurj he
    obtain ⟨-, c2, -⟩ := D1 _ ((exists_isCompl_comap_iff Φ K).1 hK)
    obtain ⟨-, c2', -⟩ := D1 _ ((exists_isCompl_comap_iff Φ K').1 hK')
    refine Submodule.comap_injective_of_surjective Φ.surjective ?_
    rw [← c2, ← c2', e]

end GlobalTheory.LiftSys
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicModelOfDeRham
section
set_option autoImplicit false

noncomputable section

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ModelAlgProof

theorem modelAlg : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ModelAlg := by
  intro hPC hDR hDC K _ _ d δ io hK hd hδ Λ₀ Ω₀ hΛ hΩ E _ _ _ _ I _ φ hφ hio c y hc
  obtain ⟨𝔠, X₀, X, p, U, v₀, v, a, hp, hh, hv, hex, hdesc⟩ :=
    GlobalTheory.T.cm_period_from_elliptic_lattice hPC hDR hDC K d δ io hK hd hδ Λ₀ Ω₀ hΛ hΩ E I φ hφ hio c y hc
  obtain ⟨δ₀, δX, C, hDCr, hdet, hCa⟩ :=
    GlobalTheory.T.lie_correspondence_differentials E I φ _ 𝔠 X₀ X p U v₀ v a hp fun i ↦ ⟨(hv i).1, (hv i).2.1⟩
  obtain ⟨N, m, ψ, yv, w, hpol, hAdm, hvec⟩ := GlobalTheory.T.cm_type_differentials_algebraic hPC hDR hDC E I φ _ 𝔠 X₀ X p U v₀ v a hφ hp
    (fun i ↦ ⟨(hv i).1, (hv i).2.1, (hv i).2.2.1⟩) hex hdesc

  have hσ : ∀ x : Qb, IsAlgebraic ℚ (algebraMap Qb ℂ x) := fun x ↦ by
    have := x.2
    rwa [mem_algebraicClosure_iff] at this
  have toQ : ∀ z : ℂ, IsAlgebraic ℚ z → z ∈ (algebraicClosure ℚ ℂ) := fun z hz ↦ by
    rwa [mem_algebraicClosure_iff]
  have ofQ : ∀ z : ℂ, z ∈ (algebraicClosure ℚ ℂ) → IsAlgebraic ℚ z := fun z hz ↦ by
    rwa [mem_algebraicClosure_iff] at hz
  let T : CxPt 𝔠 φ (lattice c y) :=
    { X := X, U := U, δ := δX, C := C, det := hdet, ψ := ψ, pol := hpol, y := yv, w := w, s := fun _ ↦ 1,
      cm := fun i ↦ (hvec i).1 }
  have ha0 : ∀ i, a i ≠ 0 := fun i ↦ (hv i).2.2.1
  refine ⟨𝔠, X₀, δ₀, N, T, hAdm, ⟨p, m, hp, hDCr, fun i x₀ x hx ↦ ?_⟩, ?_, fun i ↦ ⟨?_, ?_⟩⟩
  · have := (hvec i).2.2.2 x₀ x hx
    simpa [T, CxPt.low] using this
  · have hprod : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ ↦ ha0 i
    have e : C / Ω₀ ^ Fintype.card I = (C * ∏ i, a i) / ∏ i, (a i * Ω₀) := by
      rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, mul_comm (∏ x, a x) _,
        mul_div_mul_right _ _ hprod]
    change IsAlgebraic ℚ (C / Ω₀ ^ Fintype.card I)
    rw [e]
    apply ofQ
    exact div_mem (toQ _ hCa) (prod_mem fun i _ ↦ toQ _ (hv i).2.2.2)
  · have hw := (hvec i).2.1
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    change (Real.pi : ℂ) * (U.h i : ℂ) * 1 * w i ^ 2 ≠ 0
    have := (hh i).1
    simp only [_root_.mul_one]
    exact mul_ne_zero (mul_ne_zero hpi (Complex.ofReal_ne_zero.2 this)) (pow_ne_zero _ hw)
  · have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
    have e : T.A i * Ω₀ ^ 2 * ((Real.sqrt d : ℝ) : ℂ) / (2 * Real.pi) =
        ((U.h i : ℂ) * (Real.sqrt d : ℝ)) * (w i / a i) ^ 2 * (a i * Ω₀) ^ 2 / 2 := by
      change (Real.pi : ℂ) * (U.h i : ℂ) * 1 * w i ^ 2 * Ω₀ ^ 2 * ((Real.sqrt d : ℝ) : ℂ) / (2 * Real.pi) = _
      field_simp [ha0 i]
    rw [e]
    apply ofQ
    refine div_mem (mul_mem (mul_mem (toQ _ (hh i).2) (pow_mem (toQ _ (hvec i).2.2.1) _))
      (pow_mem (toQ _ (hv i).2.2.2) _)) ?_
    simpa using (algebraicClosure ℚ ℂ).algebraMap_mem (2 : ℚ)

end GlobalTheory.ModelAlgProof
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassEqSelfIntersectionLineBundle
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option autoImplicit false

namespace GlobalTheory.MassDegree

theorem chernInt_eq_topSelf : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  intro Y L φ hφ
  let ψ : Weight Y.str (RingHom.id ℂ) ((ProjSpace.O1 ℂ Y.N).pull Y.ι) :=
    ((ProjSpace.hermitianTwistingSheaf ℂ Y.N).φ (RingHom.id ℂ)).pull Y.ι Y.ι_str
  have hψ : ψ.IsCInf := ((ProjSpace.hermitianTwistingSheaf ℂ Y.N).cInf (RingHom.id ℂ)).pull Y.ι Y.ι_str
  obtain ⟨P, hP0, hP⟩ := GlobalTheory.T.exists_polynomial_chernIntegral_tens_pow Y L _ φ ψ hφ hψ
  obtain ⟨Q, hQ0, hQ⟩ := GlobalTheory.SelfInterPoly.exists_polynomial_topSelf Y L _ φ.isLB ψ.isLB
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.twist_ample_globally_generated Y L φ.isLB
  have key : ∀ m : ℕ, m₀ ≤ m → P.eval (m : ℝ) = Q.eval (m : ℝ) := by
    intro m hm
    obtain ⟨n, u, hu⟩ := hm₀ m hm
    rw [← hP m, ← hQ m]
    exact GlobalTheory.T.chernMass_eq_selfIntersection_of_generated Y _ (φ.tens (ψ.pow m)) (hφ.tens (hψ.zpow m)) n u hu
  have hPQ : P = Q := by
    refine Polynomial.eq_of_infinite_eval_eq P Q ?_
    refine Set.Infinite.mono ?_ ((Set.Ici_infinite m₀).image Nat.cast_injective.injOn)
    rintro _ ⟨m, hm, rfl⟩
    exact key m hm
  rw [← hP0, ← hQ0, hPQ]

end GlobalTheory.MassDegree
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumEqMassMulOrbitalIntegralStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.classSum_eq_mass_mul_orbitalIntegral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → ∀ f : ∀ w : Pl E, UL n w → ℂ, IsTest (KL n) K' f → ∀ γ : UE E n, γ.1.val.charpoly.Separable → clsSum S K' f γ = mass (MonoidHom.id _) (ratFinU E n) (finPt γ) * twOrb (MonoidHom.id _) (globLev S (KL n)) (finPt γ) (globFn S f) := by
  first | exact @GlobalTheory.BCT.ClsOrb.clsSum_eq_mass_mul_twOrb | exact GlobalTheory.BCT.ClsOrb.clsSum_eq_mass_mul_twOrb | (intros; apply GlobalTheory.BCT.ClsOrb.clsSum_eq_mass_mul_twOrb <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnectedChartEvalSquareVariablesSwapConstantStatement
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.connectedChart_evalSquare_variables_swap_constant : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k) (c : Chart G d), ∀ n, (∀ f, c.ev₂ n (inL f) = c.ev n f ⊗ₜ[k] 1) ∧ (∀ f, c.ev₂ n (inR f) = 1 ⊗ₜ[k] c.ev n f) ∧ (∀ s, c.ev₂ n (Katz.swap s) = TensorProduct.comm k _ _ (c.ev₂ n s)) ∧ ∀ s, Algebra.TensorProduct.lift (Bialgebra.counitAlgHom k (G.A n)) (Bialgebra.counitAlgHom k (G.A n)) (fun _ _ => Commute.all _ _) (c.ev₂ n s) = constantCoeff s := by
  first | exact @GlobalTheory.EvSquare.main | exact GlobalTheory.EvSquare.main | (intros; apply GlobalTheory.EvSquare.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryBoundOfInputsStatement
section
open GlobalTheory.SumSize GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionary_bound_of_inputs : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK := by
  first | exact @GlobalTheory.SumSize.dictK_of_normSum | exact GlobalTheory.SumSize.dictK_of_normSum | (intros; apply GlobalTheory.SumSize.dictK_of_normSum <;> assumption)
end

