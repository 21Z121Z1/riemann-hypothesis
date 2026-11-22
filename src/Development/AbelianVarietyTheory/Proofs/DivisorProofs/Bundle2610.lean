import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2492
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2426
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2396
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2449
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2450
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2452
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2511
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0003
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0208
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ThetaGen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2489
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0180
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0061
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0162
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2493
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0033
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2494
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2436
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0059
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemiAbelianModelFiniteExtCompleteDVRStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_semiAbelianModel_finiteExt_completeDVR : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.LN.CDvr W → ∀ (P : PolAV (Sp (FractionRing W))),
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : W →+* V₁)
      (fK : FractionRing W →+* FractionRing V₁), GlobalTheory.LN.CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
      (∀ a, fK (algebraMap W _ a) = algebraMap V₁ _ (f a)) ∧
      ∃ (A : PolAV (Sp (FractionRing V₁))) (β : A.A.left ⟶ P.A.left), IsGrpPullback A.A P.A (spMap fK) β ∧
        LBIso A.L (P.L.pull β) ∧
        ∃ (G : Over (Sp V₁)) (_ : GrpObj G) (_ : IsCommMonObj G) (gen : (Over.pullback (jK V₁)).obj G ≅ A.A),
          IsSemiAbelian G ∧ IsMonHom gen.hom := by
  first | exact @GlobalTheory.PolSemiAbModel.exists_model | exact GlobalTheory.PolSemiAbModel.exists_model | (intros; apply GlobalTheory.PolSemiAbModel.exists_model <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearCochainOfDegreeOneObstructionZer
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.Obs

theorem exists_cochain_of_isOb1_zero : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), Module.Projective R₀ (GlobForm s₀) → ∀ (C' : Type) [Category.{0} C'] (F' : C' ⥤ CommAlgCat.{0} R₀) (L : Pre I π (OAff s₀)) (L' : Pre I π F') (n : CoefMap (RingHom.id R₀) (OAff s₀) F') (l : ∀ T : C', L.B (n.G.obj T) →ₐ[R] L'.B T), (∀ w, L.IsOb1 L' n l α w 0) → ∃ (κ : ∀ (T T' : C') (_ : T ⟶ T'), Ω[(OAff s₀).obj (n.G.obj T)⁄R₀] →+ L'.B T') (u : GlobForm s₀ →+ ∀ T : C', L'.B T), (∀ (T T' : C') (a : T ⟶ T'), IsTheta I (L.p (n.G.obj T)) ((L'.ρ a).comp (l T)) ((l T').comp (L.ρ (n.G.map a))) (κ T T' a)) ∧ (∀ (r : R) w, u (π r • w) = r • u w) ∧ (∀ w T, u w T ∈ I.map (algebraMap R (L'.B T))) ∧ ∀ (w : GlobForm s₀) (T T' : C') (a : T ⟶ T'), κ T T' a (w.1 (n.G.obj T)) = u w T' - L'.ρ a (u w T) := by
  intro R R₀ _ _ I hI π hπ hk R₁ _ _ α X₀ s₀ hP C' _ F' L L' n l h
  obtain ⟨κ, -, -, hκ, -, -, -⟩ := h 0
  let W : Submodule R (∀ T : C', L'.B T) :=
    { carrier := {m | ∀ T, m T ∈ I.map (algebraMap R (L'.B T))}
      add_mem' := fun {m m'} hm hm' T ↦ Ideal.add_mem _ (hm T) (hm' T)
      zero_mem' := fun T ↦ Ideal.zero_mem _
      smul_mem' := fun r m hm T ↦ by
        show r • m T ∈ _
        rw [Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ (hm T) }
  have hW : ∀ r, π r = 0 → ∀ m ∈ W, r • m = 0 := by
    intro r hr m hm
    funext T
    show r • m T = 0
    have hrI : r ∈ I := hk ▸ RingHom.mem_ker.2 hr
    have h2 := Ideal.mul_mem_mul (Ideal.mem_map_of_mem (algebraMap R (L'.B T)) hrI) (hm T)
    rw [← sq, map_sq hI] at h2
    rw [Algebra.smul_def]
    simpa using h2
  let q : (∀ T : C', L'.B T) →ₗ[R] (∀ (T T' : C') (_ : T ⟶ T'), L'.B T') :=
    { toFun := fun m T T' a ↦ m T' - L'.ρ a (m T)
      map_add' := fun m m' ↦ by funext T T' a; simp only [Pi.add_apply, map_add]; abel
      map_smul' := fun r m ↦ by
        funext T T' a; simp only [Pi.smul_apply, map_smul, smul_sub, RingHom.id_apply] }
  let v : GlobForm s₀ →+ (∀ (T T' : C') (_ : T ⟶ T'), L'.B T') :=
    { toFun := fun w T T' a ↦ κ T T' a (w.1 (n.G.obj T))
      map_zero' := by funext T T' a; exact map_zero (κ T T' a)
      map_add' := fun w w' ↦ by funext T T' a; exact map_add (κ T T' a) _ _ }
  have hv : ∀ (r : R) w, v (π r • w) = r • v w := by
    intro r w
    funext T T' a
    show κ T T' a (π r • w.1 (n.G.obj T)) = r • κ T T' a (w.1 (n.G.obj T))
    have hp : L.p (n.G.obj T) (algebraMap R (L.B (n.G.obj T)) r) = algebraMap R₀ _ (π r) := by
      have h1 := L.semi (n.G.obj T) r 1
      rw [← Algebra.algebraMap_eq_smul_one, map_one] at h1
      rw [h1, Algebra.algebraMap_eq_smul_one]
    have h3 := (hκ T T' a).smul (algebraMap R _ r) (w.1 (n.G.obj T))
    rw [hp, algebraMap_smul, AlgHom.commutes] at h3
    rw [h3, Algebra.smul_def]
  have hq : ∀ w, ∃ m ∈ W, q m = v w := by
    intro w
    obtain ⟨κw, σw, zw, hκw, hσw, hc, hz⟩ := h w
    obtain ⟨f, hf⟩ := H1.mk_eq_zero.1 hc.symm
    have hκκ : ∀ T T' (a : T ⟶ T'), κ T T' a = κw T T' a := fun T T' a ↦
      (isTheta_add R R₀ I hI π hπ hk _ _ (L.p (n.G.obj T)) (L.semi _) (L.surj _) (L.ker _) (L'.B T') _ _ ((l T').comp (L.ρ (n.G.map a))) _ _
        (hκ T T' a)).2.2.1 (hκw T T' a)
    refine ⟨fun T ↦ σw T (f T), fun T ↦ (sig_basic R R₀ I hI π hπ hk R₁ α _ _ (L'.p T) (L'.semi T) (L'.surj T)
      (L'.ker T) (σw T) (hσw T)).1 (f T), ?_⟩
    funext T T' a
    have hn := (sig_natural R R₀ I hI π hπ hk R₁ α _ _ (L'.p T) (L'.semi T) (L'.surj T) (L'.ker T) _ _ (L'.p T')
      (L'.semi T') (L'.surj T') (L'.ker T') (L'.ρ a) (mp F' a) (L'.nat a) (σw T) (σw T') (hσw T) (hσw T')).1 (f T)
    have hzf : zw.1 T T' a = f T' - extHom R₁ (mp F' a) (f T) := by
      rw [← hf]; rfl
    show σw T' (f T') - L'.ρ a (σw T (f T)) = κ T T' a (w.1 (n.G.obj T))
    rw [hκκ, ← (hz T T' a).2, hzf, map_sub, hn]
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_semilinear_lift_of_projective R R₀ π hπ (GlobForm s₀) hP _ _ W hW q v hv hq
  exact ⟨κ, u, hκ, hu1, hu2, fun w T T' a ↦ (congrFun (congrFun (congrFun (hu3 w) T) T') a).symm⟩

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSettingOfEvenOn
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.TraitSetting

open GlobalTheory.UU GlobalTheory.LN

set_option maxHeartbeats 1000000 in

theorem exists_setting_of_evenOn (laws : Laws) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] (P : CP G) (hS : IsSemiAbelian G) (hE : EvenOn P)
    (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A) [IsMonHom gen.hom]
    (hA : LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))))
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : CDvr V) (φ : R →+* V) (hφ : Function.Injective φ)
    (hI : maximalIdeal R ≤ (maximalIdeal V).comap φ) :
    ∃ (A' : PolAV (Sp (FractionRing V))) (s : HidaSetting V A' ((Over.pullback (spMap φ)).obj G)) (w : _),
      IsCPMap s.P P (spMap φ) (pullback.fst G.hom (spMap φ)) pullback.condition w := by
  obtain ⟨X, _, _, _, Q₀, P₀, hlev, hev⟩ := hE
  have hG' : IsSemiAbelian ((Over.pullback (spMap φ)).obj G) := IsSemiAbelian.pullback _ G hS
  obtain ⟨ψ, sq'⟩ := ClosedPol.exists_generic_square φ hφ
  obtain ⟨A', gen', hgen', hA'⟩ := ClosedPol.exists_fibre_pull laws sq' P.L.isLB A gen hA
  obtain ⟨P', wP, hP', H⟩ := exists_cp_pull _ _ (spMap φ) G ((Over.pullback (spMap φ)).obj G) _ _
    (toBase_mul_pullback G (spMap φ)) P
  rw [← hP'] at hA'
  obtain ⟨P₀', w₀, H₀⟩ := exists_isLevelCP (maximalIdeal V) 0 P'
  have le : maximalIdeal R ^ (0 + 1) ≤ (maximalIdeal V ^ (0 + 1)).comap φ := by
    rw [zero_add, pow_one, pow_one]; exact hI
  let b : R ⧸ maximalIdeal R ^ (0 + 1) →+* V ⧸ maximalIdeal V ^ (0 + 1) := Ideal.quotientMap _ φ le
  have sq : spMap b ≫ thick R (maximalIdeal R) 0 = thick V (maximalIdeal V) 0 ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]
  obtain ⟨wl, hl⟩ := hlev
  obtain ⟨F, pF, w₃, k₃⟩ := ClosedPol.exists_fourth (G := G) (G' := (Over.pullback (spMap φ)).obj G)
    (H := thickObj R (maximalIdeal R) 0 G)
    (H' := thickObj V (maximalIdeal V) 0 ((Over.pullback (spMap φ)).obj G)) (P := P) (P' := P')
    (N := P₀) (N' := P₀') sq (isGrpPullback_pullback G (spMap φ))
    (isGrpPullback_pullback G (thick R (maximalIdeal R) 0))
    (isGrpPullback_pullback _ (thick V (maximalIdeal V) 0)) H hl H₀
  have := hS.smooth
  have := hS.geomConnected
  have : Smooth (thickObj R (maximalIdeal R) 0 G).hom := by
    show Smooth (pullback.snd _ _); infer_instance
  have : GeometricallyConnected (thickObj R (maximalIdeal R) 0 G).hom := by
    show GeometricallyConnected (pullback.snd _ _); infer_instance
  obtain ⟨D₀⟩ := TowerEx.nonempty_desc _ (TowerEx.isNilpotent_max 0) _ P₀ Q₀ hev
  obtain ⟨Q₀', D₀', -, -, -⟩ := ClosedPol.exists_desc_pull pF Q₀ D₀ k₃
  have ev := UniformizationSetting.exists_even_of_desc D₀'
  obtain ⟨wA, hwA⟩ := hA'
  exact ⟨A', ⟨hV, hG', gen', hgen', P', wA, hwA, _, Q₀', P₀', ⟨w₀, H₀⟩, ev⟩, wP, H⟩

end GlobalTheory.Mum.TraitSetting
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShiftSemicharactersNestedLatticesStatement
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory
  CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.TorusRM

open scoped nonZeroDivisors

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_shift_semicharacters_nested_lattices : ∀ (g : ℕ) (Λ Λ₁ : Submodule ℤ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : Λ → ℂ) (χ₁ : Λ₁ → ℂ)
    (h : Λ ≤ Λ₁), DiscreteTopology Λ → Submodule.span ℝ (Λ : Set (Fin g → ℂ)) = ⊤ → Hm.IsHermitian →
    (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ l, ‖χ l‖ = 1) → (∀ l, ‖χ₁ l‖ = 1) →
    (∀ l m : Λ, χ (l + m) = χ l * χ m * Complex.exp (Real.pi * Complex.I * (hermForm Hm l m).im)) →
    (∀ l m : Λ₁, χ₁ (l + m) = χ₁ l * χ₁ m * Complex.exp (Real.pi * Complex.I * (hermForm Hm l m).im)) →
    ∃ a : Fin g → ℂ, ∀ l : Λ,
      χ l = χ₁ (Submodule.inclusion h l) * Complex.exp (2 * Real.pi * Complex.I * (hermForm Hm a l).im) := by
  first | exact @GlobalTheory.SemicharShift.exists_shift_of_semichar | exact GlobalTheory.SemicharShift.exists_shift_of_semichar | (intros; apply GlobalTheory.SemicharShift.exists_shift_of_semichar <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothAwayOfQuotientPowEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.SmoothAdic

open TensorProduct

theorem exists_smooth_away_of_quotient_pow_equiv : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (O C : Type) [CommRing O] [Algebra R O] [CommRing C] [Algebra R C], Algebra.Smooth R O → Algebra.FiniteType R C → (∀ e : ℕ, Nonempty ((O ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R O)) ≃ₐ[R] (C ⧸ (maximalIdeal R ^ (e + 1)).map (algebraMap R C)))) → ∀ q : Ideal C, q.IsPrime → q.comap (algebraMap R C) = maximalIdeal R → ∃ g : C, g ∉ q ∧ Algebra.Smooth R (Localization.Away g) := by
  intro R _ _ _ O C _ _ _ _ hO hC hiso q hq hqm
  have hsm : ∀ e : ℕ, Algebra.Smooth (R ⧸ maximalIdeal R ^ (e + 1))
      (TensorProduct R (R ⧸ maximalIdeal R ^ (e + 1)) C) := by
    intro e
    obtain ⟨φ⟩ := hiso e
    let J := maximalIdeal R ^ (e + 1)
    let φ' : (O ⧸ J.map (algebraMap R O)) ≃ₐ[R ⧸ J] (C ⧸ J.map (algebraMap R C)) :=
      AlgEquiv.extendScalarsOfSurjective Ideal.Quotient.mk_surjective φ
    let ψ : ((R ⧸ J) ⊗[R] O) ≃ₐ[R ⧸ J] ((R ⧸ J) ⊗[R] C) :=
      ((Algebra.TensorProduct.quotIdealMapEquivQuotTensor O J).symm.trans φ').trans
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor C J)
    exact Algebra.Smooth.of_equiv ψ
  haveI := hq
  haveI : Algebra.IsSmoothAt R q :=
    isSmoothAt_of_smooth_quotient_pow R (maximalIdeal R) (maximalIdeal.isMaximal R).ne_top C hsm q hqm
  haveI : Algebra.FinitePresentation R C := Algebra.FinitePresentation.of_finiteType.mp hC
  obtain ⟨g, hg, hs⟩ := Algebra.IsSmoothAt.exists_notMem_smooth R q
  exact ⟨g, hg, hs⟩

end GlobalTheory.SmoothAdic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpanningPosDefRelationHarrisTaylorOrderStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_spanning_posDef_relation_harrisTaylorOrder : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p), ∃ (r : ℕ) (e : Fin r → D.Oᵐᵒᵖ) (W : Matrix (Fin r) (Fin r) ℤ) (d : ℕ), Submodule.span ℤ (Set.range e) = ⊤ ∧ ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef ∧ 0 < d ∧ ∑ i, ∑ j, W i j • (e j * MulOpposite.op ((D.star (e i).unop).unop)) = (d : D.Oᵐᵒᵖ) := by
  first | (exact @GlobalTheory.CasimirOrder.exists_posdef_relation) | (exact GlobalTheory.CasimirOrder.exists_posdef_relation) | (intros; apply GlobalTheory.CasimirOrder.exists_posdef_relation  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpecializationClosedInAffineNeighbourhood
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.ClosedPt

lemma exists_max_specializes {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V) (x : Y)
    (hx : x ∈ V) : ∃ N : PrimeSpectrum Γ(Y, V), N.asIdeal.IsMaximal ∧
      (hV.primeIdealOf ⟨x, hx⟩).asIdeal ≤ N.asIdeal ∧ x ⤳ hV.fromSpec N := by
  obtain ⟨N, hN, hle⟩ := Ideal.exists_le_maximal (hV.primeIdealOf ⟨x, hx⟩).asIdeal
    (hV.primeIdealOf ⟨x, hx⟩).isPrime.ne_top
  refine ⟨⟨N, hN.isPrime⟩, hN, hle, ?_⟩
  have h1 : (hV.primeIdealOf ⟨x, hx⟩) ⤳ (⟨N, hN.isPrime⟩ : PrimeSpectrum Γ(Y, V)) :=
    (PrimeSpectrum.le_iff_specializes _ _).mp hle
  have h2 := Specializes.map (f := hV.fromSpec) h1 hV.fromSpec.continuous
  rwa [hV.fromSpec_primeIdealOf] at h2

lemma fromSpec_mem {Y : Scheme.{0}} {V : Y.Opens} (hV : IsAffineOpen V)
    (N : PrimeSpectrum Γ(Y, V)) : hV.fromSpec N ∈ V := by
  have : hV.fromSpec N ∈ Set.range hV.fromSpec := ⟨N, rfl⟩
  rwa [hV.range_fromSpec] at this

theorem exists_closed_point : ∀ (Y : Scheme.{0}) (x : Y), ∃ V : Y.Opens, IsAffineOpen V ∧ ∃ y ∈ V, x ⤳ y ∧ ∀ V₂ : Y.Opens, V₂ ≤ V → IsAffineOpen V₂ → y ∈ V₂ → (∀ y₁ ∈ V₂, y ⤳ y₁ → y₁ = y) ∧ ∃ M : Ideal Γ(Y, V₂), M.IsMaximal ∧ ∀ a : Γ(Y, V₂), a ∈ M ↔ y ∉ Y.basicOpen a := by
  intro Y x
  obtain ⟨V, hV, hx, -⟩ := exists_isAffineOpen_mem_and_subset (X := Y) (x := x) (U := ⊤) trivial
  obtain ⟨N, hN, -, hxN⟩ := exists_max_specializes hV x hx
  refine ⟨V, hV, hV.fromSpec N, fromSpec_mem hV N, hxN, ?_⟩
  intro V₂ hle hV₂ hy
  have hcl : ∀ y₁ ∈ V₂, hV.fromSpec N ⤳ y₁ → y₁ = hV.fromSpec N := by
    intro y₁ hy₁ hs
    have e := hV.fromSpec_primeIdealOf ⟨y₁, hle hy₁⟩
    have hs' : hV.fromSpec N ⤳ hV.fromSpec (hV.primeIdealOf ⟨y₁, hle hy₁⟩) := by
      rw [e]; exact hs
    have h3 : N ⤳ hV.primeIdealOf ⟨y₁, hle hy₁⟩ :=
      (hV.fromSpec.isOpenEmbedding.isInducing.specializes_iff).mp hs'
    have h4 : N ≤ hV.primeIdealOf ⟨y₁, hle hy₁⟩ := (PrimeSpectrum.le_iff_specializes _ _).mpr h3
    have h5 : N = hV.primeIdealOf ⟨y₁, hle hy₁⟩ :=
      PrimeSpectrum.ext (hN.eq_of_le (hV.primeIdealOf ⟨y₁, hle hy₁⟩).isPrime.ne_top h4)
    rw [h5]; exact e.symm
  refine ⟨hcl, (hV₂.primeIdealOf ⟨_, hy⟩).asIdeal, ?_, ?_⟩
  · obtain ⟨N₂, hN₂, -, hs⟩ := exists_max_specializes hV₂ _ hy
    have e := hcl _ (fromSpec_mem hV₂ N₂) hs
    have e2 := hV₂.fromSpec_primeIdealOf ⟨_, hy⟩
    have : N₂ = hV₂.primeIdealOf ⟨_, hy⟩ :=
      hV₂.fromSpec.isOpenEmbedding.injective (e.trans e2.symm)
    rw [← this]; exact hN₂
  · intro a
    have e2 := hV₂.fromSpec_primeIdealOf ⟨_, hy⟩
    have h := hV₂.fromSpec_preimage_basicOpen a
    have h' : hV₂.fromSpec (hV₂.primeIdealOf ⟨_, hy⟩) ∈ Y.basicOpen a ↔
        hV₂.primeIdealOf ⟨_, hy⟩ ∈ PrimeSpectrum.basicOpen a := by
      rw [← h]; rfl
    rw [e2, PrimeSpectrum.mem_basicOpen] at h'
    exact (not_iff_comm.mp h'.symm).symm

end GlobalTheory.ClosedPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSpreadPolarisedAbelianVarietyFinitelyManyP
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.SpreadPolAV

theorem exists_spread : ∀ (F Ω : Type) [Field F] [Field Ω] (em : F →+* Ω) (A : PolAV (Sp Ω)) (I : Type) [Finite I] (y : I → (baseOver (Sp Ω) ⟶ A.A)), ∃ (T : Type) (_ : CommRing T) (_ : IsDomain T) (_ : Algebra F T) (jT : T →+* Ω) (P : PolAV (Sp T)) (φ : A.A.left ⟶ P.A.left) (y₀ : I → (baseOver (Sp T) ⟶ P.A)), Algebra.FiniteType F T ∧ Function.Injective jT ∧ jT.comp (algebraMap F T) = em ∧ IsGrpPullback A.A P.A (spMap jT) φ ∧ LBIso A.L (P.L.pull φ) ∧ ∀ i, (y i).left ≫ φ = spMap jT ≫ (y₀ i).left := by
  classical
  intro F Ω _ _ em A I _ y
  obtain ⟨R, P₀, φ₀, ftR, -, H₀, iso₀⟩ := GlobalTheory.KeyTf.exists_polAV_finiteType_subring Ω A
  have : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have := P₀.smoothDim
  have : Smooth P₀.A.hom := SmoothOfRelativeDimension.smooth P₀.g _
  have : LocallyOfFinitePresentation P₀.A.hom := inferInstance

  have hx : ∀ i, ((y i).left ≫ φ₀) ≫ P₀.A.hom = spMap (algebraMap R Ω) := by
    intro i
    rw [Category.assoc, H₀.1.w, ← Category.assoc, Over.w (y i)]
    exact Category.id_comp _
  obtain ⟨R', y', hR', -, hy'⟩ :=
    GlobalTheory.Spread.exists_fg_points P₀.A.hom (fun i => (y i).left ≫ φ₀) hx ⊥ Subalgebra.fg_bot
  have ftR' : Algebra.FiniteType ℤ R' :=
    Algebra.FiniteType.trans ftR ((Subalgebra.fg_iff_finiteType R').1 hR')
  obtain ⟨s₀, hs₀⟩ := ftR'.out

  letI : Algebra F Ω := em.toAlgebra
  let f₀ : R' →ₐ[ℤ] Ω := R'.val.restrictScalars ℤ
  let T : Subalgebra F Ω := Algebra.adjoin F (f₀ '' (s₀ : Set R'))
  have hTfg : T.FG := ⟨s₀.image f₀, by rw [Finset.coe_image]⟩
  have hR'T : ∀ z ∈ R', z ∈ T := by
    intro z hz
    have h₁ : (⟨z, hz⟩ : R') ∈ Algebra.adjoin ℤ (s₀ : Set R') := by rw [hs₀]; trivial
    have h₂ : f₀ ⟨z, hz⟩ ∈ Algebra.adjoin ℤ (f₀ '' (s₀ : Set R')) := by
      rw [← AlgHom.map_adjoin]
      exact Subalgebra.mem_map.2 ⟨_, h₁, rfl⟩
    have key : Algebra.adjoin ℤ (f₀ '' (s₀ : Set R')) ≤ T.restrictScalars ℤ :=
      Algebra.adjoin_le (Algebra.subset_adjoin (R := F))
    exact key h₂
  have hRT : ∀ r ∈ R, r ∈ T := fun r hr => hR'T r (R'.algebraMap_mem (⟨r, hr⟩ : R))
  let g : R →+* T := R.subtype.codRestrict T fun r => hRT r r.2
  let incl : R' →+* T := R'.val.toRingHom.codRestrict T fun z => hR'T z z.2
  let jT : T →+* Ω := T.val.toRingHom
  have e₁ : spMap jT ≫ spMap g = spMap R.subtype := by
    rw [← Spec.map_comp]; rfl
  have e₂ : spMap jT ≫ spMap incl = spMap R'.val.toRingHom := by
    rw [← Spec.map_comp]; rfl
  have e₃ : spMap incl ≫ spMap (algebraMap R R') = spMap g := by
    rw [← Spec.map_comp]; rfl

  let P : PolAV (Sp T) := GlobalTheory.AmpleSymModel.polPull P₀ (spMap g)
  have Gp : IsGrpPullback P.A P₀.A (spMap g) (pullback.fst P₀.A.hom (spMap g)) :=
    isGrpPullback_pullback P₀.A (spMap g)
  have w : φ₀ ≫ P₀.A.hom = (A.A.hom ≫ spMap jT) ≫ spMap g := by
    rw [Category.assoc, e₁]; exact H₀.1.w
  let φ : A.A.left ⟶ P.A.left := Gp.1.lift _ _ w
  have hφ : φ ≫ pullback.fst P₀.A.hom (spMap g) = φ₀ := Gp.1.lift_fst _ _ w
  have hφ' : φ ≫ P.A.hom = A.A.hom ≫ spMap jT := Gp.1.lift_snd _ _ w
  have hu : ∀ i, (spMap incl ≫ y' i) ≫ P₀.A.hom = 𝟙 (Sp T) ≫ spMap g := by
    intro i
    rw [Category.assoc, (hy' i).1, e₃, Category.id_comp]
  let y₀ : I → (baseOver (Sp T) ⟶ P.A) := fun i =>
    Over.homMk (Gp.1.lift (spMap incl ≫ y' i) (𝟙 _) (hu i)) (Gp.1.lift_snd _ _ (hu i))
  refine ⟨T, inferInstance, inferInstance, inferInstance, jT, P, φ, y₀,
    (Subalgebra.fg_iff_finiteType T).1 hTfg, Subtype.val_injective, RingHom.ext fun _ => rfl,
    Gp.cancel (H₀.congr e₁.symm hφ.symm) hφ',
    GlobalTheory.KeyTf.lbIso_pull_pull_of_comp A.isLB P₀.isLB hφ iso₀, fun i => ?_⟩
  apply Gp.1.hom_ext
  · change (y i).left ≫ φ ≫ pullback.fst P₀.A.hom (spMap g) =
      spMap jT ≫ Gp.1.lift (spMap incl ≫ y' i) (𝟙 _) (hu i) ≫ pullback.fst P₀.A.hom (spMap g)
    rw [hφ, Gp.1.lift_fst, ← Category.assoc, e₂, (hy' i).2]
  · change (y i).left ≫ φ ≫ P.A.hom = spMap jT ≫ Gp.1.lift (spMap incl ≫ y' i) (𝟙 _) (hu i) ≫ P.A.hom
    rw [hφ', Gp.1.lift_snd, ← Category.assoc, Over.w (y i)]
    exact (Category.id_comp _).trans (Category.comp_id _).symm

end GlobalTheory.SpreadPolAV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerivationOfVectorFieldOnOpenStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.Heat GlobalTheory.FormalOrigin
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_stalk_derivation_of_vectorFieldOnOpen : ∀ (X : Scheme.{0}) (W : X.Opens) (d : Fld X), IsField W d → ∀ (x : X), x ∈ W → ∃ δ : Derivation ℤ (X.presheaf.stalk x) (X.presheaf.stalk x), ∀ (O : X.Opens) (hO : x ∈ O), O ≤ W → ∀ f, δ ((X.presheaf.germ O x hO).hom f) = (X.presheaf.germ O x hO).hom (d O f) := by
  first | exact @GlobalTheory.StalkDerField.exists_stalk_derivation | exact GlobalTheory.StalkDerField.exists_stalk_derivation | (intros; apply GlobalTheory.StalkDerField.exists_stalk_derivation <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkLiftFiniteCoverNormalLocal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FiniteLift

theorem exists_retraction {V B : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V] [CommRing B]
    (φ : V →+* B) (hφ : φ.IsIntegral) (ψ : B →+* FractionRing V)
    (h : ψ.comp φ = algebraMap V (FractionRing V)) :
    ∃ s : B →+* V, s.comp φ = RingHom.id V ∧ (algebraMap V (FractionRing V)).comp s = ψ := by
  have hinj : Function.Injective (algebraMap V (FractionRing V)) := IsFractionRing.injective _ _
  have hmem : ∀ b, ψ b ∈ (algebraMap V (FractionRing V)).range := by
    intro b
    obtain ⟨p, hp, hpb⟩ := hφ b
    have : IsIntegral V (ψ b) := ⟨p, hp, by rw [← h, ← Polynomial.hom_eval₂, hpb, map_zero]⟩
    exact IsIntegrallyClosed.algebraMap_eq_of_integral this
  let e := RingEquiv.ofBijective (algebraMap V (FractionRing V)).rangeRestrict
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), RingHom.rangeRestrict_surjective _⟩
  have key : ∀ b, algebraMap V (FractionRing V) (e.symm (ψ.codRestrict _ hmem b)) = ψ b := fun b =>
    congrArg Subtype.val (e.apply_symm_apply (ψ.codRestrict _ hmem b))
  refine ⟨e.symm.toRingHom.comp (ψ.codRestrict _ hmem), ?_, ?_⟩
  · ext v
    apply hinj
    exact (key (φ v)).trans (DFunLike.congr_fun h v)
  · ext b
    exact key b

theorem exists_lift {V : Type} [CommRing V] [IsDomain V] [IsIntegrallyClosed V]
    {X Z : Scheme.{0}} (π : X ⟶ Z) [IsFinite π] (f : Sp V ⟶ Z) (y : Sp (FractionRing V) ⟶ X)
    (h : y ≫ π = jK V ≫ f) : ∃ l : Sp V ⟶ X, l ≫ π = f ∧ jK V ≫ l = y := by
  have : IsAffine (pullback π f) := isAffine_of_isAffineHom (pullback.snd π f)
  let P := pullback π f
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (P.isoSpec.inv ≫ pullback.snd π f)
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (pullback.lift y (jK V) h ≫ P.isoSpec.hom)
  have hfin : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hfin
  have hc : φ ≫ ψ = CommRingCat.ofHom (algebraMap V (FractionRing V)) := by
    apply Spec.map_injective
    rw [Spec.map_comp, hφ, hψ, Category.assoc, Iso.hom_inv_id_assoc]
    exact pullback.lift_snd _ _ _
  obtain ⟨s, hs1, hs2⟩ := exists_retraction φ.hom hfin.to_isIntegral ψ.hom
    (congrArg CommRingCat.Hom.hom hc)
  have h1 : Spec.map (CommRingCat.ofHom s) ≫ P.isoSpec.inv ≫ pullback.snd π f = 𝟙 _ := by
    rw [← hφ, ← Spec.map_comp, ← Spec.map_id]
    congr 1
    exact CommRingCat.hom_ext hs1
  have h2 : jK V ≫ Spec.map (CommRingCat.ofHom s) =
      pullback.lift y (jK V) h ≫ P.isoSpec.hom := by
    rw [← hψ, ← Spec.map_comp]
    congr 1
    exact CommRingCat.hom_ext hs2
  refine ⟨Spec.map (CommRingCat.ofHom s) ≫ P.isoSpec.inv ≫ pullback.fst π f, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% h1]
  · rw [reassoc_of% h2, Iso.hom_inv_id_assoc]
    exact pullback.lift_fst _ _ _

theorem exists_stalk_lift : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsIntegrallyClosed V₁ → ∀ (X Z : Scheme.{0}) (π : X ⟶ Z), IsFinite π → ∀ (f : Sp V₁ ⟶ Z) (yM : Sp (FractionRing V₁) ⟶ X), yM ≫ π = jK V₁ ≫ f → ∃ (z₁ : X) (ev : X.presheaf.stalk z₁ →+* V₁), IsLocalHom ev ∧ spMap ev ≫ X.fromSpecStalk z₁ ≫ π = f ∧ jK V₁ ≫ spMap ev ≫ X.fromSpecStalk z₁ = yM := by
  intro V _ _ _ hV X Z π hπ f y h
  obtain ⟨l, h1, h2⟩ := exists_lift π f y h
  have e : spMap (Scheme.stalkClosedPointTo (R := .of V) l).hom ≫ X.fromSpecStalk _ = l :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk (R := .of V) l
  refine ⟨_, (Scheme.stalkClosedPointTo (R := .of V) l).hom, inferInstance, ?_, ?_⟩
  · rw [reassoc_of% e, h1]
  · rw [e, h2]

end GlobalTheory.FiniteLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorContractionTwoCochainProductStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tangentVector_contraction_twoCochain_product : ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (v : epsR R ⟶ B), IsTangent v → (∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D), ∃ (s : trivAt (pt0 B x) ⟶ thickAt B x) (i : trivAt (ptV v x) ⟶ thickAt B x) (s' : trivAt (pt0 B (spOver φ ≫ x)) ⟶ thickAt B (spOver φ ≫ x)) (i' : trivAt (ptV v (spOver φ ≫ x)) ⟶ thickAt B (spOver φ ≫ x)) (a : trivAt (pt0 B x) ⟶ trivAt (pt0 B (spOver φ ≫ x))) (b : trivAt (ptV v x) ⟶ trivAt (ptV v (spOver φ ≫ x))) (τ : thickAt B x ⟶ thickAt B (spOver φ ≫ x)), (∀ r, s.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i.φ r = r) ∧ (∀ r, s'.φ r = TrivSqZeroExt.inl r) ∧ (∀ r, i'.φ r = r) ∧ (∀ r, a.φ r = φ r) ∧ (∀ r, b.φ r = epsHom φ r) ∧ (∀ r, τ.φ r = epsHom φ r)) ∧ ∀ z : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), ∃ κ : Fn1 A, IsContr z v κ := by
  first | exact @GlobalTheory.PtExt.ContrMor.exists_contr | exact GlobalTheory.PtExt.ContrMor.exists_contr | (intros; apply GlobalTheory.PtExt.ContrMor.exists_contr <;> assumption)
end

