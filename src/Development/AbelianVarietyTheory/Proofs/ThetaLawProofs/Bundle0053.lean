import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.Bundle0001
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0018
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0044
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0022
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0169
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGrpSchemeDescendsToFgSubring
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricLinearisationSquareDiagonalBundle
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KoszulSectionsExactAlgClosedPolarisedAV
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsProjectiveAbelianModel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open scoped CategoryTheory.Obj

namespace GlobalTheory.KeyTf

theorem exists_isGrpPullback_of_le {S : Type} [CommRing S] {R₀ R₁ : Subring S} (h : R₀ ≤ R₁) (A : Over (Sp S))
    [GrpObj A] (A₀ : Over (Sp R₀)) [GrpObj A₀] (φ : A.left ⟶ A₀.left)
    (H : IsGrpPullback A A₀ (spMap R₀.subtype) φ) :
    ∃ φ₁ : A.left ⟶ ((Over.pullback (spMap (Subring.inclusion h))).obj A₀).left,
      IsGrpPullback A ((Over.pullback (spMap (Subring.inclusion h))).obj A₀) (spMap R₁.subtype) φ₁ := by
  have e : spMap R₀.subtype = spMap R₁.subtype ≫ spMap (Subring.inclusion h) :=
    spMap_comp (Subring.inclusion h) R₁.subtype
  have hp := isGrpPullback_pullback A₀ (spMap (Subring.inclusion h))
  refine ⟨hp.1.lift φ (A.hom ≫ spMap R₁.subtype) (by rw [H.1.w, e, Category.assoc]), ?_⟩
  exact IsGrpPullback.cancel hp (H.congr e (hp.1.lift_fst _ _ _).symm) (hp.1.lift_snd _ _ _)

theorem exists_projective_abelian_model : ∀ (S : Type) [CommRing S] [IsDomain S] [IsLocalRing S] (P : Out.PolAV (Sp S)), ∃ (R : Subring S) (A₀ : Over (Sp R)) (_ : GrpObj A₀) (φ : P.A.left ⟶ A₀.left), Algebra.FiniteType ℤ R ∧ IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension P.g A₀.hom ∧ IsProjOver A₀.hom ∧ IsGrpPullback P.A A₀ (spMap R.subtype) φ := by
  intro S _ _ _ P
  have hc := P.isAb.comm
  have hs := P.isAb.smooth
  have hpr := P.isAb.proper
  have hg := P.isAb.geomConnected
  obtain ⟨R₀, A₀, _, _, φ₀, -, hft₀, hs₀, hsep₀, hqc₀, H₀⟩ :=
    GlobalTheory.smooth_grpScheme_descends_to_fg_subring S P.A ∅ hs inferInstance inferInstance
  obtain ⟨F, hF⟩ := GlobalTheory.T.isProjOver_descends_to_subring' S R₀ _ _ P.A.hom A₀.hom φ₀ H₀.1 (GlobalTheory.ProjSpace.isProjOver_polAV P)
  obtain ⟨R₁, h₀₁, hF₁, hft₁⟩ := exists_finiteType_subring_adjoin S R₀ F hft₀
  obtain ⟨A₁, _, _, φ₁, hp₁, hs₁, H₁⟩ : ∃ (A₁ : Over (Sp R₁)) (_ : GrpObj A₁) (_ : IsCommMonObj A₁)
      (φ₁ : P.A.left ⟶ A₁.left), IsProjOver A₁.hom ∧ Smooth A₁.hom ∧ IsGrpPullback P.A A₁ (spMap R₁.subtype) φ₁ := by
    obtain ⟨φ₁, H₁⟩ := exists_isGrpPullback_of_le h₀₁ P.A A₀ φ₀ H₀
    exact ⟨_, _, inferInstance, φ₁, hF R₁ h₀₁ hF₁ _ _ _ (IsPullback.of_hasPullback _ _),
      inferInstanceAs (Smooth (pullback.snd _ _)), H₁⟩
  let κ := IsLocalRing.residue S
  have e₁ : spMap (κ.comp R₁.subtype) = spMap κ ≫ spMap R₁.subtype := spMap_comp _ _
  have hfib : GeometricallyConnected (pullback.snd A₁.hom (spMap (κ.comp R₁.subtype))) := by
    have Q := IsPullback.of_hasPullback A₁.hom (spMap (κ.comp R₁.subtype))
    let l := H₁.1.lift (pullback.fst A₁.hom (spMap (κ.comp R₁.subtype))) (pullback.snd _ _ ≫ spMap κ)
      (by rw [Q.w, e₁, Category.assoc])
    have Q' : IsPullback l (pullback.snd A₁.hom (spMap (κ.comp R₁.subtype))) P.A.hom (spMap κ) :=
      IsPullback.of_right (by rw [H₁.1.lift_fst, ← e₁]; exact Q) (H₁.1.lift_snd _ _ _) H₁.1
    exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) Q' hg
  obtain ⟨f, hf, hconn⟩ := GlobalTheory.T.geometricallyConnected_open_condition_smooth_projective R₁ _ A₁.hom _ (κ.comp R₁.subtype) hp₁ hs₁ hfib
  obtain ⟨u, hu⟩ : IsUnit (f : S) := (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hf
  obtain ⟨R₂, h₁₂, hF₂, hft₂⟩ := exists_finiteType_subring_adjoin S R₁ {((u⁻¹ : Sˣ) : S)} hft₁
  obtain ⟨φ₂, H₂⟩ := exists_isGrpPullback_of_le h₁₂ P.A A₁ φ₁ H₁
  have hunit : IsUnit (Subring.inclusion h₁₂ f) :=
    IsUnit.of_mul_eq_one (⟨((u⁻¹ : Sˣ) : S), hF₂ (by simp)⟩ : R₂) (Subtype.ext (by
      show (f : S) * _ = 1
      rw [← hu]; exact u.mul_inv))
  have hp₂ : IsProjOver ((Over.pullback (spMap (Subring.inclusion h₁₂))).obj A₁).hom :=
    GlobalTheory.ProjSpace.isProjOver_pullback_snd _ hp₁
  have hab : IsAbelianScheme ((Over.pullback (spMap (Subring.inclusion h₁₂))).obj A₁) :=
    ⟨inferInstance, inferInstanceAs (Smooth (pullback.snd _ _)), projProper _ _ _ hp₂, hconn R₂ _ hunit⟩
  refine ⟨R₂, _, inferInstance, φ₂, hft₂, hab, ?_, hp₂, H₂⟩
  have e₂ : spMap (κ.comp R₂.subtype) = spMap κ ≫ spMap R₂.subtype := spMap_comp _ _
  refine GlobalTheory.CM.smoothOfRelativeDimension_of_fibre R₂ _ (κ.comp R₂.subtype) _ _
    (pullback.fst P.A.hom (spMap κ) ≫ φ₂) (pullback.snd P.A.hom (spMap κ)) P.g hab ?_ ?_
  · rw [e₂]; exact (IsPullback.of_hasPullback _ _).paste_horiz H₂.1
  · exact (smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback (IsPullback.of_hasPullback _ _)
      P.smoothDim

end GlobalTheory.KeyTf
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsSymmetricLinearisationSquareDiagonalBundleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_linearisation_square_diagonalBundle : Out.Laws → ∀ (h k : ℕ) (o : Type) [CommRing o] (ζ : o) (R : Type) [CommRing R] [Algebra ℚ R] [IsNoetherianRing R] (β : o →+* R) (c : SiegPre h k ζ (spMap β)) (g : ℕ) (i₀ : (Multiplicative (Fin (2 * g) → ZMod 2)) →* (𝟙_ (Over (Sp R)) ⟶ c.A)), c.Principal → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁), (Module.Finite R R₁ ∧ Algebra.Etale R R₁ ∧ Module.FaithfullyFlat R R₁) ∧ ∀ (A : Over (Sp R₁)) [GrpObj A] [IsCommMonObj A] (φ : A.left ⟶ c.A.left) (i : (Multiplicative (Fin (2 * g) → ZMod 2)) →* (𝟙_ (Over (Sp R₁)) ⟶ A)) (L : LB A.left), IsGrpPullback A c.A (spMap (algebraMap R R₁)) φ → (∀ a, (i a).left ≫ φ = spMap (algebraMap R R₁) ≫ (i₀ a).left) → L = lbPow (c.diag.pull φ) 2 → ∃ (u : ∀ c, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ((toUnit A ≫ i c) * 𝟙 A).left] ![1, -1])) (j : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, (GrpObj.inv : A ⟶ A).left] ![1, -1])), (∀ c, (u c).IsGen) ∧ (∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c')) (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') ((toUnit A ≫ i c) * 𝟙 A).left))) ∧ j.IsGen ∧ ∀ c (T : Over (Sp R₁)) (x : T ⟶ A) (z : T.left) (J), Good L z J → val (u c) x.left z J * val j ((toUnit T ≫ i c) * x).left z J = val j x.left z J * val (u c⁻¹) (x⁻¹).left z J := by
  first | exact @GlobalTheory.SymLin.main | exact GlobalTheory.SymLin.main | (intros; apply GlobalTheory.SymLin.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KoszulSectionsExactAlgClosedPolarisedAVStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
open GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.koszul_sections_exact_algClosed_polarisedAV : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n l : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (m) (c : x.P.A.left → x.P.L.ι), 1 ≤ n → x.P.g * n < l → FinZ x s → (∀ j ≤ x.P.g, IsBasis x (b j)) → IsMul x l s b m → (∀ y, y ∈ x.P.L.U (c y)) → (∀ v : KIx x.P.g 0 (fun j => (l - j * n) ^ x.P.g) → K, (kosD m (fun _ => 0)).mulVec v = 0 → ∃ w, ∀ p, p.1 ≠ ∅ → v (.inl p) = (kosD (d := 0) m (fun _ => 0)).mulVec w (.inl p)) ∧ (∀ a : ∀ y : x.P.A.left, x.P.A.left.presheaf.stalk y, ∃ sg : RR x l, ∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) → gs (𝟙 _) y (x.P.L.U (c y)) (sg.f (c y)) - a y ∈ Ideal.span (Set.range fun i => gs (𝟙 _) y (x.P.L.U (c y)) ((s i).f (c y)))) ∧ ∀ sg : RR x l, (∀ y, (∀ i, y ∉ Out.nonzeroLocus (s i)) → gs (𝟙 _) y (x.P.L.U (c y)) (sg.f (c y)) ∈ Ideal.span (Set.range fun i => gs (𝟙 _) y (x.P.L.U (c y)) ((s i).f (c y)))) → ∃ ta : Fin x.P.g → RR x (l - 1 * n), ∀ c', (show Γ(x.P.A.left, x.P.L.U c') from sg.f c') = ∑ i, (show Γ(x.P.A.left, x.P.L.U c') from (s i).f c') * (show Γ(x.P.A.left, x.P.L.U c') from (ta i).f c') := by
  first | exact @GlobalTheory.koszul_sections_exact_field | exact GlobalTheory.koszul_sections_exact_field | (intros; apply GlobalTheory.koszul_sections_exact_field <;> assumption)
end

