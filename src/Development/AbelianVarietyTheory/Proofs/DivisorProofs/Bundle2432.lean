import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StructureSheafCohomologyPullbackCompCupId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0610
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2240
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0206
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2341
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2355
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2345
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2354
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLocModelIsPrimeOf
import Development.AbelianVarietyTheory.Definitions.Divisors.NotDominatesTopPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowEqOneOfGeometricPointsTorsion
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.TorsGeomPow

theorem pow_eq_one_of_geometric_points : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A], IsAbelianScheme A →
    ∀ (n : ℕ), IsUnit (n : Γ(S, ⊤)) → ∀ (T : Over S) (x : T ⟶ A), x ^ n = 1 → ∀ d : ℕ,
    (∀ (k : Type) [Field k] [IsAlgClosed k] (ξ : Sp k ⟶ T.left),
      ((Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) ≫ x) ^ d = 1) → x ^ d = 1 := by
  intro S A _ hA n hn T x hx d hpt
  obtain ⟨-, -, hZe⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hn
  set P : Over S := pullback (mulN A n) (η : 𝟙_ (Over S) ⟶ A) with hP
  have hPe : Etale P.hom := hZe
  have hxd : (x ^ d) ≫ mulN A n = toUnit T ≫ (η : 𝟙_ (Over S) ⟶ A) := by
    rw [GlobalTheory.GrpTangent.comp_mulN, ← pow_mul, mul_comm, pow_mul, hx, one_pow, CategoryTheory.Hom.one_def]
  have h1 : (1 : T ⟶ A) ≫ mulN A n = toUnit T ≫ (η : 𝟙_ (Over S) ⟶ A) := by
    rw [GlobalTheory.GrpTangent.comp_mulN, one_pow, CategoryTheory.Hom.one_def]
  let y₁ : T ⟶ P := pullback.lift (x ^ d) (toUnit T) hxd
  let u₁ : T ⟶ P := pullback.lift 1 (toUnit T) h1
  have hy : y₁ ≫ pullback.fst (mulN A n) (η : 𝟙_ (Over S) ⟶ A) = x ^ d := pullback.lift_fst _ _ _
  have hu : u₁ ≫ pullback.fst (mulN A n) (η : 𝟙_ (Over S) ⟶ A) = 1 := pullback.lift_fst _ _ _
  have key : ∀ {W : Over S} (f : W ⟶ T), (f ≫ x) ^ d = 1 → f ≫ y₁ = f ≫ u₁ := by
    intro W f hf
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, hy, hu, MonObj.comp_pow, hf, MonObj.comp_one]
    · rw [Category.assoc, Category.assoc, pullback.lift_snd, pullback.lift_snd]
  have hyu : y₁ = u₁ := by
    haveI := hPe
    have hw : y₁.left ≫ P.hom = u₁.left ≫ P.hom := by rw [Over.w, Over.w]
    let l : T.left ⟶ pullback P.hom P.hom := pullback.lift _ _ hw
    have hl1 : l ≫ pullback.fst _ _ = y₁.left := pullback.lift_fst _ _ _
    have hl2 : l ≫ pullback.snd _ _ = u₁.left := pullback.lift_snd _ _ _
    have hs : Function.Surjective (pullback.snd (pullback.diagonal P.hom) l) := by
      intro s
      let k := AlgebraicClosure (T.left.residueField s)
      let ξ : Sp k ⟶ T.left :=
        Spec.map (CommRingCat.ofHom (algebraMap (T.left.residueField s) k)) ≫ T.left.fromSpecResidueField s
      have hξ : ξ ≫ y₁.left = ξ ≫ u₁.left :=
        congrArg CommaMorphism.left (key (Over.homMk ξ rfl : Over.mk (ξ ≫ T.hom) ⟶ T) (hpt k ξ))
      have hq : (ξ ≫ y₁.left) ≫ pullback.diagonal P.hom = ξ ≫ l := by
        apply pullback.hom_ext
        · simp only [Category.assoc]
          rw [pullback.diagonal_fst, Category.comp_id, hl1]
        · simp only [Category.assoc]
          rw [pullback.diagonal_snd, Category.comp_id, hl2, hξ]
      refine ⟨pullback.lift _ _ hq (IsLocalRing.closedPoint k), ?_⟩
      have e : (pullback.lift _ _ hq ≫ pullback.snd (pullback.diagonal P.hom) l) (IsLocalRing.closedPoint k) =
          ξ (IsLocalRing.closedPoint k) := by rw [Limits.pullback.lift_snd]
      refine (Eq.trans ?_ e).trans ?_
      · rfl
      exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply s _)
    have : Epi (pullback.snd (pullback.diagonal P.hom) l).base :=
      (TopCat.epi_iff_surjective _).2 hs
    have : IsIso (pullback.snd (pullback.diagonal P.hom) l) := IsOpenImmersion.isIso _
    have hl : l = inv (pullback.snd (pullback.diagonal P.hom) l) ≫ pullback.fst _ _ ≫
        pullback.diagonal P.hom := by
      rw [pullback.condition, IsIso.inv_hom_id_assoc]
    apply Over.OverMorphism.ext
    rw [← hl1, ← hl2, hl]
    simp
  rw [← hy, hyu, hu]

end GlobalTheory.TorsGeomPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageRegSet
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

set_option autoImplicit false

namespace GlobalTheory.Desc.GaussPt

variable {Y X : Scheme.{0}} [IsIntegral Y] [IsIntegral X]

theorem theta_stalk {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (y : Y)
    (a : X.presheaf.stalk (π y)) :
    θ (algebraMap _ X.functionField a) = algebraMap _ Y.functionField (π.stalkMap y a) := by
  obtain ⟨l, h₁, h₂⟩ := h
  rw [Category.comp_id] at h₁
  subst h₁
  let sY := Y.presheaf.stalkSpecializes (genericPoint_specializes y)
  let sX := X.presheaf.stalkSpecializes (genericPoint_specializes (π y))
  have e₁ : Spec.map sY ≫ Y.fromSpecStalk y = gp Y :=
    Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
  let t : X.presheaf.stalk (genericPoint X) ⟶ Y.presheaf.stalk (genericPoint Y) := CommRingCat.ofHom θ
  have e₂ : π.stalkMap y ≫ sY = sX ≫ t := by
    apply Spec.map_injective
    rw [← cancel_mono (X.fromSpecStalk (π y)), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc, e₁, h₂, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl
  exact (congrArg (fun f => CommRingCat.Hom.hom f a) e₂).symm

theorem theta_fnOf {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ)
    (U : X.Opens) (hU : genericPoint X ∈ U) (hU' : genericPoint Y ∈ π ⁻¹ᵁ U) (s : Γ(X, U)) :
    θ (fnOf U hU s) = fnOf (π ⁻¹ᵁ U) hU' (π.app U s) := by
  have hU'' : π (genericPoint Y) ∈ U := hU'
  rw [← algebraMap_germ (x := π (genericPoint Y)) hU'' s, theta_stalk h,
    Scheme.Hom.germ_stalkMap_apply]
  exact algebraMap_germ hU' _

theorem regAt_theta {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (y : Y)
    {u : X.functionField} (hu : RegAt (π y) u) : RegAt y (θ u) := by
  obtain ⟨a, rfl⟩ := hu
  exact ⟨_, (theta_stalk h y a).symm⟩

theorem unitAt_theta {π : Y ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF (𝟙 _) π θ) (y : Y)
    {u : X.functionField} (hu : UnitAt (π y) u) : UnitAt y (θ u) := by
  obtain ⟨a, ha, rfl⟩ := hu
  exact ⟨_, ha.map _, (theta_stalk h y a).symm⟩

theorem preimage_regSet {π : Y ⟶ X} [Flat π] {θ : X.functionField →+* Y.functionField}
    (h : PFF (𝟙 _) π θ) (y : Y) : θ ⁻¹' (regSet y) = regSet (π y) := by
  ext u
  refine ⟨fun ⟨c, hc⟩ => ?_, fun hu => regAt_theta h y hu⟩
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := X.presheaf.stalk (π y)) u
  have hb0 : algebraMap _ X.functionField b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  letI := (π.stalkMap y).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (π y)) (Y.presheaf.stalk y) := Flat.stalkMap π y
  have : IsLocalHom (algebraMap (X.presheaf.stalk (π y)) (Y.presheaf.stalk y)) :=
    inferInstanceAs (IsLocalHom (π.stalkMap y).hom)
  have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := X.presheaf.stalk (π y))
    (B := Y.presheaf.stalk y)
  have e : π.stalkMap y a = c * π.stalkMap y b := by
    apply IsFractionRing.injective (Y.presheaf.stalk y) Y.functionField
    rw [map_mul, hc, ← theta_stalk h, ← theta_stalk h, ← map_mul, div_mul_cancel₀ _ hb0]
  have hm : a ∈ Ideal.span {b} := by
    rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := Y.presheaf.stalk y) (Ideal.span {b}),
      Ideal.mem_comap, Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton']
    exact ⟨c, e.symm⟩
  obtain ⟨d, rfl⟩ := Ideal.mem_span_singleton'.1 hm
  exact ⟨d, by rw [map_mul, mul_div_cancel_right₀ _ hb0]⟩

theorem spMap_cst {R : Type} [CommRing R] (p : X ⟶ Sp R) : spMap (GlobalTheory.Desc.cst p) = gp X ≫ p := by
  have h : p = X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ p.appTop) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ← Spec.map_comp]
    simp
  conv_rhs => rw [h, gp, ← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp]
  rfl

theorem comp_cst {V : Scheme.{0}} {R R₁ : Type} [CommRing R] [CommRing R₁] {ρ : R →+* R₁} {p : X ⟶ Sp R}
    {q : Y ⟶ Sp R₁} {i : V ⟶ Y} {φ : V ⟶ X} {θ : X.functionField →+* Y.functionField} (h : PFF i φ θ)
    (w : φ ≫ p = (i ≫ q) ≫ spMap ρ) : θ.comp (GlobalTheory.Desc.cst p) = (GlobalTheory.Desc.cst q).comp ρ := by
  obtain ⟨l, h₁, h₂⟩ := h
  have : spMap (θ.comp (GlobalTheory.Desc.cst p)) = spMap ((GlobalTheory.Desc.cst q).comp ρ) := by
    have e1 : spMap (θ.comp (GlobalTheory.Desc.cst p)) = spMap θ ≫ spMap (GlobalTheory.Desc.cst p) := by
      rw [← Spec.map_comp]; rfl
    have e2 : spMap ((GlobalTheory.Desc.cst q).comp ρ) = spMap (GlobalTheory.Desc.cst q) ≫ spMap ρ := by
      rw [← Spec.map_comp]; rfl
    rw [e1, e2, spMap_cst, spMap_cst, ← Category.assoc, ← h₂, ← h₁]
    simp only [Category.assoc, w]
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)

theorem regAt_cst {R : Type} [CommRing R] (p : X ⟶ Sp R) (x : X) (r : R) : RegAt x (GlobalTheory.Desc.cst p r) :=
  regAt_fnOf (U := ⊤) trivial trivial _

theorem unitAt_cst_iff {R : Type} [CommRing R] (p : X ⟶ Sp R) (x : X) (r : R) :
    UnitAt x (GlobalTheory.Desc.cst p r) ↔ r ∉ (p x).asIdeal := by
  refine (unitAt_fnOf_iff (U := ⊤) trivial trivial _).trans ?_
  change x ∈ X.basicOpen (p.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)) ↔ _
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  rfl

end GlobalTheory.Desc.GaussPt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimOfAxes
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.AbCoh.PrimForm

variable {R : Type} [CommRing R]

theorem pF_comp {A B C : Over (Sp R)} (f : B ⟶ C) (g : A ⟶ B) (a : GlobForm C.hom) :
    pF g (pF f a) = pF (g ≫ f) a :=
  (GlobalTheory.AbCoh.pull_comp_cup_id.1 R R C.left B.left C.hom B.hom (RingHom.id R) f.left (ovw f) R A.left A.hom
    (RingHom.id R) g.left (ovw g) (RingHom.id R) (g ≫ f).left (ovw (g ≫ f)) (Over.comp_left _ _ _ g f) (fun _ ↦ rfl)).2.2.1 a

theorem pF_id (A : Over (Sp R)) (a : GlobForm A.hom) : pF (𝟙 A) a = a :=
  (GlobalTheory.AbCoh.pull_comp_cup_id.2.2 R A).2.2.1 a

theorem pF_unit {A B : Over (Sp R)} (f : 𝟙_ (Over (Sp R)) ⟶ A) (a : GlobForm A.hom) :
    pF (toUnit B ≫ f) a = 0 := by
  rw [← pF_comp]
  haveI := (GlobalTheory.AbCoh.Vanish.main.2 R).1
  rw [Subsingleton.elim (pF f a) 0, map_zero]

theorem prim_of_axes (A : Over (Sp R)) [GrpObj A]
    (H : ∀ y : GlobForm (A ⊗ A).hom, pF (lift (𝟙 A) (toUnit A ≫ η[A])) y = 0 →
      pF (lift (toUnit A ≫ η[A]) (𝟙 A)) y = 0 → y = 0) : PrimF A := by
  intro x
  have e := H (pF μ[A] x - pF (fst A A) x - pF (snd A A) x) ?_ ?_
  · exact (sub_eq_zero.1 ((sub_sub _ _ _).symm.trans e))
  · rw [map_sub, map_sub, pF_comp, pF_comp, pF_comp, lift_fst, lift_snd, lift_comp_one_right, pF_id, pF_unit,
      sub_self, sub_zero]
  · rw [map_sub, map_sub, pF_comp, pF_comp, pF_comp, lift_fst, lift_snd, lift_comp_one_left, pF_id, pF_unit,
      sub_zero, sub_self]

end GlobalTheory.AbCoh.PrimForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeDivisorLiftAlongEtaleMap
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.EtaleKlt

theorem divOver_lift : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] [IsLocallyNoetherian M] [IsLocallyNoetherian W] (p : W ⟶ Sp ℂ) (f : M ⟶ W) [IsDominant f] (n : ℕ) [SmoothOfRelativeDimension n p] [SmoothOfRelativeDimension n (f ≫ p)] (U : M.Opens), Etale (U.ι ≫ f) → ∀ y ∈ U, ∀ E : DivOver p, E.Through (f y) → ∃ E' : DivOver (f ≫ p), E'.Through y ∧ (∀ g : W.functionFieldˣ, E'.ord (Units.map (functionFieldMap f).toMonoidHom g) = E.ord g) ∧ ∀ η : RatForms p n, η ≠ 0 → E'.formOrd (GlobalTheory.EtaleKlt.ratPull p f n η) = E.formOrd η := by
  intro M W _ _ _ _ p f _ n _ _ U hU y hy E hE
  obtain ⟨hfl, hfe, hft⟩ := GlobalTheory.T.stalkMap_flat_formallyEtale_essFiniteType_of_etale_open M W f U hU y hy
  obtain ⟨V', h, hdvr, hS, hcomap, het, hess⟩ := GlobalTheory.T.exists_dvr_extension_of_essentially_etale_local (K := W.functionField)
    (K' := M.functionField) (R := W.presheaf.stalk (f y)) (S := M.presheaf.stalk y)
    (functionFieldMap f) (f.stalkMap y).hom hfl hfe hft
    (RingHom.ext fun a => functionFieldMap_algebraMap f y a) E.ring E.dvr (fun a => hE _ ⟨a, rfl⟩)
  have hc : ∀ a, Cartier.constFn (f ≫ p) a ∈ V' := fun a => by
    rw [← functionFieldMap_comp_constFn p f]
    exact h _ (E.const_mem a)
  have hess' : ((Cartier.constFn (f ≫ p)).codRestrict V' hc).EssFiniteType := by
    have e : (Cartier.constFn (f ≫ p)).codRestrict V' hc =
        ((functionFieldMap f).restrict E.ring V' h).comp E.const := by
      ext a
      simp [DivOver.const, ← functionFieldMap_comp_constFn p f]
    rw [e]
    exact E.essFiniteType.comp hess
  let E' : DivOver (f ≫ p) := ⟨V', hc, hdvr, hess'⟩
  haveI := SmoothOfRelativeDimension.smooth n p
  have hdim := GlobalTheory.NadelApp.topologicalKrullDim_eq_of_smooth W p n
  have hord := GlobalTheory.T.ordFrac_functionFieldMap_of_essentiallyEtale M W p f E E' h hcomap het hess
  refine ⟨E', fun g hg => ?_, hord, fun η hη => GlobalTheory.T.topFormOrder_rationalPullback_of_essentiallyEtale M W p f n hdim E E' h het hord η hη⟩
  obtain ⟨a, rfl⟩ := hg
  exact hS a

end GlobalTheory.EtaleKlt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeEqOfClassicalPointSameCentre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem natCast_prime_not_isUnit_stalk (X : Scheme.{0}) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ X) :
    ¬ IsUnit ((p : ℕ) : X.presheaf.stalk (y (cPt p))) := by
  intro hu
  have h := hu.map (Scheme.stalkClosedPointTo y).hom
  rw [map_natCast] at h
  refine (not_isUnit_OO_iff ((p : ℕ) : OO p)).2 ?_ h
  have e : (((p : ℕ) : OO p) : PadicAlgCl p) = algebraMap ℚ_[p] (PadicAlgCl p) ((p : ℕ) : ℚ_[p]) := by simp
  rw [e, PadicAlgCl.norm_extends]
  exact Padic.norm_natCast_lt_one_iff.2 dvd_rfl

theorem dvd_of_not_isUnit_stalk (X : Scheme.{0}) (q : ℕ) [Fact q.Prime] (y : Sp (OO q) ⟶ X) (n : ℕ)
    (h : ¬ IsUnit ((n : ℕ) : X.presheaf.stalk (y (cPt q)))) : q ∣ n := by
  have h1 : ¬ IsUnit ((Scheme.stalkClosedPointTo y).hom (n : X.presheaf.stalk (y (cPt q)))) :=
    fun hu => h ((isUnit_map_iff (Scheme.stalkClosedPointTo y).hom _).1 hu)
  rw [map_natCast, not_isUnit_OO_iff] at h1
  have e : (((n : ℕ) : OO q) : PadicAlgCl q) = algebraMap ℚ_[q] (PadicAlgCl q) ((n : ℕ) : ℚ_[q]) := by simp
  rw [e, PadicAlgCl.norm_extends] at h1
  exact Padic.norm_natCast_lt_one_iff.1 h1

theorem eq_of_cPt_eq : ∀ (X : Scheme.{0}) (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (y : Sp (OO p) ⟶ X)
    (y' : Sp (OO q) ⟶ X), y (cPt p) = y' (cPt q) → p = q := by
  intro X p q hp hq y y' h
  have h1 := natCast_prime_not_isUnit_stalk X p y
  have h2 : ¬ IsUnit ((p : ℕ) : X.presheaf.stalk (y' (cPt q))) := by
    rw [← h]; exact h1
  have h3 := dvd_of_not_isUnit_stalk X q y' p h2
  exact ((Nat.prime_dvd_prime_iff_eq hq.out hp.out).1 h3).symm

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdMapPairTimesIdentitySnd
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

variable {S : Scheme.{0}}

def pmap2 {A A' : Over S} (q : A ⟶ A') (T : Over S) : A ⊗ (A ⊗ T) ⟶ A' ⊗ (A' ⊗ T) :=
  lift (fst A (A ⊗ T) ≫ q) (snd A (A ⊗ T) ≫ pmap q T)

def ptFst (A T : Over S) : A ⊗ (A ⊗ T) ⟶ A ⊗ T := lift (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T)

def ptSnd (A T : Over S) : A ⊗ (A ⊗ T) ⟶ A ⊗ T := lift (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)

def ptMul (A T : Over S) [MonObj A] : A ⊗ (A ⊗ T) ⟶ A ⊗ T :=
  lift (fst A (A ⊗ T) * (snd A (A ⊗ T) ≫ fst A T)) (snd A (A ⊗ T) ≫ snd A T)

def addBundle {A T : Over S} [MonObj A] (M : LB (A ⊗ T).left) : LB (A ⊗ (A ⊗ T)).left :=
  LB.div (tens (ev M (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T))
      (ev M (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)))
    (ev M (fst A (A ⊗ T) * (snd A (A ⊗ T) ≫ fst A T)) (snd A (A ⊗ T) ≫ snd A T))

theorem preimage_le_of_comp {X Y Z W : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ W} {f' : X ⟶ Z} {g' : Z ⟶ W}
    (h : f ≫ g = f' ≫ g') (U : W.Opens) : f ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ f' ⁻¹ᵁ (g' ⁻¹ᵁ U) := by
  intro x hx
  have e : g.base (f.base x) = g'.base (f'.base x) := by
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  show g'.base (f'.base x) ∈ U
  rw [← e]
  exact hx

theorem prodMapPairTimesIdentity_fst {A A' : Over S} (q : A ⟶ A') (T : Over S) :
    (pmap2 q T).left ≫ (lift (fst A' (A' ⊗ T)) (snd A' (A' ⊗ T) ≫ snd A' T)).left =
      (ptFst A T).left ≫ (pmap q T).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp [pmap2, ptFst, pmap]

theorem prodMapPairTimesIdentity_snd {A A' : Over S} (q : A ⟶ A') (T : Over S) :
    (pmap2 q T).left ≫ (lift (snd A' (A' ⊗ T) ≫ fst A' T) (snd A' (A' ⊗ T) ≫ snd A' T)).left =
      (ptSnd A T).left ≫ (pmap q T).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp [pmap2, ptSnd, pmap]

theorem prodMapPairTimesIdentity_mul {A A' : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (T : Over S) :
    (pmap2 q T).left ≫ (lift (fst A' (A' ⊗ T) * (snd A' (A' ⊗ T) ≫ fst A' T)) (snd A' (A' ⊗ T) ≫ snd A' T)).left =
      (ptMul A T).left ≫ (pmap q T).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp [pmap2, ptMul, pmap, MonObj.comp_mul, MonObj.mul_comp]

theorem addGen_le₁ {A A' T : Over S} [MonObj A'] (q : A ⟶ A') (M : LB (A' ⊗ T).left) (k : (addBundle M).ι) :
    (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k ≤ (ptFst A T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U (k.1.1 PUnit.unit)) := by
  refine le_trans ?_ (preimage_le_of_comp (prodMapPairTimesIdentity_fst q T) _)
  intro x hx
  exact LB.wchart_le M _ k.1.1 PUnit.unit hx.1.1

theorem addGen_le₂ {A A' T : Over S} [MonObj A'] (q : A ⟶ A') (M : LB (A' ⊗ T).left) (k : (addBundle M).ι) :
    (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k ≤ (ptSnd A T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U (k.1.2 PUnit.unit)) := by
  refine le_trans ?_ (preimage_le_of_comp (prodMapPairTimesIdentity_snd q T) _)
  intro x hx
  exact LB.wchart_le M _ k.1.2 PUnit.unit hx.1.2

theorem addGen_le₃ {A A' T : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (M : LB (A' ⊗ T).left)
    (k : (addBundle M).ι) :
    (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k ≤ (ptMul A T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U (k.2 PUnit.unit)) := by
  refine le_trans ?_ (preimage_le_of_comp (prodMapPairTimesIdentity_mul q T) _)
  intro x hx
  exact LB.wchart_le M _ k.2 PUnit.unit hx.2

def addGen {A A' T : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (M : LB (A' ⊗ T).left)
    (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ) (k : (addBundle M).ι) :
    Γ((A ⊗ (A ⊗ T)).left, (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k)ˣ :=
  res (addGen_le₁ q M k) (pullU (ptFst A T).left _ (e (k.1.1 PUnit.unit))) *
    res (addGen_le₂ q M k) (pullU (ptSnd A T).left _ (e (k.1.2 PUnit.unit))) *
    (res (addGen_le₃ q M k) (pullU (ptMul A T).left _ (e (k.2 PUnit.unit))))⁻¹

end GlobalTheory.CharKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSmoothGeomConnectedDescendFiniteSurjectiveStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.properSmoothGeomConnected_descend_finite_surjective : ∀ (X X' Y Y' : Scheme.{0}) (f : X ⟶ Y) (f' : X' ⟶ Y') (p : X' ⟶ X) (q : Y' ⟶ Y) (g : ℕ), IsPullback p f' f q → IsFinite q → Surjective q → SmoothOfRelativeDimension g f → GlobalTheory.DualCon.Good g f' → GlobalTheory.DualCon.Good g f := by
  first | exact @GlobalTheory.DualCon.good_of_isPullback_finite_surjective | exact GlobalTheory.DualCon.good_of_isPullback_finite_surjective | (intros; apply GlobalTheory.DualCon.good_of_isPullback_finite_surjective <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProperSmoothGeomConnectedSigmaDescDisjointCoverStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.properSmoothGeomConnected_sigmaDesc_disjoint_cover : ∀ {X : Scheme.{0}} {κ : Type} [Finite κ] (V : κ → X.Opens), (⨆ i, V i = ⊤) → (Pairwise fun i i' => Disjoint (V i) (V i')) → ∀ {B : κ → Scheme.{0}} (f : ∀ i, B i ⟶ (V i).toScheme) (g : ℕ), (∀ i, Good g (f i)) → Good g (Sigma.desc fun i => f i ≫ (V i).ι) := by
  first | exact @GlobalTheory.DualCon.good_sigmaDesc_of_disjoint_cover | exact GlobalTheory.DualCon.good_sigmaDesc_of_disjoint_cover | (intros; apply GlobalTheory.DualCon.good_sigmaDesc_of_disjoint_cover <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullInvSymmIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymLB

theorem pull_inv_symm_iso : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → LBIso ((LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GrpObj.inv : G ⟶ G).left] ![1, 1]).pull (GrpObj.inv : G ⟶ G).left) (LB.LinComb L (K := Fin 2) ![𝟙 G.left, (GrpObj.inv : G ⟶ G).left] ![1, 1]) := by
  intro S G _ L hL
  have h₁ := LB.isLB_linComb hL (K := Fin 2) ![𝟙 G.left, (GrpObj.inv : G ⟶ G).left] ![1, 1]
  refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB h₁ _) h₁).1 ?_
  rw [GlobalTheory.CechPic.cls_pull h₁, GlobalTheory.CechPic.cls_linComb hL _ _ h₁]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, map_add,
    ← GlobalTheory.CechPic.pull_comp]
  rw [← Over.comp_left, GrpObj.inv_comp_inv, Over.id_left, Category.comp_id, add_comm]

end GlobalTheory.SymLB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullUInjectiveOfFlatSurjective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.EigenDescent
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EigenDescent

theorem app_injective_of_flat_surjective {X Y : Scheme.{0}} (π : X ⟶ Y) [Flat π] [Surjective π]
    (V : Y.Opens) : Function.Injective (π.app V) := by
  intro s t h
  apply TopCat.Presheaf.section_ext Y.sheaf V s t
  intro y hy
  obtain ⟨x, rfl⟩ := π.surjective y
  have hinj : Function.Injective (π.stalkMap x) := by
    have hf := Flat.stalkMap π x
    algebraize [(π.stalkMap x).hom]
    have : IsLocalHom (algebraMap (Y.presheaf.stalk (π x)) (X.presheaf.stalk x)) :=
      inferInstanceAs (IsLocalHom (π.stalkMap x).hom)
    have := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := Y.presheaf.stalk (π x))
      (B := X.presheaf.stalk x)
    exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (π x)) (X.presheaf.stalk x)
  apply hinj
  change π.stalkMap x (Y.presheaf.germ V (π x) hy s) = π.stalkMap x (Y.presheaf.germ V (π x) hy t)
  rw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply, h]

theorem pullU_injective_of_flat_surjective : ∀ {X Y : Scheme.{0}} (π : X ⟶ Y), Flat π → Surjective π →
    ∀ V : Y.Opens, Function.Injective (pullU π V) := by
  intro X Y π _ _ V u v h
  exact Units.ext (app_injective_of_flat_surjective π V (congrArg Units.val h))

end GlobalTheory.EigenDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalResidueFieldClosedPointProjectiveComplexStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep GlobalTheory.FieldPair
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalResidueField_closedPoint_projectiveComplex : ∀ (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ x : X,
    IsClosed ({x} : Set X) → RatRes (Cartier.constFn p) (locRing x) := by
  first | exact @GlobalTheory.FieldPair.ratRes_locRing_of_isClosed_of_isProjOver | exact GlobalTheory.FieldPair.ratRes_locRing_of_isClosed_of_isProjOver | (intros; apply GlobalTheory.FieldPair.ratRes_locRing_of_isClosed_of_isProjOver <;> assumption)
end

