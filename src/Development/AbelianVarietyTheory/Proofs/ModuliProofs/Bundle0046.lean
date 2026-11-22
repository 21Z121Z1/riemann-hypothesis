import Mathlib
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientInclusionsEtaleOpenImmersion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0034
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionField
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0018
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0033
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.FlatImageOfOverFractionFieldOfValuationRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEqMulOfContinuousOnQuotient
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0036

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientInclusionsEtaleOpenImmersionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.cmModelCoefficient_inclusions_etale_openImmersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' A A' e : ℕ), 0 < S' → 0 < A' → S ∣ S' → A ∣ A' → (∃ b : RZ H S A →+* RZ H S' A', IsInc (RZ H S A).subtype (RZ H S' A').subtype b) ∧ ∀ b : RZ H S A →+* RZ H S' A', IsInc (RZ H S A).subtype (RZ H S' A').subtype b → (S = S' → A' ∣ S ^ e → IsFinite (spMap b) ∧ Etale (spMap b) ∧ Surjective (spMap b)) ∧ (A = A' → IsOpenImmersion (spMap b) ∧ ∀ x : Sp (RZ H S A), x ∈ Set.range (spMap b) ↔ (S' : RZ H S A) ∉ x.asIdeal) := by
  first | exact @GlobalTheory.BaseRing.inclusion_RZ | exact GlobalTheory.BaseRing.inclusion_RZ | (intros; apply GlobalTheory.BaseRing.inclusion_RZ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmModelCoefficientSubringDedekindCompatibleEmbedStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.cmModelCoefficientSubring_dedekind_compatible_embedding : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (S e : ℕ), 0 < S → l.A ∣ S ^ e → (∃ β : RZ H S l.A →+* KA l, IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β) ∧ Algebra.FiniteType ℤ (RZ H S l.A) ∧ ∀ β : RZ H S l.A →+* KA l, IsInc (RZ H S l.A).subtype (KA l).val.toRingHom β → IsDedFrac β := by
  first | exact @GlobalTheory.BaseRing.isDedFrac_RZ | exact GlobalTheory.BaseRing.isDedFrac_RZ | (intros; apply GlobalTheory.BaseRing.isDedFrac_RZ <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoefficientFieldIntegersDedekindFractionFieldStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models
theorem _root_.GlobalTheory.T.coefficientField_integers_dedekind_fractionField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l), IsDedFrac (algebraMap (𝓞 c.F) c.F) ∧ Algebra.FiniteType ℤ (𝓞 c.F) ∧ (∀ A : ℕ, A ∣ l.A → ∃ b : RZ H 1 A →+* 𝓞 c.F, IsInc (RZ H 1 A).subtype (c.F.val.toRingHom.comp (algebraMap (𝓞 c.F) c.F)) b) ∧ ∀ (p : ℕ) (W : ValuationSubring ℂ), p.Prime → (p : ℂ) ∈ W.nonunits → IsDedFrac (c.V W).subtype ∧ (∀ n : ℕ, n.Coprime p → IsUnit (n : c.V W)) ∧ ∀ S A : ℕ, S.Coprime p → 0 < A → zeta A ∈ c.F → ∃ b : RZ H S A →+* c.V W, IsInc (RZ H S A).subtype (c.F.val.toRingHom.comp (c.V W).subtype) b := by
  first | exact @GlobalTheory.CoeffRings.coeff_isDedFrac | exact GlobalTheory.CoeffRings.coeff_isDedFrac | (intros; apply GlobalTheory.CoeffRings.coeff_isDedFrac <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompPowEqOneOfPullbackHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.HomExt

theorem comp_pow_eq_one_of_pullback_hom {X T Z : Scheme.{0}} (g : T ⟶ X) {G G' Γ : Over X}
    [GrpObj G] [GrpObj G'] (F : (Over.pullback g).obj G ⟶ (Over.pullback g).obj G') [IsMonHom F]
    (p : Γ ⟶ G) (q : Γ ⟶ G') (c : Z ⟶ Γ.left) (s : Z ⟶ pullback G.hom g)
    (h₁ : s ≫ pullback.fst G.hom g = c ≫ p.left)
    (h₂ : s ≫ F.left ≫ pullback.fst G'.hom g = c ≫ q.left) (n : ℕ)
    (h : c ≫ (p ^ n).left = c ≫ (1 : Γ ⟶ G).left) :
    c ≫ (q ^ n).left = c ≫ (1 : Γ ⟶ G').left := by

  let pc : Over.mk (c ≫ Γ.hom) ⟶ Γ := Over.homMk c
  let ps : Over.mk (s ≫ pullback.snd G.hom g) ⟶ (Over.pullback g).obj G := Over.homMk s
  have ht : (Over.mk (s ≫ pullback.snd G.hom g)).hom ≫ g = c ≫ Γ.hom := by
    simp only [Over.mk_hom, Category.assoc, ← pullback.condition, reassoc_of% h₁, Over.w]
  have hp : GlobalTheory.TorsionLift.ptsEquiv g G _ _ ht ps = pc ≫ p := by
    apply Over.OverMorphism.ext
    rw [GlobalTheory.TorsionLift.ptsEquiv_left]
    simpa [ps, pc] using h₁
  have hq : GlobalTheory.TorsionLift.ptsEquiv g G' _ _ ht (ps ≫ F) = pc ≫ q := by
    apply Over.OverMorphism.ext
    rw [GlobalTheory.TorsionLift.ptsEquiv_left]
    simpa [ps, pc] using h₂
  have h1 : (1 : Over.mk (c ≫ Γ.hom) ⟶ G) = pc ≫ 1 := (MonObj.comp_one pc).symm
  have hpn : (pc ≫ p) ^ n = 1 := by
    rw [← MonObj.comp_pow, h1]
    apply Over.OverMorphism.ext
    exact h
  have hps : ps ^ n = 1 := by
    apply (GlobalTheory.TorsionLift.ptsEquiv g G _ _ ht).injective
    rw [map_pow, hp, hpn, map_one]
  have hqn : (pc ≫ q) ^ n = 1 := by
    rw [← hq, ← map_pow, ← MonObj.pow_comp, hps, MonObj.one_comp, map_one]
  have key : pc ≫ q ^ n = pc ≫ 1 := by
    rw [MonObj.comp_pow, hqn, MonObj.comp_one]
  exact congrArg (fun x => Over.Hom.left x) key

theorem exists_iso_pullback_pullback {X T Z : Scheme.{0}} (p : Z ⟶ T) (f : T ⟶ X) (r : Z ⟶ X)
    (h : p ≫ f = r) (G : Over X) [GrpObj G] :
    ∃ e : (Over.pullback r).obj G ≅ (Over.pullback p).obj ((Over.pullback f).obj G),
      IsMonHom e.hom ∧ e.hom.left ≫ pullback.fst (pullback.snd G.hom f) p ≫ pullback.fst G.hom f =
        pullback.fst G.hom r := by
  subst h
  refine ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.pullCompIso p f G, inferInstance, ?_⟩
  have key := congrArg (fun x => Over.Hom.left x)
    (conjugateEquiv_counit (Over.mapPullbackAdj (p ≫ f))
      ((Over.mapPullbackAdj p).comp (Over.mapPullbackAdj f)) (Over.mapComp p f).symm.hom G)
  have e : (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pullCompIso p f G).hom.left =
      ((conjugateEquiv (Over.mapPullbackAdj (p ≫ f))
        ((Over.mapPullbackAdj p).comp (Over.mapPullbackAdj f)) (Over.mapComp p f).symm.hom).app
          G).left := rfl
  rw [e]
  simpa [Adjunction.comp_counit_app] using key

private lemma pullback_map_left_comp_fst {S S' : Scheme.{0}} (φ : S' ⟶ S) {A B : Over S} (F : A ⟶ B) :
    ((Over.pullback φ).map F).left ≫ pullback.fst B.hom φ = pullback.fst A.hom φ ≫ F.left := by
  simp
  exact pullback.lift_fst _ _ _

theorem exists_hom_along_dvr
    (H : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
      [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'],
      IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶
        (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f →
      ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
    {X U : Scheme.{0}} (j : U ⟶ X) {G G' : Over X} [GrpObj G] [GrpObj G']
    (hG : IsSemiAbelian G) (hG' : IsSemiAbelian G')
    (f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') [IsMonHom f]
    (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
    [Algebra T K] [IsFractionRing T K] (a : Sp T ⟶ G.left) (c : Sp K ⟶ pullback G.hom j)
    (hc : c ≫ pullback.fst G.hom j = spMap (algebraMap T K) ≫ a) :
    ∃ (F : (Over.pullback (a ≫ G.hom)).obj G ⟶ (Over.pullback (a ≫ G.hom)).obj G')
      (s : Sp T ⟶ pullback G.hom (a ≫ G.hom)), IsMonHom F ∧
      s ≫ pullback.fst G.hom (a ≫ G.hom) = a ∧ s ≫ pullback.snd G.hom (a ≫ G.hom) = 𝟙 _ ∧
      spMap (algebraMap T K) ≫ s ≫ F.left ≫ pullback.fst G'.hom (a ≫ G.hom) =
        c ≫ f.left ≫ pullback.fst G'.hom j := by
  have huj : (c ≫ pullback.snd G.hom j) ≫ j = spMap (algebraMap T K) ≫ (a ≫ G.hom) := by
    rw [Category.assoc, ← pullback.condition, reassoc_of% hc]
  obtain ⟨e₁, he₁, hf₁⟩ := exists_iso_pullback_pullback (c ≫ pullback.snd G.hom j) j _ huj G
  obtain ⟨e₁', he₁', hf₁'⟩ := exists_iso_pullback_pullback (c ≫ pullback.snd G.hom j) j _ huj G'
  obtain ⟨e₂, he₂, hf₂⟩ :=
    exists_iso_pullback_pullback (spMap (algebraMap T K)) (a ≫ G.hom) _ rfl G
  obtain ⟨e₂', he₂', hf₂'⟩ :=
    exists_iso_pullback_pullback (spMap (algebraMap T K)) (a ≫ G.hom) _ rfl G'
  let fK := e₂.inv ≫ e₁.hom ≫ (Over.pullback (c ≫ pullback.snd G.hom j)).map f ≫ e₁'.inv ≫ e₂'.hom
  have hfK : IsMonHom fK := inferInstance
  obtain ⟨F, ⟨hF, hFK⟩, -⟩ := H T K ((Over.pullback (a ≫ G.hom)).obj G)
    ((Over.pullback (a ≫ G.hom)).obj G')
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (a ≫ G.hom) G hG)
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback (a ≫ G.hom) G' hG') fK hfK
  have hs : a ≫ G.hom = 𝟙 _ ≫ a ≫ G.hom := (Category.id_comp _).symm
  refine ⟨F, pullback.lift a (𝟙 _) hs, hF, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩

  have hK : (spMap (algebraMap T K) ≫ pullback.lift a (𝟙 _) hs) ≫
      ((Over.pullback (a ≫ G.hom)).obj G).hom = 𝟙 _ ≫ spMap (algebraMap T K) := by
    show (spMap (algebraMap T K) ≫ pullback.lift a (𝟙 _) hs) ≫ pullback.snd G.hom (a ≫ G.hom) = _
    rw [Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  set σK := pullback.lift _ _ hK with hσK
  have inv_fst₁' : e₁'.inv.left ≫ pullback.fst G'.hom (spMap (algebraMap T K) ≫ a ≫ G.hom) =
      pullback.fst (pullback.snd G'.hom j) (c ≫ pullback.snd G.hom j) ≫ pullback.fst G'.hom j := by
    rw [← hf₁', ← Category.assoc, ← Over.comp_left, e₁'.inv_hom_id]
    simp
  have inv_fst₂ : e₂.inv.left ≫ pullback.fst G.hom (spMap (algebraMap T K) ≫ a ≫ G.hom) =
      pullback.fst (pullback.snd G.hom (a ≫ G.hom)) (spMap (algebraMap T K)) ≫
        pullback.fst G.hom (a ≫ G.hom) := by
    rw [← hf₂, ← Category.assoc, ← Over.comp_left, e₂.inv_hom_id]
    simp
  have hpt : σK ≫ e₂.inv.left ≫ e₁.hom.left ≫ pullback.fst _ _ = c := by
    apply pullback.hom_ext
    · simp only [Category.assoc]
      erw [hf₁]
      rw [inv_fst₂, hσK]
      erw [pullback.lift_fst_assoc]
      rw [Category.assoc, pullback.lift_fst, hc]
    · have hcond : pullback.fst (((Over.pullback j).obj G).hom) (c ≫ pullback.snd G.hom j) ≫
          pullback.snd G.hom j = pullback.snd _ _ ≫ c ≫ pullback.snd G.hom j := pullback.condition
      have hw₁ : e₁.hom.left ≫
          pullback.snd (((Over.pullback j).obj G).hom) (c ≫ pullback.snd G.hom j) =
          pullback.snd G.hom (spMap (algebraMap T K) ≫ a ≫ G.hom) := Over.w e₁.hom
      have hw₂ : e₂.inv.left ≫ pullback.snd G.hom (spMap (algebraMap T K) ≫ a ≫ G.hom) =
          pullback.snd (((Over.pullback (a ≫ G.hom)).obj G).hom) (spMap (algebraMap T K)) :=
        Over.w e₂.inv
      simp only [Category.assoc]
      rw [hcond, reassoc_of% hw₁, reassoc_of% hw₂, hσK, pullback.lift_snd_assoc,
        Category.id_comp]
  have step : spMap (algebraMap T K) ≫ pullback.lift a (𝟙 _) hs ≫ F.left =
      σK ≫ fK.left ≫ pullback.fst _ _ := by
    rw [← hFK, hσK, pullback_map_left_comp_fst, pullback.lift_fst_assoc, Category.assoc]
  have hmap : ((Over.pullback (c ≫ pullback.snd G.hom j)).map f).left ≫
      pullback.fst (pullback.snd G'.hom j) (c ≫ pullback.snd G.hom j) =
      pullback.fst (((Over.pullback j).obj G).hom) (c ≫ pullback.snd G.hom j) ≫ f.left :=
    pullback_map_left_comp_fst _ f
  rw [reassoc_of% step]
  simp only [fK, Over.comp_left, Category.assoc]
  erw [hf₂']
  rw [inv_fst₁', reassoc_of% hmap, reassoc_of% hpt]

end GlobalTheory.HomExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningComplexFunctionsStructureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.const_thickening_complex_functions_structure : ∀ (Y Y' : Scheme.{0}) (q : Y ⟶ Sp ℂ) (π : Y' ⟶ Sp (DualNumber ℂ)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap ℂ (DualNumber ℂ))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) → (∀ O : Y'.Opens, ρ ⁻¹ᵁ (j ⁻¹ᵁ O) = O) ∧ IsPullback j q π (spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom) ∧ ∀ (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)), ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  first | exact @GlobalTheory.EpsThick.thickening_functions | exact GlobalTheory.EpsThick.thickening_functions | (intros; apply GlobalTheory.EpsThick.thickening_functions <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ConstThickeningFieldStructureStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
theorem _root_.GlobalTheory.T.const_thickening_field_structure : ∀ (K : Type) [Field K] (Y Y' : Scheme.{0}) (q : Y ⟶ Sp K) (π : Y' ⟶ Sp (DualNumber K)) (ρ : Y' ⟶ Y) (j : Y ⟶ Y'), IsPullback ρ π q (spMap (algebraMap K (DualNumber K))) → j ≫ ρ = 𝟙 Y → j ≫ π = q ≫ (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) → (∀ O : Y'.Opens, ρ ⁻¹ᵁ (j ⁻¹ᵁ O) = O) ∧ IsPullback j q π (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) ∧ ∀ (O : Y.Opens) (F : Γ(Y', ρ ⁻¹ᵁ O)), ∃! ab : Γ(Y, O) × Γ(Y, O), F = (ρ.app O).hom ab.1 + constFn π _ DualNumber.eps * (ρ.app O).hom ab.2 := by
  first | exact @GlobalTheory.ConstThickening.structure_dualNumber | exact GlobalTheory.ConstThickening.structure_dualNumber | (intros; apply GlobalTheory.ConstThickening.structure_dualNumber <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoprimeLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory.Models

theorem exists_prime_gt_neg_not_isSquare (d : ℕ) (hd : d.Prime) (hd4 : d % 4 = 3) (b : ℕ) :
    ∃ n : ℕ, b < n ∧ n.Prime ∧ Odd n ∧ ¬ IsSquare (-(d : ZMod n)) := by
  haveI : NeZero (4 * d) := ⟨by have := hd.pos; omega⟩
  obtain ⟨n, hn, hp, hmod⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod (q := 4 * d) (a := -1) isUnit_one.neg (max b d)
  have hdvd : 4 * d ∣ n + 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast
    rw [hmod]; ring
  have h4 : n % 4 = 3 := by
    have : 4 ∣ n + 1 := Dvd.dvd.trans (Dvd.intro _ rfl) hdvd
    omega
  have hdn : (n : ZMod d) = -1 := by
    have : d ∣ n + 1 := Dvd.dvd.trans (Dvd.intro_left _ rfl) hdvd
    rw [← ZMod.natCast_eq_zero_iff] at this
    push_cast at this
    exact eq_neg_of_add_eq_zero_left this
  have hlt : d < n := lt_of_le_of_lt (le_max_right _ _) hn
  haveI : Fact n.Prime := ⟨hp⟩
  haveI : Fact d.Prime := ⟨hd⟩
  refine ⟨n, lt_of_le_of_lt (le_max_left _ _) hn, hp, by rw [Nat.odd_iff]; omega, ?_⟩
  have h1 : IsSquare (d : ZMod n) := by
    rw [ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three h4 hd4 hlt.ne', hdn,
      ZMod.exists_sq_eq_neg_one_iff]
    simp [hd4]
  have h0 : (d : ZMod n) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt hd.pos hlt
  intro h2
  have h3 : IsSquare (-1 : ZMod n) := by
    have := h2.div h1
    rwa [neg_div, div_self h0] at this
  rw [ZMod.exists_sq_eq_neg_one_iff] at h3
  exact h3 h4

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_eq_of_mem_adjoin_quadratic_generator (H : Host E) {a : 𝓞 E} (ha : a ∈ Algebra.adjoin ℤ {H.w0}) :
    ∃ u v : ℤ, a = (u : 𝓞 E) + (v : 𝓞 E) * H.w0 := by
  first
  | exact @_root_.GlobalTheory.CMGeneratorSquareModuli.main
  | exact _root_.GlobalTheory.CMGeneratorSquareModuli.main
  | (apply _root_.GlobalTheory.CMGeneratorSquareModuli.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.CMGeneratorSquareModuli.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CMGeneratorSquareModuli.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CMGeneratorSquareModuli.main ..)

theorem bar_mem_of_mem (H : Host E) {n : ℕ} (hn : AuxiliaryInertOddPrime H n) (P : Ideal (𝓞 E)) (hP : P.IsPrime)
    (hnP : (n : 𝓞 E) ∈ P) {a : 𝓞 E} (ha : a ∈ Algebra.adjoin ℤ {H.w0}) (haP : a ∈ P) : H.bar a ∈ P := by
  obtain ⟨hp, hodd, hsq, -⟩ := hn
  haveI : Fact n.Prime := ⟨hp⟩
  have key : ∀ m : ℤ, (m : 𝓞 E) ∈ P → (n : ℤ) ∣ m := by
    intro m hm
    by_contra h
    have hc : IsCoprime (n : ℤ) m :=
      (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.mp hp).irreducible).mpr h
    obtain ⟨s, t, hst⟩ := hc
    apply hP.ne_top
    rw [Ideal.eq_top_iff_one]
    have : (1 : 𝓞 E) = (s : 𝓞 E) * n + (t : 𝓞 E) * m := by
      exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 E) hst.symm
    rw [this]
    exact P.add_mem (P.mul_mem_left _ hnP) (P.mul_mem_left _ hm)
  obtain ⟨u, v, rfl⟩ := exists_eq_of_mem_adjoin_quadratic_generator H ha
  have hN : (n : ℤ) ∣ (2 * u + v) ^ 2 + H.d * v ^ 2 := by
    apply key
    have : (((2 * u + v) ^ 2 + H.d * v ^ 2 : ℤ) : 𝓞 E) =
        (2 * ((2 * u + v : 𝓞 E) - v * H.rt)) * ((u : 𝓞 E) + v * H.w0) := by
      push_cast
      linear_combination (-((2 * u + v : 𝓞 E) - v * H.rt) * v) * H.two_weight_eq_one_add_root + (v : 𝓞 E) ^ 2 * H.rt_sq
    rw [this]
    exact P.mul_mem_left _ haP
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd] at hN
  push_cast at hN
  have hv : (v : ZMod n) = 0 := by
    by_contra hv
    apply hsq
    refine ⟨(2 * u + v) / v, ?_⟩
    field_simp
    linear_combination -hN
  have h2 : (2 : ZMod n) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod n) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this
    subst this
    exact absurd hodd (by decide)
  have hu : (u : ZMod n) = 0 := by
    rw [hv] at hN
    simpa [h2] using hN
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hu hv
  obtain ⟨u', rfl⟩ := hu
  obtain ⟨v', rfl⟩ := hv
  have : H.bar (((n * u' : ℤ) : 𝓞 E) + ((n * v' : ℤ) : 𝓞 E) * H.w0) =
      ((u' : 𝓞 E) + v' * H.bar H.w0) * n := by
    simp only [map_add, map_mul, map_intCast]
    push_cast
    ring
  rw [this]
  exact P.mul_mem_left _ hnP

theorem not_Mb_le (H : Host E) {n : ℕ} (hn : AuxiliaryInertOddPrime H n) (l : Level H) (P : Ideal (𝓞 E)) (hP : P.IsPrime)
    (hnP : (n : 𝓞 E) ∈ P) : ¬ l.Mb ≤ P := by
  intro h
  apply hP.ne_top
  rw [eq_top_iff, ← l.coprime]
  refine sup_le h ?_
  rw [Ideal.map_le_iff_le_comap, l.fromK, Ideal.span_le]
  rintro a ⟨haM, ha⟩
  exact bar_mem_of_mem H hn P hP hnP ha (h haM)

theorem AuxiliaryInertOddPrime.coprime_level {H : Host E} {n : ℕ} (hn : AuxiliaryInertOddPrime H n) (l : Level H) : n.Coprime l.M := by
  rw [Nat.Prime.coprime_iff_not_dvd hn.1]
  rintro ⟨m, hm⟩
  have hnu : Ideal.span {(n : 𝓞 E)} ≠ ⊤ := by
    rw [Ne, Ideal.span_singleton_eq_top]
    intro hu
    have h1 := hu.map (Algebra.norm ℤ)
    have h2 : Algebra.norm ℤ (n : 𝓞 E) = (n : ℤ) ^ Module.finrank ℤ (𝓞 E) := by
      rw [← Algebra.norm_algebraMap]; simp
    rw [h2, isUnit_pow_iff Module.finrank_pos.ne'] at h1
    exact (Nat.prime_iff_prime_int.mp hn.1).not_unit h1
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal _ hnu
  have hnP : (n : 𝓞 E) ∈ P := hle (Ideal.mem_span_singleton_self _)
  have hM : l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) ≤ P := by
    rw [l.prod, Ideal.span_singleton_le_iff_mem, hm]
    push_cast
    exact P.mul_mem_right _ hnP
  rcases hP.isPrime.mul_le.mp hM with h | h
  · exact not_Mb_le H hn l P hP.isPrime hnP h
  · rw [Ideal.map_le_iff_le_comap] at h
    haveI := hP.isPrime
    refine not_Mb_le H hn l _ (Ideal.comap_isPrime _ P) ?_ h
    rw [Ideal.mem_comap, map_natCast]
    exact hnP

theorem exists_large_auxiliary_prime (H : Host E) (b : ℕ) : ∃ n : ℕ, b < n ∧ AuxiliaryInertOddPrime H n := by
  obtain ⟨n, hn, hp, hodd, hsq⟩ := exists_prime_gt_neg_not_isSquare H.d H.d_prime
    (by have := H.d_mod; omega) (max b (NumberField.discr E).natAbs)
  refine ⟨n, lt_of_le_of_lt (le_max_left _ _) hn, hp, hodd, hsq, ?_⟩
  rw [Int.natCast_dvd]
  exact Nat.not_dvd_of_pos_of_lt (Int.natAbs_pos.mpr (NumberField.discr_ne_zero E))
    (lt_of_le_of_lt (le_max_right _ _) hn)

theorem exists_two_auxiliary_inert_odd_primes_coprime_level :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E),
      (∃ n n' : ℕ, AuxiliaryInertOddPrime H n ∧ AuxiliaryInertOddPrime H n' ∧ n ≠ n') ∧
        ∀ n : ℕ, AuxiliaryInertOddPrime H n → ∀ l : Level H, n.Coprime l.M := by
  intro E _ _ _ H
  obtain ⟨n, -, hn⟩ := exists_large_auxiliary_prime H 0
  obtain ⟨n', hlt, hn'⟩ := exists_large_auxiliary_prime H n
  exact ⟨⟨n, n', hn, hn', hlt.ne⟩, fun _ h l => h.coprime_level l⟩

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDerivationExtendOfFormallySmoothStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_derivation_extend' : ∀ (R B C : Type) [CommRing R] [CommRing B] [CommRing C] [Algebra R B] [Algebra.FormallySmooth R B] (φ : B →+* C) (D : R → C), (∀ a b, D (a + b) = D a + D b) → (∀ a b, D (a * b) = φ (algebraMap R B a) * D b + φ (algebraMap R B b) * D a) → ∃ d : B → C, (∀ a b, d (a + b) = d a + d b) ∧ (∀ a b, d (a * b) = φ a * d b + φ b * d a) ∧ ∀ r, d (algebraMap R B r) = D r := by
  first | exact @GlobalTheory.KS.exists_derivation_extend_of_formallySmooth | exact GlobalTheory.KS.exists_derivation_extend_of_formallySmooth | (intros; apply GlobalTheory.KS.exists_derivation_extend_of_formallySmooth <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsDescOfIsFiniteOfDensePart
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory.Models

namespace GlobalTheory

theorem isFinite_graphClosure_fst_of_isFinite {S X X' Y : Scheme.{0}} (π : X ⟶ X') (s' : X' ⟶ S)
    (p : Y ⟶ S) (f : X ⟶ Y) (h : π ≫ s' = f ≫ p) [IsFinite π] [IsSeparated p]
    [LocallyOfFiniteType p] : IsFinite (graphClosure.fst s' p π f h) := by
  have e := graphClosure.incl_fst s' p π f h
  have : IsFinite (graphClosure.incl s' p π f h ≫ graphClosure.fst s' p π f h) := by
    rw [e]; infer_instance
  have : IsFinite (graphClosure.incl s' p π f h) :=
    IsFinite.of_comp _ (graphClosure.fst s' p π f h)
  have : Surjective (graphClosure.incl s' p π f h) :=
    surjective_of_isDominant_of_isClosed_range _
      (graphClosure.incl s' p π f h).isClosedMap.isClosed_range
  have : UniversallyClosed (graphClosure.fst s' p π f h) :=
    .of_comp_surjective (graphClosure.incl s' p π f h) _
  have : IsProper (graphClosure.fst s' p π f h) := {}
  have : LocallyQuasiFinite (graphClosure.fst s' p π f h) := by
    refine .of_finite_preimage_singleton _ fun s ↦ ?_
    refine (((graphClosure.incl s' p π f h ≫ graphClosure.fst s' p π f h).finite_preimage_singleton
      s).image (graphClosure.incl s' p π f h)).subset fun x hx ↦ ?_
    obtain ⟨y, rfl⟩ := (graphClosure.incl s' p π f h).surjective x
    exact ⟨y, by simpa only [Set.mem_preimage, Scheme.Hom.comp_apply] using hx, rfl⟩
  exact .of_isProper_of_locallyQuasiFinite _

theorem exists_desc_of_isFinite_of_densePart : ∀ (S X X' U U' Y : Scheme.{0}) [IsLocallyNoetherian X'] (π : X ⟶ X') (j : U ⟶ X) (j' : U' ⟶ X') (r : U ⟶ U') (s' : X' ⟶ S) (p : Y ⟶ S) (f : X ⟶ Y) (f₀ : U' ⟶ Y), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X' → IsReduced X → IsFinite π → Surjective π → Surjective r → IsDominant j → QuasiCompact j → IsPreimmersion j' → Flat j' → IsDominant j' → QuasiCompact j' → IsSeparated p → LocallyOfFiniteType p → j ≫ π = r ≫ j' → j ≫ f = r ≫ f₀ → f ≫ p = π ≫ s' → f₀ ≫ p = j' ≫ s' → ∃ f' : X' ⟶ Y, j' ≫ f' = f₀ ∧ π ≫ f' = f := by
  intro S X X' U U' Y _ π j j' r s' p f f₀ hX' _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h₃ h₄
  have := GlobalTheory.IsNormalScheme.of_pred hX'
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j'
  have : GlobalTheory.IsNormalScheme U' := GlobalTheory.IsNormalScheme.of_isIso_stalkMap j'
  have := IsSchemeTheoreticallyDominant.of_isDominant r
  have := isFinite_graphClosure_fst_of_isFinite π s' p f h₃.symm
  let g := graphClosure.lift s' p π f h₃.symm j' f₀ h₄.symm r j h₁.symm h₂.symm
  have hg₁ : g ≫ graphClosure.fst s' p π f h₃.symm = j' := graphClosure.lift_fst ..
  have hg₂ : g ≫ graphClosure.snd s' p π f h₃.symm = f₀ := graphClosure.lift_snd ..
  obtain ⟨σ, ⟨hσ₁, hσ₂⟩, -⟩ := existsUnique_lift_of_densePart X' U' X' _ j' hX' ‹_› ‹_› ‹_› ‹_›
    (graphClosure.fst s' p π f h₃.symm) (𝟙 X') g inferInstance (by rw [hg₁, Category.comp_id])
  have h₅ : j' ≫ σ ≫ graphClosure.snd s' p π f h₃.symm = f₀ := by rw [reassoc_of% hσ₁, hg₂]
  refine ⟨σ ≫ graphClosure.snd s' p π f h₃.symm, h₅,
    ext_of_isDominant_of_isSeparated p ?_ j ?_⟩
  · rw [Category.assoc, Category.assoc, ← graphClosure.condition, reassoc_of% hσ₂, h₃]
  · rw [reassoc_of% h₁, h₅, h₂]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEqMulOfContinuousOnQuotientStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_eq_mul_of_valAt'_eq_continuous_mul : ∀ (P : Out.PolAV (Sp ℂ)) (L : LB P.A.left) (u : HolUnif P.A L P.g) (U : P.A.left.Opens) (a b : Γ(P.A.left, U)) (φ : (Fin P.g → ℂ) → ℂ), Out.Laws → IsAffineOpen U → b ≠ 0 → ContinuousOn φ {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ U} → (∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ U → valAt' (u.ex z).left U a = φ z * valAt' (u.ex z).left U b) → ∃ c : Γ(P.A.left, U), a = c * b := by
  first | exact @GlobalTheory.exists_eq_mul_of_continuousOn_quotient | exact GlobalTheory.exists_eq_mul_of_continuousOn_quotient | (intros; apply GlobalTheory.exists_eq_mul_of_continuousOn_quotient <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFinsetIsProjOverDescendsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.exists_finset_isProjOver_descends_to_subfield : ∀ (K : Type) [Field K] (K₀ : Subfield K) (X : Scheme.{0}) (p : X ⟶ Sp K), IsProjOver p → ∃ s : Finset K, ∀ K₁ : Subfield K, K₀ ≤ K₁ → (s : Set K) ⊆ K₁ → ∃ (X₁ : Scheme.{0}) (p₁ : X₁ ⟶ Sp K₁) (φ : X ⟶ X₁), IsProjOver p₁ ∧ IsPullback φ p p₁ (spMap K₁.subtype) := by
  first | exact @GlobalTheory.exists_finset_isProjOver_descends | exact GlobalTheory.exists_finset_isProjOver_descends | (intros; apply GlobalTheory.exists_finset_isProjOver_descends <;> assumption)
end

