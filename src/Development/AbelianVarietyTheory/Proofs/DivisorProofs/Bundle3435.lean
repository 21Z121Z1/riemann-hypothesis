import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSysGlobalModels
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0046
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2231
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3112
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCoversOfHalves
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0239
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverOfIsIso
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0174
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.Bundle0005
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3035
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsValueEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPolarizationFormPrimitive
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2633
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2853
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3178
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3428
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantVectorFieldOfTangentVectorOrigin
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionUnitaryPointGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TraitSemi

theorem spMap_comp'' {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (f : R' →+* R'') (g : R →+* R') :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  rw [← Spec.map_comp]; rfl

theorem exists_int_map (F : Type) [Field F] [NumberField F] (V : Type) [CommRing V] [IsDomain V] [IsIntegrallyClosed V]
    (g : F →+* FractionRing V) :
    ∃ oV : 𝓞 F →+* V, (algebraMap V (FractionRing V)).comp oV = g.comp (algebraMap (𝓞 F) F) := by
  have hint : ∀ a : 𝓞 F, ∃ r : V, algebraMap V (FractionRing V) r = g a := fun a => by
    have h2 : IsIntegral V (g a) := by
      obtain ⟨p, hp, h0⟩ := RingOfIntegers.isIntegral_coe a
      refine ⟨p.map (Int.castRingHom V), hp.map _, ?_⟩
      rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap V (FractionRing V)).comp (Int.castRingHom V))
        (g.comp (algebraMap ℤ F)), ← Polynomial.hom_eval₂, h0, map_zero]
    exact IsIntegrallyClosed.isIntegral_iff.1 h2
  choose f hf using hint
  have hi := IsFractionRing.injective V (FractionRing V)
  let b : 𝓞 F →+* V :=
    { toFun := f
      map_one' := hi (by simp [hf])
      map_mul' := fun _ _ => hi (by simp [hf])
      map_zero' := hi (by simp [hf])
      map_add' := fun _ _ => hi (by simp [hf]) }
  refine ⟨b, ?_⟩
  ext a
  exact hf a

end GlobalTheory.TraitSemi

namespace GlobalTheory.TraitSemi

theorem exists_genOf_of_model {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (algebraMap (𝓞 c.F) c.F))
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsDiscreteValuationRing V]
    (y : Sp (FractionRing V) ⟶ Xo.XF c) : ∃ t : SAB H (Sp V), GenOf Xo c y t := by
  obtain ⟨g, hg⟩ := GlobalTheory.Models.RankZero.exists_spMap (y ≫ pullback.snd _ _)
  obtain ⟨oV, hoV⟩ := exists_int_map c.F V g
  obtain ⟨⟨yt, ⟨-, hyt⟩, -⟩, hG⟩ :=
    GlobalTheory.ValuativeExtension.valuation_extension E H Dw l Xo c (𝓞 c.F) _ Y V (FractionRing V) oV g y hoV hg
  obtain ⟨G, ⟨m⟩⟩ := hG yt
  obtain ⟨PP₁, cub₁, sym₁, adj₁, prim₁, n₁, -⟩ := sabPull Out.CubePf.cubePull y Y.oF.t
  obtain ⟨b, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m n₁
  have hy' : y ≫ Y.jQ ≫ pullback.fst _ _ = jK V ≫ yt := hyt.symm
  rw [hy'] at b
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m b
  obtain ⟨mx, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ Y.m0.toSABMap n₁
  exact ⟨G, _, ⟨mK⟩, ⟨mx⟩⟩

end GlobalTheory.TraitSemi

namespace GlobalTheory.TraitSemi

theorem exists_finite_point' {X Y : Scheme.{0}} (π : X ⟶ Y) [IsFinite π] (K : Type) [Field K] (x : Sp K ⟶ Y)
    (hx : x (closedPoint K) ∈ Set.range π) :
    ∃ (L : Type) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L) (η : Sp L ⟶ X),
      η ≫ π = spMap (algebraMap K L) ≫ x := by
  obtain ⟨p, hp⟩ := hx
  haveI : IsAffine (pullback π x) := isAffine_of_isAffineHom (pullback.snd π x)
  obtain ⟨S, e, -⟩ : ∃ (S : CommRingCat.{0}) (_ : Spec S ≅ pullback π x), True :=
    ⟨_, (pullback π x).isoSpec.symm, trivial⟩
  obtain ⟨f, hf⟩ := Spec.map_surjective (R := CommRingCat.of K) (S := S) (e.hom ≫ pullback.snd π x)
  letI : Algebra K S := f.hom.toAlgebra
  have hsp : spMap (algebraMap K S) = e.hom ≫ pullback.snd π x := hf
  have hfin : Module.Finite K S := by
    have h1 : IsFinite (Spec.map f) := by rw [hf]; infer_instance
    exact (IsFinite.SpecMap_iff f).1 h1
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (closedPoint K) hp
  haveI : Nontrivial S := (e.inv z).nontrivial
  obtain ⟨m, hm⟩ := Ideal.exists_maximal S
  letI : Field (S ⧸ m) := Ideal.Quotient.field m
  haveI : FiniteDimensional K (S ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ K m).toLinearMap Ideal.Quotient.mk_surjective
  refine ⟨S ⧸ m, inferInstance, inferInstance, inferInstance, spMap (Ideal.Quotient.mk m) ≫ e.hom ≫ pullback.fst π x, ?_⟩
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.hom, ← hsp, ← Category.assoc, spMap_comp'']

theorem exists_closure_finite (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    [IsAdicComplete (maximalIdeal V) V] (L : Type) [Field L] [Algebra (FractionRing V) L]
    [FiniteDimensional (FractionRing V) L] :
    ∃ (V₂ : Type) (_ : CommRing V₂) (_ : IsDomain V₂) (_ : IsLocalRing V₂) (j : V →+* V₂) (e : L →+* FractionRing V₂),
      GlobalTheory.Mum.Base V₂ ∧ IsDiscreteValuationRing V₂ ∧ Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧
        ∀ a : V, e (algebraMap (FractionRing V) L (algebraMap V (FractionRing V) a)) =
          algebraMap V₂ (FractionRing V₂) (j a) := by
  letI : Algebra V L := ((algebraMap (FractionRing V) L).comp (algebraMap V (FractionRing V))).toAlgebra
  haveI : IsScalarTower V (FractionRing V) L := IsScalarTower.of_algebraMap_eq' rfl
  haveI : Module.Finite V (integralClosure V L) := GlobalTheory.FormalIsogeny.finite_integralClosure V (FractionRing V) L
  haveI := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful V (FractionRing V) L
  haveI hloc : IsLocalRing (integralClosure V L) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalRing V L
  haveI hdvr : IsDiscreteValuationRing (integralClosure V L) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V (FractionRing V) L
  haveI : IsFractionRing (integralClosure V L) L := integralClosure.isFractionRing_of_finite_extension (FractionRing V) L
  have hj := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_inj V L
  haveI : CharZero (integralClosure V L) := charZero_of_injective_algebraMap hj
  refine ⟨integralClosure V L, inferInstance, inferInstance, hloc, algebraMap V (integralClosure V L),
    (FractionRing.algEquiv (integralClosure V L) L).symm.toRingEquiv.toRingHom,
    ⟨⟨inferInstance, inferInstance, inferInstance,
      GlobalTheory.CompleteFiniteExtension.isAdicComplete_of_finite_local V (integralClosure V L)⟩, inferInstance⟩,
    hdvr, hj, ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom V L, RingHom.finite_algebraMap.2 inferInstance, fun a => ?_⟩
  have h1 : algebraMap (FractionRing V) L (algebraMap V (FractionRing V) a) =
      algebraMap (integralClosure V L) L (algebraMap V (integralClosure V L) a) := rfl
  rw [h1]
  exact (FractionRing.algEquiv (integralClosure V L) L).symm.commutes _

theorem finite_surjective_spMap {F F' : IntermediateField ℚ ℂ} [FiniteDimensional ℚ F'] (h : F ≤ F') :
    IsFinite (spMap (IntermediateField.inclusion h).toRingHom) ∧
      Surjective (spMap (IntermediateField.inclusion h).toRingHom) := by
  have hq : (algebraMap ℚ F').Finite := RingHom.finite_algebraMap.2 inferInstance
  have he : algebraMap ℚ F' = (IntermediateField.inclusion h).toRingHom.comp (algebraMap ℚ F) := Subsingleton.elim _ _
  rw [he] at hq
  refine ⟨(IsFinite.SpecMap_iff _).2 (RingHom.Finite.of_comp_finite hq), ⟨fun x => ?_⟩⟩
  refine ⟨closedPoint F', Subsingleton.elim _ _⟩

end GlobalTheory.TraitSemi

namespace GlobalTheory.TraitSemi

theorem exists_rankZero {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (hD : Dw.p + Dw.q = 0) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (hB : GlobalTheory.Mum.Base V) (hV : IsDiscreteValuationRing V) (y : Sp (FractionRing V) ⟶ Xo.XF c) :
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
      (fK : FractionRing V →+* FractionRing V₁), CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
      (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧ ∃ t : SAB H (Sp V₁), GenOf Xo c (spMap fK ≫ y) t := by
  have hz := (GlobalTheory.Models.RankZero.isIso_moduli GlobalTheory.card_torsion_abelianVariety hD Xo).2
  refine ⟨V, inferInstance, inferInstance, inferInstance, RingHom.id V, RingHom.id _, ⟨hV, hB.1.2.2.2, hB.2⟩,
    Function.injective_id, inferInstance, RingHom.Finite.id V, fun a => rfl, Inhab.zeroTriple H _,
    Inhab.zeroTriple H _, GlobalTheory.Models.RankZero.nonempty_sabMap (GlobalTheory.Models.RankZero.isIso_zeroTriple _)
      (GlobalTheory.Models.RankZero.isIso_zeroTriple _) _,
    GlobalTheory.Models.RankZero.nonempty_sabMap (GlobalTheory.Models.RankZero.isIso_zeroTriple _) hz _⟩

theorem exists_pos {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (hD : 1 ≤ Dw.p + Dw.q) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V]
    [IsLocalRing V] (hB : GlobalTheory.Mum.Base V) (hV : IsDiscreteValuationRing V) (y : Sp (FractionRing V) ⟶ Xo.XF c) :
    ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
      (fK : FractionRing V →+* FractionRing V₁), CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
      (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧ ∃ t : SAB H (Sp V₁), GenOf Xo c (spMap fK ≫ y) t := by
  haveI := c.fin
  obtain ⟨l₂, hdvd, -, hgood⟩ := GlobalTheory.GoodMultipleLevel.exists_good_multiple E H l
  obtain ⟨c₂, hle⟩ := GlobalTheory.TupleCover.exists_coeff_ge l₂ c.F
  haveI := c₂.fin
  let Xf : ∀ l' : Geo.Tor.Level H, Moduli Dw l' := fun l' => (GlobalTheory.moduliScheme_levelMaps_heckePoints.1 E H Dw l' hD).some
  obtain ⟨s, hs⟩ := GlobalTheory.GlobalAllLevels.exists_sys_global_models E H Dw hD Xf
  obtain ⟨Ygl, -⟩ := hs l₂ c₂ hgood
  obtain ⟨r, h, r₀, m, hr, hfin, -, hsurj⟩ :=
    GlobalTheory.LevelMapBase.levelMap_coeff_le E H Dw l l₂ Xo (Xf l₂) c c₂ hle hD hdvd
  obtain ⟨hF, hS⟩ := finite_surjective_spMap hle
  have hrl : pullback.lift r _ h ≫ pullback.fst _ _ = r := pullback.lift_fst _ _ _
  haveI : IsFinite r := hrl ▸ inferInstance
  have hrs : Surjective r := hrl ▸ inferInstance
  obtain ⟨L, _, _, _, η, hη⟩ := exists_finite_point' r (FractionRing V) y (hrs.surj _)
  haveI : IsAdicComplete (maximalIdeal V) V := hB.1.2.2.2
  haveI : CharZero V := hB.2
  obtain ⟨V₁, _, _, _, j, e, hB₁, hD₁, hj, hjl, hjf, he⟩ := exists_closure_finite V L
  obtain ⟨t, tK, ⟨mK⟩, ⟨mx⟩⟩ := exists_genOf_of_model Ygl V₁ (spMap e ≫ η)
  obtain ⟨mx', -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m mx
  have key : ((spMap e ≫ η) ≫ pullback.fst _ _) ≫ r₀ =
      (spMap (e.comp (algebraMap (FractionRing V) L)) ≫ y) ≫ pullback.fst _ _ := by
    rw [Category.assoc, Category.assoc, ← hr, ← Category.assoc η, hη, ← spMap_comp'']
    simp only [Category.assoc]
  refine ⟨V₁, inferInstance, inferInstance, inferInstance, j, e.comp (algebraMap (FractionRing V) L),
    ⟨hD₁, hB₁.1.2.2.2, hB₁.2⟩, hj, hjl, hjf, fun a => he a, t, tK, ⟨mK⟩, ⟨?_⟩⟩
  rw [key] at mx'
  exact mx'

end GlobalTheory.TraitSemi

namespace GlobalTheory.TraitSemi

theorem exists_ext_semi : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V],
    GlobalTheory.Mum.Base V → IsDiscreteValuationRing V → ∀ y : Sp (FractionRing V) ⟶ Xo.XF c,
      ∃ (V₁ : Type) (_ : CommRing V₁) (_ : IsDomain V₁) (_ : IsLocalRing V₁) (f : V →+* V₁)
        (fK : FractionRing V →+* FractionRing V₁), CDvr V₁ ∧ Function.Injective f ∧ IsLocalHom f ∧ f.Finite ∧
        (∀ a, fK (algebraMap V _ a) = algebraMap V₁ _ (f a)) ∧ ∃ t : SAB H (Sp V₁), GenOf Xo c (spMap fK ≫ y) t := by
  intro E _ _ _ H Dw l Xo c V _ _ _ hB hV y
  rcases Nat.eq_zero_or_pos (Dw.p + Dw.q) with hD | hD
  · exact exists_rankZero H Dw hD l Xo c V hB hV y
  · exact exists_pos H Dw hD l Xo c V hB hV y

end GlobalTheory.TraitSemi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHolomorphicSectionOfAnalytic
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen

namespace GlobalTheory.UPel.HT.GTateGlue

section Grp

variable {G : Type} [CommGroup G]

theorem bezout {a b : ℕ} (h : a.Coprime b) : (a : ℤ) * Nat.gcdA a b + b * Nat.gcdB a b = 1 := by
  rw [← Nat.gcd_eq_gcd_ab, h.gcd_eq_one, Nat.cast_one]

theorem ext_pow {a b : ℕ} (h : a.Coprime b) {q r : G} (ha : q ^ a = r ^ a) (hb : q ^ b = r ^ b) : q = r := by
  have e : ∀ t : G, t = (t ^ a) ^ Nat.gcdA a b * (t ^ b) ^ Nat.gcdB a b := fun t => by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, bezout h, zpow_one]
  rw [e q, ha, hb, ← e r]

def crt (a b : ℕ) (x y : G) : G := x ^ Nat.gcdB a b * y ^ Nat.gcdA a b

theorem crt_mul (a b : ℕ) (x y x' y' : G) : crt a b (x * x') (y * y') = crt a b x y * crt a b x' y' := by
  simp only [crt, mul_zpow]
  exact mul_mul_mul_comm _ _ _ _

theorem crt_pow_right {a b : ℕ} (h : a.Coprime b) {x y : G} (hx : x ^ a = 1) (hy : y ^ b = 1) :
    crt a b x y ^ b = x := by
  have e : Nat.gcdB a b * (b : ℤ) = 1 + a * (-Nat.gcdA a b) := by linear_combination bezout h
  rw [crt, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, e, mul_comm (Nat.gcdA a b), zpow_add,
    zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hx, hy, one_zpow, one_zpow, zpow_one, _root_.mul_one,
    _root_.mul_one]

theorem crt_pow_left {a b : ℕ} (h : a.Coprime b) {x y : G} (hx : x ^ a = 1) (hy : y ^ b = 1) :
    crt a b x y ^ a = y := by
  have e : Nat.gcdA a b * (a : ℤ) = 1 + b * (-Nat.gcdB a b) := by linear_combination bezout h
  rw [crt, mul_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, e, mul_comm (Nat.gcdB a b), zpow_add,
    zpow_mul, zpow_mul, zpow_natCast, zpow_natCast, hx, hy, one_zpow, one_zpow, zpow_one, _root_.mul_one,
    _root_.one_mul]

variable (p : ℕ) [hp : Fact p.Prime]

def cp (n : ℕ) : ℕ := n / p ^ n.factorization p

theorem cp_mul_pow (n : ℕ) : cp p n * p ^ n.factorization p = n := by
  rw [mul_comm]; exact Nat.ordProj_mul_ordCompl_eq_self n p

theorem cp_pos {n : ℕ} (hn : 0 < n) : 0 < cp p n := Nat.ordCompl_pos p hn.ne'

theorem cp_coprime {n : ℕ} (hn : 0 < n) : (cp p n).Coprime p := (Nat.coprime_ordCompl hp.out hn.ne').symm

theorem cp_coprime_pow {n : ℕ} (hn : 0 < n) : (cp p n).Coprime (p ^ n.factorization p) :=
  (cp_coprime p hn).pow_right _

theorem cp_mul (n m : ℕ) : cp p (n * m) = cp p n * cp p m := Nat.ordCompl_mul n m p

def sys (f g : ℕ → G) (n : ℕ) : G := crt (cp p n) (p ^ n.factorization p) (f (cp p n)) (g (n.factorization p))

variable {p} {f g : ℕ → G} (hf : ∀ n, 0 < n → n.Coprime p → f n ^ n = 1) (hg : ∀ e, g e ^ p ^ e = 1)

include hf hg in
theorem sys_right {n : ℕ} (hn : 0 < n) : sys p f g n ^ p ^ n.factorization p = f (cp p n) :=
  crt_pow_right (cp_coprime_pow p hn) (hf _ (cp_pos p hn) (cp_coprime p hn)) (hg _)

include hf hg in
theorem sys_left {n : ℕ} (hn : 0 < n) : sys p f g n ^ cp p n = g (n.factorization p) :=
  crt_pow_left (cp_coprime_pow p hn) (hf _ (cp_pos p hn) (cp_coprime p hn)) (hg _)

include hf hg in
theorem sys_tower (hf' : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → f (n * m) ^ m = f n)
    (hg' : ∀ e, g (e + 1) ^ p = g e) {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    sys p f g (n * m) ^ m = sys p f g n := by
  have hg'' : ∀ e d, g (e + d) ^ p ^ d = g e := fun e d => by
    induction d with
    | zero => simp
    | succ d ih => rw [pow_succ', pow_mul, ← add_assoc, hg', ih]
  have hnm : 0 < n * m := Nat.mul_pos hn hm
  have ef : (n * m).factorization p = n.factorization p + m.factorization p := by
    rw [Nat.factorization_mul hn.ne' hm.ne']; rfl
  have r := sys_right hf hg hnm
  have l := sys_left hf hg hnm
  refine ext_pow (cp_coprime_pow p hn) ?_ ?_
  · have e : m * cp p n = cp p (n * m) * p ^ m.factorization p := by
      rw [cp_mul, _root_.mul_assoc, cp_mul_pow, mul_comm]
    rw [← pow_mul, e, pow_mul, l, ef, hg'', sys_left hf hg hn]
  · have e : m * p ^ n.factorization p = p ^ (n * m).factorization p * cp p m := by
      rw [ef, pow_add, _root_.mul_assoc, mul_comm _ (cp p m), cp_mul_pow, mul_comm]
    rw [← pow_mul, e, pow_mul, r, cp_mul, hf' _ _ (cp_pos p hn) (cp_pos p hm)
      (Nat.Coprime.mul_left (cp_coprime p hn) (cp_coprime p hm)), sys_right hf hg hn]

include hf hg in
theorem sys_of_coprime {n : ℕ} (hn : 0 < n) (h : n.Coprime p) : sys p f g n = f n := by
  have e : n.factorization p = 0 := Nat.factorization_eq_zero_of_not_dvd ((Nat.Prime.coprime_iff_not_dvd hp.out).1 h.symm)
  have r := sys_right hf hg hn
  rwa [cp, e, pow_zero, pow_one, Nat.div_one] at r

end Grp

theorem exists_gTateIso {p : ℕ} [Fact p.Prime] (D : Datum p) {k : Type} [Field k] {Q : Type} [CommGroup Q]
    (act : D.O → Q → Q) (hact : ∀ c q r, act c (q * r) = act c q * act c r) (W : ℕ → Q → Q → kˣ → Prop)
    (hW : ∀ (a b : ℕ) (q r : Q) (c : kˣ), 0 < a → 0 < b → a.Coprime b → q ^ (a * b) = 1 → r ^ (a * b) = 1 →
      W a (q ^ b) (r ^ b) (c ^ b) → W b (q ^ a) (r ^ a) (c ^ a) → W (a * b) q r c)
    (I : TateIsoO D k Q act W) (ζ : ℕ → kˣ) (ev : ℕ → D.La → Q)
    (h₁ : ∀ e, IsPrimitiveRoot (ζ e) (p ^ e)) (h₂ : ∀ e, ζ (e + 1) ^ p = ζ e)
    (h₃ : ∀ e y z, ev e (y + z) = ev e y * ev e z) (h₄ : ∀ e (c : D.O) y, ev e (c • y) = act c (ev e y))
    (h₅ : ∀ e y, ev e y = 1 ↔ ∃ z, y = p ^ e • z) (h₆ : ∀ e (q : Q), q ^ (p ^ e) = 1 ↔ ∃ y, ev e y = q)
    (h₇ : ∀ e y, ev (e + 1) y ^ p = ev e y)
    (h₈ : ∀ e y z, W (p ^ e) (ev e y) (ev e z) (ζ e ^ (2 * D.EF y z))) :
    ∃ J : GTateIso D.toG k Q act W, ∀ n, 0 < n → n.Coprime p → ∀ y, J.ev n y = I.ev n y := by
  have zf : ∀ n, 0 < n → n.Coprime p → I.ζ n ^ n = 1 := fun n a b => (I.ζ_prim n a b).pow_eq_one
  have zg : ∀ e, ζ e ^ p ^ e = 1 := fun e => (h₁ e).pow_eq_one
  have ef : ∀ y n, 0 < n → n.Coprime p → I.ev n y ^ n = 1 := fun y n a b => (I.onto n a b _).2 ⟨y, rfl⟩
  have eg : ∀ y e, ev e y ^ p ^ e = 1 := fun y e => (h₆ e _).2 ⟨y, rfl⟩
  let E : ℕ → D.La → Q := fun n y => sys p (fun m => I.ev m y) (fun e => ev e y) n
  have ER : ∀ n, 0 < n → ∀ y, E n y ^ p ^ n.factorization p = I.ev (cp p n) y := fun n hn y =>
    sys_right (ef y) (eg y) hn
  have EL : ∀ n, 0 < n → ∀ y, E n y ^ cp p n = ev (n.factorization p) y := fun n hn y =>
    sys_left (ef y) (eg y) hn
  have tors : ∀ n, 0 < n → ∀ y, E n y ^ (cp p n * p ^ n.factorization p) = 1 := fun n hn y => by
    rw [pow_mul, EL n hn, eg]
  refine ⟨{ ζ := sys p I.ζ ζ
            ζ_prim := fun n hn => ⟨?_, fun l hl => ?_⟩
            ζ_pow := fun n m hn hm => sys_tower zf zg I.ζ_pow h₂ hn hm
            ev := E
            add := fun n (y z : D.La) => ?_
            lin := fun n (c : D.O) (y : D.La) => ?_
            ker := fun n hn (y : D.La) => ⟨fun h => ?_, ?_⟩
            onto := fun n hn q => ⟨fun h => ?_, ?_⟩
            tower := fun n m hn hm y =>
              sys_tower (ef y) (eg y) (fun a b ha hb hab => I.tower a b ha hb hab y) (fun e => h₇ e y) hn hm
            isom := fun n hn (y z : D.La) => ?_ },
    fun n hn h y => sys_of_coprime (ef y) (eg y) hn h⟩
  · have e : sys p I.ζ ζ n ^ (cp p n * p ^ n.factorization p) = 1 := by rw [pow_mul, sys_left zf zg hn, zg]
    rwa [cp_mul_pow] at e
  · have a := (I.ζ_prim _ (cp_pos p hn) (cp_coprime p hn)).dvd_of_pow_eq_one l (by
      rw [← sys_right zf zg hn, pow_right_comm, hl, one_pow])
    have b := (h₁ (n.factorization p)).dvd_of_pow_eq_one l (by
      rw [← sys_left zf zg hn, pow_right_comm, hl, one_pow])
    have := (cp_coprime_pow p hn).mul_dvd_of_dvd_of_dvd a b
    rwa [cp_mul_pow] at this
  · exact (congrArg₂ (crt _ _) (I.add _ y z) (h₃ _ y z)).trans (crt_mul _ _ _ _ _ _)
  · refine (congrArg₂ (crt _ _) (I.lin _ c y) (h₄ _ c y)).trans ?_
    let φ : Q →* Q := MonoidHom.mk' (act c) (hact c)
    show φ _ ^ _ * φ _ ^ _ = φ (_ ^ _ * _ ^ _)
    rw [map_mul, map_zpow, map_zpow]
  · obtain ⟨z₁, e₁⟩ := (I.ker _ (cp_pos p hn) (cp_coprime p hn) y).1 (by rw [← ER n hn, h, one_pow])
    obtain ⟨z₂, e₂⟩ := (h₅ (n.factorization p) y).1 (by rw [← EL n hn, h, one_pow])
    have bz := bezout (cp_coprime_pow p hn)
    have en := cp_mul_pow p n
    generalize cp p n = a at *
    generalize p ^ n.factorization p = b at *
    refine ⟨(Nat.gcdB a b • z₁ + Nat.gcdA a b • z₂ : D.La), ?_⟩
    show y = n • (Nat.gcdB a b • z₁ + Nat.gcdA a b • z₂ : D.La)
    calc y = ((a : ℤ) * Nat.gcdA a b) • y + ((b : ℤ) * Nat.gcdB a b) • y := by rw [← add_smul, bz, one_smul]
      _ = ((a : ℤ) * Nat.gcdA a b) • (b • z₂) + ((b : ℤ) * Nat.gcdB a b) • (a • z₁) := by rw [← e₁, ← e₂]
      _ = _ := by rw [← en]; module
  · rintro (⟨z, hz⟩ : ∃ z : D.La, y = n • z)
    have hz' : y = (cp p n * p ^ n.factorization p) • z := by rw [cp_mul_pow]; exact hz
    refine ext_pow (cp_coprime_pow p hn) ?_ ?_
    · rw [EL n hn, one_pow]
      exact (h₅ _ _).2 ⟨cp p n • (z : D.La), by rw [hz', mul_comm, mul_smul]⟩
    · rw [ER n hn, one_pow]
      exact (I.ker _ (cp_pos p hn) (cp_coprime p hn) _).2 ⟨p ^ n.factorization p • (z : D.La), by rw [hz', mul_smul]⟩
  · obtain ⟨y₁, e₁⟩ := (I.onto _ (cp_pos p hn) (cp_coprime p hn) (q ^ p ^ n.factorization p)).1 (by
      rw [← pow_mul, mul_comm, cp_mul_pow, h])
    obtain ⟨y₂, e₂⟩ := (h₆ (n.factorization p) (q ^ cp p n)).1 (by rw [← pow_mul, cp_mul_pow, h])
    have bz := bezout (cp_coprime_pow p hn)
    refine ⟨(y₁ + cp p n • Nat.gcdA (cp p n) (p ^ n.factorization p) • (y₂ - y₁) : D.La),
      ext_pow (cp_coprime_pow p hn) ?_ ?_⟩
    · have e : y₁ + cp p n • Nat.gcdA (cp p n) (p ^ n.factorization p) • (y₂ - y₁) =
          y₂ + p ^ n.factorization p • Nat.gcdB (cp p n) (p ^ n.factorization p) • (y₁ - y₂) := by
        generalize cp p n = a at *
        generalize p ^ n.factorization p = b at *
        linear_combination (norm := module) bz • (y₂ - y₁)
      rw [EL n hn, e, h₃, e₂, (h₅ _ _).2 ⟨_, rfl⟩, _root_.mul_one]
    · rw [ER n hn, I.add, e₁, (I.ker _ (cp_pos p hn) (cp_coprime p hn) _).2 ⟨_, rfl⟩, _root_.mul_one]
  · rintro ⟨y, rfl⟩
    have := tors n hn y
    rwa [cp_mul_pow] at this
  · have sw : ∀ (u : kˣ) (t : ℤ) (j : ℕ), (u ^ t) ^ j = (u ^ j) ^ t := fun u t j => by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
    have := hW (cp p n) (p ^ n.factorization p) (E n y) (E n z) (sys p I.ζ ζ n ^ (2 * D.EF y z)) (cp_pos p hn)
      (pow_pos (Fact.out : p.Prime).pos _) (cp_coprime_pow p hn) (tors n hn y) (tors n hn z)
      (by rw [ER n hn, ER n hn, sw, sys_right zf zg hn]; exact I.isom _ (cp_pos p hn) (cp_coprime p hn) y z)
      (by rw [EL n hn, EL n hn, sw, sys_left zf zg hn]; exact h₈ _ y z)
    rwa [cp_mul_pow] at this

section Weil

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A) {L : LB A.left}
  (hL : L.IsLB) {T : Over S}

include hA hL in

theorem weilIs_pow_eq {a b : ℕ} (hb : 0 < b) {x y : T ⟶ A} {c c' : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs A L ((a * b : ℕ) : ℤ) x y c) (h' : Out.WeilIs A L a (x ^ b) (y ^ b) c') : c ^ b = c' := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  obtain ⟨t, ht⟩ := GlobalTheory.HodgeWeil.triv_theta GlobalTheory.CubeTop.cubeTheorem hA hL
  have h₀ := CommPairing.weilIs_symm hL h
  have pw : ∀ j : ℕ, Out.WeilIs A L ((a * b : ℕ) : ℤ) (y ^ (j + 1)) x (c⁻¹ ^ (j + 1)) := fun j => by
    induction j with
    | zero => rwa [zero_add, pow_one, pow_one]
    | succ j ih => rw [pow_succ, pow_succ c⁻¹]; exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL ih h₀
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hb.ne'
  have h₂ := CommPairing.weilIs_symm hL (pw j)
  rw [inv_pow, inv_inv, Nat.cast_mul] at h₂
  exact PairingLevels.weilIs_value_eq hG hA hL ht h₂ h'

include hA hL in

theorem weilIs_of_coprime {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b) {x y : T ⟶ A}
    {c : Γ(T.left, ⊤)ˣ} (hx : x ^ (a * b) = 1) (hy : y ^ (a * b) = 1)
    (h₁ : Out.WeilIs A L a (x ^ b) (y ^ b) (c ^ b)) (h₂ : Out.WeilIs A L b (x ^ a) (y ^ a) (c ^ a)) :
    Out.WeilIs A L ((a * b : ℕ) : ℤ) x y c := by
  obtain ⟨w, -, hw⟩ := GlobalTheory.HolTorsionAny.exists_weilIs_pow_eq_one hA hL hx hy
  have e₁ := weilIs_pow_eq hA hL hb hw h₁
  have e₂ := weilIs_pow_eq hA hL ha (by rw [mul_comm]; exact hw) h₂
  rwa [ext_pow hab e₂ e₁] at hw

end Weil

theorem glue : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → (∃ (ζ : ℕ → kˣ) (ev : ℕ → D.La → (Over.mk x ⟶ o.A)), (∀ e, IsPrimitiveRoot (ζ e) (p ^ e)) ∧ (∀ e, ζ (e + 1) ^ p = ζ e) ∧ (∀ e y z, ev e (y + z) = ev e y * ev e z) ∧ (∀ e (c : D.O) y, ev e (c • y) = ev e y ≫ o.act.act c) ∧ (∀ e y, ev e y = 1 ↔ ∃ z, y = p ^ e • z) ∧ (∀ e (q : Over.mk x ⟶ o.A), q ^ (p ^ e) = 1 ↔ ∃ y, ev e y = q) ∧ (∀ e y, ev (e + 1) y ^ p = ev e y) ∧ (∀ e y z, Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (p ^ e) (ev e y) (ev e z) (unitOn (ζ e ^ (2 * D.EF y z))))) → ∃ I : GTateIso D.toG k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ o.eta y = I.ev N y := by
  intro p _ D R _ b N hN hNp S s o k _ _ _ x β hx ⟨ζ, ev, h₁, h₂, h₃, h₄, h₅, h₆, h₇, h₈⟩
  obtain ⟨I, hI⟩ := o.geom k x β hx
  have hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := LB.isLB_pull o.isLB _
  have up : ∀ (u : kˣ) (j : ℕ), unitOn (u ^ j) = unitOn u ^ j := fun u j => map_pow _ _ _
  obtain ⟨J, hJ⟩ := exists_gTateIso D (Q := Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
    (fun c q r => by have := o.act.hom c; exact MonObj.mul_comp _ _ _)
    (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z))
    (fun a b q r c ha hb hab hq hr w₁ w₂ => weilIs_of_coprime o.ab hL ha hb hab hq hr
      (by rw [up] at w₁; exact w₁) (by rw [up] at w₂; exact w₂))
    I ζ ev h₁ h₂ h₃ h₄ h₅ h₆ h₇ (fun e y z => by rw [Nat.cast_pow]; exact h₈ e y z)
  exact ⟨J, fun y => (hI y).trans (hJ N (by omega) hNp y).symm⟩

end GlobalTheory.UPel.HT.GTateGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerRingActionOnTensorDegenerationDataA
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.TensAct

theorem exists_integer_ring_action_on_tensor_degeneration_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → ∃ (_ : Module (𝓞 E) D'.toPre.X) (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) ∧ (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) := by
  intro R _ _ _ hR E _ _ _ H D D' r W hpos hdet T ρ hρ hw
  letI := H.starRing
  letI md : Module (𝓞 E) D'.toPre.X := tensModule T ρ
  let oB : D'.toPre.P.OAct (𝓞 E) :=
    { ringAct T ρ with rosati := fun a ↦ GlobalTheory.T.rosatiAdj_tensorPowerIntMatrixEndomorphism R D.toPre D'.toPre W T (ρ a) (ρ (star a)) (hρ a) }
  let o : D'.toPre.OAct (𝓞 E) :=
    { onB := oB
      c_lin := fun a y ↦ c_lin T (ρ a) y
      tau_bal := fun a ↦ GlobalTheory.T.tensorDegeneration_tauBalanced_of_adjointIntMatrices R _ D D' W T (ρ a) (ρ (star a)) (hρ a) }
  exact ⟨md, o, ⟨fun a z i ↦ xe_latAct T (ρ a) z i, fun a i ↦ matAct_pr T (ρ a) i⟩,
    GlobalTheory.T.traceFormTwistIso_of_matAct_of_latAct R _ D D' W T (ρ H.w0) (𝓞 E) o H.w0 rfl (fun y ↦ rfl) hw⟩

end GlobalTheory.TensAct
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantVectorFieldOfTangentVectorOriginStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariantVectorField_of_tangentVector_origin : ∀ (R : Type) [CommRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (v : TanM (𝟙 (Sp R)) G), ∃ dd : Fld G.left, IsInv G v dd := by
  first | exact @GlobalTheory.InvFieldBase.exists_isInv | exact GlobalTheory.InvFieldBase.exists_isInv | (intros; apply GlobalTheory.InvFieldBase.exists_isInv <;> assumption)
end

