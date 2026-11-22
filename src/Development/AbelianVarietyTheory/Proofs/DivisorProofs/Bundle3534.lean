import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBaseAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrdegResidueFieldOfIsOpenImmersion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
import GroundTheory.ArithmeticGeometry.SchemeCohomology.Bundle0002
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0014
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0582
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3489
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3485
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2496
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3184
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3504
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3493
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0058
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0038
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3514
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3442
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0638
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3501
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2410
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3516
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3488

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalCompactificationSmoothSncBoundary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChartSmooth

theorem trdeg_residueField_eq_zero {F : Type} [Field F] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of F))
    [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    letI : Algebra F (X.residueField x) := (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra
    Algebra.trdeg F (X.residueField x) = 0 := by
  letI : Algebra F (X.residueField x) := (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom.toAlgebra
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have h : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  rw [← Spec.map_preimage (X.fromSpecResidueField x ≫ f), HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h
  have : Algebra.FiniteType F (X.residueField x) := RingHom.finiteType_algebraMap.mp h
  have : Module.Finite F (X.residueField x) := finite_of_finite_type_of_isJacobsonRing F _
  have : Algebra.IsAlgebraic F (X.residueField x) := Algebra.IsAlgebraic.of_finite F _
  exact trdeg_eq_zero

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)} {Z : Scheme.{0}} {zs : Z ⟶ Sp c.F} {i : Xo.XF c ⟶ Z} {OZ : LB Z}
  {N d : ℕ} {J : Z.IdealSheafData} {S : Scheme.{0}} {π : S ⟶ Z} {j : Xo.XF c ⟶ S} {BD : EffCartierData S}

theorem locallyOfFiniteType (h : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD) : LocallyOfFiniteType (π ≫ zs) := by
  obtain ⟨-, -, -, -, ⟨-, hproj, -⟩, -⟩ := h
  obtain ⟨M, i', hi', hcomp⟩ := hproj
  haveI := hi'
  haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str c.F M
  rw [← hcomp]
  infer_instance

theorem smooth_j (h : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD) :
    SmoothOfRelativeDimension Dw.dim (j ≫ π ≫ zs) := by
  obtain ⟨⟨-, -, -, -, hizs, -⟩, -, -, -, ⟨-, -, -, -, hji, -⟩, -⟩ := h
  rw [← Category.assoc, hji, hizs]
  exact Formalism.L2.Pj.smoothOfRelativeDimension_strK Xo c

theorem isRegularLocalRing_stalk [IsOpenImmersion j] (h : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD)
    (hU : ∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) (x : S) : IsRegularLocalRing (S.presheaf.stalk x) := by
  haveI := locallyOfFiniteType h
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  by_cases hx : x ∈ Set.range j
  · obtain ⟨z, rfl⟩ := hx
    haveI := smooth_j h
    haveI : Smooth (j ≫ π ≫ zs) := SmoothOfRelativeDimension.smooth Dw.dim _
    haveI := GroundTheory.Arith.SchemeCoh.isRegularLocalRing_stalk_of_smooth_field (j ≫ π ≫ zs) z
    exact IsRegularLocalRing.of_ringEquiv (asIso (j.stalkMap z)).commRingCatIsoToRingEquiv.symm
  · obtain ⟨k, _, m, e, C, ξ, a, -, -, rfl, hE, -⟩ := hU x hx
    haveI : IsRegularLocalRing (ChartRing k m e) := GlobalTheory.FormalIsogeny.isRegularLocalRing_mvPowerSeries k (Fin m ⊕ Fin e)
    exact (GlobalTheory.RegSmooth.isRegularLocalRing_of_isEtaleCompletion _ hE).1

theorem smooth [IsOpenImmersion j] (h : GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD)
    (hU : ∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) : SmoothOfRelativeDimension Dw.dim (π ≫ zs) := by
  haveI := locallyOfFiniteType h
  refine GlobalTheory.RegSmooth.smoothOfRelativeDimension_of_isRegularLocalRing (π ≫ zs) Dw.dim fun x hx => ⟨isRegularLocalRing_stalk h hU x, ?_⟩
  obtain ⟨a, b, ha, hb, hab⟩ := stalk_dim_add_trdeg_of_uPoinOnX h x
  have h0 := trdeg_residueField_eq_zero (π ≫ zs) x hx
  have hb0 : b = 0 := by
    have := hb.symm.trans h0
    exact_mod_cast this
  rw [ha, ← hab, hb0, add_zero]

end GlobalTheory.UChartSmooth

namespace GlobalTheory.UChartSmooth

theorem smooth_and_snc : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → (∀ x : S, x ∉ Set.range j → UPre Xo c φ j BD d x) → SmoothOfRelativeDimension Dw.dim (π ≫ zs) ∧ FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) := by
  intro E _ _ _ H Dw l Xo c φ hpq hfan hno Z zs i OZ N d J S π j _ BD h hsep hU
  refine ⟨smooth h hU, ?_⟩
  haveI := locallyOfFiniteType h
  haveI : IsLocallyNoetherian S := LocallyOfFiniteType.isLocallyNoetherian (π ≫ zs)
  intro x
  by_cases hx : x ∈ Set.range j
  · refine sncAt_of_not_mem _ x ?_ (isRegularLocalRing_stalk h hU x)
    intro hc
    exact hc hx
  · obtain ⟨k, _, m, e, C, ξ, a, hT, hy, rfl, hE, hid, hrange, -⟩ := hU x hx
    have hs' := GlobalTheory.T.boundaryBranches_distinct_primes_toricChart Xo c φ hpq hfan hno zs i OZ N d J π j BD h hsep hU k m e C ξ hT hy hx hE hid hrange
    obtain ⟨hm, hs, -⟩ := hT
    have hprod : ∏ i, C.s i = ∏ i : Fin m, bdParam k m e i :=
      Fintype.prod_equiv (finCongr hm) (fun i => C.s i) (fun i => bdParam k m e i) (fun i => by rw [hs i]; rfl)
    rw [hprod] at hid
    obtain ⟨n, r, T, hr, hD⟩ := GlobalTheory.T.strictNormalCrossings_descent_etale_completion _ k m e _ _ hE hid hs'
    exact GlobalTheory.T.sncAt_of_stalkId_eq_span_prod_of_isRegularLocalRing S _ _ (isRegularLocalRing_stalk h hU _) n r T hr hD
end GlobalTheory.UChartSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsProjectionsDefinedOverSubfield
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

namespace GlobalTheory.USep.EvG

theorem points_defOver : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (N : ℕ), 1 ≤ N → ∀ (b : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A), b ^ N = 1 → ∀ a : D.X,
      DefOver k₀ (spMap ev ≫ b.left ≫ β) ∧ DefOver k₀ (spMap ev ≫ (D.c a).left ≫ β) ∧
        DefOver k₀ (spMap ev ≫ (b * D.c a).left ≫ β) ∧ DefOver k₀ (spMap ev ≫ (D.c a * b).left ≫ β) := by
  intro V₁ _ _ _ hV hunit D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hF K _ _ ev k₀ hk₀ hk N hN b hb a
  classical
  obtain ⟨-, -, hβ, -, hc, -, -⟩ := hF
  haveI : IsNoetherianRing V₁ := hV.1
  have hg : spMap ev ≫ spMap ib = spMap (ev.comp ib) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  obtain ⟨Φ, hΦ⟩ :=
    GlobalTheory.GroupBplus.Aff.exists_mulEquiv_points_of_isGrpPullback hβ (spMap ev) (spMap (ev.comp ib)) hg

  have htor : ∀ x : Over.mk (spMap ev) ⟶ D.P.A, x ^ N = 1 → DefOver k₀ (x.left ≫ β) := by
    intro x hx
    have hNK : (N : K) ≠ 0 := by
      have := ((hunit N (by omega)).map ev).ne_zero
      simpa using this
    have hcard := (GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp V₁) D.P N hN).2.2.2.2 K (spMap ev) hNK
    have hfin : Finite {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ (by omega))
    refine defOver_of_finite_orbit K k₀ hk₀ _ _ ((Set.finite_range
      fun y : {y : Over.mk (spMap ev) ⟶ D.P.A // y ^ N = 1} => (Φ y.1).left).subset ?_)
    rintro _ ⟨σ, hσ, rfl⟩
    have hσf : spMap σ.toRingHom ≫ spMap (ev.comp ib) = spMap (ev.comp ib) := by
      have e1 : (σ.toRingHom).comp (ev.comp ib) = ev.comp ib := RingHom.ext fun u => hσ _ (hk u)
      have e0 : spMap σ.toRingHom ≫ spMap (ev.comp ib) = spMap ((σ.toRingHom).comp (ev.comp ib)) := by
        simp only [spMap, ← Spec.map_comp]; rfl
      rw [e0, e1]
    let hh : Over.mk (spMap (ev.comp ib)) ⟶ Over.mk (spMap (ev.comp ib)) := Over.homMk (spMap σ.toRingHom) hσf
    refine ⟨⟨Φ.symm (hh ≫ Φ x), ?_⟩, ?_⟩
    · rw [← map_pow, ← MonObj.comp_pow, ← map_pow, hx, map_one, MonObj.comp_one, map_one]
    · show (Φ (Φ.symm (hh ≫ Φ x))).left = _
      rw [MulEquiv.apply_symm_apply, Over.comp_left, hΦ]
      rfl

  have hsub : spMap k₀.subtype ≫ spMap ((ev.comp ib).codRestrict k₀ hk) = spMap (ev.comp ib) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  let j : Over.mk (spMap (ev.comp ib)) ⟶ Over.mk (spMap ((ev.comp ib).codRestrict k₀ hk)) :=
    Over.homMk (spMap k₀.subtype) hsub
  have hdesc : ∀ p : Over.mk (spMap (ev.comp ib)) ⟶ B₀, DefOver k₀ p.left →
      ∃ p₀ : Over.mk (spMap ((ev.comp ib).codRestrict k₀ hk)) ⟶ B₀, j ≫ p₀ = p := by
    intro p ⟨P₀, hP₀⟩
    have e : P₀ ≫ B₀.hom = spMap ((ev.comp ib).codRestrict k₀ hk) := spMap_subtype_cancel k₀ (by
      rw [← Category.assoc, hP₀, Over.w p, hsub]; rfl)
    exact ⟨Over.homMk P₀ e, Over.OverMorphism.ext hP₀⟩
  have hmul : ∀ p q : Over.mk (spMap (ev.comp ib)) ⟶ B₀, DefOver k₀ p.left → DefOver k₀ q.left →
      DefOver k₀ (p * q).left := by
    intro p q hp hq
    obtain ⟨p₀, rfl⟩ := hdesc p hp
    obtain ⟨q₀, rfl⟩ := hdesc q hq
    rw [← MonObj.comp_mul]
    exact ⟨(p₀ * q₀).left, rfl⟩
  have hprod : ∀ y z : Over.mk (spMap ev) ⟶ D.P.A, DefOver k₀ (y.left ≫ β) → DefOver k₀ (z.left ≫ β) →
      DefOver k₀ ((y * z).left ≫ β) := by
    intro y z hy hz
    rw [← hΦ, map_mul]
    exact hmul _ _ (by rw [hΦ]; exact hy) (by rw [hΦ]; exact hz)

  let h : Over.mk (spMap ev) ⟶ 𝟙_ (Over (Sp V₁)) := Over.homMk (spMap ev) (Category.comp_id _)
  have hl : ∀ y : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A, spMap ev ≫ y.left ≫ β = (h ≫ y).left ≫ β := by
    intro y
    rw [Over.comp_left, Category.assoc]
    rfl
  have h1 : DefOver k₀ (spMap ev ≫ b.left ≫ β) := by
    rw [hl]
    exact htor _ (by rw [← MonObj.comp_pow, hb, MonObj.comp_one])
  have h2 : DefOver k₀ (spMap ev ≫ (D.c a).left ≫ β) := by
    have e : spMap ev ≫ (D.c a).left ≫ β = spMap (ev.comp ib) ≫ c₀ a := by
      rw [show (D.c a).left ≫ β = spMap ib ≫ c₀ a from hc a, ← Category.assoc, hg]
    rw [e]
    exact defOver_comp k₀ (defOver_spMap k₀ _ hk) _
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [hl, MonObj.comp_mul]
    exact hprod _ _ (by rw [← hl]; exact h1) (by rw [← hl]; exact h2)
  · rw [hl, MonObj.comp_mul]
    exact hprod _ _ (by rw [← hl]; exact h2) (by rw [← hl]; exact h1)

end GlobalTheory.USep.EvG
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionSectionsExhaustOfGenericGeometric
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.Poinc.IntTerm

theorem tf_apply_eq_genericPoint {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F]
    [Algebra (FractionRing R) F] (a : Sp F) : (TF (R := R) F).hom a = genericPoint (Sp R) := by
  rw [genericPoint_eq_bot_of_affine]
  have ha : (a : PrimeSpectrum F).asIdeal = ⊥ :=
    @Ideal.eq_bot_of_prime _ _ _ (a : PrimeSpectrum F).isPrime
  have hinj : Function.Injective ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R))) :=
    (algebraMap (FractionRing R) F).injective.comp (IsFractionRing.injective R (FractionRing R))
  apply PrimeSpectrum.ext
  show Ideal.comap _ (Ideal.comap _ (a : PrimeSpectrum F).asIdeal) = ⊥
  rw [ha, Ideal.comap_comap]
  exact Ideal.comap_bot_of_injective _ hinj

theorem exists_eq_section_of_finite_flat {R : Type} [CommRing R] [IsDomain R] (T : Over (Sp R))
    [IsFinite T.hom] [Flat T.hom] {C : Type} (σ : C → (𝟙_ (Over (Sp R)) ⟶ T))
    (H : ∀ t : TF (R := R) (AlgebraicClosure (FractionRing R)) ⟶ T, ∃ c, t = toUnit _ ≫ σ c)
    (K : Type) [Field K] (x : Sp K ⟶ Sp R) (p : Over.mk x ⟶ T) : ∃ c, p = toUnit _ ≫ σ c := by
  set Kb := AlgebraicClosure (FractionRing R)
  set q := p.left (IsLocalRing.closedPoint K) with hqdef
  obtain ⟨q', hq'q, hq'⟩ := Flat.generalizingMap T.hom (genericPoint_specializes (T.hom q))
  let j : Sp Kb ⟶ Sp R := (TF (R := R) Kb).hom
  obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := T.hom) (g := j) q'
    (IsLocalRing.closedPoint Kb) (by rw [hq']; exact (tf_apply_eq_genericPoint (R := R) Kb _).symm)
  have : LocallyOfFiniteType (pullback.snd T.hom j) := inferInstance
  have : IsIntegralHom (pullback.snd T.hom j) := inferInstance
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd T.hom j)
  obtain ⟨c, hcz, hcc⟩ := nonempty_inter_closedPoints (X := (pullback T.hom j : Scheme))
    (Z := closure {z}) ⟨z, subset_closure rfl⟩ isClosed_closure.isLocallyClosed
  have hzc : z = c := GlobalTheory.eq_of_specializes_of_isIntegralHom (pullback.snd T.hom j)
    (specializes_iff_mem_closure.2 hcz) (Subsingleton.elim _ _)
  subst hzc
  let s : Sp Kb ⟶ pullback T.hom j := pointOfClosedPoint (pullback.snd T.hom j) z hcc
  have hs : s ≫ pullback.snd T.hom j = 𝟙 _ := pointOfClosedPoint_comp (pullback.snd T.hom j) z hcc
  have hsz : ∀ a, s a = z := fun a => pointOfClosedPoint_apply (pullback.snd T.hom j) z hcc a
  let t : TF (R := R) Kb ⟶ T := Over.homMk (s ≫ pullback.fst T.hom j) (by
    show (s ≫ pullback.fst T.hom j) ≫ T.hom = j
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp])
  obtain ⟨c0, hc0⟩ := H t
  have hσ : IsClosedImmersion (σ c0).left := by
    have h1 : (σ c0).left ≫ T.hom = 𝟙 _ := Over.w (σ c0)
    have : IsClosedImmersion ((σ c0).left ≫ T.hom) := by rw [h1]; infer_instance
    exact IsClosedImmersion.of_comp (σ c0).left T.hom
  have hq'mem : q' ∈ Set.range (σ c0).left := by
    let pt : Sp Kb := IsLocalRing.closedPoint Kb
    refine ⟨(toUnit (TF (R := R) Kb)).left pt, ?_⟩
    have e1 : t.left pt = q' := by
      show pullback.fst T.hom j (s pt) = q'
      rw [hsz, hz1]
    rw [← e1, hc0]
    rfl
  have hqmem : q ∈ Set.range (σ c0).left :=
    hq'q.mem_closed (σ c0).left.isClosedEmbedding.isClosed_range hq'mem
  have : IsReduced (Sp K) := inferInstance
  obtain ⟨l, hl⟩ := GlobalTheory.AbelianSubgroupFinite.exists_lift_of_range_subset (T := Sp K) p.left (σ c0).left (by
    rintro _ ⟨(a : Sp K), rfl⟩
    rw [Subsingleton.elim a (IsLocalRing.closedPoint K)]
    exact hqmem)
  have hlx : l = x := by
    have h1 : (σ c0).left ≫ T.hom = 𝟙 _ := Over.w (σ c0)
    have h2 : p.left ≫ T.hom = x := Over.w p
    rw [← h2, ← hl, Category.assoc, h1, Category.comp_id]
  refine ⟨c0, Over.OverMorphism.ext ?_⟩
  rw [Over.comp_left, ← hl, hlx]
  congr 1

end GlobalTheory.Poinc.IntTerm

namespace GlobalTheory.Poinc.IntTerm

theorem exhausts_of_generic : ∀ (V : Type) [CommRing V] [IsDomain V] [IsNoetherianRing V]
    (P : PolAV (Sp V)) (N : ℕ), 1 ≤ N → ∀ (C : Type) (b : C → (𝟙_ (Over (Sp V)) ⟶ P.A)),
    (∀ c, b c ^ N = 1) →
    (∀ p : TF (R := V) (AlgebraicClosure (FractionRing V)) ⟶ P.A, p ^ N = 1 → ∃ c, p = toUnit _ ≫ b c) →
    IntTerm.Exhausts P N b := by
  intro V _ _ _ P N hN C b hb H K _ _ x p hp
  obtain ⟨h1, h2, -⟩ := GlobalTheory.abelianSchemeLaws_all.1.mulN (Sp V) P N hN
  rw [Out.mulA, ← GrpTangent.mulN_eq_pow] at h1 h2
  haveI : IsFinite (torsion P.A N).hom :=
    MorphismProperty.of_isPullback (P := @IsFinite) (GrpTangent.isPullback_torsion P.A N) h1
  haveI : Flat (torsion P.A N).hom :=
    MorphismProperty.of_isPullback (P := @Flat) (GrpTangent.isPullback_torsion P.A N) h2
  haveI : Mono (torsion.ι P.A N) := inferInstanceAs (Mono (pullback.fst _ _))
  obtain ⟨hι, hu⟩ := GlobalTheory.LamF.torsion_universal P.A N
  choose σ hσ using fun c => hu _ (b c) (hb c)
  obtain ⟨t, ht⟩ := hu _ p hp
  obtain ⟨c, hc⟩ := exists_eq_section_of_finite_flat (torsion P.A N) σ (fun t' => by
      obtain ⟨c, hc⟩ := H (t' ≫ torsion.ι P.A N) (by rw [← comp_pow, hι, comp_one])
      exact ⟨c, by rw [← cancel_mono (torsion.ι P.A N), hc, Category.assoc, hσ]⟩) K x t
  exact ⟨c, by rw [← ht, hc, Category.assoc, hσ]⟩

end GlobalTheory.Poinc.IntTerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraitPullbackSemiAbelianModelIdentificationStatement
section
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc
open ReciprocityTheory.AnForm.R
open scoped CategoryTheory.Obj
open GlobalTheory.SiegJoin
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HodgeFrameGen
open GlobalTheory.QCoh (pullbackSections)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traitPullback_semiAbelianModel_identification : ∀ {S' : Scheme.{0}} {G : Over S'} [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ {R : Type} [CommRing R] [IsDomain R] {G₁ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁], IsSemiAbelian G₁ →
    ∀ {y : Sp (FractionRing R) ⟶ S'} {α : pullback G₁.hom (jK R) ⟶ G.left},
    IsGrpPullback ((Over.pullback (jK R)).obj G₁) G y α →
    ∀ {W : Type} [CommRing W] [IsDomain W] [IsNoetherianRing W] [IsIntegrallyClosed W] (φ : R →+* W)
    (gam : FractionRing R →+* FractionRing W), (∀ r, gam (algebraMap R _ r) = algebraMap W _ (φ r)) →
    ∀ (χ' : Sp W ⟶ S'), spMap gam ≫ y = jK W ≫ χ' →
    ∃ (ρ' : ((Over.pullback (spMap gam)).obj ((Over.pullback (jK R)).obj G₁)).left ⟶
        ((Over.pullback (spMap φ)).obj G₁).left) (ψ' : ((Over.pullback (spMap φ)).obj G₁).left ⟶ G.left),
      IsGrpPullback ((Over.pullback (spMap gam)).obj ((Over.pullback (jK R)).obj G₁))
        ((Over.pullback (spMap φ)).obj G₁) (jK W) ρ' ∧
      IsGrpPullback ((Over.pullback (spMap φ)).obj G₁) G χ' ψ' ∧
      ρ' ≫ ψ' = pullback.fst _ _ ≫ α ∧
      ρ' ≫ pullback.fst G₁.hom (spMap φ) = pullback.fst _ _ ≫ pullback.fst G₁.hom (jK R) := by
  first | exact @GlobalTheory.HodgeFrameGen.traitPullback_identification | exact GlobalTheory.HodgeFrameGen.traitPullback_identification | (intros; apply GlobalTheory.HodgeFrameGen.traitPullback_identification <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryNormDescentIdealToComponent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

noncomputable section

namespace GlobalTheory.UPoinc.UNormDown

theorem jK_spMap {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (fK : FractionRing R →+* FractionRing S)
    (hc : ∀ a, fK (algebraMap R _ a) = algebraMap S _ (f a)) : jK S ≫ spMap f = spMap fK ≫ jK R := by
  simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  exact (hc a).symm

theorem normDescent : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), 1 ≤ Dw.p + Dw.q → ∀ φ : InvFun (𝓞 E), IsPolFan H.bar (min Dw.p Dw.q) φ → ∀ (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (A : Set C.Z), IsClopen A → IsIrreducible A → (A ∩ Set.range C.i).Nonempty → ∀ (X₁ : USetup C) (ι : ℕ) (J₁ : X₁.M.Z.IdealSheafData), 1 ≤ ι → Set.range X₁.π = A → (∀ x ∈ J₁.support, X₁.π x ∉ Set.range C.i) → UValThru Xo c C.i X₁.π Set.univ φ J₁ ι → ∃ (k : ℕ) (J : C.Z.IdealSheafData), 1 ≤ k ∧ (∀ x ∈ J.support, x ∈ A ∧ x ∉ Set.range C.i) ∧ ∀ (T : UTrait Xo c) (ξ₁ : Sp T.V ⟶ X₁.M.Z), T.y ≫ C.i = jK T.V ≫ ξ₁ ≫ X₁.π → idlAlong J (ξ₁ ≫ X₁.π) = idlAlong J₁ ξ₁ ^ k := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C A hAc hAi hAm X₁ ι J₁ hι hπ hsupp hv
  have hne : ((⊤ : X₁.M.Z.Opens) : Set X₁.M.Z).Nonempty := Set.univ_nonempty
  haveI : CharZero X₁.Ω₁ := X₁.ar.char
  haveI hchar : CharZero Γ(X₁.M.Z, ⊤) := RingHom.charZero (X₁.M.res ⊤ hne)
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI := X₁.M.lft
  have hLN : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  obtain ⟨d, J, hd, hJs, hJl⟩ := GlobalTheory.T.norm_descent_idealSheaf_finite_open_closed_image X₁.M.Z C.Z X₁.π X₁.fin inferInstance hLN X₁.normal C.normal
    (by rw [hπ]; exact hAc.isOpen) hchar J₁
  refine ⟨d, J, hd, fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hJs x hx
    exact ⟨hπ ▸ ⟨y, rfl⟩, hsupp y hy⟩
  intro T ξ₁ hgen
  obtain ⟨hdvr, hcpl, hch⟩ := (GlobalTheory.LN.cDvr_iff T.V).1 T.cdvr
  obtain ⟨V', _, _, _, _, f, ψ, hc', hfi, hfl, hψ, hprod⟩ :=
    hJl T.V hcpl (ξ₁ ≫ X₁.π) ⟨ξ₁ (closedPoint T.V), rfl⟩
  let fK : FractionRing T.V →+* FractionRing V' :=
    IsLocalization.map (FractionRing V') f (nonZeroDivisors_le_comap_nonZeroDivisors_of_injective f hfi)
  have hfK : ∀ a, fK (algebraMap T.V _ a) = algebraMap V' _ (f a) := fun a => IsLocalization.map_eq _ a
  have hB : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc'⟩, inferInstance⟩
  obtain ⟨T₂, f₂, fK₂, hi₂, hl₂, -, hc₂, hy₂⟩ := GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint E H Dw l Xo c V' hB inferInstance (spMap fK ≫ T.y)

  have hover : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π →
      T₂.y ≫ C.i = jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π := by
    intro χ hχ
    have e1 : jK T₂.V ≫ (spMap f₂ ≫ χ) ≫ X₁.π = (jK T₂.V ≫ spMap f₂) ≫ (χ ≫ X₁.π) := by
      simp only [Category.assoc]
    have e2 : (jK V' ≫ spMap f) ≫ ξ₁ ≫ X₁.π = spMap fK ≫ T.y ≫ C.i := by
      rw [jK_spMap f fK hfK, Category.assoc, hgen]
    rw [e1, hχ, jK_spMap f₂ fK₂ hc₂, Category.assoc, ← Category.assoc (jK V'), e2, hy₂]
    simp only [Category.assoc]
  have hord : ∀ χ : Sp V' ⟶ X₁.M.Z, χ ≫ X₁.π = spMap f ≫ ξ₁ ≫ X₁.π →
      ∃ a : ℕ, (a : ℝ) = ι * φ.evalZ T₂.be ∧ idlAlong J₁ (spMap f₂ ≫ χ) = Ideal.span {T₂.ϖ ^ a} := by
    intro χ hχ
    obtain ⟨tK, h1, h2⟩ := T₂.gen
    exact hv T₂.V T₂.cdvr T₂.ϖ T₂.irr (spMap f₂ ≫ χ) T₂.y (hover χ hχ) trivial T₂.t tK h1 h2 T₂.P T₂.be T₂.lev
      T₂.mono
  obtain ⟨a₀, ha₀, h₀⟩ := hord (spMap f ≫ ξ₁) (Category.assoc _ _ _)
  have hj : ∀ j, idlAlong J₁ (spMap f₂ ≫ ψ j) = Ideal.span {T₂.ϖ ^ a₀} := by
    intro j
    obtain ⟨a, ha, h⟩ := hord (ψ j) (hψ j)
    rw [h, show a = a₀ from by exact_mod_cast ha.trans ha₀.symm]
  have hcomp : spMap (f₂.comp f) = spMap f₂ ≫ spMap f := by
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  haveI : IsLocalHom (f₂.comp f) := RingHom.isLocalHom_comp f₂ f
  apply GlobalTheory.TraitOrder.map_injective (f₂.comp f) (hi₂.comp hfi)
  have hmp := map_prod (Ideal.mapHom f₂) (fun j => idlAlong J₁ (ψ j)) Finset.univ
  simp only [Ideal.mapHom_apply] at hmp
  rw [← Ideal.map_map, hprod, Ideal.map_pow, ← GlobalTheory.TraitOrder.idlAlong_comp, hcomp, Category.assoc, h₀, hmp]
  simp only [← GlobalTheory.TraitOrder.idlAlong_comp, hj, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end GlobalTheory.UPoinc.UNormDown
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryTraitLiftsToThetaSetupModel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

open GlobalTheory.Poinc.TraitLift in

theorem exists_uTrait_lift_setup (hExt : UTraitExtSt) : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), IsClopen (Set.range X₁.π) → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ C.Z), T.y ≫ C.i = jK T.V ≫ ξ → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : UTrait Xo c) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ T'.y ≫ C.i = jK T'.V ≫ ξ₁ ≫ X₁.π := by
  intro E _ _ _ H Dw l Xo c C X₁ hcl T ξ hξ hc
  haveI : IsFinite X₁.π := X₁.fin
  obtain ⟨hdvr, hcpl, hch⟩ := T.cdvr
  haveI := hdvr
  haveI := hcpl
  haveI := hch
  have hgen : (jK T.V ≫ ξ) (closedPoint (FractionRing T.V)) ∈ Set.range X₁.π :=
    mem_of_closedPoint _ hcl.isOpen T.V ξ hc _
  obtain ⟨L, _, _, _, η, hη⟩ := exists_finite_point X₁.π (FractionRing T.V) (jK T.V ≫ ξ) hgen
  obtain ⟨V₂, _, _, _, j, e, hB, hD, hj, hjl, he⟩ := exists_closure T.V L
  have hring : (algebraMap V₂ (FractionRing V₂)).comp j =
      (e.comp (algebraMap (FractionRing T.V) L)).comp (algebraMap T.V (FractionRing T.V)) :=
    RingHom.ext fun a => (he a).symm
  haveI : ValuationRing V₂ := inferInstance
  have hsq : (spMap e ≫ η) ≫ X₁.π = jK V₂ ≫ (spMap j ≫ ξ) := by
    rw [Category.assoc, hη, ← Category.assoc, spMap_comp', ← Category.assoc, ← Category.assoc, spMap_comp',
      show jK V₂ = spMap (algebraMap V₂ (FractionRing V₂)) from rfl, spMap_comp', hring]
  obtain ⟨l₁, hl1, -⟩ := exists_lift_of_isFinite X₁.π V₂ (spMap e ≫ η) (spMap j ≫ ξ) hsq
  obtain ⟨T', f'', fK'', hinj'', hloc'', -, hc'', hy''⟩ := hExt E H Dw l Xo c V₂ hB hD
    (spMap (e.comp (algebraMap (FractionRing T.V) L)) ≫ T.y)
  have hring2 : (algebraMap T'.V (FractionRing T'.V)).comp (f''.comp j) =
      (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))).comp (algebraMap T.V (FractionRing T.V)) := by
    ext a
    simp only [RingHom.comp_apply]
    rw [← hc'', ← he]
  have key : jK T'.V ≫ spMap (f''.comp j) = spMap (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))) ≫ jK T.V := by
    rw [show jK T'.V = spMap (algebraMap T'.V (FractionRing T'.V)) from rfl,
      show jK T.V = spMap (algebraMap T.V (FractionRing T.V)) from rfl, spMap_comp', spMap_comp', hring2]
  haveI := hloc''
  refine ⟨T', f''.comp j, fK''.comp (e.comp (algebraMap (FractionRing T.V) L)), spMap f'' ≫ l₁, hinj''.comp hj,
    inferInstance, fun a => (RingHom.congr_fun hring2 a).symm, ?_, ?_, ?_⟩
  · rw [hy'', ← Category.assoc, spMap_comp']
  · rw [Category.assoc, hl1, ← Category.assoc, spMap_comp']
  · symm
    calc jK T'.V ≫ (spMap f'' ≫ l₁) ≫ X₁.π = jK T'.V ≫ spMap (f''.comp j) ≫ ξ := by
          rw [Category.assoc, hl1, ← spMap_comp', Category.assoc]
      _ = spMap (fK''.comp (e.comp (algebraMap (FractionRing T.V) L))) ≫ jK T.V ≫ ξ := by
          rw [← Category.assoc, key, Category.assoc]
      _ = T'.y ≫ C.i := by
          rw [← hξ, hy'', ← spMap_comp']
          simp only [Category.assoc]

theorem uTraitLift_setup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (C : UCompact Xo c) (X₁ : USetup C), IsClopen (Set.range X₁.π) → ∀ (T : UTrait Xo c) (ξ : Sp T.V ⟶ C.Z), T.y ≫ C.i = jK T.V ≫ ξ → ξ (closedPoint T.V) ∈ Set.range X₁.π → ∃ (T' : UTrait Xo c) (f : T.V →+* T'.V) (fK : FractionRing T.V →+* FractionRing T'.V) (ξ₁ : Sp T'.V ⟶ X₁.M.Z), Function.Injective f ∧ IsLocalHom f ∧ (∀ a, fK (algebraMap T.V (FractionRing T.V) a) = algebraMap T'.V (FractionRing T'.V) (f a)) ∧ T'.y = spMap fK ≫ T.y ∧ spMap f ≫ ξ = ξ₁ ≫ X₁.π ∧ T'.y ≫ C.i = jK T'.V ≫ ξ₁ ≫ X₁.π :=
  exists_uTrait_lift_setup GlobalTheory.T.exists_unitaryTrait_through_moduliGenericPoint

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinKernelLinearAlgebraTrivialStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.zarhin_kernel_linearAlgebra_trivial : ∀ (d : ℕ) (GA GB : Type) [CommGroup GA] [CommGroup GB] (f : GA →* GB) (g : GB →* GA), 0 < d → (∀ a, g (f a) = a ^ d) → ∀ (u : Fin 4 → GA) (v : Fin 4 → GB), (∀ i, f (u i) * ∏ j, v j ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ j, f (∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i) * v j ^ d = 1) → ((∀ j, v j = 1) → ∀ j, ∏ i, u i ^ GlobalTheory.ZarhinFam.quat d j i = 1) → (∀ i, u i = 1) ∧ ∀ j, v j = 1 := by
  first | (exact @GlobalTheory.ZarhinFam.zarhin_kernel_trivial) | (exact GlobalTheory.ZarhinFam.zarhin_kernel_trivial) | (intros; apply GlobalTheory.ZarhinFam.zarhin_kernel_trivial  <;> assumption)
end

