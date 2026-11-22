import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0023
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0002
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0067
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0089
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.BtExistsBc
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0091
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0003
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CpIntegersValuationRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem norm_prime_padicComplex (p : Nat.Primes) : ‖((p : ℕ) : ℂ_[p])‖ = ((p : ℕ) : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] ℂ_[p]), norm_algebraMap', Padic.norm_p]

theorem ocp_integers : ∀ p : Nat.Primes, (NormedField.valuation (K := ℂ_[p])).Integers (OCp p) ∧
    (∃ x : ℂ_[p], 0 < NormedField.valuation (K := ℂ_[p]) x ∧ NormedField.valuation (K := ℂ_[p]) x < 1) ∧
    ∀ x : ℂ_[p], x ∈ (algebraMap (OCp p) ℂ_[p]).range ↔ ‖x‖ ≤ 1 := by
  intro p
  have hI : (NormedField.valuation (K := ℂ_[p])).Integers (GlobalTheory.CompanionTheory.Ar.Flat.CPoint.OCp p) :=
    Valuation.valuationSubring.integers _
  refine ⟨hI, ⟨((p : ℕ) : ℂ_[p]), ?_, ?_⟩, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_zero,
      GlobalTheory.CompanionTheory.Ar.Flat.CPoint.norm_prime_padicComplex]
    exact inv_pos.2 (by exact_mod_cast p.2.pos)
  · rw [NormedField.valuation_apply, ← NNReal.coe_lt_coe, coe_nnnorm, NNReal.coe_one,
      GlobalTheory.CompanionTheory.Ar.Flat.CPoint.norm_prime_padicComplex]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast p.2.one_lt)
  · obtain ⟨y, rfl⟩ := RingHom.mem_range.1 hx
    have h := hI.map_le_one y
    rwa [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one] at h
  · refine RingHom.mem_range.2 (hI.exists_of_le_one ?_)
    rwa [NormedField.valuation_apply, ← NNReal.coe_le_coe, coe_nnnorm, NNReal.coe_one]

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrPointComponentEigenReduction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint.PointVal

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def baseFn {O : Type} [CommRing O] (s : X ⟶ Sp O) (o : O) : Γ(X, ⊤) :=
  s.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of O)).inv.hom o)

set_option backward.isDefEq.respectTransparency false in

theorem baseFn_value {O R : Type} [CommRing O] [CommRing R] [IsLocalRing R] (s : X ⟶ Sp O) (f : Sp R ⟶ X)
    (φ : O →+* R) (hf : f ≫ s = spMap φ) (o : O) :
    (Scheme.stalkClosedPointTo f).hom (X.presheaf.germ ⊤ (centre f) trivial (baseFn s o)) = φ o := by
  have e : X.presheaf.germ ⊤ (f (IsLocalRing.closedPoint R)) trivial ≫ Scheme.stalkClosedPointTo f =
      f.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.appTop]
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of O)).inv ≫ s.appTop ≫ f.appTop ≫
      (Scheme.ΓSpecIso (CommRingCat.of R)).hom = CommRingCat.ofHom φ := by
    rw [← Category.assoc s.appTop, ← Scheme.Hom.comp_appTop, hf, Scheme.ΓSpecIso_naturality,
      Iso.inv_hom_id_assoc]
  rw [← e] at e2
  exact congrArg (fun q => q.hom o) e2

set_option backward.isDefEq.respectTransparency false in

theorem genMap_germ (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (g : Γ(X, ⊤)) :
    genMap ξ p (X.presheaf.germ ⊤ p.1 trivial g) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ ⊤ (genPt ξ) trivial g) := by
  have e := TopCat.Presheaf.germ_stalkSpecializes X.presheaf (U := ⊤) (x := genPt ξ) (y := p.1) trivial p.2
  have e2 := congrArg (fun q => (q ≫ Scheme.stalkClosedPointTo ξ).hom g) e
  exact e2

set_option backward.isDefEq.respectTransparency false in

theorem genMap_specializes (ξ : Sp Ω ⟶ X) (p q : Cpt ξ) (h : p.1 ⤳ q.1) (s : X.presheaf.stalk q.1) :
    genMap ξ p ((X.presheaf.stalkSpecializes h).hom s) = genMap ξ q s := by
  have e := TopCat.Presheaf.stalkSpecializes_comp X.presheaf p.2 h
  have e2 := congrArg (fun r => (r ≫ Scheme.stalkClosedPointTo ξ).hom s) e
  exact e2

theorem exists_inv {A L₁ L₂ : Type} [CommRing A] [Field L₁] [Field L₂] (f₁ : A →+* L₁) (f₂ : A →+* L₂)
    (hl : ∀ b, IsUnit (f₂ b) → IsUnit b) (g : A) (a₁ : L₁) (a₂ : L₂) (ha : a₂ ≠ 0)
    (h₁ : f₁ g = a₁⁻¹) (h₂ : f₂ g = a₂⁻¹) : ∃ u, f₁ u = a₁ ∧ f₂ u = a₂ := by
  obtain ⟨g, rfl⟩ := hl g (by rw [h₂]; exact (inv_ne_zero ha).isUnit)
  refine ⟨(g⁻¹ : Aˣ), ?_, ?_⟩
  · have := map_units_inv f₁.toMonoidHom g
    refine this.trans ?_
    show (f₁ g)⁻¹ = _
    rw [h₁, inv_inv]
  · have := map_units_inv f₂.toMonoidHom g
    refine this.trans ?_
    show (f₂ g)⁻¹ = _
    rw [h₂, inv_inv]

def valMap (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (hi : Function.Injective (genMap ξ p)) {R : Type} [CommRing R]
    (ev : X.presheaf.stalk p.1 →+* R) : regAt ξ p →+* R :=
  ev.comp (RingEquiv.ofBijective (genMap ξ p).rangeRestrict
    ⟨fun _ _ h => hi (congrArg Subtype.val h), (genMap ξ p).rangeRestrict_surjective⟩).symm.toRingHom

theorem valMap_genMap (ξ : Sp Ω ⟶ X) (p : Cpt ξ) (hi : Function.Injective (genMap ξ p)) {R : Type} [CommRing R]
    (ev : X.presheaf.stalk p.1 →+* R) (s : X.presheaf.stalk p.1) (h : genMap ξ p s ∈ regAt ξ p) :
    valMap ξ p hi ev ⟨genMap ξ p s, h⟩ = ev s := by
  have : (RingEquiv.ofBijective (genMap ξ p).rangeRestrict
      ⟨fun _ _ h => hi (congrArg Subtype.val h), (genMap ξ p).rangeRestrict_surjective⟩).symm
      ⟨genMap ξ p s, h⟩ = s := by
    rw [RingEquiv.symm_apply_eq]
    rfl
  show ev _ = ev s
  exact congrArg ev this

variable {O F V K : Type} [CommRing O] [Field F] [CommRing V] [IsLocalRing V] [Field K] [Algebra V K]

theorem exists_germ (ξ : Sp Ω ⟶ X) (s : X ⟶ Sp O) (inc : F →+* Ω) (β : O →+* F) (βK : F →+* K) (y : Sp K ⟶ X)
    (hξ : ξ ≫ s = spMap (inc.comp β)) (hy : y ≫ s = spMap (βK.comp β)) (h₁ : genPt ξ ⤳ centre y) (x : F)
    (hx : x ∈ β.range ∨ x⁻¹ ∈ β.range) :
    ∃ u : X.presheaf.stalk (centre y), genMap ξ ⟨_, h₁⟩ u = inc x ∧ (Scheme.stalkClosedPointTo y).hom u = βK x := by
  have key : ∀ o : O, genMap ξ ⟨_, h₁⟩ (X.presheaf.germ ⊤ (centre y) trivial (baseFn s o)) = inc (β o) ∧
      (Scheme.stalkClosedPointTo y).hom (X.presheaf.germ ⊤ (centre y) trivial (baseFn s o)) = βK (β o) := by
    intro o
    refine ⟨?_, baseFn_value s y (βK.comp β) hy o⟩
    exact (genMap_germ ξ ⟨_, h₁⟩ (baseFn s o)).trans (baseFn_value s ξ (inc.comp β) hξ o)
  by_cases h0 : x = 0
  · subst h0
    exact ⟨0, (map_zero _).trans (map_zero inc).symm,
      (map_zero (Scheme.stalkClosedPointTo y).hom).trans (map_zero βK).symm⟩
  rcases hx with ⟨o, rfl⟩ | ⟨o, ho⟩
  · exact ⟨_, key o⟩
  obtain ⟨k1, k2⟩ := key o
  rw [ho] at k1 k2
  exact exists_inv (genMap ξ ⟨_, h₁⟩) (Scheme.stalkClosedPointTo y).hom
    (fun b hb => (Scheme.isLocalHom_stalkClosedPointTo' y).map_nonunit b hb) _ (inc x) (βK x) ((map_ne_zero βK).2 h0)
    (k1.trans (map_inv₀ inc x)) (k2.trans (map_inv₀ βK x))

theorem val_abs (ξ : Sp Ω ⟶ X) (hg : IsCptGen ξ) (s : X ⟶ Sp O) (inc : F →+* Ω) (β : O →+* F) (βK : F →+* K)
    (y : Sp K ⟶ X) (z : Sp V ⟶ X) (hξ : ξ ≫ s = spMap (inc.comp β)) (hy : y ≫ s = spMap (βK.comp β))
    (hz : spMap (algebraMap V K) ≫ z = y) (h₁ : genPt ξ ⤳ centre y)
    (hF : ∀ x : F, x ∈ β.range ∨ x⁻¹ ∈ β.range) :
    ∃ (h₂ : genPt ξ ⤳ centre z) (ψ : regAt ξ ⟨_, h₁⟩ →+* K),
      centre y ⤳ centre z ∧ regAt ξ ⟨_, h₂⟩ ≤ regAt ξ ⟨_, h₁⟩ ∧
      (∀ a : regAt ξ ⟨_, h₁⟩, ValAt ξ y (a : Ω) (ψ a)) ∧
      (∀ (a : Ω) (r : K), ValAt ξ y a r → ∃ h, ψ ⟨a, h⟩ = r) ∧
      (∀ (a : Ω) (h : a ∈ regAt ξ ⟨_, h₁⟩), a ∈ regAt ξ ⟨_, h₂⟩ → ψ ⟨a, h⟩ ∈ (algebraMap V K).range) ∧
      ∀ x : F, ∃ h : inc x ∈ regAt ξ ⟨_, h₁⟩, ψ ⟨_, h⟩ = βK x := by
  have hsp : centre y ⤳ centre z := by
    subst hz
    exact (IsLocalRing.specializes_closedPoint _).map z.continuous
  have h₂ : genPt ξ ⤳ centre z := h₁.trans hsp
  let ψ : regAt ξ ⟨_, h₁⟩ →+* K := valMap ξ ⟨_, h₁⟩ (hg.inj _) (Scheme.stalkClosedPointTo y).hom
  have c3 : ∀ a : regAt ξ ⟨_, h₁⟩, ValAt ξ y (a : Ω) (ψ a) := by
    rintro ⟨_, s', rfl⟩
    exact ⟨h₁, s', rfl, (valMap_genMap ξ ⟨_, h₁⟩ (hg.inj _) _ s' _).symm⟩
  have c4 : ∀ (a : Ω) (r : K), ValAt ξ y a r → ∃ h, ψ ⟨a, h⟩ = r := by
    rintro a r ⟨h, s', rfl, rfl⟩
    exact ⟨⟨s', rfl⟩, valMap_genMap ξ ⟨_, h₁⟩ (hg.inj _) _ s' _⟩
  refine ⟨h₂, ψ, hsp, ?_, c3, c4, ?_, ?_⟩
  · rintro _ ⟨s', rfl⟩
    refine ⟨(X.presheaf.stalkSpecializes hsp).hom s', ?_⟩
    exact genMap_specializes ξ ⟨_, h₁⟩ ⟨_, h₂⟩ hsp s'
  · rintro a h ⟨s', rfl⟩
    have v : ValAt ξ z (genMap ξ ⟨_, h₂⟩ s') ((Scheme.stalkClosedPointTo z).hom s') := ⟨h₂, s', rfl, rfl⟩
    have v' := GlobalTheory.T.valAt_comp_local_hom X Ω ξ V K (algebraMap V K) z _ _ v (by rw [hz]; exact h₁)
    rw [hz] at v'
    obtain ⟨h', e⟩ := c4 _ _ v'
    exact ⟨_, e.symm⟩
  · intro x
    obtain ⟨u, e1, e2⟩ := exists_germ ξ s inc β βK y hξ hy h₁ x (hF x)
    obtain ⟨h, e⟩ := c4 _ _ (⟨h₁, u, e1, e2⟩ : ValAt ξ y (inc x) (βK x))
    exact ⟨h, e⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint.PointVal

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem point_val : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (j : K →+* ℂ_[p]) (βK : c.F →+* K) (y : Sp K ⟶ Xo.XF c) (z : Sp V ⟶ Y.X),
    Function.Injective β → (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range) →
    j.comp βK = κ → y ≫ pullback.snd _ _ = spMap βK → Set.range y ⊆ U → spMap (algebraMap V K) ≫ z = y ≫ Y.j →
    ∃ (h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)) (h₂ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre z)
      (ψ : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ →+* K),
      centre (y ≫ Y.j) ⤳ centre z ∧ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ ≤ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩ ∧
      (∀ a : regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) (a : Z.Ω) (ψ a)) ∧
      (∀ (a : Z.Ω) (r : K), ValAt (Z.ξ₀ ≫ Y.j) (y ≫ Y.j) a r → ∃ h, ψ ⟨a, h⟩ = r) ∧
      (∀ (a : Z.Ω) (h : a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩), a ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₂⟩ →
        ψ ⟨a, h⟩ ∈ (algebraMap V K).range) ∧
      ∀ x : c.F, ∃ h : Z.inc x ∈ regAt (Z.ξ₀ ≫ Y.j) ⟨_, h₁⟩, ψ ⟨_, h⟩ = βK x := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y U Z p κ V K _ _ _ _ _ _ j βK y z hβ hκ hj hjk hy hU hz
  have hsj : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
    rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]
  have hξ : (Z.ξ₀ ≫ Y.j) ≫ Y.s = spMap (Z.inc.comp β) := by
    rw [Category.assoc, hsj, ← Category.assoc, Z.over_inc, ← Spec.map_comp]
    rfl
  have hy' : (y ≫ Y.j) ≫ Y.s = spMap (βK.comp β) := by
    rw [Category.assoc, hsj, ← Category.assoc, hy, ← Spec.map_comp]
    rfl
  have h₁ : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j) :=
    ((Z.closure _).1 (hU ⟨IsLocalRing.closedPoint K, rfl⟩)).map Y.j.continuous
  have hF : ∀ x : c.F, x ∈ β.range ∨ x⁻¹ ∈ β.range := by
    intro x
    by_cases h : ‖κ x‖ ≤ 1
    · exact Or.inl ((hκ x).1 h)
    · refine Or.inr ((hκ _).1 ?_)
      rw [map_inv₀, norm_inv]
      exact inv_le_one_of_one_le₀ (not_le.1 h).le
  obtain ⟨h₂, ψ, r⟩ := PointVal.val_abs (Z.ξ₀ ≫ Y.j) Z.gen Y.s Z.inc β βK (y ≫ Y.j) z hξ hy' hz h₁ hF
  exact ⟨h₁, h₂, ψ, r⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.DvrPointEigenFrameReduction
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

theorem exists_modelPoint_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (β : O →+* c.F) (Y : Model Xo c β) (p : Nat.Primes) (κ : c.F →+* ℂ_[p]) (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K] [IsFractionRing V K] (j : K →+* ℂ_[p]) (βK : c.F →+* K) (y : Sp K ⟶ Xo.XF c),
    (∀ x : c.F, ‖κ x‖ ≤ 1 ↔ x ∈ β.range) → (∀ a : K, ‖j a‖ ≤ 1 ↔ a ∈ (algebraMap V K).range) → j.comp βK = κ →
    y ≫ pullback.snd _ _ = spMap βK → ∃ z : Sp V ⟶ Y.X, spMap (algebraMap V K) ≫ z = y ≫ Y.j := by
  intro E _ _ _ H D l Xo c O _ _ _ β Y p κ V K _ _ _ _ _ _ j βK y hκ hj hjκ hy
  have hpr : IsProper Y.s := GlobalTheory.SchemeWords.isProper_of_isProjOver Y.proj
  have hmem : ∀ o : O, (βK.comp β) o ∈ (algebraMap V K).range := by
    intro o
    refine (hj _).1 ?_
    have h1 : j (βK (β o)) = κ (β o) := by rw [← hjκ]; rfl
    simp only [RingHom.comp_apply]
    rw [h1]
    exact (hκ _).2 ⟨o, rfl⟩
  let e : V ≃+* (algebraMap V K).range :=
    RingEquiv.ofBijective (algebraMap V K).rangeRestrict
      ⟨fun a b h => IsFractionRing.injective V K (congrArg Subtype.val h),
        (algebraMap V K).rangeRestrict_surjective⟩
  let b : O →+* V := e.symm.toRingHom.comp ((βK.comp β).codRestrict _ hmem)
  have hb : (algebraMap V K).comp b = βK.comp β := by
    ext o
    have h2 : e (b o) = (βK.comp β).codRestrict _ hmem o := e.apply_symm_apply _
    exact congrArg Subtype.val h2
  have hsq : (y ≫ Y.j) ≫ Y.s = Spec.map (CommRingCat.ofHom ((algebraMap V K).comp b)) := by
    rw [hb]
    have h3 : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
      simp only [Model.j, Category.assoc]
      rw [pullback.condition, ← Category.assoc, Y.jQ_over]
    rw [Category.assoc, h3, ← Category.assoc, hy]
    simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨z, ⟨hz, _⟩, _⟩ := existsUnique_valuationRing_lift O V K b Y.X Y.s (y ≫ Y.j) hsq
  exact ⟨z, hz⟩

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFrameIffEigenspaceBasis
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame

variable {S : Scheme.{0}} {R : Type} [CommRing R] {G : Over S} [GrpObj G] {x : Sp R ⟶ S} {Em : Type}
  [AddCommGroup Em] [Module R Em]

theorem isComb_pt_iff (M : LieModel G x Em) {n : ℕ} (b : Fin n → Em) (cf : Fin n → R) (w : epsAt x ⟶ G) :
    IsComb cf (fun i => M.pt (b i)) w ↔ w = M.pt (∑ i, cf i • b i) := by
  have hsum : M.pt (∑ i, cf i • b i) = (List.ofFn fun i => M.pt (cf i • b i)).prod :=
    GlobalTheory.CompanionTheory.Ar.CombEig.pt_sum M fun i => cf i • b i
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hue : u = fun i => M.pt (cf i • b i) :=
      funext fun i => Over.OverMorphism.ext (by rw [hu i, M.smul])
    rw [hsum, hue]
  · rintro rfl
    exact ⟨fun i => M.pt (cf i • b i), fun i => M.smul _ _, hsum⟩

theorem isEigVec_pt_iff {Oe : Type} [CommRing Oe] (M : LieModel G x Em) (act : OAct Oe G)
    {ρ : Oe →+* Module.End R Em} (τ : Oe →+* R) (hρ : M.IsActOf act.act ρ) (e : Em) :
    IsEigVec act x τ (M.pt e) ↔ e ∈ eigSp ρ τ := by
  have hmem : e ∈ eigSp ρ τ ↔ ∀ a, ρ a e = τ a • e := by
    simp [eigSp, Submodule.mem_iInf, sub_eq_zero]
  rw [hmem]
  constructor
  · intro h a
    exact M.inj (Over.OverMorphism.ext (by rw [hρ a e, M.smul]; exact h.2 a))
  · intro h
    exact ⟨M.tan e, fun a => by rw [← hρ a e, h a, M.smul]⟩

theorem isEigFrame_pt_iff : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (Em : Type)
    [AddCommGroup Em] [Module R Em] (M : LieModel G x Em) (Oe : Type) [CommRing Oe] (act : OAct Oe G)
    (ρ : Oe →+* Module.End R Em) (τ : Oe →+* R) (n : ℕ) (b : Fin n → Em), M.IsActOf act.act ρ →
    (IsEigFrame act x τ (fun i => M.pt (b i)) ↔
      (∀ i, b i ∈ eigSp ρ τ) ∧ ∀ e ∈ eigSp ρ τ, ∃! cf : Fin n → R, e = ∑ i, cf i • b i) := by
  intro S R _ G _ _ x Em _ _ M Oe _ act ρ τ n b hρ
  have eig := isEigVec_pt_iff M act τ hρ
  have key := isComb_pt_iff M b
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (eig _).1 (h1 i), fun e he => ?_⟩
    obtain ⟨c, hc, hu⟩ := h2 (M.pt e) ((eig e).2 he)
    exact ⟨c, M.inj ((key c _).1 hc), fun c' hc' => hu c' ((key c' _).2 (congrArg M.pt hc'))⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun i => (eig _).2 (h1 i), fun w hw => ?_⟩
    obtain ⟨e, rfl⟩ := M.onto w hw.1
    obtain ⟨c, hc, hu⟩ := h2 e ((eig e).1 hw)
    exact ⟨c, (key c _).2 (congrArg M.pt hc), fun c' hc' => hu c' (M.inj ((key c' _).1 hc'))⟩

end GlobalTheory.CompanionTheory.Ar.Flat.LieEigFrame
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceDecompositionInternalStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenspace_decomposition_internal : ∀ (Ω : Type) [Field Ω] [CharZero Ω] (E : Type) [AddCommGroup E] [Module Ω E] (F : Type) [Field F] [NumberField F] (ρ : NumberField.RingOfIntegers F →+* Module.End Ω E) (I : Type) [Fintype I] [DecidableEq I] (σ : I → (NumberField.RingOfIntegers F →+* Ω)), Function.Injective σ → Fintype.card I = Module.finrank ℚ F → DirectSum.IsInternal fun s => eigSp ρ (σ s) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isInternal_eigSp | exact GlobalTheory.CompanionTheory.Ar.isInternal_eigSp | (intros; apply GlobalTheory.CompanionTheory.Ar.isInternal_eigSp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EqOfEqGenericProjectiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_eq_generic_projective : ∀ (R : Type) [CommRing R] (Z W : Scheme.{0}) [IsIntegral Z] (s : W ⟶ Sp R) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ Z) (f g : Z ⟶ W), IsProjOver s → (∀ q : Z, genPt ξ ⤳ q) → ξ ≫ f = ξ ≫ g → f = g := by
  first | exact @GlobalTheory.CompanionTheory.Ar.maps_eq_of_eq_at_generic | exact GlobalTheory.CompanionTheory.Ar.maps_eq_of_eq_at_generic | (intros; apply GlobalTheory.CompanionTheory.Ar.maps_eq_of_eq_at_generic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsBaseChangeGroup
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem QFGroup.exists_isBaseChange_of_injective : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] (φ : R →+* R'), Function.Injective φ → ∃ (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ φ F :=
  @PositivityTheory.UnitarySelfGeneration.bt_exists_bc

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsCompatibleLieModel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

theorem GlobalTheory.CompanionTheory.Ar.FrameModelsGeometry.main : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G G' : Over X) [GrpObj G] [GrpObj G'] (GΩ : Over (Sp Ω)) [GrpObj GΩ] (φ : GΩ.left ⟶ G.left) (φ' : GΩ.left ⟶ G'.left), IsGrpPullback GΩ G ξ φ → IsGrpPullback GΩ G' ξ φ' → ∀ (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V), ∃ M' : LieModel G' ξ V, ∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left := by
  intro X Ω _ ξ G G' _ _ GΩ _ φ φ' h h' V _ _ M
  obtain ⟨M₀, h₀⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main Ω X ξ G GΩ φ V h).1 M
  obtain ⟨M', h₁⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main Ω X ξ G' GΩ φ' V h').2 M₀
  exact ⟨M', fun e => ⟨M₀.pt e, h₀ e, h₁ e⟩⟩
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FieldPointLiftsGenericFibreStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.M0
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.field_point_lifts_generic_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), (letI := β.toAlgebra; IsFractionRing O c.F) → ∀ (K : Type) [Field K] (x : Sp K ⟶ Y.X), Set.range x ⊆ Set.range Y.j → ∃ y : Sp K ⟶ Xo.XF c, y ≫ Y.j = x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.M0.fieldPoint_lifts | exact GlobalTheory.CompanionTheory.Ar.M0.fieldPoint_lifts | (intros; apply GlobalTheory.CompanionTheory.Ar.M0.fieldPoint_lifts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlatHermUnitSectionAvoidStatement
section
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 GlobalTheory.CompanionTheory.Ar.Flat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flat_herm_unit_section_avoid : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] (F : Type) [Field F] [NumberField F] (y : (Σ k, ι k) → Ω) (φ : F →+* Ω) (A : HermLine ι) (S : FlatHerm y φ A) (d : ℕ) (W : Ideal (MRing ι)), OverInt y φ → IsArithVar (mCoordIdeal y) d → IsSmoothHerm A → IsMultiProjPrime W → mCoordIdeal y ≤ W → ∃ (f' g' : MRing ι) (df' dg' : K → ℕ), IsMultiHomog f' df' ∧ IsMultiHomog g' dg' ∧ (∀ k, (df' k : ℤ) - dg' k = S.M * A.a k) ∧ f' ∉ W ∧ g' ∉ W ∧ f' * S.g - g' * S.f ∈ mCoordIdeal y ∧ IsUnitSec (mCoordIdeal y) f' g' ∧ ∀ σ z, PtOver y φ σ z → ‖evC z f'‖ = (S.κ σ * A.h z) ^ S.M * ‖evC z g'‖ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.exists_rep | exact GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.exists_rep | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.FlatHerm.exists_rep <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FullTorsionPullbackStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.full_torsion_pullback : ∀ (X X' : Scheme.{0}) (Ω Ω' : Type) [Field Ω] [Field Ω'] (ξ : Sp Ω ⟶ X) (ξ' : Sp Ω' ⟶ X') (f : X' ⟶ X) (i : Ω →+* Ω') (G : Over X) (G' : Over X') [GrpObj G] [GrpObj G'] [IsCommMonObj G] [IsCommMonObj G'] (φ : G'.left ⟶ G.left) (n : ℕ), GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f i → IsGrpPullback G' G f φ → FullTorsion G ξ n → FullTorsion G' ξ' n := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HcptPull.fullTorsion_of_dominates | exact GlobalTheory.CompanionTheory.Ar.HcptPull.fullTorsion_of_dominates | (intros; apply GlobalTheory.CompanionTheory.Ar.HcptPull.fullTorsion_of_dominates <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointComponentLocalRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.CPoint

namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

noncomputable def regAtEquivStalk {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
    (h : IsCptGen ξ) (q : Cpt ξ) : X.presheaf.stalk q.1 ≃+* regAt ξ q :=
  RingEquiv.ofBijective (genMap ξ q).rangeRestrict
    ⟨fun _ _ e => h.inj q (congrArg Subtype.val e), (genMap ξ q).rangeRestrict_surjective⟩

theorem isLocalRing_regAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → ∀ q : Cpt ξ, IsLocalRing (regAt ξ q) := by
  intro X Ω _ ξ h q
  exact (regAtEquivStalk h q).isLocalRing

end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end

