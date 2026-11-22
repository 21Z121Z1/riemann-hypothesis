import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0041
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrData
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.WchartLePreimage
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0011
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0086
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GermSys
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHodgeLine
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0016
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0001
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0083
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Bundle0016
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0015
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0037

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericPointsInGenericFibre
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.M0
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.M0

theorem genericPoints_subset_range_j : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β), IsDomain O → (letI := β.toAlgebra; IsFractionRing O c.F) → genericPoints Y.X ⊆ Set.range Y.j :=
  @PositivityTheory.HtPt.Ml.generic_points_range

end GlobalTheory.CompanionTheory.Ar.M0
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianPairingTorsionFreeStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_pairing_torsion_free : ∀ (E : Type) [Field E] [NumberField E] (cc : E ≃+* E) (p R N : ℕ) [Fact p.Prime], 1 ≤ R → ¬ (p : ℤ) ∣ NumberField.discr E → ∀ (e : (Fin N → 𝓞 E) →+ (Fin N → 𝓞 E) →+ ZMod (p ^ R)), (∀ (a : 𝓞 E) (x y : Fin N → 𝓞 E), e (a • x) y = e x (RingOfIntegers.mapRingEquiv cc a • y)) → (∀ x, e x = 0 → ∃ x', x = (p ^ R) • x') → ∀ (O Ω : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [Field Ω] [Algebra O Ω], Function.Injective (algebraMap O Ω) → ¬ IsUnit (p : O) → ∀ σ : E →+* Ω, (∀ a : 𝓞 E, ∃ o : O, algebraMap O Ω o = σ (a : E)) → ∃ C : Matrix (Fin N) (Fin N) Ω, (∀ i j, C i j ∈ (algebraMap O Ω).range) ∧ (Matrix.of fun i j => ∑ k, σ (HT.dualInt E k) * ((e (Pi.single i (RingOfIntegers.basis E k)) (Pi.single j 1)).val : Ω)) * C = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.gram_invertible_of_unramified | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.gram_invertible_of_unramified | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.gram_invertible_of_unramified <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat.CPoint

abbrev OCp (p : Nat.Primes) : Type :=
  (NormedField.valuation (K := ℂ_[p])).valuationSubring

def inE {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {l : Level H} (c : Coeff l) (τ : E →+* ℂ) :
    E →+* c.F := τ.codRestrict c.F.toSubfield (c.conj τ)

def stdLat (A C : Type) [CommRing A] [Field C] [Algebra A C] (g : ℕ) : Submodule A (Fin g → C) where
  carrier := {x | ∀ i, x i ∈ (algebraMap A C).range}
  add_mem' := fun ha hb i => add_mem (ha i) (hb i)
  zero_mem' := fun _ => zero_mem _
  smul_mem' := fun a x hx i => by
    rw [Pi.smul_apply, Algebra.smul_def]
    exact mul_mem ⟨a, rfl⟩ (hx i)

section Eval

variable {E : Type} [Field E] [NumberField E] {Ω : Type} [Field Ω] {Vs : Type} [AddCommGroup Vs] [Module Ω Vs]
  {C : Type} [Field C] {g : ℕ}

def comb {R : Subring Ω} (ℓ : Fin g → Vs) (x : Fin g → R) : Vs := ∑ i, (x i : Ω) • ℓ i

def Tied {R : Subring Ω} (ℓ : Fin g → Vs) (ψ : R →+* C) (ρ : 𝓞 E →+* Module.End Ω Vs)
    (ρC : 𝓞 E →+* Module.End C (Fin g → C)) : Prop :=
  ∀ (a : 𝓞 E) (x x' : Fin g → R), ρ a (comb ℓ x) = comb ℓ x' → ρC a (fun i => ψ (x i)) = fun i => ψ (x' i)

def HodgeAt {R : Subring Ω} {N : ℕ} (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (HL : Submodule R (Vs × Module.Dual Ω Vs)) (ℓ : Fin g → Vs) (t : Fin N → Vs × Module.Dual Ω Vs) : Prop :=
  HT.IsFreeOn ρH HL t ∧
    HL.map ((LinearMap.fst Ω Vs (Module.Dual Ω Vs)).restrictScalars R) = Submodule.span R (Set.range ℓ) ∧
    ∀ f : Module.Dual Ω Vs, ((0 : Vs), f) ∈ HL ↔ ∀ e ∈ Submodule.span R (Set.range ℓ), f e ∈ R

def IsEval {R : Subring Ω} (ℓ : Fin g → Vs) (ψ : R →+* C) (ρH : 𝓞 E →+* Module.End Ω (Vs × Module.Dual Ω Vs))
    (ρHC : 𝓞 E →+* Module.End C ((Fin g → C) × Module.Dual C (Fin g → C)))
    (HL : Submodule R (Vs × Module.Dual Ω Vs))
    (ev : HL →ₛₗ[ψ] (Fin g → C) × Module.Dual C (Fin g → C)) : Prop :=
  (∀ (a : 𝓞 E) (h : HL) (h' : ρH a (h : Vs × Module.Dual Ω Vs) ∈ HL), ev ⟨_, h'⟩ = ρHC a (ev h)) ∧
  (∀ (h : HL) (x : Fin g → R), (h : Vs × Module.Dual Ω Vs).1 = comb ℓ x → (ev h).1 = fun i => ψ (x i)) ∧
  (∀ (h : HL) (x : Fin g → R) (r : R), (h : Vs × Module.Dual Ω Vs).1 = 0 →
    (h : Vs × Module.Dual Ω Vs).2 (comb ℓ x) = r → (ev h).2 (fun i => ψ (x i)) = ψ r)

end Eval
end GlobalTheory.CompanionTheory.Ar.Flat.CPoint
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptInteriorIff
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.IntOpen

theorem epi_of_mono_spMap {O F : Type} [CommRing O] [CommRing F] (β : O →+* F) (h : Mono (spMap β))
    {T : Type} [CommRing T] (g₁ g₂ : F →+* T) (e : g₁.comp β = g₂.comp β) : g₁ = g₂ := by
  have h1 : spMap g₁ ≫ spMap β = spMap g₂ ≫ spMap β := by
    rw [← spMap_comp, ← spMap_comp, e]
  have h2 := Spec.map_injective ((cancel_mono (spMap β)).1 h1)
  exact congrArg CommRingCat.Hom.hom h2

theorem lift_local {R : CommRingCat} [IsLocalRing R] {U X : Scheme.{0}} (j : U ⟶ X) [IsOpenImmersion j]
    (g : Spec R ⟶ X) (h : g (IsLocalRing.closedPoint R) ∈ Set.range j) : ∃ u, u ≫ j = g := by
  have hr : Set.range g ⊆ Set.range j := by
    rintro _ ⟨p, rfl⟩
    have hs : p ⤳ IsLocalRing.closedPoint R := IsLocalRing.specializes_closedPoint p
    exact (hs.map g.continuous).mem_open j.isOpenEmbedding.isOpen_range h
  exact ⟨IsOpenImmersion.lift j g hr, IsOpenImmersion.lift_fac _ _ _⟩

theorem interior_iff_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (A : HodgeCpt Y S y) (z : Sp ℂ ⟶ A.X), Mono (spMap β) → Mono Y.j ∧ (A.Interior z ↔ ∃ u : Spec (A.X.presheaf.stalk (centre z)) ⟶ Xo.XF c, u ≫ Y.j = A.X.fromSpecStalk (centre z) ≫ A.f) := by
  intro E _ _ _ H D l Xo c O _ β Y S Ω _ K _ J y A z hβ
  have hab : ∀ x : A.X, A.f x ∈ abLocus Y.t.G ↔ x ∈ abLocus A.t.G :=
    abLocus_pullback abLocusOne Y.t.semi A.m.cart.1
  refine ⟨?_, ?_⟩
  · have : IsOpenImmersion Y.jQ := Y.jQ_open
    unfold Model.j; infer_instance
  constructor
  · intro hx
    have hx' : A.f (centre z) ∈ abLocus Y.t.G := (hab _).2 hx
    haveI : FiniteDimensional ℚ c.F := c.fin
    haveI : NumberField c.F := {}
    haveI : IsReduced A.X := by
      have : ∀ x : A.X, _root_.IsReduced (A.X.presheaf.stalk x) := fun x => by
        have := (A.normal x).1
        infer_instance
      exact isReduced_of_isReduced_stalk A.X
    let g : Spec (A.X.presheaf.stalk (centre z)) ⟶ Sp O := A.X.fromSpecStalk (centre z) ≫ A.f ≫ Y.s
    let θ : O →+* A.X.presheaf.stalk (centre z) := (Spec.preimage g).hom
    have hk : ∀ a, β a = 0 → θ a = 0 := fun a ha =>
      GlobalTheory.T.generic_vanishing_stalk_vanishing A.X Ω O A.ξ A.all (A.f ≫ Y.s) (A.cst.comp β) A.cst_over (centre z) a (by simp [ha])
    have hu : ∀ b, β b ≠ 0 → IsUnit (θ b) := fun b hb =>
      GlobalTheory.T.local_hom_char_zero_units O c.F _ ℂ β θ (Scheme.stalkClosedPointTo z).hom (Scheme.isLocalHom_stalkClosedPointTo' z) hk b hb
    obtain ⟨χ, hχ⟩ := GlobalTheory.T.extend_to_fraction_field O c.F _ β θ (GlobalTheory.T.epi_ring_hom_field_closure O c.F β (fun T _ g₁ g₂ e => epi_of_mono_spMap β hβ g₁ g₂ e)) hu hk
    have w : (A.X.fromSpecStalk (centre z) ≫ A.f) ≫ Y.s = spMap χ ≫ spMap β := by
      rw [← spMap_comp, hχ, Category.assoc]
      change g = _
      rw [← Spec.map_preimage g]
      rfl
    haveI : IsOpenImmersion Y.jQ := Y.jQ_open
    obtain ⟨u, hu⟩ := lift_local Y.jQ (pullback.lift _ _ w) (by
      rw [← Y.ab_gen]
      show (pullback.lift _ _ w ≫ pullback.fst _ _) _ ∈ abLocus _
      rw [pullback.lift_fst]
      have e1 : (A.X.fromSpecStalk (centre z) ≫ A.f) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z))) = A.f (centre z) := by
        show A.f ((A.X.fromSpecStalk (centre z)) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) = _
        rw [Scheme.fromSpecStalk_closedPoint]
      exact e1 ▸ hx')
    refine ⟨u, ?_⟩
    rw [Model.j, ← Category.assoc, hu, pullback.lift_fst]
  · rintro ⟨u, hu⟩
    show centre z ∈ abLocus A.t.G
    rw [← hab]
    have h1 : A.f (centre z) = Y.j (u (IsLocalRing.closedPoint _)) := by
      have e1 := congrArg (fun φ : Spec (A.X.presheaf.stalk (centre z)) ⟶ Y.X => φ (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) hu
      change Y.j (u (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) = A.f ((A.X.fromSpecStalk (centre z)) (IsLocalRing.closedPoint (A.X.presheaf.stalk (centre z)))) at e1
      rw [Scheme.fromSpecStalk_closedPoint] at e1
      exact e1.symm
    rw [h1]
    have h2 : Y.jQ (u (IsLocalRing.closedPoint _)) ∈ Set.range Y.jQ := ⟨_, rfl⟩
    rw [← Y.ab_gen] at h2
    exact h2

end GlobalTheory.CompanionTheory.Ar.IntOpen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeLatticeTransportEquiv
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.Flat

namespace HodgeTransport

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {V V' : Type} [AddCommGroup V] [Module Ω V]
  [AddCommGroup V'] [Module Ω V'] {F F' : Type} [AddCommGroup F] [Module Ω F] [AddCommGroup F'] [Module Ω F']
  {E : Type} [Field E] [NumberField E]

def conjE (e : V ≃ₗ[Ω] V') : (V × Module.Dual Ω V) ≃ₗ[Ω] (V' × Module.Dual Ω V') :=
  e.prodCongr e.symm.dualMap

theorem conjE_apply (e : V ≃ₗ[Ω] V') (y : V × Module.Dual Ω V) :
    conjE e y = (e y.1, y.2 ∘ₗ e.symm.toLinearMap) := rfl

theorem conjE_symm_apply (e : V ≃ₗ[Ω] V') (y : V' × Module.Dual Ω V') :
    (conjE e).symm y = (e.symm y.1, y.2 ∘ₗ e.toLinearMap) := rfl

def cj (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) : 𝓞 E →+* Module.End Ω F' :=
  (g.conjRingEquiv : Module.End Ω F →+* Module.End Ω F').comp ρ

theorem cj_apply (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (a : 𝓞 E) (y : F') :
    cj g ρ a y = g (ρ a (g.symm y)) := rfl

theorem mem_map_equiv (M : Lat ξ F) (g : F ≃ₗ[Ω] F') (p : Cpt ξ) (y : F') :
    y ∈ M.map g.toLinearMap p ↔ g.symm y ∈ M p := by
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa using hx
  · intro h
    exact ⟨_, h, by simp⟩

theorem map_symm_map (M : Lat ξ F) (g : F ≃ₗ[Ω] F') :
    (M.map g.toLinearMap).map g.symm.toLinearMap = M := by
  funext p
  ext y
  rw [mem_map_equiv, mem_map_equiv]
  simp

theorem isFrameAt_map {M : Lat ξ F} (g : F ≃ₗ[Ω] F') {r : ℕ} {b : Fin r → F} {p : Cpt ξ}
    (h : M.IsFrameAt b p) : (M.map g.toLinearMap).IsFrameAt (g ∘ b) p := by
  refine ⟨(LinearMap.linearIndependent_iff g.toLinearMap (LinearEquiv.ker g)).2 h.1, ?_⟩
  change Submodule.map _ (M p) = _
  rw [h.2, Submodule.map_span, Set.range_comp]
  rfl

theorem isFrameAt_map_iff {M : Lat ξ F} (g : F ≃ₗ[Ω] F') {r : ℕ} {b : Fin r → F'} {p : Cpt ξ} :
    (M.map g.toLinearMap).IsFrameAt b p ↔ M.IsFrameAt (g.symm ∘ b) p := by
  constructor
  · intro h
    have := isFrameAt_map g.symm h
    rwa [map_symm_map] at this
  · intro h
    have := isFrameAt_map g h
    have e : g ∘ g.symm ∘ b = b := by funext i; simp
    rwa [e] at this

theorem detLat_map (M : Lat ξ F) (g : F ≃ₗ[Ω] F') {r : ℕ} (u : Fin r → F') :
    detLat (M.map g.toLinearMap) u = detLat M (g.symm ∘ u) := by
  funext p
  simp only [detLat]
  congr 1
  ext t
  refine exists_congr fun A => and_congr_left fun _ => ?_
  rw [isFrameAt_map_iff]
  have e : (g.symm ∘ fun i => ∑ j, A i j • u j) = fun i => ∑ j, A i j • (g.symm ∘ u) j := by
    funext i
    simp
  rw [e]

theorem isFreeOn_map {M : Lat ξ F} (g : F ≃ₗ[Ω] F') {ρ : 𝓞 E →+* Module.End Ω F} {p : Cpt ξ} {N : ℕ}
    {t : Fin N → F} (h : HT.IsFreeOn ρ (M p) t) :
    HT.IsFreeOn (cj g ρ) (M.map g.toLinearMap p) (g ∘ t) := by
  have e : (fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      cj g ρ (RingOfIntegers.basis E q.2) ((g ∘ t) q.1)) =
      g ∘ fun q : Fin N × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
        ρ (RingOfIntegers.basis E q.2) (t q.1) := by
    funext q
    simp [cj_apply]
  refine ⟨?_, ?_, ?_⟩
  · rw [e]
    exact (LinearMap.linearIndependent_iff g.toLinearMap (LinearEquiv.ker g)).2 h.1
  · have e2 : ((M.map g.toLinearMap p : Submodule _ F') : Set F') = g '' (M p : Set F) := rfl
    rw [e2]
    have := Submodule.map_span g.toLinearMap (M p : Set F)
    rw [h.2.1, Submodule.map_top, LinearEquiv.range] at this
    exact this.symm
  · rw [e]
    change Submodule.map _ (M p) = _
    rw [h.2.2, Submodule.map_span, Set.range_comp]
    rfl

theorem eigProj_cj (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (σ : E →+* Ω) (y : F') :
    HT.eigProj (cj g ρ) σ y = g (HT.eigProj ρ σ (g.symm y)) := by
  simp [HT.eigProj, LinearMap.sum_apply, cj_apply, map_sum]

theorem mem_eigSp_cj (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (σ : E →+* Ω) (y : F') :
    y ∈ HT.eigSp (cj g ρ) σ ↔ g.symm y ∈ HT.eigSp ρ σ := by
  rw [HT.LatBasic.mem_eigSp, HT.LatBasic.mem_eigSp]
  refine forall_congr' fun a => ?_
  rw [cj_apply, ← map_smul, LinearEquiv.eq_symm_apply]

theorem eigQuot_map (M : Lat ξ F) (g : F ≃ₗ[Ω] F') (ρ : 𝓞 E →+* Module.End Ω F) (σ : E →+* Ω) :
    (M.map g.toLinearMap).map (HT.eigProj (cj g ρ) σ) = (M.map (HT.eigProj ρ σ)).map g.toLinearMap := by
  funext p
  ext y
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by simp [eigProj_cj]⟩
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩, by simp [eigProj_cj]⟩

variable {L : Lat ξ V} {ρ : 𝓞 E →+* Module.End Ω V} {ρ' : 𝓞 E →+* Module.End Ω V'} {bar : 𝓞 E ≃+* 𝓞 E} {r : ℕ}

def transport (e : V ≃ₗ[Ω] V') (𝓗 : HodgeLat L ρ bar r) (h : ∀ a v, e (ρ a v) = ρ' a (e v)) :
    HodgeLat (L.map e.toLinearMap) ρ' bar r where
  ρH := cj (conjE e) 𝓗.ρH
  HL := 𝓗.HL.map (conjE e).toLinearMap
  act_fst a y := by
    rw [cj_apply, conjE_apply, 𝓗.act_fst, h, conjE_symm_apply]
    simp
  act_inr a φ := by
    rw [cj_apply, conjE_symm_apply]
    simp only [map_zero]
    rw [𝓗.act_inr, conjE_apply]
    refine Prod.ext (by simp) (LinearMap.ext fun x => ?_)
    simp [h]
  map_fst := by
    funext p
    conv_rhs => rw [← 𝓗.map_fst]
    ext y
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  comap_inr := by
    funext p
    ext φ
    have h1 : (φ ∈ (𝓗.HL.map (conjE e).toLinearMap).comap (LinearMap.inr Ω V' (Module.Dual Ω V')) p) ↔
        ((0, φ ∘ₗ e.toLinearMap) : V × Module.Dual Ω V) ∈ 𝓗.HL p := by
      change ((0, φ) : V' × Module.Dual Ω V') ∈ 𝓗.HL.map (conjE e).toLinearMap p ↔ _
      rw [mem_map_equiv, conjE_symm_apply]
      simp
    have h2 : ((0, φ ∘ₗ e.toLinearMap) : V × Module.Dual Ω V) ∈ 𝓗.HL p ↔
        φ ∘ₗ e.toLinearMap ∈ L.dual p := by
      rw [← 𝓗.comap_inr]
      rfl
    rw [h1, h2]
    change (∀ x ∈ L p, φ (e x) ∈ regAt ξ p) ↔ ∀ x ∈ L.map e.toLinearMap p, φ x ∈ regAt ξ p
    constructor
    · rintro hφ _ ⟨z, hz, rfl⟩
      exact hφ z hz
    · intro hφ z hz
      exact hφ _ ⟨z, hz, rfl⟩
  free p := by
    obtain ⟨U, hU, x, hx⟩ := 𝓗.free p
    exact ⟨U, hU, conjE e ∘ x, fun q hq => isFreeOn_map (conjE e) (hx q hq)⟩
  vb := by
    rw [← e.finrank_eq]
    intro p hp
    obtain ⟨U, hU, b, hb, hf⟩ := 𝓗.vb p hp
    refine ⟨U, hU, e ∘ b, ?_, fun q hq hqU => isFrameAt_map e (hf q hq hqU)⟩
    rw [Set.range_comp]
    have := Submodule.map_span e.toLinearMap (Set.range b)
    rw [hb, Submodule.map_top, LinearEquiv.range] at this
    exact this.symm

theorem transport_degZero (e : V ≃ₗ[Ω] V') (𝓗 : HodgeLat L ρ bar r) (h : ∀ a v, e (ρ a v) = ρ' a (e v))
    (σ : E →+* Ω) (ϖ : Ω) (hd : 𝓗.DegZero σ ϖ) : (transport e 𝓗 h).DegZero σ ϖ := by
  intro u hu hsp
  have hq : (transport e 𝓗 h).quot σ = (𝓗.quot σ).map (conjE e).toLinearMap :=
    eigQuot_map 𝓗.HL (conjE e) 𝓗.ρH σ
  rw [hq, detLat_map]
  refine hd _ ((LinearMap.linearIndependent_iff (conjE e).symm.toLinearMap (LinearEquiv.ker _)).2 hu) ?_
  ext y
  have h1 : Set.range ((conjE e).symm ∘ u) = (conjE e).symm.toLinearMap '' Set.range u := Set.range_comp _ _
  rw [h1, ← Submodule.map_span, hsp]
  change _ ↔ y ∈ HT.eigSp 𝓗.ρH σ
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (mem_eigSp_cj (conjE e) 𝓗.ρH σ z).1 hz
  · intro hy
    refine ⟨conjE e y, (mem_eigSp_cj (conjE e) 𝓗.ρH σ _).2 (by simpa using hy), by simp⟩

end HodgeTransport

theorem hodgeLat_transport : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [Field E] [NumberField E] (V V' : Type) [AddCommGroup V] [Module Ω V] [AddCommGroup V'] [Module Ω V'] (e : V ≃ₗ[Ω] V') (L : Lat ξ V) (ρ : 𝓞 E →+* Module.End Ω V) (ρ' : 𝓞 E →+* Module.End Ω V') (bar : 𝓞 E ≃+* 𝓞 E) (r : ℕ) (𝓗 : HodgeLat L ρ bar r), (∀ a v, e (ρ a v) = ρ' a (e v)) → ∃ 𝓗' : HodgeLat (L.map e.toLinearMap) ρ' bar r, ∀ σ ϖ, 𝓗.DegZero σ ϖ → 𝓗'.DegZero σ ϖ := by
  intro X Ω _ ξ E _ _ V V' _ _ _ _ e L ρ ρ' bar r 𝓗 h
  exact ⟨HodgeTransport.transport e 𝓗 h, fun σ ϖ hd => HodgeTransport.transport_degZero e 𝓗 h σ ϖ hd⟩

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntegralPointsEqOfGenericStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_points_eq_of_generic : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω), CoordTie ℤ ξ x → ∀ c : κ, x c ≠ 0 → ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra B Ω], Function.Injective (algebraMap B Ω) → (∀ c', x c' / x c ∈ (algebraMap B Ω).range) → ∀ z z' : Spec (CommRingCat.of B) ⟶ X, Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ z = ξ → Spec.map (CommRingCat.ofHom (algebraMap B Ω)) ≫ z' = ξ → z = z' := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.coordTie_points_eq | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.coordTie_points_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.coordTie_points_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFreeOfSmoothStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_free_of_smooth : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (g : ℕ), SmoothOfRelativeDimension g G.hom → ∀ (R : Type) [CommRing R] [IsLocalRing R] (x : Spec (CommRingCat.of R) ⟶ S) (E : Type) [AddCommGroup E] [Module R E] (M : LieModel G x E), Nonempty (Module.Basis (Fin g) R E) := by
  first | exact @GlobalTheory.CompanionTheory.Relay.lie_model_free_of_smooth | exact GlobalTheory.CompanionTheory.Relay.lie_model_free_of_smooth | (intros; apply GlobalTheory.CompanionTheory.Relay.lie_model_free_of_smooth <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LineBundleSectionDivisibleStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open GlobalTheory.CompanionTheory.Ar.Sl.Reg

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.line_bundle_section_divisible : ∀ (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (π : X ⟶ Sp R) (M : LB X) (s : LB.Sec M) (δ : R), sc π ⊤ δ ≠ 0 → (∀ i (W : X.Opens) (hW : W ≤ M.U i), IsAffineOpen W → ∃ a : Γ(X, W), (X.presheaf.map (homOfLE hW).op).hom (s.f i) = sc π W δ * a) → ∃ s' : LB.Sec M, ∀ i, s.f i = sc π (M.U i) δ * s'.f i := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.Reg.Glue.sec_eq_smul_of_local | exact GlobalTheory.CompanionTheory.Ar.Sl.Reg.Glue.sec_eq_smul_of_local | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.Reg.Glue.sec_eq_smul_of_local <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ModelDescentIntegralClosureStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.model_descent_integral_closure : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Ω : Type) [Field Ω] [CharZero Ω] [Algebra O Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (d : ℕ), IsModelOver (pointIdeal O y) d → IsIntegrallyClosedIn O Ω → ∀ (O' : Type) [CommRing O'] [IsDomain O'] [IsDiscreteValuationRing O'] [Algebra O O'] [IsLocalHom (algebraMap O O')] [Algebra.IsAlgebraic O O'] (Ω' : Type) [Field Ω'] [Algebra Ω Ω'] [Algebra O' Ω'] [Algebra O Ω'] [IsScalarTower O O' Ω'] [IsScalarTower O Ω Ω'], Function.Injective (algebraMap O' Ω') → ∀ (ϖ : O), Irreducible ϖ → ∀ p : ℕ, (p ≠ 0 → ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (φ : Equiv.Perm (Ψ ⊕ Ψ)) (T : LocPair J O (Ψ × Fin N)), T.IsVert (pointIdeal O y) ϖ → FlagChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p j φ (T.map (algebraMap O O')) → FlagChernComparison (pointIdeal O y) d p j φ T) ∧ ∀ (r s : ℕ) (lie : LocPair J O (Fin r)) (om : LocPair J O (Fin s)), lie.IsVert (pointIdeal O y) ϖ → om.IsVert (pointIdeal O y) ϖ → BundleChernComparison (pointIdeal O' (fun v => algebraMap Ω Ω' (y v))) d p (lie.map (algebraMap O O')) (om.map (algebraMap O O')) → BundleChernComparison (pointIdeal O y) d p lie om := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.model_descends_from_dvr_ext | exact GlobalTheory.CompanionTheory.Ar.Num.model_descends_from_dvr_ext | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.model_descends_from_dvr_ext <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ObjMapCompStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.obj_map_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S : Scheme.{0}) (s : S ⟶ Sp B) (S' S'' : Scheme.{0}) (s' : S' ⟶ Sp B) (s'' : S'' ⟶ Sp B) (o : Obj D l b s) (o' : Obj D l b s') (o'' : Obj D l b s'') (f : S' ⟶ S) (f' : S'' ⟶ S') (m : ObjMap o' o f) (m' : ObjMap o'' o' f'), ∃ n : ObjMap o'' o (f' ≫ f), n.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.objMap_exists_comp | exact GlobalTheory.CompanionTheory.Ar.objMap_exists_comp | (intros; apply GlobalTheory.CompanionTheory.Ar.objMap_exists_comp <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.QuasiFiniteGroupFinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.BT

theorem QFGroup.finite_of_qfGroup : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] (Γ : BT.QFGroup R T), Finite T := by
  intro R _ _ T _ Γ
  have hqf : LocallyQuasiFinite Γ.G.hom := Γ.quasiFinite
  have hqc : QuasiCompact Γ.G.hom := Γ.quasiCompact
  let F := pullback Γ.G.hom (genPt R).hom
  let g : F ⟶ Spec (CommRingCat.of (FractionRing R)) := pullback.snd Γ.G.hom (genPt R).hom
  have hK : ∀ u v : Spec (CommRingCat.of (FractionRing R)), u = v := fun u v =>
    Subsingleton.elim (α := PrimeSpectrum (FractionRing R)) u v
  let b : Spec (CommRingCat.of (FractionRing R)) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing R))
  have hgqf : LocallyQuasiFinite g := inferInstance
  have hgqc : QuasiCompact g := inferInstance
  have huniv : g ⁻¹' {b} = Set.univ := by
    ext x; simp [hK (g x) b]
  have hfin : Finite F := by
    have h := g.finite_preimage_singleton b
    rw [huniv] at h
    exact Set.finite_univ_iff.mp h
  have hw : ∀ t, (Γ.pt t).left ≫ Γ.G.hom = 𝟙 _ ≫ (genPt R).hom := fun t => by
    rw [Category.id_comp]; exact Over.w (Γ.pt t)
  let f : T → F := fun t => (pullback.lift _ _ (hw t)) b
  refine Finite.of_injective f ?_
  intro s t hst
  have h := congrArg (pullback.fst Γ.G.hom (genPt R).hom) hst
  simp only [f] at h
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, pullback.lift_fst, pullback.lift_fst] at h
  exact Γ.pt_inj s t b b h

end GlobalTheory.CompanionTheory.Ar.BT
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SabMapId
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_sabMap_id : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0})
    (t : SAB H S), ∃ m : SABMap t t (𝟙 S), m.φ = 𝟙 t.G.left :=
  fun _ _ _ _ _ _ t => ⟨GlobalTheory.ObjRebase.sabMapId t, rfl⟩

end GlobalTheory.CompanionTheory.Ar
end
end

