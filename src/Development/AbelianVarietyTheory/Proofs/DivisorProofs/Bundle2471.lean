import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2259
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2347
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2377
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2429
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitNatCastRes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2406
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2421
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2380
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2189
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2381
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2413
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1849
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2443
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1685
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0095
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0060
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0684
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2422
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartsNormalProjective
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

theorem exists_unit_ratio_of_close : ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → DensSt → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsProjOver s → Flat s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → ∀ (R1 R2 A : Type) [CommRing R1] [CommRing R2] [CommRing A] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X) (w : Sp A ⟶ X) (c1 : (Localization.Away (p : R1))ˣ) (c2 : (Localization.Away (p : R2))ˣ) (a1 : R1 →+* A) (a2 : R2 →+* A), IsOpenImmersion ξ1 → IsOpenImmersion ξ2 → IsOpenImmersion w → spMap a1 ≫ ξ1 = w → spMap a2 ≫ ξ2 = w → (∀ φ : R1 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ1) → ∀ ψ : Localization.Away (p : R1) →+* ℂ_[p], ψ.comp (algebraMap R1 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ1), ‖ψ (c1 : Localization.Away (p : R1)) - κ‖ < ‖κ‖) → (∀ φ : R2 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ2) → ∀ ψ : Localization.Away (p : R2) →+* ℂ_[p], ψ.comp (algebraMap R2 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ2), ‖ψ (c2 : Localization.Away (p : R2)) - κ‖ < ‖κ‖) → ∃ u : Aˣ, (u : A) - 1 ∈ (Ideal.span {(p : A)}).radical ∧ ∀ (χ1 : Localization.Away (p : R1) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : R2) →+* Localization.Away (p : A)), χ1.comp (algebraMap R1 _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap R2 _) = (algebraMap A _).comp a2 → algebraMap A (Localization.Away (p : A)) (u : A) * χ2 (c2 : Localization.Away (p : R2)) = χ1 (c1 : Localization.Away (p : R1)) := by
  intro F _ _ V _ p _ hp hD X s Xw hXi hXn hproj hflat hXw hne K hK R1 R2 A _ _ _ ξ1 ξ2 w c1 c2 a1 a2 hξ1 hξ2 hw e1 e2 hc1 hc2
  classical
  have hlft : LocallyOfFiniteType s := GlobalTheory.T.locallyOfFiniteType_of_isProjOver V X s hproj
  have hu1 : IsUnit (((algebraMap A (Localization.Away (p : A))).comp a1) (p : R1)) := by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : A)) (p : A)
  have hu2 : IsUnit (((algebraMap A (Localization.Away (p : A))).comp a2) (p : R2)) := by
    simpa using IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (p : A)) (p : A)
  let χ1 : Localization.Away (p : R1) →+* Localization.Away (p : A) := IsLocalization.Away.lift (p : R1) hu1
  let χ2 : Localization.Away (p : R2) →+* Localization.Away (p : A) := IsLocalization.Away.lift (p : R2) hu2
  have hχ1 : χ1.comp (algebraMap R1 _) = (algebraMap A _).comp a1 := RingHom.ext fun x => IsLocalization.lift_eq _ x
  have hχ2 : χ2.comp (algebraMap R2 _) = (algebraMap A _).comp a2 := RingHom.ext fun x => IsLocalization.lift_eq _ x
  have hcl := GlobalTheory.T.chart_ratio_on_overlap p X Xw K hK R1 R2 A ξ1 ξ2 w c1 c2 a1 a2 e1 e2 hc1 hc2 χ1 χ2 hχ1 hχ2
  let r : (Localization.Away (p : A))ˣ := Units.map (χ1 : _ →* _) c1 * (Units.map (χ2 : _ →* _) c2)⁻¹
  have hr : (r : Localization.Away (p : A)) * χ2 (c2 : Localization.Away (p : R2)) = χ1 (c1 : Localization.Away (p : R1)) := by
    have h0 : r * Units.map (χ2 : _ →* _) c2 = Units.map (χ1 : _ →* _) c1 := by simp [r]
    have h0' := congrArg Units.val h0
    simpa using h0'
  have hnorm : ∀ φ : A →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ w) → ∀ ψ : Localization.Away (p : A) →+* ℂ_[p],
      ψ.comp (algebraMap A _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ →
      ‖ψ (r : Localization.Away (p : A)) - 1‖ < 1 ∧ ‖ψ (r : Localization.Away (p : A))‖ = 1 ∧
        ‖ψ ((r⁻¹ : (Localization.Away (p : A))ˣ) : Localization.Away (p : A))‖ = 1 := by
    intro φ hφ ψ hψ
    have h := hcl φ hφ ψ hψ
    set b := ψ (χ2 (c2 : Localization.Away (p : R2)))
    have hb : b ≠ 0 := ((c2.isUnit.map χ2).map ψ).ne_zero
    have hbn : 0 < ‖b‖ := norm_pos_iff.2 hb
    have hrb : ψ (r : Localization.Away (p : A)) * b = ψ (χ1 (c1 : Localization.Away (p : R1))) := by
      rw [← map_mul, hr]
    have h1 : ‖ψ (r : Localization.Away (p : A)) - 1‖ < 1 := by
      have : (ψ (r : Localization.Away (p : A)) - 1) * b = ψ (χ1 (c1 : Localization.Away (p : R1))) - b := by
        rw [sub_mul, hrb, _root_.one_mul]
      have h2 : ‖ψ (r : Localization.Away (p : A)) - 1‖ * ‖b‖ < 1 * ‖b‖ := by
        rw [← norm_mul, this, _root_.one_mul]; exact h
      exact lt_of_mul_lt_mul_right h2 hbn.le
    have h3 : ‖ψ (r : Localization.Away (p : A))‖ = 1 := by
      have := IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (x := (1 : ℂ_[p])) (y := ψ (r : Localization.Away (p : A)) - 1) (by rw [norm_one]; exact h1.ne')
      rw [add_sub_cancel, norm_one, max_eq_left h1.le] at this
      exact this
    refine ⟨h1, h3, ?_⟩
    have h4 : ψ (r : Localization.Away (p : A)) * ψ ((r⁻¹ : (Localization.Away (p : A))ˣ) : Localization.Away (p : A)) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have h5 := congrArg norm h4
    rw [norm_mul, h3, _root_.one_mul, norm_one] at h5
    exact h5
  have hfin : ∀ χ1' : Localization.Away (p : R1) →+* Localization.Away (p : A), ∀ χ2' : Localization.Away (p : R2) →+* Localization.Away (p : A),
      χ1'.comp (algebraMap R1 _) = (algebraMap A _).comp a1 → χ2'.comp (algebraMap R2 _) = (algebraMap A _).comp a2 →
      χ1' = χ1 ∧ χ2' = χ2 := fun χ1' χ2' h1 h2 =>
    ⟨IsLocalization.ringHom_ext (Submonoid.powers (p : R1)) (h1.trans hχ1.symm),
      IsLocalization.ringHom_ext (Submonoid.powers (p : R2)) (h2.trans hχ2.symm)⟩
  by_cases hA : Nonempty (Sp A)
  swap
  · have hsub : Subsingleton A := by
      by_contra h
      rw [not_subsingleton_iff_nontrivial] at h
      exact hA inferInstance
    have hsubL : Subsingleton (Localization.Away (p : A)) := by
      refine ⟨fun x y => ?_⟩
      rw [← _root_.mul_one x, ← _root_.mul_one y, ← map_one (algebraMap A (Localization.Away (p : A))), Subsingleton.elim (1 : A) 0, map_zero, mul_zero, mul_zero]
    refine ⟨1, by simp, fun χ1' χ2' _ _ => Subsingleton.elim _ _⟩
  obtain ⟨hdom, hic, alg, hft, hinjV, e, he0, htest⟩ := GlobalTheory.T.open_affine_integrally_closed_domain F V p hp X s Xw hXi hXn hflat hlft hXw hne A w hw hA
  have hbdd : ∀ x : (Localization.Away (p : A))ˣ, (x = r ∨ x = r⁻¹) → ∃ a : A, algebraMap A _ a = (x : Localization.Away (p : A)) := by
    intro x hx
    refine GlobalTheory.T.element_of_dvr_test_points F V p hp A hinjV e he0 _ fun T kO φ hT hkO hφe ψ hψ => ?_
    have := hnorm (kO.comp φ) (htest T kO φ hT hkO hφe) ψ hψ
    rcases hx with rfl | rfl
    · exact this.2.1.le
    · exact this.2.2.le
  obtain ⟨a, ha⟩ := hbdd r (Or.inl rfl)
  obtain ⟨b, hb⟩ := hbdd r⁻¹ (Or.inr rfl)
  have hp0 : (p : A) ≠ 0 := by
    intro h0
    have : algebraMap V A (p : V) = algebraMap V A 0 := by rw [map_natCast, map_zero, h0]
    have h1 := hinjV this
    have h2 := congrArg (fun x : V => (x : F)) h1
    simp at h2
    exact (Fact.out : p.Prime).ne_zero h2
  have hinjL : Function.Injective (algebraMap A (Localization.Away (p : A))) :=
    IsLocalization.injective _ (powers_le_nonZeroDivisors_of_noZeroDivisors hp0)
  have hab : a * b = 1 := hinjL (by rw [map_mul, ha, hb, Units.mul_inv, map_one])
  let u : Aˣ := ⟨a, b, hab, by rw [mul_comm]; exact hab⟩
  refine ⟨u, ?_, fun χ1' χ2' h1 h2 => ?_⟩
  · refine GlobalTheory.T.unit_of_test_point_estimate F V p hp hD X s Xw hXi hflat hlft hXw hne A w hw a fun φ hφ => ?_
    have hpu : IsUnit (((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ) (p : A)) := by
      rw [map_natCast]
      exact IsUnit.mk0 _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
    let ψ : Localization.Away (p : A) →+* ℂ_[p] := IsLocalization.Away.lift (p : A) hpu
    have hψ : ψ.comp (algebraMap A _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ := IsLocalization.lift_comp _
    have := (hnorm φ hφ ψ hψ).1
    rw [← ha] at this
    have e3 : ψ (algebraMap A _ a) = (φ a : ℂ_[p]) := RingHom.congr_fun hψ a
    rw [e3] at this
    exact this
  · obtain ⟨rfl, rfl⟩ := hfin χ1' χ2' h1 h2
    change algebraMap A _ a * _ = _
    rw [ha, hr]

end GlobalTheory.FlatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsChartsNormalProjectiveCovering
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete
open GlobalTheory.FlatModel
open GlobalTheory.UnitGlue

namespace GlobalTheory.UnitGlue

theorem exists_glued_bundle : (∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → DensSt → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsProjOver s → Flat s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → ∀ (R1 R2 A : Type) [CommRing R1] [CommRing R2] [CommRing A] (ξ1 : Sp R1 ⟶ X) (ξ2 : Sp R2 ⟶ X) (w : Sp A ⟶ X) (c1 : (Localization.Away (p : R1))ˣ) (c2 : (Localization.Away (p : R2))ˣ) (a1 : R1 →+* A) (a2 : R2 →+* A), IsOpenImmersion ξ1 → IsOpenImmersion ξ2 → IsOpenImmersion w → spMap a1 ≫ ξ1 = w → spMap a2 ≫ ξ2 = w → (∀ φ : R1 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ1) → ∀ ψ : Localization.Away (p : R1) →+* ℂ_[p], ψ.comp (algebraMap R1 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ1), ‖ψ (c1 : Localization.Away (p : R1)) - κ‖ < ‖κ‖) → (∀ φ : R2 →+* 𝓞_ℂ_[p], IsTest p Xw (spMap φ ≫ ξ2) → ∀ ψ : Localization.Away (p : R2) →+* ℂ_[p], ψ.comp (algebraMap R2 _) = (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ → ∀ κ ∈ K (spMap φ ≫ ξ2), ‖ψ (c2 : Localization.Away (p : R2)) - κ‖ < ‖κ‖) → ∃ u : Aˣ, (u : A) - 1 ∈ (Ideal.span {(p : A)}).radical ∧ ∀ (χ1 : Localization.Away (p : R1) →+* Localization.Away (p : A)) (χ2 : Localization.Away (p : R2) →+* Localization.Away (p : A)), χ1.comp (algebraMap R1 _) = (algebraMap A _).comp a1 → χ2.comp (algebraMap R2 _) = (algebraMap A _).comp a2 → algebraMap A (Localization.Away (p : A)) (u : A) * χ2 (c2 : Localization.Away (p : R2)) = χ1 (c1 : Localization.Away (p : R1))) → DensSt → ∀ (F : Type) [Field F] [NumberField F] (V : ValuationSubring F) [IsDiscreteValuationRing V] (p : ℕ) [Fact p.Prime], (p : F) ∈ V.nonunits → ∀ (X : Scheme.{0}) (s : X ⟶ Sp V) (Xw : X.Opens), IsIntegral X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsProjOver s → Flat s → Xw ≤ X.basicOpen (p : Γ(X, ⊤)) → (Xw : Set X).Nonempty → ∀ (K : (Sp 𝓞_ℂ_[p] ⟶ X) → Set ℂ_[p]), (∀ yb, IsTest p Xw yb → (K yb).Nonempty) → (∀ x : X, UnitChartAt p Xw K x) → ∃ D : LB X, D.IsLB ∧ (∃ t : (D.pull (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.reducedSpecialι s)).Gen, t.IsGen) ∧ ∃ sig : (D.pull (GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s)).Gen, sig.IsGen ∧ ∀ yb, IsTest p Xw yb → ∀ (y : Spec (.of ℂ_[p]) ⟶ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericFibre s), y ≫ GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.genericι s = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ yb → ∀ (e : (D.pull yb).Gen) (cc : ℂ_[p]ˣ), e.IsGen → GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits.IsCoord s D sig yb y e cc → ∀ κ ∈ K yb, ‖(cc : ℂ_[p])‖ = ‖κ‖ := by
  intro ZetaZeros hDens F _ _ V _ p _ hp X s Xw hXi hXn hproj hflat hXw hne K hK h
  have hR : ∀ x y : X, ∃ u, RatioProp h x y u := by
    intro x y
    obtain ⟨A, _, w, a1, a2, hw, h1, h2, hr⟩ :=
      GlobalTheory.T.exists_affine_intersection_charts V X s hproj (cR h x) (cR h y) (cξ h x) (cξ h y) inferInstance inferInstance
    obtain ⟨u, hu1, hu2⟩ := ZetaZeros F V p hp hDens X s Xw hXi hXn hproj hflat hXw hne K hK (cR h x) (cR h y) A (cξ h x)
      (cξ h y) w (cu h x) (cu h y) a1 a2 inferInstance inferInstance hw h1 h2 (c_spec h x).2.2 (c_spec h y).2.2
    exact GlobalTheory.T.unit_ratio_on_chart_overlap p X Xw K h x y A w a1 a2 hw h1 h2 hr u hu1 hu2
  refine ⟨glueLB h, GlobalTheory.T.glued_line_bundle_invertible p X Xw K h hXi hne hXw hR, GlobalTheory.T.glued_bundle_special_fibre_generator F V p hp X s Xw K h hR, sigGen h s,
    GlobalTheory.T.glued_generator_is_generator F V p X s Xw K h hR, ?_⟩
  intro yb hyb y hy e cc _ hco κ hκ
  obtain ⟨φ, hφ⟩ := GlobalTheory.T.local_point_factors_open_immersion 𝓞_ℂ_[p] X (cR h (yb (IsLocalRing.closedPoint 𝓞_ℂ_[p]))) (cξ h _) yb inferInstance
    (c_spec h _).2.1
  obtain ⟨ψ, hψ, hn⟩ := GlobalTheory.T.chart_point_generic_fibre F V p X s Xw K h _ φ yb hφ y hy e cc hco
  have hc := (c_spec h _).2.2 φ (by rw [hφ]; exact hyb) ψ hψ κ (by rw [hφ]; exact hκ)
  rw [← hn]
  set a := ψ (cu h (yb (IsLocalRing.closedPoint 𝓞_ℂ_[p])) : Localization.Away _)
  have e1 : a = (a - κ) + κ := by ring
  rw [e1, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hc.ne, max_eq_right hc.le]

end GlobalTheory.UnitGlue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalAbelianPartValuesOfNormalFormStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.MBModel GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_classical_abelianPart_values_of_normalForm : AllC fun {R} _ _ {D} _ {N} ν => ∀ (y : KeyIn R) (_ : y.P = D.P), HEq y.rig D.rig → (∃ th : D.P.L.Sec, HEq y.th th ∧ ∀ i : D.P.L.ι, ∀ h : LB.wchart D.P.L (fun _ : Fin 1 => 𝟙 D.P.A.left) (fun _ => i) ≤ D.P.L.U i, ν.th.f (fun _ => i) = resG _ h (th.f i)) → ∀ (x : KeyIn ℂ) (hg : x.P.g = D.P.g) (hy : y.P.g = D.P.g) (u : HolUnif x.P.A x.P.L D.P.g) (τ : Matrix (Fin D.P.g) (Fin D.P.g) ℂ) (a b : Fin D.P.g → ℂ) (c : ℂ) (W : Fin D.P.g → Fin D.P.g → ℂ), KeyPB x y ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R))) → NF x hg u τ a b c W → ∃ (d : AB N.toNumB D.P.g) (_ : Geo ν d), d.c = c ∧ ∀ (vB : Fin D.P.g → (epsR R ⟶ D.P.A)), (∀ i, HEq (y.v (i.cast hy.symm)) (vB i)) → ∀ i (bb : TE R ℂ ⟶ D.P.A), bb.left = spMap (dualMap ((algebraMap (FractionRing R) ℂ).comp (algebraMap R (FractionRing R)))) ≫ (vB i).left → ∀ W', IsD ν d W' bb ↔ W' = W i := by
  first | exact @GlobalTheory.MBLow.Cl.exists_ab_geo_of_nf | exact GlobalTheory.MBLow.Cl.exists_ab_geo_of_nf | (intros; apply GlobalTheory.MBLow.Cl.exists_ab_geo_of_nf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalPointCentredClosedPointArithmeticStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_classicalPoint_centred_closedPoint_arithmetic : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (x : M.Z), IsClosed ({x} : Set M.Z) → ∀ U : M.Z.Opens, (U : Set M.Z).Nonempty → ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U x y := by
  first | exact @GlobalTheory.Poinc.exists_cen_main | exact GlobalTheory.Poinc.exists_cen_main | (intros; apply GlobalTheory.Poinc.exists_cen_main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedPowTransitionOfFrobeniusKillsClass
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.ConjSeq GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CechDR.FrobKill

variable (p : ℕ) [Fact p.Prime] {R : Type} [CommRing R] (hR : (p : R) = 0) {X : Scheme.{0}}
  {s : X ⟶ Sp R}

abbrev tU (s : X ⟶ Sp R) (U : AffOp X) : Thick (dp0 R) s :=
  Thick.triv (Sec s U.unop.1) (affPt s U.unop) (affPt_w s U.unop)

include hR in

theorem cast_sec (U : X.Opens) : (p : Sec s U) = 0 := by
  rw [← map_natCast (algebraMap R (Sec s U)), hR, map_zero]

abbrev resHom (s : X ⟶ Sp R) {U V : AffOp X} (a : U ⟶ V) : tU s U ⟶ tU s V :=
  Thick.trivHom (hx := affPt_w s U.unop) (T := tU s V) (Sec.res s (leOfHom a.unop))
    (affPt_res s (leOfHom a.unop))

variable {hX : (p : Γ(X, ⊤)) = 0}
  (h : IsMor (dp0 R) s (dp0 R) s (frobR p R hR) (GlobalTheory.VB.frob X p hX))

def eta (U : AffOp X) : tU s U ⟶ h.obj (tU s U) :=
  Thick.trivHom (hx := affPt_w s U.unop) (T := h.obj (tU s U))
    { frobR p (Sec s U.unop.1) (cast_sec p hR U.unop.1) with
      commutes' := fun r ↦ by
        show frobR p (Sec s U.unop.1) (cast_sec p hR U.unop.1) (algebraMap R (Sec s U.unop.1) r) = _
        rw [frobR_apply]
        change _ = algebraMap R (Sec s U.unop.1) (frobR p R hR r)
        rw [frobR_apply, map_pow] }
    (by
      have h0 : (p : Γ(Sp (Sec s U.unop.1), ⊤)) = 0 :=
        GlobalTheory.SS.FrobField.cast_zero_sp _ (cast_sec p hR U.unop.1)
      change spMap (frobR p (Sec s U.unop.1) (cast_sec p hR U.unop.1)) ≫ affPt s U.unop =
        affPt s U.unop ≫ GlobalTheory.VB.frob X p hX
      rw [← frob_sp p _ _ h0, GlobalTheory.VB.frob_naturality p hX _ h0])

theorem eta_φ (U : AffOp X) (b : Sec s U.unop.1) : (eta p hR h U).φ b = b ^ p :=
  frobR_apply p _ (cast_sec p hR U.unop.1) b

attribute [local instance] opModule isCentralScalar_kaehler isScalarTower_kaehler

theorem exists_closed_pow : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R] (hR : (p : R) = 0) (X : Scheme.{0}) (s : X ⟶ Sp R) (hX : (p : Γ(X, ⊤)) = 0) (h : IsMor (dp0 R) s (dp0 R) s (frobR p R hR) (GlobalTheory.VB.frob X p hX)) (f : Z1 (O (dp0 R) s)), h.pull1 (GlobalTheory.CatCoh.H1.mk _ f) = 0 → ∃ u : ∀ U : GlobalTheory.CechDR.AffOp X, GlobalTheory.CechDR.Sec s U.unop.1, (∀ U, KaehlerDifferential.D R (GlobalTheory.CechDR.Sec s U.unop.1) (u U) = 0) ∧ ∀ (U V : GlobalTheory.CechDR.AffOp X) (a : U ⟶ V), (show GlobalTheory.CechDR.Sec s V.unop.1 from (GlobalTheory.CechDR.cmpZZ s f).1.1 U V a) ^ p = u V - GlobalTheory.CechDR.Sec.res s (leOfHom a.unop) (u U) := by
  intro p _ R _ hR X s hX h f hf
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 hf
  have hg' : ∀ {T T' : Thick (dp0 R) s} (φ : T ⟶ T'), g T' - φ.φ (g T) = ev f (h.functor.map φ) :=
    fun {T T'} φ ↦ congrFun (congrFun (congrFun hg T) T') φ
  refine ⟨fun U ↦ (show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U)),
    fun U ↦ ?_, fun U V a ↦ ?_⟩
  · let p₁ := (diagExt R (Sec s U.unop.1)).secHom (affPt_w s U.unop) (diagExt R (Sec s U.unop.1)).i
      fun _ ↦ rfl
    let p₂ := (diagExt R (Sec s U.unop.1)).secHom (affPt_w s U.unop) (diagSec R (Sec s U.unop.1))
      (fst_derSec _)
    let P := (diagExt R (Sec s U.unop.1)).thick (affPt s U.unop) (affPt_w s U.unop)
    have e : eta p hR h U ≫ h.functor.map p₁ = eta p hR h U ≫ h.functor.map p₂ :=
      Thick.hom_ext fun b ↦ by
        change (diagExt R (Sec s U.unop.1)).i ((eta p hR h U).φ b) =
          diagSec R (Sec s U.unop.1) ((eta p hR h U).φ b)
        rw [eta_φ]
        ext
        · simp
        · rw [snd_derSec, Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul (Sec s U.unop.1),
            cast_sec p hR, zero_smul]
          simp
    have k := (ev_comp f (eta p hR h U) (h.functor.map p₁)).symm.trans
      ((congrArg (ev f) e).trans (ev_comp f (eta p hR h U) (h.functor.map p₂)))
    have k' : p₁.φ (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₁)) =
        p₂.φ (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₂)) := k
    have h1 : (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from g P) -
        p₁.φ (show Sec s U.unop.1 from g (tU s U)) =
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₁)) := hg' p₁
    have h2 : (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from g P) -
        p₂.φ (show Sec s U.unop.1 from g (tU s U)) =
        (show TrivSqZeroExt (Sec s U.unop.1) Ω[Sec s U.unop.1⁄R] from ev f (h.functor.map p₂)) := hg' p₂
    have key : p₁.φ ((show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U))) =
        p₂.φ ((show Sec s U.unop.1 from g (tU s U)) - (show Sec s U.unop.1 from ev f (eta p hR h U))) := by
      rw [map_sub, map_sub]
      linear_combination -h1 + h2 - k'
    have l := congrArg (TrivSqZeroExt.snd (R := Sec s U.unop.1)) key
    change ((diagExt R (Sec s U.unop.1)).i _).snd = (diagSec R (Sec s U.unop.1) _).snd at l
    rw [snd_derSec] at l
    exact l.symm.trans (by simp)
  · have k := ev_sq f (eta p hR h U) (h.functor.map (resHom s a)) (resHom s a) (eta p hR h V)
      fun c ↦ by
        change Sec.res s (leOfHom a.unop) ((eta p hR h U).φ c) = (eta p hR h V).φ (Sec.res s (leOfHom a.unop) c)
        rw [eta_φ, eta_φ, map_pow]
    have k' : Sec.res s (leOfHom a.unop) (show Sec s U.unop.1 from ev f (eta p hR h U)) +
        (show Sec s V.unop.1 from ev f (h.functor.map (resHom s a))) =
        (ev f (resHom s a)) ^ p + (show Sec s V.unop.1 from ev f (eta p hR h V)) := by
      rw [← eta_φ p hR h V]; exact k
    have hg'' : (show Sec s V.unop.1 from g (tU s V)) - Sec.res s (leOfHom a.unop) (show Sec s U.unop.1 from g (tU s U)) =
        (show Sec s V.unop.1 from ev f (h.functor.map (resHom s a))) :=
      hg' (resHom s a)
    change (ev f (resHom s a)) ^ p = _
    rw [map_sub]
    linear_combination -hg'' - k'

end GlobalTheory.CechDR.FrobKill
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmHomGramMatrixDetNeZeroDefinite
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CM

namespace GlobalTheory.FlatCM.HomLat

theorem exists_isGram_det_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E),
    GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H → ∀ (K : Type) [Field K] [NumberField K] (ρ : 𝓞 K) (σ₁ : K →+* ℂ) (p : ℕ)
    (X : GlobalTheory.CM.CMObj H K ρ σ₁ p 0),
    ∃ (gP : Matrix (Fin p) (Fin p) (𝓞 E)) (gQ : Matrix (Fin 0) (Fin 0) (𝓞 E)),
      GlobalTheory.FlatCM.IsGram X gP gQ ∧ gP.det ≠ 0 := by
  intro E _ _ _ H _ K _ _ ρ σ₁ p X
  obtain ⟨gP, gQ, h⟩ := GlobalTheory.FlatCM.GramExists.exists_isGram E H K ρ σ₁ p 0 X
  exact ⟨gP, gQ, h, (GlobalTheory.GramAt.gram_det X h).1⟩

end GlobalTheory.FlatCM.HomLat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCombinationLieGroupPullbackStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_combination_lie_group_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0})
    (t : SAB H X) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (yb : Sp 𝓞_ℂ_[p] ⟶ X) (π : P.G.left ⟶ t.G.left),
    IsGrpPullback P.G t.G yb π → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left)) (xb : Fin g → LieG P.Gt),
    (∀ b, ITie P π (xb b) (e b)) → ∀ U : Fin g → 𝓞_ℂ_[p],
    ∃ u0 : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left, IsCombAtG t yb e U u0 ∧ ITie P π (lieComb P.Gt U xb) u0 := by
  first | exact @GlobalTheory.FlatModel.TieComb.main | exact GlobalTheory.FlatModel.TieComb.main | (intros; apply GlobalTheory.FlatModel.TieComb.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteAlgClosedFieldDvrEmbedding
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.CompleteDvrToComplex

theorem norm_lt_one_of_mem_maximalIdeal {W C : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] [NormedField C] (g : W →+* C) (hg : ∀ a, ‖g a‖ ≤ 1) {b : W}
    (hb0 : b ≠ 0) (hb : ‖g b‖ < 1) {a : W} (ha : a ∈ IsLocalRing.maximalIdeal W) : ‖g a‖ < 1 := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
  rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at ha
  obtain ⟨c, hc⟩ : (u : W) * π ^ n ∣ a ^ n := Units.mul_left_dvd.2 (pow_dvd_pow_of_dvd ha n)
  have h : ‖g a‖ ^ n < 1 := by
    rw [← norm_pow, ← map_pow, hc, map_mul, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hb (hg c)
  exact lt_of_not_ge fun h1 => absurd (one_le_pow₀ h1) (not_le.2 h)

theorem norm_le_one_padicComplexInt (p : ℕ) [Fact p.Prime] (x : 𝓞_ℂ_[p]) : ‖(x : ℂ_[p])‖ ≤ 1 := by
  have hv : ((Valued.v (x : ℂ_[p]) : NNReal) : ℝ) = ‖(x : ℂ_[p])‖ := by
    rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding,
      Valuation.embedding_restrict]
  rw [← hv]
  have : Valued.v (x : ℂ_[p]) ≤ 1 := x.2
  exact_mod_cast this

theorem norm_natCast_prime_lt_one (p : ℕ) [Fact p.Prime] : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have hc : ((p : ℚ_[p]) : ℂ_[p]) = (p : ℂ_[p]) := by push_cast; rfl
  rw [hc] at h
  rw [h]
  exact Padic.norm_p_lt_one

theorem exists_complete_closed_field :
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (IsLocalRing.maximalIdeal V) V → Finite (IsLocalRing.ResidueField V) → ∃ (C : Type) (_ : NontriviallyNormedField C) (_ : IsUltrametricDist C) (_ : CompleteSpace C) (_ : IsAlgClosed C) (_ : CharZero C) (_ : Algebra (FractionRing V) C), CExt V (IsLocalRing.maximalIdeal V) C ∧ Nonempty (C ≃+* ℂ) := by
  intro V _ _ _ _ hc hf
  let T : Formalism.L2.Pj.CDVR := { V := V }
  obtain ⟨p, hp, k, kO, hk⟩ := GlobalTheory.CompleteDvrEmbedding.exists_embedding_padicComplexInt T hf
  letI : Algebra (FractionRing V) ℂ_[p] := k.toAlgebra
  obtain ⟨eC⟩ := GlobalTheory.MomOne.Inh.nonempty_iso p
  refine ⟨ℂ_[p], inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, this, ⟨?_, ?_⟩, ⟨eC.symm⟩⟩
  · have hle : ∀ r : V, ‖k (algebraMap V (FractionRing V) r)‖ ≤ 1 := fun r => by
      rw [← hk r]
      exact norm_le_one_padicComplexInt p (kO r)
    exact hle
  · have hle : ∀ r : V, ‖(k.comp (algebraMap V (FractionRing V))) r‖ ≤ 1 := fun r => by
      rw [RingHom.comp_apply, ← hk r]
      exact norm_le_one_padicComplexInt p (kO r)
    have hp0 : (p : V) ≠ 0 := Nat.cast_ne_zero.2 hp.out.ne_zero
    have hpl : ‖(k.comp (algebraMap V (FractionRing V))) (p : V)‖ < 1 := by
      rw [map_natCast]; exact norm_natCast_prime_lt_one p
    intro r hr
    exact norm_lt_one_of_mem_maximalIdeal _ hle hp0 hpl hr

end GlobalTheory.CompleteDvrToComplex
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteNormalLocalCoverOfFiniteHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LocExt

theorem exists_isCN_cover_of_finite : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (C : Type) [CommRing C] (φ : R →+* C), IsCN R → Function.Injective φ → φ.Finite → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (σ : C →+* R'), IsCN R' ∧ Function.Injective ρ ∧ ρ.Finite ∧ IsLocalHom ρ ∧ σ.comp φ = ρ := by
  first
  | exact @_root_.GlobalTheory.FiniteLocalCompleteness.main
  | exact _root_.GlobalTheory.FiniteLocalCompleteness.main
  | (apply _root_.GlobalTheory.FiniteLocalCompleteness.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiniteLocalCompleteness.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiniteLocalCompleteness.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiniteLocalCompleteness.main ..)

end GlobalTheory.LocExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteRegularLocalMeetOfFlatMapsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_complete_regular_local_meet_of_flat_maps : ∀ (O R₁ R' Ω : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R₁] [IsRegularLocalRing R₁] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [Field Ω] (φ₁ : O →+* R₁) (φ' : O →+* R') (u : R₁ →+* Ω) (u' : R' →+* Ω), φ₁.Flat → IsLocalHom φ₁ → IsAdicComplete (maximalIdeal R') R' → IsEtaleCompletion φ' → ((residue R').comp φ').FormallyUnramified → RingHom.ker u = maximalIdeal R₁ → RingHom.ker u' = maximalIdeal R' → u.comp φ₁ = u'.comp φ' → ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (_ : IsDomain E) (a : R₁ →+* E) (b : R' →+* E) (v : E →+* Ω), a.Flat ∧ b.Flat ∧ a.comp φ₁ = b.comp φ' ∧ RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ v.comp b = u' ∧ (maximalIdeal R₁).map a = maximalIdeal E ∧ IsAdicComplete (maximalIdeal E) E := by
  first | exact @GlobalTheory.exists_complete_regular_meet | exact GlobalTheory.exists_complete_regular_meet | (intros; apply GlobalTheory.exists_complete_regular_meet <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulHorizontalDetLieCoordinateStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_const_mul_horizontalDetLieCoordinate : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (e : c.F →+* ℂ) (h : CxFr Y e → ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y) (V : Set (gen Y)), IsOpenImmersion io → Set.range io = V → io ≫ genStr Y = B.str → τ (H.rt : E) = H.rt0 → HorFn τ h → ∀ σb : RuleY Y, SecY Y V τ σb → ∃ κ : ℂ, ∀ (a : CxFr Y e) v w, Inner a.1 → FrY Y V τ e a.1.1 v w → Match τ a.2 v w → σb ℂ a.1.1 v w = κ * h a := by
  first | exact @GlobalTheory.DetLine.HorConst.exists_const_mul_horFn | exact GlobalTheory.DetLine.HorConst.exists_const_mul_horFn | (intros; apply GlobalTheory.DetLine.HorConst.exists_const_mul_horFn <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinateFunctionalsFunctionFieldExtensioStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinateFunctionals_functionField_extension : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f], f.residueDegree (genericPoint M) ≠ 0 → ∃ (r : ℕ) (co : Fin r → (M.functionField →+ W.functionField)), (∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x) ∧ ∀ x, (∀ j, co j x = 0) → x = 0 := by
  first | exact @GlobalTheory.functionField_coords | exact GlobalTheory.functionField_coords | (intros; apply GlobalTheory.functionField_coords <;> assumption)
end

