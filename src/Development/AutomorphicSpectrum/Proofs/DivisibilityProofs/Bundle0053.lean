import Development.WeilBound.CoreStatements.MultihomogeneousSquares.GoodTowerAntisymmetry
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0176
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.Bundle0045
import Development.AutomorphicSpectrum.Proofs.MetricProofs.AntisymmetryStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0184
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0187
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0168
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0172
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0259
import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0004
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
import Development.AutomorphicSpectrum.Statements.TowerExistence.GoodTowerExistsX
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0003
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0007
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CodimOneIntegralSubschemeDim
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2618
import Development.AbelianVarietyTheory.Definitions.Divisors.GenericPointAsIdeal
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Bundle0002
import Development.AutomorphicSpectrum.PublishedTheorems.Divisibility₂.PairingExists
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0295
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0185
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArithHeightIffStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0181
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ToZPowCombIsometricStatement

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FullIntersectionTowerI8Identity
section
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem full_intersection_tower_I8_relation : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → T.I8 II (hhFl (CMType H) (D.p + D.q) II) :=
  @SquareStatements.good_tower_antisymmetry

end GlobalTheory.CompanionTheory.Ar.Top
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.HeightProjectionOfInt
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem heightProjection_of_int : (∀ (X Y : Scheme.{0}) [IsIntegral Y] (p : X ⟶ Sp ℤ) (q : Y ⟶ Sp ℤ) (D e : ℕ), IsArithVar p D → IsArithVar q e → ∀ (π : Y ⟶ X) (hπ : π ≫ p = q), topologicalKrullDim (closure ({π (genericPoint Y)} : Set X)) = (e + 1 : ℕ) → π.residueDegree (genericPoint Y) ≠ 0 → ∀ (L : HermLB p) (h : X → ℝ), L.IsArithHeight h → (L.pull π hπ).IsSelfInter ((π.residueDegree (genericPoint Y) : ℝ) * h (π (genericPoint Y)))) → GlobalTheory.Published.HeightProjection := by
  intro H k _ X Y _ p q D e hp hq π hπ hdim hdeg L h hL
  haveI : Module.Finite ℤ k := hp.finite
  have hc : ∀ τ : ℤ →+* ℂ, (wZ L (p ≫ spMap (Int.castRingHom k)) τ).IsCInf :=
    GlobalTheory.T.wZ_isCInf' k X p (p ≫ spMap (Int.castRingHom k)) L
  have hc' : ∀ τ : ℤ →+* ℂ,
      (wZ (L.pull π hπ) (π ≫ p ≫ spMap (Int.castRingHom k)) τ).IsCInf :=
    GlobalTheory.T.wZ_isCInf' k Y q (π ≫ p ≫ spMap (Int.castRingHom k)) (L.pull π hπ)
  have htX : GlobalTheory.IsArithVar (p ≫ spMap (Int.castRingHom k)) D :=
    isArithVar_int k X p _ D hp
  have htY : GlobalTheory.IsArithVar (π ≫ p ≫ spMap (Int.castRingHom k)) e :=
    isArithVar_int k Y q _ e hq
  have hLZ : (toZ L (p ≫ spMap (Int.castRingHom k)) hc).IsArithHeight h :=
    (GlobalTheory.T.toZ_isArithHeight_iff k X p _ D hp L hc h).mpr hL
  have key := H X Y (p ≫ spMap (Int.castRingHom k)) (π ≫ p ≫ spMap (Int.castRingHom k)) D e
    htX htY π rfl hdim hdeg (toZ L (p ≫ spMap (Int.castRingHom k)) hc) h hLZ
  have iso := GlobalTheory.T.toZ_pull_isometric k X Y p q (p ≫ spMap (Int.castRingHom k))
    (π ≫ p ≫ spMap (Int.castRingHom k)) π hπ rfl L hc hc'
  obtain ⟨h', hh', hv⟩ := GlobalTheory.HermLB.Isometric.isSelfInter htY iso.symm key
  exact ⟨h', (GlobalTheory.T.toZ_isArithHeight_iff k Y q _ e hq (L.pull π hπ) hc' h').mp hh', hv⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

-- bundled from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ToZIsArFunIff
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Points GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjSpace GlobalTheory.CompanionTheory.Ar.BaseZ GlobalTheory.CompanionTheory.Ar.BGS

namespace GlobalTheory.CompanionTheory.Ar.BaseZ

theorem isArFun_toZ_iff : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (t : X ⟶ Sp ℤ) (D : ℕ),
    IsArithVar p D → ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (hL : ∀ i τ, (wZ (L i) t τ).IsCInf)
    (Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ), IsArFun (fun i => toZ (L i) t (hL i)) D Φ ↔ IsArFun L D Φ := by
  intro k _ X _ p t D hX ι _ L hL Φ
  have : Module.Finite ℤ k := hX.finite
  have H : ∀ (M : HermLB p) (τ : ℤ →+* ℂ), (wZ M t τ).IsCInf := fun M τ => GlobalTheory.T.wZ_isCInf' k X p t M τ
  have hZ : IsArithVar t D := isArithVar_int k X p t D hX
  have key : ∀ (n : ι → ℤ) (a : ℝ),
      (comb (fun i => toZ (L i) t (hL i)) n).IsSelfInter a ↔ (comb L n).IsSelfInter a := by
    intro n a
    have e : (toZ (comb L n) t (H _)).Isometric (comb (fun i => toZ (L i) t (hL i)) n) :=
      (GlobalTheory.T.toZ_pow_comb_isometric k X p t H).2 ι L n
    constructor
    · intro h₀
      obtain ⟨h, h₁, h₂⟩ := e.symm.isSelfInter hZ h₀
      exact ⟨h, (GlobalTheory.T.toZ_isArithHeight_iff k X p t D hX (comb L n) (H _) h).1 h₁, h₂⟩
    · rintro ⟨h, h₁, h₂⟩
      exact e.isSelfInter hZ ⟨h, (GlobalTheory.T.toZ_isArithHeight_iff k X p t D hX (comb L n) (H _) h).2 h₁, h₂⟩
  exact ⟨fun h => ⟨fun n => (key n _).1 (h.1 n), h.2⟩, fun h => ⟨fun n => (key n _).2 (h.1 n), h.2⟩⟩

end GlobalTheory.CompanionTheory.Ar.BaseZ
end

