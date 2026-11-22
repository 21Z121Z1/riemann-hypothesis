import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0147
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0012
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0011
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0099
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0108
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0077
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0143
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0141

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataUniformisationUnconditionaStatement
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degenerationData_uniformisation_unconditional : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), U.LG = s.P.L ∧ U.gen = s.gen ∧ HEq U.cubG s.P.c := by
  first | exact @GlobalTheory.UU.exists_degData_unif_unconditional | exact GlobalTheory.UU.exists_degData_unif_unconditional | (intros; apply GlobalTheory.UU.exists_degData_unif_unconditional <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsLinearUniformisationOfCompleteDvr
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem exists_pelUnif_of_cdvr : (AllSet fun {V} _ _ _ {A} {G} _ _ s => ∃ (D : DegData V (IsLocalRing.maximalIdeal V)) (U : Unif (IsLocalRing.maximalIdeal V) D A G), U.LG = s.P.L ∧ U.gen = s.gen ∧ HEq U.cubG s.P.c) → Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → ∀ (E : Type) [Field E] [NumberField E] [NumberField.IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDVR V → ∀ (t : SAB H (Sp V)) (A : PolAV (Sp (FractionRing V))) (gen : (Over.pullback (jK V)).obj t.G ≅ A.A), IsMonHom gen.hom → (∃ w : LB.Iso (A.L.pull gen.hom.left) (t.PP.L.pull (pullback.fst t.G.hom (jK V))), w.IsGen) → (∃ S : SplitExt (Sp (IsLocalRing.ResidueField V)), S.IsGt ((Over.pullback (spMap (IsLocalRing.residue V))).obj t.G)) → ∃ P : PELUnif (maximalIdeal V) t, P.A = A ∧ HEq P.U.gen gen ∧ P.TorsionIso := by
  intro hU h1 h2 h3 h4 h5 hTB hVR hTW hUU E _ _ _ H V _ _ _ hV t A gen hgen ⟨w, hw⟩ ⟨S, ⟨d⟩⟩
  obtain ⟨hdvr, hcomp, hchar⟩ := id hV
  have hnoeth : IsNoetherianRing V := inferInstance
  have hic : IsIntegrallyClosed V := inferInstance
  obtain ⟨P, hPL, -⟩ := GlobalTheory.T.exists_cubical_bundle_of_symmetric_semiAbelian h1 V A t.G t.semi gen hgen t.PP t.cub t.sym
  obtain ⟨r, hr⟩ := thick_zero_factor V
  obtain ⟨Q₀⟩ : Nonempty (TQ (thickObj V (maximalIdeal V) 0 t.G) S.X) :=
    nonempty_tq_pullback_comp r _ hr t.G (TQ.ofGtDatum d)
  obtain ⟨P₀, hP₀⟩ := exists_isLevelCP (maximalIdeal V) 0 P
  have hfree := S.free
  have hfin := S.finite
  have hprim : LBIso P.L.L (cubeLB t.G ![𝟙 t.G, t.act.act H.w0] P.L.L) := by rw [hPL]; exact t.prim
  have heven := GlobalTheory.T.exists_even_cubical_trivialisation_specialFibre h1 V hV A t.G t.semi gen hgen P _ (t.act.hom H.w0) hprim S.X Q₀ P₀ hP₀
  obtain ⟨w', hw'⟩ : ∃ w : LB.Iso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst t.G.hom (jK V))), w.IsGen := by
    rw [hPL]; exact ⟨w, hw⟩
  let s : HidaSetting V A t.G :=
    { cdvr := hV, semi := t.semi, gen := gen, gen_hom := hgen, P := P, wA := w', wA_gen := hw', X := S.X,
      Q₀ := Q₀, P₀ := P₀, lev₀ := hP₀, even₀ := heven }
  obtain ⟨D, U, hL, hg, -⟩ := hU V A t.G s
  obtain ⟨Pu, hD, hA, hPU, hT⟩ := GlobalTheory.T.uniformisation_triple_linear_torsionIso ⟨h1, h2, h3, h4, h5⟩ hTB hVR hTW hUU E H V (maximalIdeal V)
    ⟨hnoeth, inferInstance, hic, hcomp⟩ t D A U (hL.trans hPL)
  refine ⟨Pu, hA, ?_, hT⟩
  subst hD hA
  rw [eq_of_heq hPU]
  exact heq_of_eq hg

end GlobalTheory.UU
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationLinearAndTorsion
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

theorem uniformisation_linear_and_torsion : PelSt :=
  GlobalTheory.T.uniformisation_triple_linear_torsionIso GlobalTheory.T.all_uniformization_laws_hold GlobalTheory.twistBaseChange_and_valuation_statements.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.2.1
    GlobalTheory.twistBaseChange_and_valuation_statements.2.2.2.2

end GlobalTheory
end

