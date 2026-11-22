import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0283
import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.Bundle0001
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0105
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CInfGood
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0015
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.OnbMat
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0001
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0014
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CuspOnto
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0006
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Statements.GeometryStatements.LamLevel
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0005
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0010
import Development.AutomorphicSpectrum.Statements.MetricStatements.SmallOnTower
import Development.AutomorphicSpectrum.Statements.MetricStatements.RankBound
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.Bundle0001
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.ShareLow
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.SpecFirstDetFormNeZero
import Development.AutomorphicSpectrum.Statements.GeometryStatements.GoodTwistGoodTwist
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0284
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsLatFamilyCongr
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0177
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0072
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0280
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0151
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0013
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0031
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0001
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerComponentsCompatibleLaws

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyInputFromPpDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.key_input_from_pp_data : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), 1 ≤ D.g → ∀ (s : Out.H0 D.t.PP.L 1) (e : Fin D.g → D.B.carrier), KeyDeg.NonVan D.t.G.hom s → LinearIndependent (𝓞 L) e → Submodule.span (𝓞 L) (Set.range e) = ⊤ → ∃ (x : KeyIn L) (th : D.t.PP.L.Sec) (hg : x.P.g = D.g) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ D.t.G)), KeyDeg.SameSec s th ∧ KeyDeg.NonVan D.t.G.hom th ∧ KeyOver (algebraMap (𝓞 L) L) D.t th x v ∧ IsLieBasis v ∧ ∀ i, (v i).left = (D.MB.pt (e (i.cast hg))).left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sl.KeyDatum.exists_keyIn | exact GlobalTheory.CompanionTheory.Ar.Sl.KeyDatum.exists_keyIn | (intros; apply GlobalTheory.CompanionTheory.Ar.Sl.KeyDatum.exists_keyIn <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LevelLawsSectionVolumeBoundStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sqrt_bergman_lower_bound_le_pnorm_mul_height : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c) (W : HSp D) (dict : ∀ σ : c.F →+* ℂ, GA D W → Σ k, Frame ((U σ).X k).Ψ D.R.r), CompLaws U h e → abelian₂.LevelLaws U W dict → FinVol W → ∀ (a₁ : WZ D.host.E) (Z : Comp Xo c) (n : ℕ) (ω : Fin n → Rul Xo c) (I : Type) [Fintype I] (L : HermLine (fun _ : Unit => I)) (ei : I ≃ Fin n), OntoZ U h e a₁ Z → Submodule.span c.F (Set.range ω) = cuspOn U h a₁ Z → ∀ (σ : c.F →+* ℂ) (k : (U (goodOf c σ)).Comp) (y : Frame ((U (goodOf c σ)).X k).Ψ D.R.r) (lin : Rul Xo c →ₛₗ[σ] ℂ), (∀ f, lin f = Small.goodTwist c σ (rdU (U (goodOf c σ)) f k y)) → (∀ as : Fin n → ℂ, ‖∑ j, as j * lin (ω j)‖ ^ 2 ≤ (∑ j, ∑ j', as j * starRingEnd ℂ (as j') * ipOn U W dict (xiR D) a₁ (e Z) σ (ω j) (ω j')).re * L.h (fun x => lin (ω (ei x.2))) ^ 2) → Over (U (goodOf c σ)) (e Z) k → y ∈ ((U (goodOf c σ)).X k).dom → ∀ (x0 : Frame ((U (goodOf c σ)).X k).Ψ D.R.r) (FF : Set (ReciprocityTheory.L2DbarEstimates.V (nd ((U (goodOf c σ)).X k)))) (t : ℝ), IsOrth ((U (goodOf c σ)).X k) x0 → IsFundSet ((U (goodOf c σ)).X k) x0 FF → 0 < t → ThA.BergLB ((U (goodOf c σ)).X k) x0 FF (laZ (U (goodOf c σ)) a₁ k) y t → (∃ j, lin (ω j) ≠ 0) ∧ 0 < ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y ∧ Real.sqrt t ≤ lieFacZ Dw (xiR D) a₁ * ((U (goodOf c σ)).X k).pnorm (laZ (U (goodOf c σ)) a₁ k) (fun _ => 1) y * L.h (fun x => lin (ω (ei x.2))) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.berg_dual | exact GlobalTheory.CompanionTheory.Ar.Rec.berg_dual | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.berg_dual <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelActionSubalgebraStatement
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_model_action_subalgebra : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (Li : Type) [AddCommGroup Li] [Module Ω Li] (M₀ : LieModel G ξ Li) (B : Type) [CommRing B] (act : OAct B G) (ρ₀ : B →+* Module.End Ω Li), M₀.IsActOf act.act ρ₀ → ∀ (O : Type) [CommRing O] [Algebra O Ω] (R : Subalgebra O Ω) (x : Spec (CommRingCat.of R) ⟶ X), spMap (algebraMap R Ω) ≫ x = ξ → ∃ (L : Type) (_ : AddCommGroup L) (_ : Module R L) (M : LieModel G x L) (ρ : B →+* Module.End R L) (toLi : L →ₗ[R] Li), Module.Finite R L ∧ Module.Projective R L ∧ M.IsActOf act.act ρ ∧ IsBaseChange Ω toLi ∧ (∀ v, (M₀.pt (toLi v)).left = spMap (dualMap (algebraMap R Ω)) ≫ (M.pt v).left) ∧ ∀ a v, toLi (ρ a v) = ρ₀ a (toLi v) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackLie.lieModel_along_generic | exact GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackLie.lieModel_along_generic | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.FamEx.PackLie.lieModel_along_generic <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianTorsionInjective
section
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
open Limits MonoidalCategory CartesianMonoidalCategory MonObj
open GlobalTheory.CompanionTheory.Ar.Num.FamEx GlobalTheory.CompanionTheory.Ar.BT

namespace GlobalTheory.CompanionTheory.Ar.Num.FamEx

theorem exists_qfGroup_of_generic_fullTorsion : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [CharZero R'] (Ω : Type) [Field Ω] [Algebra R' Ω] [IsFractionRing R' Ω] (T : Type) [CommGroup T] (X : Scheme.{0}) (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (x' : Spec (CommRingCat.of R') ⟶ X) (ξ : Spec (CommRingCat.of Ω) ⟶ X), Spec.map (CommRingCat.ofHom (algebraMap R' Ω)) ≫ x' = ξ → ∀ N : ℕ, 1 ≤ N → ∀ pt : T →* (Over.mk ξ ⟶ G), Function.Injective pt → (∀ g : Over.mk ξ ⟶ G, g ^ N = 1 ↔ ∃ t, pt t = g) → FullTorsion G ξ N → ∃ (Γ' : QFGroup R' T) (i' : Γ'.G.left ⟶ G.left), Γ'.IsTorsionAlong G x' N i' ∧ ∀ (a : FractionRing R' →+* Ω), a.comp (algebraMap R' (FractionRing R')) = algebraMap R' Ω → ∀ t, (pt t).left = Spec.map (CommRingCat.ofHom a) ≫ (Γ'.pt t).left ≫ i' :=
  @PositivityTheory.Xgn.exists_torsion_group_extension

end GlobalTheory.CompanionTheory.Ar.Num.FamEx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TateIsoTorsionTowerStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_iso_torsion_tower : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) [IsLocallyNoetherian S] (t : SAB H S) (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [IsDomain O] [CharZero O] [IsAlgClosed (FractionRing O)] (y : Sp O ⟶ S) (I : TateIso D (FractionRing O) (Over.mk ((BT.genPt O).hom ≫ y) ⟶ t.G) (fun a g => g ≫ t.act.act a) (fun n g g' c => Out.WeilIs t.G t.PP.L n g g' (unitOn c))), ∃ X : TorsTower p t.G y D.La, (∀ n (a : D.La), ((X.Γ n).pt (lev p n a)).left ≫ X.i n = (I.ev (p ^ n) a).left) ∧ ∀ a : 𝓞 E, X.Induces (t.act.act a) (DistribMulAction.toAddMonoidHom D.La a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.tower_exists | exact GlobalTheory.CompanionTheory.Ar.HT.tower_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.tower_exists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEndomorphismLiftStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_group_endomorphism_lift : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → ∀ (a : G ⟶ G) [IsMonHom a], ∃ a' : Γ.G ⟶ Γ.G, IsMonHom a' ∧ a'.left ≫ i = i ≫ a.left := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.TorsEnd.endomorphism_restricts_to_torsion | exact GlobalTheory.CompanionTheory.Ar.BT.TorsEnd.endomorphism_restricts_to_torsion | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.TorsEnd.endomorphism_restricts_to_torsion <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupEtaleOfUnitStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_group_etale_of_unit : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → Smooth G.hom → IsUnit (N : R) → Etale Γ.G.hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit | exact GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.torsion_etale_of_isUnit <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionGroupFiniteOfProperStatement
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT ReciprocityTheory.ChartRestriction.G.Semi
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsion_group_finite_of_proper : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Spec (CommRingCat.of R) ⟶ S) (N : ℕ) (i : Γ.G.left ⟶ G.left), Γ.IsTorsionAlong G x N i → IsProper (pullback.snd G.hom x) → IsFinite Γ.G.hom := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BT.Tors.nTorsion_finite_of_isProper | exact GlobalTheory.CompanionTheory.Ar.BT.Tors.nTorsion_finite_of_isProper | (intros; apply GlobalTheory.CompanionTheory.Ar.BT.Tors.nTorsion_finite_of_isProper <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerComponentsCompatibleLawsStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_components_compatible_laws : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (h : GenFrEx Xo c) (e : Comp Xo c → Rul Xo c), CompLaws U h e → ∀ (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : TowerOrigin Y T) (κ : Comp Xo c ≃ T.Comp), CompOf o κ → ∀ (B : ℕ) (Z : Comp Xo c), ∃ Fr : Small.GenFrame (o.Or B (κ Z)), Nonempty (Reading Fr h Z) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Rec.read_exists | exact GlobalTheory.CompanionTheory.Ar.Rec.read_exists | (intros; apply GlobalTheory.CompanionTheory.Ar.Rec.read_exists <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.TowerComponentsEquivOfGivenStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tower_components_equiv_of_given : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (T : Top.RootTower (CMType H) (Dw.p + Dw.q)) (o : TowerOrigin Y T), Top.Given → ∃ κ : Comp Xo c ≃ T.Comp, CompOf o κ := by
  first | exact @GlobalTheory.CompanionTheory.Relay.tower_components_equiv_of_given | exact GlobalTheory.CompanionTheory.Relay.tower_components_equiv_of_given | (intros; apply GlobalTheory.CompanionTheory.Relay.tower_components_equiv_of_given <;> assumption)
end

