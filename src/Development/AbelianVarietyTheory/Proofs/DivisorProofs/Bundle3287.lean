import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3273
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0023
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3274
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUniqueLiesUnder
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0074
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0834
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0079
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3254
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3277
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPsiCoordOfIsPsiCoord
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3275
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3283
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3279
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianOverFieldAxesWedge
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false

namespace GlobalTheory.AbCoh.FieldSq

theorem axes_noPrim_wedge : (∀ (k : Type) [CommRing k], IsField k → ∀ (B : Over (Sp k)) [GrpObj B] (g : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → AxesVanishingStructureSheafDegOne B ∧ NoPrimitiveStructureSheafH2 B ∧ WedgeO (OAff B.hom)) := by
  intro k _ hk B _ g hab hsm
  letI : Field k := hk.toField
  obtain ⟨-, -, hw, hn, ha⟩ := GlobalTheory.T.abelianVariety_structureSheaf_cohomology_anyField k B g hab hsm
  exact ⟨ha, hn, hw⟩

end GlobalTheory.AbCoh.FieldSq
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDifferentialsFromGlobalFormsStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_differentials_from_globalForms : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Par A.hom := by
  first | exact @GlobalTheory.ParForm.par | exact GlobalTheory.ParForm.par | (intros; apply GlobalTheory.ParForm.par <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeUnobstructedOfCohomologyStructureStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_unobstructed_of_cohomology_structure : GlobalTheory.AbCoh.OStr → (∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → GlobalTheory.AbCoh.HasFrame (OAff A.hom) ∧ GlobalTheory.AbCoh.UConst A.hom ∧ GlobalTheory.AbCoh.PrimF A) → GlobalTheory.Published.AbelianUnobstructed := by
  first | exact @GlobalTheory.abelianUnobstructed_of_struct | exact GlobalTheory.abelianUnobstructed_of_struct | (intros; apply GlobalTheory.abelianUnobstructed_of_struct <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianVarietyIntCastSmulIsogenyDegreeStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianVariety_intCast_smul_isogeny_degree : ∀ (K : Type) [Field K] (A : AbVar K) (n : ℤ), n ≠ 0 → IsIsogeny (n • 𝟙 A) ∧ deg (n • 𝟙 A) = n.natAbs ^ (2 * A.dim) := by
  first | exact @GlobalTheory.MulIsogeny.mul_isogeny | exact GlobalTheory.MulIsogeny.mul_isogeny | (intros; apply GlobalTheory.MulIsogeny.mul_isogeny <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdmissibleDeRhamHomologySummandsCrystalStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.admissible_deRhamHomology_summands_crystal : CrystallineSmoothLift → AbelianHodgeDeRham → ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (g : ℕ) (A₀ : Over (Sp R₀)) [GrpObj A₀] (A' : Over (Sp R)) [GrpObj A'] (i' : A₀.left ⟶ A'.left) (h' : IsGrpPullback A₀ A' (spMap π) i'), IsAbelianScheme A' → SmoothOfRelativeDimension g A'.hom → (∀ K : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) → (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) → ∃ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F ∧ (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h')) ∧ (∀ F : Submodule R (HdR A'), GrothendieckMessing.IsAdmissible h' F → ∃ K : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) ∧ (∀ c, c ∈ K ⊔ I • ⊤ ↔ rho hI hk A₀.hom c ∈ F1 A₀.hom) ∧ (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = F.comap (crysToDR (divided₂ hI) h')) ∧ ∀ K K' : Submodule R (Cr hI π A₀.hom), (∃ N, IsCompl K N) → (∃ N, IsCompl K' N) → (K.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator = (K'.comap (prim (divided₂ hI) (spMap π) A₀).subtype).dualAnnihilator → K = K' := by
  first | exact @GlobalTheory.LiftSys.admissible_classification | exact GlobalTheory.LiftSys.admissible_classification | (intros; apply GlobalTheory.LiftSys.admissible_classification <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicModelOfDeRhamStatement
section
open GlobalTheory.LatVal GlobalTheory.LatJet
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algebraic_model_of_de_rham : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → ModelAlg := by
  first | exact @GlobalTheory.ModelAlgProof.modelAlg | exact GlobalTheory.ModelAlgProof.modelAlg | (intros; apply GlobalTheory.ModelAlgProof.modelAlg <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLowerBoundStatement
section
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.base_lower_bound : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → BaseGe := by
  first | exact @GlobalTheory.BigOn.Exp.baseGe_of | exact GlobalTheory.BigOn.Exp.baseGe_of | (intros; apply GlobalTheory.BigOn.Exp.baseGe_of <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierLogHeightFormula
section
open NumberField Formalism.BasicNotions Formalism.MainNotions GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Cartier CategoryTheory AlgebraicGeometry
open IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CovolFin

theorem log_valAt_prod {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z) (w : AbsoluteValue K ℝ)
    {ι : Type} (s : Finset ι) (u : ι → Z.functionFieldˣ) (hu : ∀ i ∈ s, UnitAt (below y) (u i : Z.functionField)) :
    UnitAt (below y) ((∏ i ∈ s, u i : Z.functionFieldˣ) : Z.functionField) ∧
      Real.log (w (valAt y ((∏ i ∈ s, u i : Z.functionFieldˣ) : Z.functionField))) =
        ∑ i ∈ s, Real.log (w (valAt y (u i : Z.functionField))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h₁ : valAt y (1 : Z.functionField) = 1 := by simpa using Base.valAt_stalk y 1
    simp [h₁, unitAt_one]
  | insert a s ha ih =>
    obtain ⟨U, e⟩ := ih fun i hi => hu i (Finset.mem_insert_of_mem hi)
    have Ua := hu a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Units.val_mul]
    refine ⟨Ua.mul U, ?_⟩
    rw [SmallSec.valAt_mul Ua.regAt U.regAt, map_mul,
      Real.log_mul (w.pos (SmallSec.valAt_ne_zero Ua)).ne' (w.pos (SmallSec.valAt_ne_zero U)).ne', e]

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)

theorem zpow_finsum {G : Type} [CommGroup G] (a : G) {ι : Type} (s : Finset ι) (f : ι → ℤ) :
    a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.prod_insert hj, zpow_add, ih]

variable (Dw) in

theorem expo_sum {ι : Type} (s : Finset ι) (ρ : ι → Sym E →₀ ℤ) :
    expo Dw (∑ i ∈ s, ρ i) = ∑ i ∈ s, expo Dw (ρ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [LineTest.expo_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, LineTest.expo_add, ih]

theorem sum_neg_sum {ι : Type} (s : Finset ι) (ρ : ι → Sym E →₀ ℤ) (K : Sym E → ℝ) :
    ((-∑ i ∈ s, ρ i).sum fun a n => (n : ℝ) * K a) = -∑ i ∈ s, (ρ i).sum fun a n => (n : ℝ) * K a := by
  classical
  rw [Finsupp.sum_neg_index (fun _ => by simp)]
  simp only [Int.cast_neg, neg_mul]
  rw [Finsupp.sum_finset_sum_index (fun _ => by simp) (fun _ _ _ => by push_cast; ring)]
  simp [Finsupp.sum, Finset.sum_neg_distrib]

open Classical in

theorem lgOf_neg_sum {ι : Type} (s : Finset ι) (ρ : ι → Sym E →₀ ℤ) (v : HeightOneSpectrum (𝓞 F)) (ε : Ext v)
    (y : AlgPt Y.Y) :
    lgOf Y (-∑ i ∈ s, ρ i) v ε y = Real.log (ε.w (valAt y.1
      (((eqn (divOf Y (expo Dw (-∑ i ∈ s, ρ i))) (below y.1))⁻¹ *
        ∏ i ∈ s, (eqn (divOf Y (expo Dw (ρ i))) (below y.1))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn))) -
      ∑ i ∈ s, lgOf Y (ρ i) v ε y := by
  have hp := LineTest.residueCharacteristic_prime v
  have UW := GlobalTheory.CombInd.Tens.unitAt_prod Y (-∑ i ∈ s, ρ i) (below y.1)
  have Ui := fun i => GlobalTheory.CombInd.Tens.unitAt_prod Y (ρ i) (below y.1)
  simp only [lgOf, dif_pos hp]
  rw [sum_neg_sum]
  set b := below y.1 with hb
  set t := (Y.gr_spec b).choose_spec.choose_spec.choose with ht
  have hP : (∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (-∑ i ∈ s, ρ i) x) =
      (∏ i ∈ s, ∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (ρ i) x)⁻¹ := by
    rw [GlobalTheory.CombInd.DualComb.expo_neg, expo_sum, Finset.prod_comm, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr rfl fun x _ => ?_
    rw [Pi.neg_apply, Finset.sum_apply, zpow_neg, zpow_finsum]
  have hprod : ((eqn (divOf Y (expo Dw (-∑ i ∈ s, ρ i))) b)⁻¹ * ∏ i ∈ s, (eqn (divOf Y (expo Dw (ρ i))) b)⁻¹ : Y.Y.Fnˣ) =
      ((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (-∑ i ∈ s, ρ i) x) * (eqn (divOf Y (expo Dw (-∑ i ∈ s, ρ i))) b)⁻¹) *
        ∏ i ∈ s, ((∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (ρ i) x) * (eqn (divOf Y (expo Dw (ρ i))) b)⁻¹) := by
    rw [hP, Finset.prod_mul_distrib, mul_mul_mul_comm, inv_mul_cancel, one_mul]
  obtain ⟨Us, hs⟩ := GlobalTheory.CovolFin.log_valAt_prod y.1 ε.w s
    (fun i => (∏ x : Letter Dw, t x.1 x.2 ^ expo Dw (ρ i) x) * (eqn (divOf Y (expo Dw (ρ i))) b)⁻¹) fun i _ => Ui i
  rw [hprod, Units.val_mul _ (∏ i ∈ s, _), SmallSec.valAt_mul UW.regAt Us.regAt, map_mul,
    Real.log_mul (ε.w.pos (SmallSec.valAt_ne_zero UW)).ne' (ε.w.pos (SmallSec.valAt_ne_zero Us)).ne', hs,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Units.val_mul]
  ring

end Free

theorem detOmSym_eq (E : Type) [Field E] (g : ℕ) :
    detOmSym E g = -∑ k : Fin g, Finsupp.single (ArIn.ind ∅, (none : Option ℝ), (Sum.inr (k : ℕ) : ((E →+* ℂ) × ℕ) ⊕ ℕ)) 1 := by
  have hind : ArIn.ind ∅ = fun _ => false := funext fun q => by simp [ArIn.ind]
  rw [hind, ← Finset.sum_neg_distrib]
  unfold detOmSym
  refine Fintype.sum_equiv Fin.revPerm _ _ fun k => ?_
  simp [wholeSym, Finsupp.single_neg]

theorem lg_detOmSym : ∀ (D : D7) (O : Setup D) (c : O.s.Comp) (v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.what₂.LL)) (e : GlobalTheory.TrueGeo.Ext v) (y : AlgPt (O.var c)), (O.adl0 c (detOmSym D.host.E (D.R.f * O.N))).lg v e y = Real.log (e.w (valAt y.1 (genAt (O.adl0 c (detOmSym D.host.E (D.R.f * O.N))).D (below y.1) / ∏ k : Fin (D.R.f * O.N), genAt (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)).D (below y.1) ^ (-1 : ℤ)))) - ∑ k : Fin (D.R.f * O.N), (O.adl0 c (Finsupp.single (ArIn.ind ∅, none, Sum.inr (k : ℕ)) 1)).lg v e y := by
  intro D O c v e y
  rw [detOmSym_eq]
  refine (lgOf_neg_sum (O.Φ.C c) Finset.univ _ v e y).trans ?_
  congr 3
  simp only [Setup.adl0, adlOf, genAt, Units.val_mul, Units.coe_prod, zpow_neg, zpow_one, div_eq_mul_inv,
    Finset.prod_inv_distrib, inv_inv, Units.val_inv_eq_inv_val]

end GlobalTheory.CovolFin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterGroupEqEighthPowerLatticeOverTrait
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc.Eq8.PeriodsEighth

theorem main : ∀ (g n : ℕ) (o : Type) [CommRing o] (ζ : o) (F : SFam g n ζ) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.Over₀ M U₀ → ∀ (V : M.Z.Opens) (v : V.toScheme ⟶ F.X), (∀ x : Sp Ω ⟶ V.toScheme, x ≫ V.ι = M.pt → x ≫ v = spMap S.R.val.toRingHom ≫ u) → ∀ (f : Fin 8 → Fin 8 → (FinalForm.G ⟶ FinalForm.G)), (∀ a b, MatOn FinalForm pr a b (f a b)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ M.Z) (D : DegPre R) (m : Fin 8 → Fin 8 → (D.X →+ D.X)) (T : Trait F) (ψ : R →+* T.V), ThroughU M V v (𝟙 F.X) T (spMap ψ ≫ ξ) → ∀ (G' : Over (Sp T.V)) [GrpObj G'] [IsCommMonObj G'] (D' : DegData T.V (maximalIdeal T.V)) (A' : PolAV (Sp (FractionRing T.V))) (U' : Unif (maximalIdeal T.V) D' A' G') (gm : G'.left ⟶ FinalForm.G.left) (ι : D.X ≃+ D'.toPre.X), IsSemiAbelian G' → IsGrpPullback G' FinalForm.G (spMap ψ ≫ ξ) gm → LBIso U'.LG.L (FinalForm.L.L.pull gm) → CoordMap D D'.toPre ψ ι.toAddMonoidHom → (∀ a b, ∃ f' : G' ⟶ G', IsMonHom f' ∧ f'.left ≫ gm = gm ≫ (f a b).left ∧ ∀ m', EndChar U' f' m' → ∀ y, ι (m a b y) = m' (ι y)) → ∃ ρT : D.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (ψ r) (T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧ ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y)) := by
  intro g n o _ ζ F W hW o' Ω _ _ _ _ S ρ u c pr hsh M U₀ EE FinalForm hov V v hv f hf R _ _ _ ξ D m T ψ hT G' _ _ D' A' U'
    gm ι hG hpb hL hco hm
  have hBV : GlobalTheory.Mum.Base T.V := ⟨⟨inferInstance, inferInstance, inferInstance, T.complete⟩, inferInstance⟩
  obtain ⟨ξ₀, h1, h2⟩ := hT
  obtain ⟨c', pr', hs', hmat⟩ := (GlobalTheory.T.thetaModel_open_abelian_eighthPower_with_bundle g n o ζ F W o' Ω S ρ u c pr hsh M U₀ EE FinalForm hov V v hv).2 T.V hBV G' hG
    D' A' U' (spMap ψ ≫ ξ) gm hpb hL ξ₀ h1
  have e0 : spMap (RingHom.id (FractionRing T.V)) ≫ T.y = ξ₀ ≫ v := by
    have : spMap (RingHom.id (FractionRing T.V)) = 𝟙 _ := Spec.map_id _
    rw [this, Category.id_comp, ← h2, Category.comp_id]
  have key : ∀ y₀ : Sp (FractionRing T.V) ⟶ F.X, spMap (RingHom.id (FractionRing T.V)) ≫ T.y = y₀ →
      ∀ c'' pr'', SharpBy F W A' y₀ c'' pr'' → ∃ e : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X),
      (∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W T.β (e y) ∧ Associated r (T.ϖ ^ (qW W T.β (e y)).toNat)) ∧
      ∀ (a b : Fin 8) (f : G' ⟶ G') (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f →
        MatEnd pr'' a b f₁ → (Over.pullback (jK T.V)).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m →
        ∀ y, MatRel W a b (e y) (e (m y)) := by
    rintro _ rfl c'' pr'' hs''
    exact GlobalTheory.T.exists_eighthPowerTrait_lattice_equiv_localExt g n o ζ F W hW T T.V hBV inferInstance G' hG D' A' U' (RingHom.id _) (RingHom.id _)
      inferInstance (fun _ => rfl) c'' pr'' hs''
  obtain ⟨e, he1, he2⟩ := key _ e0 c' pr' hs'
  refine ⟨ι.trans e, fun y r hr => ?_, fun a b y => ?_⟩
  · obtain ⟨r', hr'⟩ := (GlobalTheory.PeriodFormCompare.exists_psiCoord_iff D'.toPre (ι y)).2
      (GlobalTheory.PeriodFormCompare.psiIn_top D' _)
    obtain ⟨h0, ha⟩ := he1 _ _ hr'
    exact ⟨h0, (hco y r r' hr hr').trans ha⟩
  · obtain ⟨f', hfm, hf', hmm⟩ := hm a b
    obtain ⟨m', hm'⟩ := endChar_exists_of_isMonHom T.V hBV G' hG D' A' U' f' hfm
    obtain ⟨f₁, hf₁, hgen⟩ := hmat a b (f a b) f' (hf a b) hf'
    have := he2 a b f' f₁ m' hfm hf₁ hgen hm' (ι y)
    rw [← hmm m' hm' y] at this
    exact this

end GlobalTheory.Poinc.Eq8.PeriodsEighth
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDimAddFinrankDualLieEqHeightStatement
section
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartDim_add_finrank_dual_lie_eq_height : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d), d + Module.finrank O G.dual.Lie = G.height := by
  first | exact @GlobalTheory.PDivGroup.chart_dim_add_finrank_dual_lie | exact GlobalTheory.PDivGroup.chart_dim_add_finrank_dual_lie | (intros; apply GlobalTheory.PDivGroup.chart_dim_add_finrank_dual_lie <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSquareCoordinatesPresentLevels
section
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz

namespace GlobalTheory

theorem chart_square_presents : ∀ (p : ℕ) (k : Type) [CommRing k] (d : ℕ) (G : PDivGroup p k)
    (c : Chart G d), Presents k c.x₂ c.nil₂ ∧ ∀ z : ∀ n, G.A n ⊗[k] G.A n,
      (∀ n, pullbackTwo (G.res n) (z (n + 1)) = z n) → ∃! s, ∀ n, c.ev₂ n s = z n := by
  intro p k _ d G c
  have ht := fun n => GlobalTheory.T.powerSeriesPresentation_up_to_order_tensorProduct k (Fin d) (Fin d) (G.A n) (G.A n) (c.x n) (c.nil n) (c.x n)
    (c.nil n) (c.nil₂ n) (c.presents.1 n) (c.presents.1 n)
  refine ⟨⟨fun n => (ht n).1, fun N => ?_⟩, fun z hz => ?_⟩
  · obtain ⟨n, hn⟩ := c.presents.2 N
    exact ⟨n, (ht n).2 N hn hn⟩
  · let r : ∀ n, G.A n.succ ⊗[k] G.A n.succ →ₐ[k] G.A n ⊗[k] G.A n := fun n =>
      Algebra.TensorProduct.map (G.res n : G.A (n + 1) →ₐ[k] G.A n)
        (G.res n : G.A (n + 1) →ₐ[k] G.A n)
    have hr : ∀ n t, r n t = pullbackTwo (G.res n) t := fun n t => by
      induction t with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul a b => rfl
    refine GlobalTheory.T.existsUnique_powerSeries_of_compatible_system k (Fin d ⊕ Fin d) (fun n => G.A n ⊗[k] G.A n) c.x₂ c.nil₂ r
      (fun n i => ?_) ⟨fun n => (ht n).1, fun N => ?_⟩ z (fun n => by rw [hr]; exact hz n)
    · rw [hr]
      cases i with
      | inl i => simp [Chart.x₂, c.res]
      | inr i => simp [Chart.x₂, c.res]
    · obtain ⟨n, hn⟩ := c.presents.2 N
      exact ⟨n, (ht n).2 N hn hn⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernMassEqSelfIntersectionLineBundleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernMass_eq_selfIntersection_lineBundle : ∀ (Y : Var ℂ) (L : LB Y.X) (φ : Weight Y.str (RingHom.id ℂ) L), φ.IsCInf → Weight.chernInt φ Y.dim Set.univ (fun _ => 1) = (topSelfIntersection ℂ L Y.dim : ℝ) := by
  first | exact @GlobalTheory.MassDegree.chernInt_eq_topSelf | exact GlobalTheory.MassDegree.chernInt_eq_topSelf | (intros; apply GlobalTheory.MassDegree.chernInt_eq_topSelf <;> assumption)
end

