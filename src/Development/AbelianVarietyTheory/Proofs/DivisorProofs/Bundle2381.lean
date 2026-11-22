import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0197
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2323
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0066
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0051
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0046
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2289
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2310
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0007
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModuliModelUltrametricPoints
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsRegularOfSupportDimQuotientAddLengthLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0316
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0378
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0803
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0801
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0276
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2321
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2319
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0671
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0618
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsEqnIffGeneratesAtInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2322
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringDominatingSubring
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2290
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2326
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClassicalPointCentredClosedPointArithmetic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc

theorem flat_and_lft_toInt {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [h : ArithBase o Ω] (M : RatModel o Ω) :
    Flat (M.s ≫ spMap (algebraMap ℤ o)) ∧ LocallyOfFiniteType (M.s ≫ spMap (algebraMap ℤ o)) := by
  have := h.ded
  have hΩ := h.char
  have : CharZero o := ⟨fun a b hab => by
    have := congrArg (algebraMap o Ω) hab
    simpa using this⟩
  have hft := h.ft
  have := M.lft
  have : Flat M.s := GlobalTheory.ModelOfOutput.flat_ratModel M
  have : Flat (spMap (algebraMap ℤ o)) :=
    Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : LocallyOfFiniteType (spMap (algebraMap ℤ o)) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.2 hft
  exact ⟨inferInstance, inferInstance⟩

theorem exists_cen (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (x : M.Z)
    (hx : IsClosed ({x} : Set M.Z)) (U : M.Z.Opens) (hU : (U : Set M.Z).Nonempty) :
    ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U x y := by
  obtain ⟨h1, h2⟩ := flat_and_lft_toInt M
  exact GlobalTheory.padicAlgCl_integral_points.1 M.Z (M.s ≫ spMap (algebraMap ℤ o)) x hx U hU

theorem exists_cen_main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M : RatModel o Ω) (x : M.Z),
    IsClosed ({x} : Set M.Z) → ∀ U : M.Z.Opens, (U : Set M.Z).Nonempty →
      ∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U x y :=
  fun o Ω _ _ _ _ M x hx U hU => exists_cen o Ω M x hx U hU

end GlobalTheory.Poinc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmPointNonvanishingSectionStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LamT (CMPt)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cm_point_nonvanishing_section : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o →
    2 < Module.finrank ℚ D.host.E / 2 → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), GapGe 1 la →
    ∀ [StarRing (𝓞 D.host.E)], (∀ a : 𝓞 D.host.E, star a = T.Q.H.bar a) →
    ∀ F ∈ Y.V (wtOf _ la 0), F ≠ 0 →
    ∃ (z : CMPt Y.d.Xo₂ Y.d.c₂) (La : ℝ) (y : FrPt Y.d.Xo₂ Y.d.c₂ z.K),
      z.Good (Module.finrank ℚ D.host.E / 2) La ∧ y.x = z.x ∧ evR Y.d.Xo₂ Y.d.c₂ F y ≠ 0 := by
  first | exact @GlobalTheory.CovDetect.exists_good_cmPt_frame_ne_zero | exact GlobalTheory.CovDetect.exists_good_cmPt_frame_ne_zero | (intros; apply GlobalTheory.CovDetect.exists_good_cmPt_frame_ne_zero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCombinationLieGroupPullback
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

open GlobalTheory.FlatModel

set_option autoImplicit false

namespace GlobalTheory.FlatModel.TieComb

open GlobalTheory.HTLat.OmegaRank

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X} {p : ℕ} [Fact p.Prime] [StarRing (𝓞 E)] {P : PtP E p}

theorem corr_lieComb : ∀ {g : ℕ} (U : Fin g → 𝓞_ℂ_[p]) (xb : Fin g → LieG P.Gt) (xG : Fin g → LieG P.G),
    (∀ b, Corr P (xb b).1 (xG b).1) → Corr P (lieComb P.Gt U xb).1 (lieComb P.G U xG).1
  | 0, _, _, _, _ => Corr.one
  | g + 1, U, xb, xG, h => by
    rw [lieComb_succ, lieComb_succ]
    exact Corr.mul (Corr.comp (dualScale (U 0)) (h 0))
      (corr_lieComb (Fin.tail U) (Fin.tail xb) (Fin.tail xG) fun b => h b.succ)

variable {yb : Sp 𝓞_ℂ_[p] ⟶ X} {π : P.G.left ⟶ t.G.left}

theorem prod_push (hP : IsGrpPullback P.G t.G yb π) :
    ∀ {g : ℕ} (U : Fin g → 𝓞_ℂ_[p]) (xG : Fin g → LieG P.G),
    (List.ofFn fun i => pushPt hP.1.w (AvDefs.lieScale P.G (U i) (xG i)).1).prod.left =
      (lieComb P.G U xG).1.left ≫ π
  | 0, U, xG => by
    rw [List.ofFn_zero, List.prod_nil, lieComb_zero]
    exact grpPull_one hP _
  | g + 1, U, xG => by
    rw [List.ofFn_succ, List.prod_cons, lieComb_succ]
    exact hP.2 _ _ _ _ _ rfl (prod_push hP (Fin.tail U) (Fin.tail xG))

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0})
    (t : SAB H X) (p : ℕ) [Fact p.Prime] [StarRing (𝓞 E)] (P : PtP E p) (yb : Sp 𝓞_ℂ_[p] ⟶ X) (π : P.G.left ⟶ t.G.left),
    IsGrpPullback P.G t.G yb π → ∀ (g : ℕ) (e : Fin g → (Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left)) (xb : Fin g → LieG P.Gt),
    (∀ b, ITie P π (xb b) (e b)) → ∀ U : Fin g → 𝓞_ℂ_[p],
    ∃ u0 : Sp (DualNumber 𝓞_ℂ_[p]) ⟶ t.G.left, IsCombAtG t yb e U u0 ∧ ITie P π (lieComb P.Gt U xb) u0 := by
  intro E _ _ _ H X t p _ _ P yb π hP g e xb hT U
  choose xG hc he using hT
  refine ⟨(lieComb P.G U xG).1.left ≫ π, ⟨fun i => pushPt hP.1.w (AvDefs.lieScale P.G (U i) (xG i)).1, fun i => ?_,
    prod_push hP U xG⟩, lieComb P.G U xG, corr_lieComb U xb xG hc, rfl⟩
  rw [← he i]
  rfl

end GlobalTheory.FlatModel.TieComb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteDvrSplitExt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SplitExtDVR

theorem exists_complete_dvr_split_ext : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (IsLocalRing.maximalIdeal V) V → ∀ (G : Over (Sp V)) [GrpObj G], IsSemiAbelian G →
    ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsDiscreteValuationRing W) (_ : CharZero W) (g : V →+* W),
      IsAdicComplete (IsLocalRing.maximalIdeal W) W ∧ g.IsIntegral ∧ Function.Injective g ∧ IsLocalHom g ∧
      ∃ E : SplitExt (Sp (IsLocalRing.ResidueField W)),
        E.IsGt ((Over.pullback (spMap (IsLocalRing.residue W))).obj ((Over.pullback (spMap g)).obj G)) := by
  intro V _ _ _ _ hcV G _ hG
  haveI := hcV
  let F := AlgebraicClosure (FractionRing V)
  have : Algebra.IsAlgebraic V F :=
    (IsFractionRing.comap_isAlgebraic_iff (A := V) (K := FractionRing V) (C := F)).2 inferInstance
  have hi : Function.Injective (algebraMap V F) := by
    rw [IsScalarTower.algebraMap_eq V (FractionRing V) F]
    exact (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective _ _)
  have : FaithfulSMul V F := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  obtain ⟨W, hd, hc, hfin, hs⟩ := GlobalTheory.Ex.UnifModel.exists_split V F G hG
  have hW : Function.Injective (algebraMap V W) := fun _ _ h => hi (congrArg (fun z : W => (z : F)) h)
  have : CharZero W := charZero_of_injective_algebraMap hW
  have : FaithfulSMul V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hW
  have hl : IsLocalHom (algebraMap V W) := inferInstance
  have hint : (algebraMap V W).IsIntegral := by
    have : Algebra.IsIntegral V W := Algebra.IsIntegral.of_finite V W
    exact Algebra.IsIntegral.isIntegral
  exact ⟨W, inferInstance, inferInstance, hd, inferInstance, algebraMap V W, hc, hint, hW, hl, hs⟩

end GlobalTheory.SplitExtDVR
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompleteRegularLocalMeetOfFlatMaps
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory

theorem exists_complete_regular_meet : ∀ (O R₁ R' Ω : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing R₁] [IsRegularLocalRing R₁] [CommRing R'] [IsLocalRing R'] [IsNoetherianRing R'] [Field Ω] (φ₁ : O →+* R₁) (φ' : O →+* R') (u : R₁ →+* Ω) (u' : R' →+* Ω), φ₁.Flat → IsLocalHom φ₁ → IsAdicComplete (maximalIdeal R') R' → IsEtaleCompletion φ' → ((residue R').comp φ').FormallyUnramified → RingHom.ker u = maximalIdeal R₁ → RingHom.ker u' = maximalIdeal R' → u.comp φ₁ = u'.comp φ' → ∃ (E : Type) (_ : CommRing E) (_ : IsRegularLocalRing E) (_ : IsDomain E) (a : R₁ →+* E) (b : R' →+* E) (v : E →+* Ω), a.Flat ∧ b.Flat ∧ a.comp φ₁ = b.comp φ' ∧ RingHom.ker v = maximalIdeal E ∧ v.comp a = u ∧ v.comp b = u' ∧ (maximalIdeal R₁).map a = maximalIdeal E ∧ IsAdicComplete (maximalIdeal E) E := by
  intro O R₁ R' Ω _ _ _ _ _ _ _ _ _ φ₁ φ' u u' hφ₁ hloc _hR' het hunr hu hu' hcomm
  obtain ⟨G, β, hGm, hGr, hGs, hspan⟩ := GlobalTheory.T.exists_monic_simple_root_generating_residue O R' Ω φ' u' het hunr hu'
  obtain ⟨C, _, _, c, uC, hcf, hcm, hcc, huC, huCc⟩ := GlobalTheory.T.exists_regular_completion_flat R₁ Ω u hu
  have hcomp : uC.comp (c.comp φ₁) = u'.comp φ' := by rw [← RingHom.comp_assoc, huCc, hcomm]
  obtain ⟨E, _, _, e, v, hef, hem, hec, hv, hve, hβ⟩ := GlobalTheory.T.exists_regular_local_extension_with_simple_root C Ω uC (G.map (c.comp φ₁)) β huC hcc
    (hGm.map _) (by rw [Polynomial.map_map, hcomp]; exact hGr) (by rw [Polynomial.map_map, hcomp]; exact hGs)
  have hdom : IsDomain E := GlobalTheory.isDomain_of_isRegularLocalRing E
  have hmapE : (maximalIdeal R₁).map (e.comp c) = maximalIdeal E := by
    rw [← Ideal.map_map, hcm, hem]
  have hva : v.comp (e.comp c) = u := by rw [← RingHom.comp_assoc, hve, huCc]
  have hψl : IsLocalHom ((e.comp c).comp φ₁) := by
    refine ⟨fun x hx => ?_⟩
    by_contra h
    have h1 : φ₁ x ∈ maximalIdeal R₁ := by
      rw [mem_maximalIdeal, mem_nonunits_iff]; exact fun h' => h (isUnit_of_map_unit φ₁ x h')
    have h2 : (e.comp c) (φ₁ x) ∈ maximalIdeal E := hmapE ▸ Ideal.mem_map_of_mem _ h1
    exact (mem_maximalIdeal _).1 h2 hx
  have hv' : v.comp ((e.comp c).comp φ₁) = u'.comp φ' := by rw [← RingHom.comp_assoc, hva, hcomm]
  have hrange : ∀ r : R', u' r ∈ v.range := by
    intro r
    obtain ⟨q, hq⟩ := hspan r
    obtain ⟨y, hy⟩ := hβ
    refine ⟨Polynomial.eval₂ ((e.comp c).comp φ₁) y q, ?_⟩
    rw [hq, ← hv', Polynomial.eval_map, ← hy, Polynomial.hom_eval₂]
  obtain ⟨b, hb1, hb2⟩ := GlobalTheory.T.exists_extension_etaleCompletion_to_complete_local O R' E Ω φ' ((e.comp c).comp φ₁) u' v het hunr hec hψl hu' hv hv' hrange
  have hbl : IsLocalHom b := by
    refine ⟨fun r hr => ?_⟩
    by_contra h
    have h1 : r ∈ maximalIdeal R' := (mem_maximalIdeal _).2 h
    rw [← hu', RingHom.mem_ker] at h1
    have h2 : b r ∈ RingHom.ker v := by rw [RingHom.mem_ker, ← RingHom.comp_apply, hb2, h1]
    rw [hv, mem_maximalIdeal] at h2
    exact h2 hr
  have haf : (e.comp c).Flat := RingHom.Flat.comp hcf hef
  have hbf : b.Flat := GlobalTheory.T.flat_of_flat_comp_of_map_maximalIdeal_eq O R' E φ' b het.1 het.2.1 hbl (by rw [hb1]; exact RingHom.Flat.comp hφ₁ haf)
  exact ⟨E, inferInstance, inferInstance, hdom, e.comp c, b, v, haf, hbf, hb1.symm, hv, hva, hb2, hmapE, hec⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentStalkDerivationOfFunctionFieldExtStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_componentStalkDerivation_of_functionField_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), ∀ [IsIntegral (X₀ TF.Y Z)] [SmoothOfRelativeDimension Dw.dim (s₀ TF.Y Z)] (x : X₀ TF.Y Z) (U : TF.Y.X.affineOpens), U.1 ≤ barComp TF.Y Z → ∀ (hx : (barComp TF.Y Z).ι x ∈ U.1) (ρ : Γ(TF.Y.X, U.1) →+* (X₀ TF.Y Z).functionField), (∀ r, ρ r = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r)) → ∀ (d : Fin Dw.dim → Derivation ℤ Γ(TF.Y.X, U.1) Γ(TF.Y.X, U.1)) (D : Fin Dw.dim → GlobalTheory.LogKSDiv.GenDer TF Z), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j r, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (ρ r) = ρ (d j r)) → letI := (GlobalTheory.LogKSDiv.stalkAlg TF Z x).toAlgebra; ∃ δ : Fin Dw.dim → Derivation c.F ((X₀ TF.Y Z).presheaf.stalk x) ((X₀ TF.Y Z).presheaf.stalk x), (letI := (GlobalTheory.Cartier.constFn (s₀ TF.Y Z)).toAlgebra; ∀ j a, (show Derivation c.F (X₀ TF.Y Z).functionField (X₀ TF.Y Z).functionField from D j) (algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField a) = algebraMap ((X₀ TF.Y Z).presheaf.stalk x) (X₀ TF.Y Z).functionField (δ j a)) ∧ ∀ j r, δ j (GlobalTheory.LogKSDiv.stalkHom TF Z x U hx r) = GlobalTheory.LogKSDiv.stalkHom TF Z x U hx (d j r) := by
  first | exact @GlobalTheory.LogKSDiv.exists_stalkDer_extend | exact GlobalTheory.LogKSDiv.exists_stalkDer_extend | (intros; apply GlobalTheory.LogKSDiv.exists_stalkDer_extend <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMulHorizontalDetLieCoordinate
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open Formalism.L2.Pj

namespace GlobalTheory.DetLine.HorConst

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

theorem exists_matrix {S : Scheme.{0}} {t : SAB H S} {R : Type} [CommRing R] {x : Sp R ⟶ S} {m n : ℕ} (h : m = n)
    {v v' : Fin n → (epsAt x ⟶ t.G)} {u u' : Fin m → (Sp (DualNumber R) ⟶ t.G.left)}
    (hv : ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v i).left = u k)
    (hv' : ∀ (i : Fin n) (k : Fin m), (i : ℕ) = k → (v' i).left = u' k)
    {M : Matrix (Fin m) (Fin m) R} (hM : ∀ i, IsCombAtG t x u (M i) (u' i)) :
    ∃ M' : Matrix (Fin n) (Fin n) R, M'.det = M.det ∧ ∀ i, IsCombAt x (M' i) v (v' i) := by
  subst h
  refine ⟨M, rfl, fun i => (EigParts.comb_iff v _ _).2 ?_⟩
  rw [hv' i i rfl, show (fun i => (v i).left) = u from funext fun i => hv i i rfl]
  exact hM i

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Y : Model Xo c β}

open GlobalTheory.LieLocBasis GlobalTheory.ShFam.EigLoc GlobalTheory.ShFam.CoordUniq in

theorem exists_matrix_det_ne {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Y.X} (f₁ f₂ : EigFrame Y φ x)
    (ρ : E →+* ℂ) : ∃ M : Matrix (Fin (D.mult ρ)) (Fin (D.mult ρ)) k,
      (∀ i, IsCombAtG Y.t x (f₁.v ρ) (M i) (f₂.v ρ i)) ∧ M.det ≠ 0 := by
  obtain ⟨n, xc, hx⟩ := exists_chart Y.t x
  choose e₁ he₁ using fun i => vec_exists hx _ (f₁.tan ρ i)
  choose e₂ he₂ using fun i => vec_exists hx _ (f₂.tan ρ i)
  choose M hM using fun i => (f₁.basis ρ _ (f₂.tan ρ i) (f₂.eig ρ i)).exists
  have hM' : ∀ i, e₂ i = ∑ j, M i j • e₁ j := fun i => by
    have := hM i
    rw [he₂ i, show f₁.v ρ = fun j => vec Y.t x xc (e₁ j) from funext he₁] at this
    exact (comb_iff hx _ _ _).1 this
  have hind : ∀ a : Fin (D.mult ρ) → k, ∑ i, a i • e₂ i = 0 → a = 0 := fun a ha => by
    have hb := f₂.basis ρ _ (vec_tan hx 0) ((vec_eig_iff hx _ _).2 (Submodule.zero_mem _))
    rw [show f₂.v ρ = fun j => vec Y.t _ xc (e₂ j) from funext he₂] at hb
    exact hb.unique ((comb_iff hx _ _ _).2 ha.symm) ((comb_iff hx _ _ _).2 (by simp))
  refine ⟨Matrix.of M, hM, fun h0 => ?_⟩
  obtain ⟨a, ha, ha0⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  refine ha (hind a ?_)
  simp only [hM', Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [← Finset.sum_smul]
  have : ∑ i, a i * M i j = 0 := congrFun ha0 j
  rw [this, zero_smul]

theorem quot_eq {τ : E →+* ℂ} (hτ : τ (H.rt : E) = H.rt0) {e : c.F →+* ℂ} {h : CxFr Y e → ℂ} (hh : HorFn τ h)
    {V : Set (gen Y)} {σb : RuleY Y} (hσ : SecY Y V τ σb) (a a' : CxFr Y e) (ha : a.1.1 = a'.1.1) (hi : Inner a.1)
    {v w v' w'} (hf : FrY Y V τ e a.1.1 v w) (hm : Match τ a.2 v w) (hf' : FrY Y V τ e a'.1.1 v' w')
    (hm' : Match τ a'.2 v' w') : σb ℂ a.1.1 v w * (h a)⁻¹ = σb ℂ a'.1.1 v' w' * (h a')⁻¹ := by
  obtain ⟨x, f⟩ := a
  obtain ⟨x', f'⟩ := a'
  obtain rfl : x = x' := Subtype.ext ha
  obtain ⟨M, hM, hM0⟩ := exists_matrix_det_ne f f' τ
  obtain ⟨N, hN, -⟩ := exists_matrix_det_ne f f' (conjEmb τ)
  obtain ⟨M', eM, hM'⟩ := exists_matrix (GlobalTheory.Harm.mult_of_mem D hτ) hm.1 hm'.1 hM
  obtain ⟨N', eN, hN'⟩ := exists_matrix (GlobalTheory.Harm.mult_conjEmb_of_mem D hτ) hm.2 hm'.2 hN
  have e₁ := hσ.2 ℂ e x.1 v w v' w' M' N' hf hf' hM' hN'
  have e₂ := hh.2.1 ⟨x, f⟩ ⟨x, f'⟩ M N hi ⟨rfl, hM⟩ ⟨rfl, hN⟩
  have h₁ := hh.1 ⟨x, f⟩ hi
  have h₂ := hh.1 ⟨x, f'⟩ hi
  rw [eM, eN] at e₁
  rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff h₁ h₂]
  refine mul_right_cancel₀ hM0 ?_
  linear_combination σb ℂ x.1 v w * e₂ + h ⟨x, f⟩ * e₁

open GlobalTheory.CxPts GlobalTheory.ShFam.Hor.Sec in

theorem exists_const_mul_horFn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (τ : E →+* ℂ) (e : c.F →+* ℂ) (h : CxFr Y e → ℂ) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y) (V : Set (gen Y)), IsOpenImmersion io → Set.range io = V → io ≫ genStr Y = B.str → τ (H.rt : E) = H.rt0 → HorFn τ h → ∀ σb : RuleY Y, SecY Y V τ σb → ∃ κ : ℂ, ∀ (a : CxFr Y e) v w, Inner a.1 → FrY Y V τ e a.1.1 v w → Match τ a.2 v w → σb ℂ a.1.1 v w = κ * h a := by
  intro E _ _ _ H D l Xo c O _ β Y τ e h B io V hio hV hstr hτ hh σb hσ
  obtain ⟨W, hW, φ, fr, a, hy, hφ, ha, hv, hf⟩ :=
    GlobalTheory.ShFam.HolFrames.exists_affine_holFrames E H D l Xo c O β Y e B io hio hstr
  choose v₀ w₀ hf₀ hm₀ using fun y => (EigParts.eigFrame_match E H D l Xo c O β Y τ hτ V _ (φ y) _ (hφ y)
    (by rintro _ ⟨z, rfl⟩; rw [← hV, Scheme.Hom.comp_apply]; exact ⟨_, rfl⟩) (fr y)).1
  let s (y : B.X) : Γ(B.X, W y) := σb _ _ (v₀ y) (w₀ y)
  have key (y) (p : GlobalTheory.CxPts B.str e) (hp : p ∈ ptsIn B.str e (W y)) :
      ∃ v w, FrY Y V τ e (a y p).1.1 v w ∧ Match τ (a y p).2 v w ∧ σb ℂ (a y p).1.1 v w = ev B.str e _ (s y) p := by
    have hx : (a y p).1.1 = spMap (evHom hp) ≫ (show Sp Γ(B.X, W y) ⟶ B.X from (hW y).fromSpec) ≫ io := by
      have : spMap (evHom hp) ≫ (show Sp Γ(B.X, W y) ⟶ B.X from (hW y).fromSpec) = p.1 :=
        GlobalTheory.Points.specMap_valMap_fromSpec (hW y) p.1 hp
      rw [ha, ← Category.assoc, this]
    obtain ⟨v, w, h₁, h₂, h₃⟩ := exists_pull (evHom hp) (hf₀ y) hx
    have hj : (evHom hp).comp (φ y) = e :=
      congrArg CommRingCat.Hom.hom (Spec.map_injective (h₁.1.symm.trans (a y p).1.2))
    refine ⟨v, w, by have := h₁; rwa [hj] at this, ⟨fun i k hik => ?_, fun i k hik => ?_⟩, ?_⟩
    · rw [h₂, (hm₀ y).1 i k hik, hv y p hp]
    · rw [h₃, (hm₀ y).2 i k hik, hv y p hp]
    · rw [ev_eq hp]
      exact hσ.1 _ ℂ (evHom hp) (Chart.dualMapR (evHom hp)) _ _ _ _ _ _ v w
        (fun a => by ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
        (by ext <;> simp [Chart.dualMapR]) (hf₀ y) h₁ hx h₂ h₃
  have hA : Dense (ptsIn B.str e (io ⁻¹ᵁ (genBd Y).compl)) := by
    refine (GlobalTheory.T.complexPoints_nonempty_dense_variety c.F B e).2 _ ?_
    obtain ⟨_, ⟨z, rfl⟩, hz⟩ := Y.jQ_dense.inter_open_nonempty _ io.isOpenEmbedding.isOpen_range
      (Set.range_nonempty _)
    exact ⟨z, fun hb => hb hz⟩
  let R := AnRead.all B.str e B.dim
  choose u hu he using fun y => exists_extension R io hA (isOpen_ptsIn (W y)) (fun z _ => ha y z) (hf y)
    (h := fun a => (h a)⁻¹) (fun V _ _ _ B a hB ha hi => (hh.2.2.1 V B a hB ha hi).inv fun b hb => hh.1 _ (hi b hb))
    (logGrowth_inv hh.2.2.2)
  let pt (z : GlobalTheory.CxPts B.str e) : B.X := z.1 (IsLocalRing.closedPoint ℂ)
  have hpt (z : GlobalTheory.CxPts B.str e) : z ∈ ptsIn B.str e (W (pt z)) := mem_ptsIn.2 (hy _)
  obtain ⟨q, hq, hqe⟩ := exists_holoOn_of_local (R := R) hA (S := Set.univ)
    (u := fun z => ev B.str e _ (s (pt z)) z * (h (a (pt z) z))⁻¹) fun y _ =>
    ⟨ptsIn B.str e (W (pt y)), fun z => ev B.str e _ (s (pt y)) z * u (pt y) z, isOpen_ptsIn _, hpt y,
      (R.holoOn_ev _ _).mul (hu _), fun z hz => by
        obtain ⟨v, w, h₁, h₂, h₃⟩ := key _ z hz.1
        obtain ⟨v', w', h₁', h₂', h₃'⟩ := key _ z (hpt z)
        have := quot_eq hτ hh hσ _ _ ((ha _ _).trans (ha _ _).symm) ((inner_iff (ha _ z)).2 hz.2) h₁ h₂ h₁' h₂'
        rw [h₃, h₃'] at this
        simp only [he _ hz]
        exact this⟩
  obtain ⟨κ, hκ⟩ := GlobalTheory.ConstFn.holoOn_univ_const c.F B e R q hq
  refine ⟨κ, fun b v w hi hb hm => ?_⟩
  have hr : Set.range b.1.1 ⊆ Set.range io := hV ▸ hb.2.1
  have hl : IsOpenImmersion.lift io b.1.1 hr ≫ io = b.1.1 := IsOpenImmersion.lift_fac _ _ _
  let z : GlobalTheory.CxPts B.str e := ⟨IsOpenImmersion.lift io b.1.1 hr, by rw [← hstr, ← Category.assoc, hl]; exact b.1.2⟩
  obtain ⟨v', w', h₁', h₂', h₃'⟩ := key _ z (hpt z)
  have e₁ := quot_eq hτ hh hσ b _ (hl.symm.trans (ha _ z).symm) hi hb hm h₁' h₂'
  have e₂ := hqe (x := z) ⟨trivial, (inner_iff hl.symm).1 hi⟩
  rw [hκ] at e₂
  rw [h₃'] at e₁
  rw [e₂]
  exact (mul_inv_eq_iff_eq_mul₀ (hh.1 b hi)).1 e₁

end GlobalTheory.DetLine.HorConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantFunctionNormalCompactificationStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_constant_function_normal_compactification : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (V : (gen Y).Opens), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme (gen Y) → IsClosed (U : Set (Xo.XF c)) → GeometricallyConnected (U.ι ≫ toF Xo c) → (V : Set (gen Y)) = compactOf Y U → ∀ f : Γ(gen Y, V), ∃ a : c.F, f = ReciprocityTheory.ChartRestriction.G.Geo.Tor.constFn (genStr Y) V a := by
  first | exact @GlobalTheory.CptConst.exists_eq_constFn_compactOf | exact GlobalTheory.CptConst.exists_eq_constFn_compactOf | (intros; apply GlobalTheory.CptConst.exists_eq_constFn_compactOf <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinateFunctionalsFunctionFieldExtensio
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FunctionFieldCoords

theorem map_genericPoint_eq {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y)
    [IsDominant f] : f (genericPoint X) = genericPoint Y := by
  have := (genericPoint_spec X).image f.continuous
  rw [Set.image_univ, f.denseRange.closure_range] at this
  exact this.eq (genericPoint_spec Y)

theorem functionFieldMap_finite {M W : Scheme.{0}} [IsIntegral M] [IsIntegral W] (f : M ⟶ W)
    [IsDominant f] (h : f.residueDegree (genericPoint M) ≠ 0) : (functionFieldMap f).Finite := by
  have hfin : (f.residueFieldMap (genericPoint M)).hom.Finite := by
    letI := (f.residueFieldMap (genericPoint M)).hom.toAlgebra
    change Module.finrank (W.residueField (f (genericPoint M))) (M.residueField (genericPoint M)) ≠ 0
      at h
    exact Module.finite_of_finrank_pos (Nat.pos_of_ne_zero h)
  have hsurj : ∀ {x : W} (h : x ⤳ genericPoint W), x = genericPoint W →
      Function.Surjective (W.presheaf.stalkSpecializes h).hom := by
    rintro x h rfl
    rw [TopCat.Presheaf.stalkSpecializes_refl]
    exact fun a => ⟨a, rfl⟩
  have hinj : Function.Injective (M.residue (genericPoint M)).hom :=
    RingHom.injective (f := ((M.residue (genericPoint M)).hom : M.functionField →+* _))
  let e := RingEquiv.ofBijective (M.residue (genericPoint M)).hom
    ⟨hinj, M.residue_surjective _⟩
  have key : ∀ (hs : f (genericPoint M) ⤳ genericPoint W),
      ((W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom).Finite := by
    intro hs
    have hc : (M.residue (genericPoint M)).hom.comp
        (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom =
        (f.residueFieldMap (genericPoint M)).hom.comp
          ((W.residue _).hom.comp (W.presheaf.stalkSpecializes hs).hom) := by
      rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, ← CommRingCat.hom_comp,
        Category.assoc, Category.assoc, Scheme.residue_residueFieldMap]
    have h1 : ((M.residue (genericPoint M)).hom.comp
        (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom).Finite := by
      rw [hc]
      exact hfin.comp (RingHom.Finite.of_surjective _
        ((W.residue_surjective _).comp (hsurj hs (map_genericPoint_eq f))))
    have h2 : (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom =
        (e.symm : _ →+* _).comp ((M.residue (genericPoint M)).hom.comp
          (W.presheaf.stalkSpecializes hs ≫ f.stalkMap (genericPoint M)).hom) := by
      ext a
      exact (e.symm_apply_apply _).symm
    rw [h2]
    exact (RingHom.Finite.of_surjective _ e.symm.surjective).comp h1
  exact key _

end GlobalTheory.FunctionFieldCoords

theorem GlobalTheory.functionField_coords : ∀ (M W : Scheme.{0}) [IsIntegral M] [IsIntegral W] (f : M ⟶ W) [IsDominant f], f.residueDegree (genericPoint M) ≠ 0 → ∃ (r : ℕ) (co : Fin r → (M.functionField →+ W.functionField)), (∀ j c x, co j (GlobalTheory.functionFieldMap f c * x) = c * co j x) ∧ ∀ x, (∀ j, co j x = 0) → x = 0 := by
  intro M W _ _ f _ h
  letI := (functionFieldMap f).toAlgebra
  haveI : Module.Finite W.functionField M.functionField :=
    GlobalTheory.FunctionFieldCoords.functionFieldMap_finite f h
  let b := Module.finBasis W.functionField M.functionField
  refine ⟨Module.finrank W.functionField M.functionField, fun j => (b.coord j).toAddMonoidHom,
    fun j c x => ?_, fun x hx => ?_⟩
  · change b.coord j (c • x) = c * b.coord j x
    rw [map_smul, smul_eq_mul]
  · exact b.ext_elem fun i => by simpa using hx i
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoordinatesExtendingRegularParametersStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_coordinates_extending_regular_parameters : ∀ (F A R : Type) [Field F] [CharZero F] [CommRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsRegularLocalRing R] [Algebra F A] [Algebra A R] [Algebra F R] [IsScalarTower F A R] (P : Ideal A) [P.IsPrime] [IsLocalization.AtPrime R P] (n : ℕ) [Module.Free R Ω[R⁄F]] [Module.Finite R Ω[R⁄F]], Module.finrank R Ω[R⁄F] = n → ∀ (m : ℕ) (a : Fin m → A), ReciprocityTheory.AnForm.R.FinalTheorems.Rsp R m (fun i => algebraMap A R (a i)) → ∃ (x : Fin n → A) (e : Fin m ↪ Fin n), (∀ j, x (e j) = a j) ∧ ∃ bs : Module.Basis (Fin n) R Ω[R⁄F], ∀ i, bs i = KaehlerDifferential.D F R (algebraMap A R (x i)) := by
  first | exact @GlobalTheory.exists_coords_extending_regularParams | exact GlobalTheory.exists_coords_extending_regularParams | (intros; apply GlobalTheory.exists_coords_extending_regularParams <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameCoordsBasisEigenLatticeSpanStatement
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_frameCoords_basis_eigenLattice_span : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (ρ' : E →+* ℂ) (t : 𝓞 E →+* 𝓞 K), (∀ a, ((t a : 𝓞 K) : K) = algebraMap c.F K (embK c ρ' a)) → ∃ v : Fin (Dw.mult ρ') → Fin F.P₀.g → K, GlobalTheory.PtDeg.FrameCoord y m1 m2 F ρ' v ∧ LinearIndependent K v ∧ Submodule.span K (Set.range v) = Submodule.span K (F.eigLat B.t.act t : Set (Fin F.P₀.g → K)) := by
  first | exact @GlobalTheory.PtDeg.exists_frameCoord_basis | exact GlobalTheory.PtDeg.exists_frameCoord_basis | (intros; apply GlobalTheory.PtDeg.exists_frameCoord_basis <;> assumption)
end

